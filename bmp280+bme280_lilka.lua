--[[
    BME280 / BMP280 — датчик температури, тиску (та вологості для BME280) для Lilka
    Підключення: VCC=3.3V, GND=GND, SCL=пін14, SDA=пін13

    Автодетекція: код сам визначає який датчик підключено.
      BMP280 (chip ID 0x56/0x57/0x58): температура + тиск
      BME280 (chip ID 0x60):           температура + тиск + вологість

    Режим: forced mode, вимір раз на 60 секунд (мінімальний самонагрів)
    osrs_t=x2, osrs_p=x4, osrs_h=x1 (BME280), IIR filter=OFF
    Даташит BME280 стор.19 табл.7: weather monitoring - forced, filter OFF

    Головний екран:
      A - журнал   B - вихід   D - графік

    Debug (список):
      UP/DOWN - прокрутка   A - деталі виміру   B - назад

    Debug (деталі):
      B - назад до списку
]]

local SCL = 14
local SDA = 13
local BME280_ADDR   = 0x76
local AUTO_INTERVAL = 60
local MAX_HISTORY   = 100
local LIST_VISIBLE  = 7

local BLACK  = display.color565(0,   0,   0)
local WHITE  = display.color565(255, 255, 255)
local GREEN  = display.color565(0,   200, 80)
local YELLOW = display.color565(255, 220, 0)
local CYAN   = display.color565(0,   220, 220)
local GRAY   = display.color565(140, 140, 140)
local RED    = display.color565(255, 60,  60)
local BLUE   = display.color565(80,  140, 255)
local DKGRAY = display.color565(50,  50,  50)

local error_msg   = nil
local dig_T = {}
local dig_P = {}
local dig_H = {}          -- калібрування вологості (тільки BME280)
local initialized = false
local sensor_type = "BMP280"  -- "BMP280" або "BME280", визначається при ініціалізації

local current = {
    temp_raw=nil, press_pa=nil, hum_pct=nil,
    adc_T=nil, adc_P=nil, adc_H=nil,
    var1_T=nil, var2_T=nil, t_fine=nil,
}

local auto_timer    = AUTO_INTERVAL
local measure_count = 0
local uptime        = 0
local history       = {}
local screen        = "main"
local dbg_sel       = 1
local dbg_scroll    = 1
local GRAPH_SIZE  = 10
local graph_page  = 0
local graph_cur   = 0

-- Лог ініціалізації
local log_lines = {}
local function log(msg)
    table.insert(log_lines, msg)
    if #log_lines > 10 then table.remove(log_lines, 1) end
    display.fill_screen(BLACK)
    display.set_font("5x7")
    display.set_text_color(CYAN)
    display.set_cursor(4, 12)
    display.print("Ініціалізація датчика...")
    display.set_text_color(WHITE)
    for i, line in ipairs(log_lines) do
        display.set_cursor(4, 12 + i * 14)
        display.print(line)
    end
    display.queue_draw()
end

-- I2C
local function i2c_write_byte(byte)
    for i = 7, 0, -1 do
        gpio.write(SDA, (byte >> i) & 1)
        gpio.write(SCL, gpio.HIGH)
        gpio.write(SCL, gpio.LOW)
    end
    gpio.set_mode(SDA, gpio.INPUT)
    gpio.write(SCL, gpio.HIGH)
    local ack = gpio.read(SDA)
    gpio.write(SCL, gpio.LOW)
    gpio.set_mode(SDA, gpio.OUTPUT)
    return ack == 0
end

local function i2c_read_byte(send_ack)
    local byte = 0
    gpio.set_mode(SDA, gpio.INPUT)
    for i = 7, 0, -1 do
        gpio.write(SCL, gpio.HIGH)
        byte = (byte << 1) | gpio.read(SDA)
        gpio.write(SCL, gpio.LOW)
    end
    gpio.set_mode(SDA, gpio.OUTPUT)
    gpio.write(SDA, send_ack and 0 or 1)
    gpio.write(SCL, gpio.HIGH)
    gpio.write(SCL, gpio.LOW)
    return byte
end

local function i2c_start()
    gpio.write(SDA, gpio.HIGH); gpio.write(SCL, gpio.HIGH)
    gpio.write(SDA, gpio.LOW);  gpio.write(SCL, gpio.LOW)
end

local function i2c_stop()
    gpio.write(SDA, gpio.LOW);  gpio.write(SCL, gpio.HIGH)
    gpio.write(SDA, gpio.HIGH)
end

local function i2c_read_reg(reg, count)
    i2c_start()
    if not i2c_write_byte(BME280_ADDR << 1) then return nil end
    if not i2c_write_byte(reg) then return nil end
    i2c_start()
    if not i2c_write_byte((BME280_ADDR << 1) | 1) then return nil end
    local result = {}
    for i = 1, count do result[i] = i2c_read_byte(i < count) end
    i2c_stop()
    return result
end

local function i2c_write_reg(reg, value)
    i2c_start()
    i2c_write_byte(BME280_ADDR << 1)
    i2c_write_byte(reg)
    i2c_write_byte(value)
    i2c_stop()
    util.sleep(0.01)
end

-- Допоміжні
local function read16_LE(b, o)
    return b[o] | (b[o+1] << 8)
end
local function read16_LE_s(b, o)
    local v = read16_LE(b, o)
    if v > 32767 then v = v - 65536 end
    return v
end
local function fmt_temp(raw)
    if not raw then return "---" end
    local s = ""
    if raw < 0 then s="-"; raw=-raw end
    raw = math.floor(raw)
    return string.format("%s%d.%02d", s, raw//100, raw%100)
end
local function fmt_press(pa)
    if not pa then return "---" end
    pa = math.floor(pa)
    return string.format("%d.%01d", pa//100, (pa%100)//10)
end
local function fmt_hum(pct)
    if not pct then return "---" end
    return string.format("%.1f", pct)
end
local function fmt_time(secs)
    local s = math.floor(secs)
    local h = s // 3600
    local m = (s % 3600) // 60
    local sc = s % 60
    return string.format("%02d:%02d:%02d", h, m, sc)
end

-- Ініціалізація датчика (BMP280 або BME280)
local function bmp280_init()
    log("SCL="..SCL.." SDA="..SDA)
    log("Адреса: "..string.format("0x%02X", BME280_ADDR))
    util.sleep(0.05)
    log("Читаємо chip ID...")
    local id = i2c_read_reg(0xD0, 1)
    if not id then
        log("ПОМИЛКА: немає відповіді!")
        util.sleep(2)
        error_msg = "Немає відповіді від датчика"
        return false
    end
    local chip_id = id[1]
    log("Chip ID: "..string.format("0x%02X", chip_id))
    util.sleep(0.3)

    if chip_id == 0x60 then
        sensor_type = "BME280"
        log("BME280 знайдено!")
    elseif chip_id == 0x58 or chip_id == 0x57 or chip_id == 0x56 then
        sensor_type = "BMP280"
        log("BMP280 знайдено!")
    else
        log("ПОМИЛКА: невідомий ID")
        util.sleep(2)
        error_msg = "Невірний chip ID: "..string.format("0x%02X", chip_id)
        return false
    end
    util.sleep(0.3)

    -- Читаємо калібрування температури і тиску (спільне для обох)
    log("Читаємо калібрування T/P...")
    local calib = i2c_read_reg(0x88, 24)
    if not calib then
        log("ПОМИЛКА калібрування T/P")
        util.sleep(2)
        error_msg = "Помилка читання калібрування"
        return false
    end
    dig_T[1] = read16_LE(calib, 1)
    dig_T[2] = read16_LE_s(calib, 3)
    dig_T[3] = read16_LE_s(calib, 5)
    dig_P[1] = read16_LE(calib, 7)
    for i = 2, 9 do dig_P[i] = read16_LE_s(calib, 7+(i-1)*2) end
    log("Калібрування T/P OK")

    -- Калібрування вологості — тільки для BME280
    if sensor_type == "BME280" then
        log("Читаємо калібрування H...")
        local h1 = i2c_read_reg(0xA1, 1)
        local h26 = i2c_read_reg(0xE1, 7)
        if not h1 or not h26 then
            log("ПОМИЛКА калібрування H")
            util.sleep(2)
            error_msg = "Помилка читання калібрування вологості"
            return false
        end
        -- dig_H1: unsigned byte
        dig_H[1] = h1[1]
        -- dig_H2: signed short, little-endian
        local h2 = h26[1] | (h26[2] << 8)
        if h2 > 32767 then h2 = h2 - 65536 end
        dig_H[2] = h2
        -- dig_H3: unsigned byte
        dig_H[3] = h26[3]
        -- dig_H4: signed 12-bit (0xE4[7:4|3:0] | 0xE5[3:0])
        local h4 = (h26[4] << 4) | (h26[5] & 0x0F)
        if h4 > 2047 then h4 = h4 - 4096 end
        dig_H[4] = h4
        -- dig_H5: signed 12-bit (0xE5[7:4] | 0xE6[7:0])
        local h5 = (h26[6] << 4) | (h26[5] >> 4)
        if h5 > 2047 then h5 = h5 - 4096 end
        dig_H[5] = h5
        -- dig_H6: signed byte
        local h6 = h26[7]
        if h6 > 127 then h6 = h6 - 256 end
        dig_H[6] = h6
        log("Калібрування H OK")
    end

    i2c_write_reg(0xF4, 0x00)  -- sleep mode
    log("Готово! ("..sensor_type..")")
    util.sleep(0.5)
    return true
end

-- Компенсація температури (даташит розділ 4.2.3, 32-bit integer)
-- ВАЖЛИВО: // замість >> бо Lua >> = логічний (unsigned) зсув.
-- На від'ємних проміжних значеннях >> дає хибний результат.
-- // (floor division) = арифметичний зсув для від'ємних чисел.
local function compensate_T(adc_T)
    local v1 = (((adc_T >> 3) - (dig_T[1] << 1)) * dig_T[2]) // 2048
    local v2 = (((((adc_T >> 4) - dig_T[1]) * ((adc_T >> 4) - dig_T[1])) // 4096) * dig_T[3]) // 16384
    local tf = v1 + v2
    local T  = (tf * 5 + 128) // 256
    return T, tf, v1, v2
end

-- Компенсація тиску (даташит розділ 4.2.3, 32-bit integer)
local function compensate_P(adc_P, t_fine)
    local var1 = t_fine // 2 - 64000
    local var2 = ((var1//4)*(var1//4)) // 2048 * dig_P[6]
    var2 = var2 + ((var1 * dig_P[5]) << 1)
    var2 = var2 // 4 + (dig_P[4] << 16)
    var1 = (((dig_P[3]*(((var1//4)*(var1//4))//8192))//8)+((dig_P[2]*var1)//2))//131072
    var1 = ((32768 + var1) * dig_P[1]) // 32768
    if var1 == 0 then return 0 end
    local p = ((1048576 - adc_P) - var2//4096) * 3125
    if p < 0x80000000 then
        p = (p << 1) // var1
    else
        p = (p // var1) * 2
    end
    var1 = (dig_P[9]*((p//8)*(p//8))//8192) // 4096
    var2 = (p//4 * dig_P[8]) // 8192
    p = p + (var1 + var2 + dig_P[7]) // 16
    return p
end

-- Компенсація вологості (даташит розділ 8.1, double precision)
-- Повертає вологість у %RH (float)
-- Використовуємо floating point формулу — Lilka не є 8-bit MCU,
-- тому float тут доречний і значно простіший ніж 32-bit integer варіант.
local function compensate_H(adc_H, t_fine)
    local x = t_fine - 76800.0
    x = (adc_H - (dig_H[4] * 64.0 + dig_H[5] / 16384.0 * x)) *
        (dig_H[2] / 65536.0 * (1.0 + dig_H[6] / 67108864.0 * x *
        (1.0 + dig_H[3] / 67108864.0 * x)))
    x = x * (1.0 - dig_H[1] * x / 524288.0)
    if x > 100.0 then x = 100.0 end
    if x < 0.0   then x = 0.0   end
    return x
end

-- Запуск forced mode:
--   BMP280: osrs_t=x2(010), osrs_p=x4(011), mode=01 → 0x4D
--   BME280: те саме + osrs_h=x1(001) через ctrl_hum (0xF2)
-- ВАЖЛИВО для BME280: спочатку пишемо ctrl_hum (0xF2),
-- потім ctrl_meas (0xF4) — тільки тоді ctrl_hum набуває чинності (даташит 5.4.3)
local measure_pending = false

local function bmp280_trigger()
    if sensor_type == "BME280" then
        i2c_write_reg(0xF2, 0x01)  -- ctrl_hum: osrs_h = x1
    end
    i2c_write_reg(0xF4, 0x4D)      -- forced mode: osrs_t=x2, osrs_p=x4
    measure_pending = true
end

-- Читання результатів:
--   BMP280: burst read 0xF7..0xFC (6 байт: press + temp)
--   BME280: burst read 0xF7..0xFE (8 байт: press + temp + hum)
local function bmp280_read()
    local count = (sensor_type == "BME280") and 8 or 6
    local raw = i2c_read_reg(0xF7, count)
    measure_pending = false
    if not raw then
        error_msg = "Помилка читання даних"
        return false
    end
    local adc_P = (raw[1]<<12)|(raw[2]<<4)|(raw[3]>>4)
    local adc_T = (raw[4]<<12)|(raw[5]<<4)|(raw[6]>>4)
    local T_raw, t_fine, v1, v2 = compensate_T(adc_T)
    local P_raw = compensate_P(adc_P, t_fine)
    current.temp_raw=T_raw; current.press_pa=P_raw
    current.adc_T=adc_T;   current.adc_P=adc_P
    current.var1_T=v1;      current.var2_T=v2
    current.t_fine=t_fine

    -- Вологість — тільки для BME280
    if sensor_type == "BME280" then
        local adc_H = (raw[7] << 8) | raw[8]
        current.adc_H = adc_H
        -- 0x8000 = датчик вимкнений (skipped), не компенсуємо
        if adc_H ~= 0x8000 then
            current.hum_pct = compensate_H(adc_H, t_fine)
        else
            current.hum_pct = nil
        end
    else
        current.hum_pct = nil
        current.adc_H   = nil
    end

    error_msg = nil
    return true
end

local function do_measure()
    if bmp280_read() then
        measure_count = measure_count + 1
        local e = {
            n=measure_count, time_s = os.date("%H:%M"),
            temp_raw=current.temp_raw, press_pa=current.press_pa,
            hum_pct=current.hum_pct,
            adc_T=current.adc_T,      adc_P=current.adc_P,
            adc_H=current.adc_H,
            var1_T=current.var1_T,    var2_T=current.var2_T,
            t_fine=current.t_fine,
        }
        table.insert(history, 1, e)
        if #history > MAX_HISTORY then table.remove(history, #history) end
        if graph_page == 0 then
            local _a = GRAPH_SIZE - 1; local _b = #history - 1
            graph_cur = _a < _b and _a or _b
        end
        auto_timer = AUTO_INTERVAL
        return true
    end
    return false
end

function lilka.init()
    gpio.set_mode(SCL, gpio.OUTPUT)
    gpio.set_mode(SDA, gpio.OUTPUT)
    gpio.write(SCL, gpio.HIGH)
    gpio.write(SDA, gpio.HIGH)
    util.sleep(0.01)
    initialized = bmp280_init()
    if initialized then bmp280_trigger() end
end

function lilka.update(delta)
    uptime = uptime + delta
    if initialized and not error_msg then
        if measure_pending then
            do_measure()
        else
            auto_timer = auto_timer - delta
            if auto_timer <= 0 then
                bmp280_trigger()
            end
        end
    end

    local btn = controller.get_state()

    if screen == "main" then
        if btn.b.just_pressed then util.exit() end
        if btn.a.just_pressed then
            screen="debug_list"; dbg_sel=1; dbg_scroll=1
        end
        if btn.d.just_pressed then
            screen="graph"; graph_page=0; graph_cur=0
        end

    elseif screen == "graph" then
        if btn.b.just_pressed then screen = "main" end

        if btn.right.just_pressed then
            if graph_cur > 0 then
                graph_cur = graph_cur - 1
            elseif graph_page > 0 then
                graph_page = graph_page - 1
                graph_cur  = GRAPH_SIZE - 1
            end
        end

        if btn.left.just_pressed then
            local total_pages = (#history - 1) // GRAPH_SIZE
            if graph_cur < GRAPH_SIZE - 1 then
                local page_start = graph_page * GRAPH_SIZE
                local next_idx   = page_start + graph_cur + 1
                if next_idx < #history then
                    graph_cur = graph_cur + 1
                end
            elseif graph_page < total_pages then
                graph_page = graph_page + 1
                graph_cur  = 0
            end
        end

    elseif screen == "debug_list" then
        if btn.b.just_pressed then screen = "main" end
        if btn.a.just_pressed and #history > 0 then screen = "debug_detail" end
        if btn.up.just_pressed and dbg_sel > 1 then
            dbg_sel = dbg_sel - 1
            if dbg_sel < dbg_scroll then dbg_scroll = dbg_sel end
        end
        if btn.down.just_pressed and dbg_sel < #history then
            dbg_sel = dbg_sel + 1
            if dbg_sel >= dbg_scroll + LIST_VISIBLE then
                dbg_scroll = dbg_sel - LIST_VISIBLE + 1
            end
        end

    elseif screen == "debug_detail" then
        if btn.b.just_pressed then screen = "debug_list" end
    end
end

-- Малювання кнопки
local function draw_btn(cx, cy, label, text, color)
    display.fill_circle(cx, cy, 10, color or GREEN)
    display.set_font("6x13")
    display.set_text_color(BLACK)
    display.set_cursor(cx-3, cy+5)
    display.print(label)
    display.set_font("7x13")
    display.set_text_color(WHITE)
    display.set_cursor(cx+14, cy+4)
    display.print(text)
end

-- Головний екран
local function draw_main()
    local W = display.width
    local H = display.height
    display.fill_screen(BLACK)
    if error_msg then
        display.set_font("6x13")
        display.set_text_color(RED)
        display.set_cursor(10, H//2-10)
        display.print("Помилка:")
        display.set_text_color(YELLOW)
        display.set_cursor(10, H//2+10)
        display.print(error_msg)
    else
        display.set_font("5x7")
        display.set_text_color(GRAY)
        display.set_cursor(20, 18)
        display.print(sensor_type.."  вимір #"..measure_count)
        display.set_cursor(20, 28)
        display.print("час: "..fmt_time(uptime))
        display.set_cursor(20, 38)
        display.print("наст.авто: "..math.floor(auto_timer + 0.5).." с")

        -- Температура
        display.set_font("10x20")
        display.set_text_color(YELLOW)
        display.set_cursor(20, 60)
        display.print("Температура")
        display.set_font("10x20")
        display.set_text_size(3)
        display.set_text_color(WHITE)
        display.set_cursor(20, 110)
        display.print(fmt_temp(current.temp_raw).." C")
        display.set_text_size(1)

        -- Тиск
        display.set_font("10x20")
        display.set_text_color(CYAN)
        display.set_cursor(20, 150)
        display.print("Тиск")
        display.set_font("10x20")
        display.set_text_color(WHITE)
        display.set_cursor(20, 170)
        display.print(fmt_press(current.press_pa).." hPa")

        -- Вологість — тільки для BME280
        if sensor_type == "BME280" then
            display.set_font("10x20")
            display.set_text_color(BLUE)
            display.set_cursor(160, 150)
            display.print("Вологість")
            display.set_font("10x20")
            display.set_text_color(WHITE)
            display.set_cursor(160, 170)
            display.print(fmt_hum(current.hum_pct).." %")
        end
    end
    draw_btn(30,         H-20, "D", "Графік")
    draw_btn(W//2 - 20,  H-20, "B", "Вихід", RED)
    draw_btn(W//2 + 60,  H-20, "A", "Журнал", YELLOW)
end

-- Debug: список
local function draw_debug_list()
    local W = display.width
    local H = display.height
    display.fill_screen(BLACK)
    display.set_font("6x13")
    display.set_text_color(CYAN)
    display.set_cursor(25, 20)
    display.print("ВИМІРИ ("..#history..")  UP/DN A=деталі B=вихід")
    if #history == 0 then
        display.set_text_color(GRAY)
        display.set_cursor(4, 50)
        display.print("Немає вимірів")
    else
        for i = 0, LIST_VISIBLE-1 do
            local idx = dbg_scroll + i
            if idx > #history then break end
            local e = history[idx]
            local y = 40 + i * 18
            if idx == dbg_sel then
                display.fill_rect(0, y-1, W, 17, DKGRAY)
                display.set_text_color(YELLOW)
            else
                display.set_text_color(WHITE)
            end
            display.set_font("7x13")
            display.set_cursor(18, y+5)
            -- Показуємо вологість в списку якщо BME280
            if sensor_type == "BME280" then
                display.print(string.format("#%-3d %s %s C %s%%",
                    e.n, e.time_s, fmt_temp(e.temp_raw), fmt_hum(e.hum_pct)))
            else
                display.print(string.format("#%-3d %s  %s C",
                    e.n, e.time_s, fmt_temp(e.temp_raw)))
            end
        end
    end
    draw_btn(30,         H-20, "A", "Деталі")
    draw_btn(W//2 - 20,  H-20, "B", "Назад", RED)
end

-- Debug: деталі виміру
local function draw_debug_detail()
    local W = display.width
    local H = display.height
    display.fill_screen(BLACK)
    if dbg_sel < 1 or dbg_sel > #history then
        screen = "debug_list"; return
    end
    local e = history[dbg_sel]
    display.set_font("5x7")
    display.set_text_color(CYAN)
    display.set_cursor(4, 30)
    display.print("Вимір #"..e.n.."  "..e.time_s.."  ("..sensor_type..")")
    local rows = {
        {"adc_T",  e.adc_T,    "сирі дані T"},
        {"adc_P",  e.adc_P,    "сирі дані P"},
        {"dig_T1", dig_T[1],   "калібр T1"},
        {"dig_T2", dig_T[2],   "калібр T2"},
        {"dig_T3", dig_T[3],   "калібр T3"},
        {"var1",   e.var1_T,   "пром. T (крок 1)"},
        {"var2",   e.var2_T,   "пром. T (крок 2)"},
        {"t_fine", e.t_fine,   "точна T внутр."},
        {"T_raw",  e.temp_raw, "T в 0.01 C"},
        {"Темп.",  nil,        fmt_temp(e.temp_raw).." C"},
        {"P(Pa)",  e.press_pa, "тиск Па"},
        {"Тиск",   nil,        fmt_press(e.press_pa).." hPa"},
    }
    -- Додаємо рядки вологості для BME280
    if sensor_type == "BME280" then
        table.insert(rows, {"adc_H",  e.adc_H,   "сирі дані H"})
        table.insert(rows, {"Волог.", nil,        fmt_hum(e.hum_pct).." %RH"})
    end
    local y = 65
    for _, row in ipairs(rows) do
        if y > H-25 then break end
        display.set_cursor(4, y)
        display.set_text_color(GRAY)
        display.print(string.format("%-7s", row[1]))
        if row[2] ~= nil then
            display.set_text_color(WHITE)
            display.print(string.format("%d", math.floor(row[2])))
        else
            display.set_text_color(YELLOW)
            display.print(row[3])
        end
        y = y + 13
    end
    display.set_font("5x7")
    display.set_text_color(RED)
    display.set_cursor(4, H-10)
    display.print("B = назад до списку")
end

-- Графік температури
local function draw_graph()
    local W = display.width
    local H = display.height
    display.fill_screen(BLACK)

    local GX = 30
    local GY = 20
    local GW = W - GX - 6
    local GH = H - GY - 42

    if #history < 2 then
        display.set_font("6x13")
        display.set_text_color(GRAY)
        display.set_cursor(GX, H//2)
        display.print("Потрібно мінімум 2 виміри")
        draw_btn(W//2 - 20, H-20, "B", "Назад", RED)
        return
    end

    local page_start_hi = graph_page * GRAPH_SIZE + 1
    local _a = page_start_hi + GRAPH_SIZE - 1; local _b = #history
    local page_end_hi   = _a < _b and _a or _b
    local count         = page_end_hi - page_start_hi + 1

    local t_min = history[page_start_hi].temp_raw
    local t_max = history[page_start_hi].temp_raw
    for i = page_start_hi, page_end_hi do
        local t = history[i].temp_raw
        if t < t_min then t_min = t end
        if t > t_max then t_max = t end
    end
    local t_range = t_max - t_min
    if t_range < 100 then
        t_min = t_min - 50
        t_max = t_max + 50
        t_range = 100
    end

    for step = 0, 2 do
        local gy = GY + GH * step // 2
        display.draw_line(GX, gy, GX + GW, gy, DKGRAY)
        local t_label = t_max - t_range * step // 2
        display.set_font("5x7")
        display.set_text_color(GRAY)
        display.set_cursor(0, gy - 3)
        display.print(fmt_temp(t_label))
    end

    display.draw_line(GX, GY, GX, GY + GH, GRAY)

    local step_w = GW // (GRAPH_SIZE - 1)

    local pts = {}
    for idx = 0, count - 1 do
        local hi = page_end_hi - idx
        local e  = history[hi]
        local px = GX + (count - 1 - idx) * step_w
        local py = GY + GH - (e.temp_raw - t_min) * GH // t_range
        pts[idx] = {px=px, py=py, hi=hi, e=e}
    end

    for idx = 0, count - 2 do
        local p1 = pts[idx]
        local p2 = pts[idx+1]
        display.draw_line(p1.px, p1.py,   p2.px, p2.py,   CYAN)
        display.draw_line(p1.px, p1.py-1, p2.px, p2.py-1, CYAN)
        display.draw_line(p1.px, p1.py+1, p2.px, p2.py+1, CYAN)
    end

    local cur_screen = count - 1 - graph_cur
    if cur_screen < 0 then cur_screen = 0 end
    if cur_screen >= count then cur_screen = count - 1 end

    for idx = 0, count - 1 do
        local p = pts[idx]
        if idx == cur_screen then
            display.fill_circle(p.px, p.py, 5, BLACK)
            display.fill_circle(p.px, p.py, 4, WHITE)
            display.fill_circle(p.px, p.py, 2, CYAN)
        else
            display.fill_circle(p.px, p.py, 3, BLACK)
            display.fill_circle(p.px, p.py, 2, CYAN)
        end
    end

    local cp = pts[cur_screen]
    if cp then
        -- Підпис: температура + вологість якщо BME280
        local label
        if sensor_type == "BME280" and cp.e.hum_pct then
            label = fmt_temp(cp.e.temp_raw).."C "..fmt_hum(cp.e.hum_pct).."%  "..cp.e.time_s
        else
            label = fmt_temp(cp.e.temp_raw).." C  "..cp.e.time_s
        end
        local lx = cp.px - #label * 3
        if lx < GX then lx = GX end
        if lx + #label * 6 > W then lx = W - #label * 6 end
        local ly = cp.py - 12
        if ly < GY + 4 then ly = cp.py + 8 end
        display.set_font("5x7")
        display.set_text_color(WHITE)
        display.set_cursor(lx, ly)
        display.print(label)
    end

    display.set_font("5x7")
    display.set_text_color(YELLOW)
    display.set_cursor(GX, 9)
    local _tp = (#history + GRAPH_SIZE - 1) // GRAPH_SIZE
    local total_pages = _tp > 1 and _tp or 1
    display.print("Графік  стор."..(graph_page+1).."/"..total_pages.."  #"..history[page_end_hi].n.."-#"..history[page_start_hi].n)

    display.set_text_color(GRAY)
    display.set_cursor(GX, GY + GH + 6)
    display.print(history[page_end_hi].time_s.."  "..history[page_start_hi].time_s)

    draw_btn(W//2 - 20, H-20, "B", "Назад", RED)
end

function lilka.draw()
    if screen == "main" then draw_main()
    elseif screen == "graph" then draw_graph()
    elseif screen == "debug_list" then draw_debug_list()
    elseif screen == "debug_detail" then draw_debug_detail()
    end
end
