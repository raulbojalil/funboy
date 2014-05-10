(*  
    FunBoy - A Gameboy emulator written in F#
    Copyright (C) 2014 Raúl A. Bojalil Becerra
      
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

*)

open System
open System.Windows.Forms
open System.Threading
open System.IO
open System.Text
open System.Drawing
open Microsoft.FSharp.Core.LanguagePrimitives

//TODOS:
//Windows
//Palettes
//Sprite priorities
//MBC2, MBC3, MBC5
//Sound

type CartridgeType = | RomOnly = 0uy | RomMbc1 = 0x1uy | RomMbc1Ram = 0x2uy | RomMbc1RamBatt = 0x3uy
                     | RomMbc2 = 0x5uy | RomMbc2Batt = 0x6uy | RomRam = 0x8uy | RomRamBatt = 0x9uy
                     | RomMbc3TimerBatt = 0xFuy | RomMbc3TimerRamBatt = 0x10uy | RomMbc3 = 0x11uy
                     | RomMbc3Ram = 0x12uy | RomMbc3RamBatt = 0x13uy | RomMbc5 = 0x19uy
                     | RomMbc5Ram = 0x1Auy | RomMbc5RamBatt = 0x1Buy | RomMbc5Rumble = 0x1Cuy
                     | RomMbc5RumbleSram = 0x1Duy | RomMbc5RumbleSramBatt = 0x1Euy
                              
type MbcType = | RomOnly = 0 | Mbc1 = 1 | Mbc2 = 2 | Mbc3 = 3 | Mbc5 = 4 

type DoubleBufferForm() =
    inherit Form()
    do base.SetStyle(ControlStyles.AllPaintingInWmPaint ||| ControlStyles.UserPaint ||| ControlStyles.DoubleBuffer, true)

let form = new DoubleBufferForm()

let SCREEN_WIDTH, SCREEN_HEIGHT, SCALE = 160, 144, 2

let mutable IME = false //INTERRUPT MASTER ENABLE
let VBLANK_INT,LCD_STATUS_INT,TIMEROF_INT,P10_P13_INT = 0x0040us,0x0048us,0x0058us,0x0060us //INTERRUPT ADDRESSES
let VBLANK_INT_BIT,LCD_STATUS_INT_BIT,TIMEROF_INT_BIT,P10_P13_INT_BIT = 0,1,2,4 //INTERRUPT BITS (IF, IE)

let ROM0 = (0us, 0x3FFFus) //ROM 0 (16 KB)
let ROM1 = (0x4000us, 0x7FFFus) //ROM 1 (16 KB)
let VRAM = (0x8000us,0x9FFFus) //VIDEO RAM (TILE PATTERN TABLES 0&1, BG_TILE_MAPS 0&1) (8KB)
let SWRAMBANK = (0xA000us,0xBFFFus) //SWITCHABLE RAM BANK (8KB) 
let IRAM = (0xC000us,0xDFFFus) //INTERNAL RAM (8KB)
let ECHO = (0xE000us,0xFDFFus) //ECHO RAM OF INTERNAL RAM (8KB)
let OAM = (0xFE00us, 0xFE9Fus) //OBJECT ATTRIBUTE MEMORY (OAM)

let TILE_PATTERN_TABLE_0 = 0x8000us //$8000-$8FFF
let TILE_PATTERN_TABLE_1 = 0x8800us //$8800-$97FF
let BG_TILE_MAP_0 = 0x9800us  //$9800-$9BFF
let BG_TILE_MAP_1 = 0x9C00us  //$9C00-$9FFF

let mutable TILE_PATTERN_TABLE_SEL = TILE_PATTERN_TABLE_0
let mutable BG_TILE_MAP_SEL = BG_TILE_MAP_0
let mutable WINDOW_TILE_MAP_SEL = BG_TILE_MAP_1

let mutable A, B, C, D, E, F, H, L, SP, PC = 0x01uy,0uy,0x13uy,0uy,0xD8uy,0xB0uy,0x01uy,0x4duy,0xFFFEus,0x0100us 
let mutable ZF,NF,HF,CF = true, false, true, true //F = 1011 (0xB0)
let FF () = byte (((if ZF then 1 else 0) <<< 7) ||| ((if NF then 1 else 0) <<< 6) ||| 
                 ((if HF then 1 else 0) <<< 5) ||| ((if CF then 1 else 0) <<< 4)) ||| (F &&& 0x0Fuy) 

let mutable frameCount,fps = 0,0
let mutable unhandledCBOpcode = false
let mutable stopped = false
let mutable cycles, lcdCycles, timerCycles, timerOverflow, divCycles = 0uy, 0, 0, 0, 0
let mutable romBank, romBankOffset = 0,0x4000
let mutable ramBank, ramBankOffset = 0,0

let screen = Array.create (256*256) 0uy
let memory = Array.create (0xFFFF+1) 0uy

let P1,DIV,TAC,WY,WX = 0xFF00us,0xFF04us,0xFF07us,0xFF4Aus,0xFF4Bus 
let LCDC,STAT,SCROLLY,SCROLLX = 0xFF40us, 0xFF41us, 0xFF42us, 0xFF43us 
let LY,LYC,DMA = 0xFF44us, 0xFF45us, 0xFF46us
let BGP,OBP0,OBP1 = 0xFF47us, 0xFF48us, 0xFF49us
let IF,IE = 0xFF0Fus, 0xFFFFus
let TIMA,TMA = 0xFF05us,0xFF06us
let TAC_TIMER_STOP_BIT = 2

let STAT_MODE_00_HBLANK,STAT_MODE_01_VBLANK,STAT_MODE_10_OAM,STAT_MODE_11_OAM_RAM = 0b00uy,0b01uy,0b10uy,0b11uy
let STAT_MODE_00_BIT,STAT_MODE_01_BIT,STAT_MODE_10_BIT,STAT_LY_LYC_BIT = 3,4,5,6 

let mutable P14, P15 = 0xEFuy,0xDFuy //JOYPAD OUT PORTS

//DEFAULT VALUES
memory.[int LCDC] <-    0x91uy ; memory.[int STAT] <- STAT_MODE_10_OAM ; memory.[int SCROLLX] <- 0x0uy
memory.[int SCROLLY] <- 0x0uy  ; memory.[int LY] <-   0x0uy            ; memory.[int LYC] <-     0x0uy 
memory.[int IE] <- 0x0uy       

let mutable rom = [|0uy|]
let openRomDialog = new OpenFileDialog()
openRomDialog.Title <- "Select Game Boy ROM" 
openRomDialog.Filter <- "Gameboy ROM Files|*.gb|All files|*.*"
if openRomDialog.ShowDialog() = DialogResult.OK then
    rom <- File.ReadAllBytes(openRomDialog.FileName)
else Environment.Exit(1)

//let mutable rom = File.ReadAllBytes("I:\\GBROMS\\abc.gb")
if rom.Length > int (snd ROM1+1us) then
    rom.[0..int (snd ROM1)].CopyTo(memory,0) //Greater than 32KB ROMs
else
    rom.CopyTo(memory,0) //32kB ROMs fit entirely in memory (0..0x8000)
 
let cartridgeType = EnumOfValue<byte, CartridgeType>(memory.[0x0147])
if not (CartridgeType.IsDefined(typeof<CartridgeType>, cartridgeType)) then
    MessageBox.Show(String.Format("The cartridge type 0x{0:X} is not supported", cartridgeType))
    Environment.Exit(1)

let mbcType = match cartridgeType with
              | CartridgeType.RomMbc1 | CartridgeType.RomMbc1Ram | CartridgeType.RomMbc1RamBatt  -> MbcType.Mbc1
              | CartridgeType.RomMbc2 | CartridgeType.RomMbc2Batt  -> MbcType.Mbc2
              | CartridgeType.RomMbc3TimerBatt | CartridgeType.RomMbc3TimerRamBatt | CartridgeType.RomMbc3 | CartridgeType.RomMbc3Ram | CartridgeType.RomMbc3RamBatt -> MbcType.Mbc3
              | CartridgeType.RomMbc5 | CartridgeType.RomMbc5Ram | CartridgeType.RomMbc5RamBatt | CartridgeType.RomMbc5Rumble | CartridgeType.RomMbc5RumbleSram | CartridgeType.RomMbc5RumbleSramBatt -> MbcType.Mbc5
              | _ -> MbcType.RomOnly

if mbcType = MbcType.Mbc2 || mbcType = MbcType.Mbc3 || mbcType =  MbcType.Mbc5 then
    MessageBox.Show(String.Format("This cartridge MBC is not implemented yet", cartridgeType))
    Environment.Exit(1)

let hasExternalRam = match cartridgeType with
                     | CartridgeType.RomMbc1Ram | CartridgeType.RomMbc1RamBatt | CartridgeType.RomRam | CartridgeType.RomRamBatt | CartridgeType.RomMbc3TimerRamBatt | CartridgeType.RomMbc3Ram | CartridgeType.RomMbc3RamBatt | CartridgeType.RomMbc5Ram | CartridgeType.RomMbc5RamBatt -> true
                     | _ -> false

let hasBattery = match cartridgeType with
                 | CartridgeType.RomMbc1RamBatt | CartridgeType.RomMbc2Batt | CartridgeType.RomRamBatt | CartridgeType.RomMbc3TimerBatt | CartridgeType.RomMbc3TimerRamBatt | CartridgeType.RomMbc3RamBatt | CartridgeType.RomMbc5RamBatt | CartridgeType.RomMbc5RumbleSramBatt -> true
                 | _ -> false

let mutable mbc1RamMode = false
let mutable externalRamEnabled = false

let opcodeHandlers = Array.create 0x100 (fun () -> 0uy)
let CBopcodeHandlers = Array.create 0x100 (fun () -> 0uy)

let writeAddress (address:uint16, data:byte) = 
    match address with
    //Writing to ROM space (ROM0&ROM1)
    | address when address <= snd ROM1 -> if mbcType <> MbcType.RomOnly || hasExternalRam then 
                                                match address with
                                                //0000 - 1FFF Enable external RAM (if XXXX1010 (0x0A))
                                                | address when address <= 0x1FFFus -> externalRamEnabled <- if ((data&&&0x0Fuy) = 0x0Auy) then true else false
                                                //2000 - 3FFF Switch ROM Banks (MBC1: XXXBBBBB (0x1F), MBC3: XBBBBBBB (0x7F) )
                                                | address when address >= 0x2000us && address <= 0x3FFFus ->  if mbcType = MbcType.Mbc1 then
                                                                                                                  romBank <- romBank &&& 0x60
                                                                                                                  let mutable temp = int (data &&& 0x1Fuy)
                                                                                                                  if temp = 0 then temp <- 1
                                                                                                                  romBank <- romBank ||| temp
                                                                                                                  romBankOffset <- romBank * 0x4000
                                                                                                              else 
                                                                                                                  romBank <- int data  
                                                                                                                  if romBank = 0 then romBank <- 1
                                                                                                                  romBankOffset <- romBank * 0x4000                                                                                                                               
                                                //4000 - 5FFF Switch ROM Bank set / RAM Bank (MBC1)
                                                | address when address >= 0x4000us && address <= 0x5FFFus -> if mbcType = MbcType.Mbc1 then
                                                                                                                 if mbc1RamMode then 
                                                                                                                    ramBank <- int (data &&& 0b11uy)
                                                                                                                    ramBankOffset <- ramBank * 0x2000
                                                                                                                 else
                                                                                                                    romBank <- romBank &&& 0x1F
                                                                                                                    romBank <- romBank ||| (((int data &&& 0b11))<<<5)
                                                                                                                    romBankOffset <- romBank * 0x4000
                                                                                                              else 
                                                                                                                 let mutable temp = int (data &&& 0x0Fuy)
                                                                                                                 if temp < 4 then 
                                                                                                                    ramBank <- temp
                                                                                                                    mbc1RamMode <- true
                                                                                                                 else if temp > 7 && temp < 0xD then
                                                                                                                    ramBank <- temp
                                                                                                                    mbc1RamMode <- false                                                                                                                                                                        //romBankOffset <- uint16 (data) * 0x4000us     
                                                //6000 - 7FFF ROM(0) or RAM(1) Mode (MBC1), 
                                                | address when address >= 0x6000us && address <= 0x7FFFus -> if mbcType = MbcType.Mbc1 then 
                                                                                                                mbc1RamMode <- if (data &&& 1uy) = 1uy then true else false
                                                                                                             else MessageBox.Show("TODO") ; () 
               
    //Writing to SWRAMBANK
    | address when address >= (fst SWRAMBANK) && 
                   address <= (snd SWRAMBANK) ->  if (hasExternalRam && externalRamEnabled) then
                                                     rom.[int address + int ramBankOffset] <- data
                                                  if not hasExternalRam then 
                                                     memory.[int address] <- data
                                                  //if hasExternalRam && hasBattery then //TODO:
                                                     //File.WriteAllBytes("test.sav", rom.[int (fst SWRAMBANK)..(int (snd SWRAMBANK)])
                                               
    | address when address = P1 -> match ((data &&& 0b110000uy) >>> 4) with //bits 4 (P14 out port) & 5 (P15 out port)
                                   | 0b00uy -> memory.[int address] <- P14 &&& P15
                                   | 0b01uy -> memory.[int address] <- P15
                                   | 0b10uy -> memory.[int address] <- P14
                                   | 0b11uy -> memory.[int address] <- 0xFFuy 
    
    | address when address = LY -> memory.[int address] <- 0uy
    | address when address = TAC -> memory.[int address] <- data
                                    match data &&& 0b11uy with
                                   | 0b00uy -> timerOverflow <- 0x0400 //4.096 KHz
                                   | 0b01uy -> timerOverflow <- 0x0010 //262.144 Khz
                                   | 0b10uy -> timerOverflow <- 0x0040 //65.536 KHz
                                   | 0b11uy -> timerOverflow <- 0x0100 //16.384 KHz 
                                          
    | address when address = IF -> memory.[int address] <- data &&& 0x1Fuy
    | address when address = IE -> memory.[int address] <- data &&& 0x1Fuy
    | address when address = DMA -> let mutable dmaAddress = uint16 data <<< 8
                                    for oamAddress in [fst OAM..snd OAM] do
                                        memory.[int oamAddress] <- memory.[int dmaAddress]
                                        dmaAddress <- dmaAddress+1us
    | address when address = DIV -> memory.[int address] <- 0uy
    | address when address = BGP -> memory.[int address] <- data //TODO: BGP
    | address when address = OBP0 -> memory.[int address] <- data //TODO: OBP0
    | address when address = OBP1 -> memory.[int address] <- data //TODO: OBP1
    | address when address = LCDC -> if (data >>> 7) <> (memory.[int address] >>> 7) then
                                        lcdCycles <- 0
                                        memory.[int LY] <- 0uy
                                        //if memory.[int LYC] = memory.[int LY] then memory.[int STAT] <- memory.[int STAT] ||| 0b100uy else memory.[int STAT] <- memory.[int STAT] &&& ~~~(0b100uy)
                                        //memory.[int STAT] <- (memory.[int STAT] &&& 0xFCuy) ||| 0b10uy //->OAM
                                     memory.[int address] <- data
                                     BG_TILE_MAP_SEL <- if data &&& (1uy <<< 3) = 0uy then BG_TILE_MAP_0 else BG_TILE_MAP_1 
                                     TILE_PATTERN_TABLE_SEL <- if data &&& (1uy <<< 4) > 0uy then TILE_PATTERN_TABLE_0 else TILE_PATTERN_TABLE_1 
                                     WINDOW_TILE_MAP_SEL <- if data &&& (1uy <<< 6) = 0uy then BG_TILE_MAP_0 else BG_TILE_MAP_1                                       
    | address when (address >= fst ECHO && address <= snd ECHO) -> memory.[int address] <- data
                                                                   memory.[int address - 0x2000] <- data                                                    
    | address when (address >= fst IRAM && address <= snd IRAM) -> memory.[int address] <- data
                                                                   if address < 0xDE00us then memory.[int address + 0x2000] <- data
    | _ -> memory.[int address] <- data 

let writeAddress_2 (msb:byte, lsb: byte, data:byte) = writeAddress((uint16 msb <<< 8) ||| uint16 lsb, data)
let writeAddress16 (address:uint16, data:uint16) = writeAddress(address, byte (data &&& 0xFF00us >>> 8)); writeAddress(address+1us, byte (data &&& 0xFFus))
let writeAddress16_2 (addressmsb:byte, addresslsb:byte, data:uint16) = writeAddress16(uint16 addressmsb <<< 8 ||| uint16 addresslsb, data)
let writeAddress16_2_2 (addressmsb:byte, addresslsb:byte, datamsb:byte, datalsb:byte) = writeAddress16(uint16 addressmsb <<< 8 ||| uint16 addresslsb, uint16 datamsb <<< 8 ||| uint16 datalsb)

let readAddress (address:uint16) = 
    if mbcType = MbcType.RomOnly then 
        memory.[int address] 
    else
        match address with
        | address when address <= (snd ROM0) -> memory.[int address] //ROM0. Read from GB Memory 
        | address when address >= (fst ROM1) && address <= (snd ROM1) -> rom.[int romBankOffset + (int address &&& int 0x3FFF)] //Read from ROM
        | address when address >= (fst SWRAMBANK) && address <= (snd SWRAMBANK) -> rom.[int ramBankOffset + (int address &&& int 0x1FFF)] //Read from ROM
        | _ -> memory.[int address] //Read from GB Memory 

let readAddress_2 (msb:byte, lsb: byte) = readAddress((uint16 msb <<< 8) ||| uint16 lsb)
let readAddress16 (address:uint16) = uint16 (readAddress(address+1us)) <<< 8 ||| uint16 (readAddress(address))
let readAddress16_2 (msb:byte, lsb: byte) = readAddress16(uint16 msb <<< 8 ||| uint16 lsb)

let mutable cbOpCycles = 0uy
let mutable temp16 = 0us
let mutable temp = 0uy

let addHL (m:byte, l:byte) =
    let hl = (uint16 H <<< 8 ||| uint16 L)
    let reg = (uint16 m <<< 8 ||| uint16 l)
    let sum = hl + reg
    CF <- sum < hl
    HF <- ((int hl &&& 0x0FFF)+(int reg &&& 0x0FFF)) > 0x0FFF 
    H <- byte ((sum &&& 0xFF00us) >>> 8) 
    L <- byte (sum &&& 0x00FFus)
    NF <- false
let addHLSP () = addHL(byte ((SP &&& 0xFF00us) >>> 8), byte (SP &&& 0x00FFus))
let addSP () = 
    let sum = SP + uint16 (sbyte (readAddress(PC+1us)))
    CF <- (int SP + int (sbyte (readAddress(PC+1us)))) > 0xFFFF
    //CF <- sum < SP
    HF <- ((int SP &&& 0x0FFF)+(int (sbyte (readAddress(PC+1us))) &&& 0x0FFF)) > 0x0FFF 
    SP <- sum
    ZF <- false
    NF <- false

let daa () = //TODO: Fix 
    let mutable temp3 = int A
    let mutable temp = temp3 &&& 0x0F
    let mutable temp2 = (temp &&& 0xF0) >>> 4

    if NF then
        if CF then
            if temp2 > 6 && temp < 10 && (not HF) then temp3 <- temp3+0xA0
            else if temp2 > 5 && HF && temp > 5 then temp3 <- temp3 + 0x9A ; CF <- true
        else if (temp2 < 10) && (not HF) && (temp < 10) then CF <- false
        else if (temp2 < 9) && HF && (temp > 5) then temp3 <- temp3 + 0xFA
    else if CF then
        if temp2 < 3 && (not HF) && temp < 10 then temp3 <- temp3 + 0x60
        else if temp2 < 3 && (not HF) && temp > 9 then temp3 <- temp3 + 0x66 ; CF <- true
        else if (temp2 < 4) && HF && (temp < 4) then temp3 <- temp3 + 0x66
    else
        if (temp2 < 10) && (not HF) && (temp < 10) then CF <- false
        else if (temp2 < 9) && (not HF) && (temp > 9) then temp3 <- temp3 + 0x06
        else if (temp2 < 10) && HF && (temp < 4) then temp3 <- temp3 + 0x06 ; CF <- false
        else if (temp2 > 9) && (not HF) && (temp < 10) then temp3 <- temp3 + 0x60 ; CF <- true
        else if (temp2 > 8) && (not HF) && (temp > 9) then temp3 <- temp3 + 0x66 ; CF <- true
        else if (temp2 > 9) && HF && (temp < 4) then temp3 <- temp3 + 0x66 ; CF <- true
        
    temp3 <- temp3 &&& 0xFF
    A <- byte temp3
    ZF <- (A = 0uy)

let adcA (n:byte) = temp <- (if CF then 1uy else 0uy) ; NF <- false ; HF <- ((A &&& 0x0Fuy) + (n &&& 0x0Fuy) + temp) > 0x0Fuy ; CF <- (int A + int n + int temp) > 0xFF ; A <- A + n + temp ; ZF <- A = 0uy
let addA (n:byte) = NF <- false ; HF <- ((A &&& 0x0Fuy) + (n &&& 0x0Fuy)) > 0x0Fuy ; CF <- (A + n) < A ; A <- A + n ; ZF <- A = 0uy
let andA (n:byte) =  A <- A &&& n ; ZF <- (A = 0uy) ; NF <- false; HF <- true; CF <- false 
let bit (b:int, reg:byte) = ZF <- ((reg &&& (1uy <<< b)) = 0uy); NF <- false; HF <- true
let bitHL (b:int) = bit(b, readAddress_2(H,L))
let cp (n:byte) = ZF <- (A = n) ; NF <- true; HF <- (A &&& 0x0Fuy) < (n &&& 0x0Fuy); CF <- A < n;
let dec (reg:byte byref) = reg <- reg - 1uy; ZF <- (reg = 0uy) ; NF <- true; HF <- (reg = 0x0Fuy)
let dec16 (msb:byte byref, lsb:byte byref) = temp16 <- (uint16 msb <<< 8 ||| uint16 lsb) - 1us ; msb <- byte ((temp16 &&& 0xFF00us) >>> 8) ; lsb <- byte (temp16 &&& 0x00FFus)
let decHL () = temp <- readAddress_2(H,L) ; dec(&temp) ; writeAddress_2(H,L,temp)
let decSP () = SP <- SP - 1us 
let inc (reg:byte byref) = reg <- reg + 1uy; ZF <- (reg = 0uy) ; NF <- false; HF <- (reg = 0xF0uy)
let inc16 (msb:byte byref, lsb:byte byref) = temp16 <- (uint16 msb <<< 8 ||| uint16 lsb) + 1us ; msb <- byte ((temp16 &&& 0xFF00us) >>> 8) ; lsb <- byte (temp16 &&& 0x00FFus)
let incHL () = temp <- readAddress_2(H,L) ; inc(&temp) ; writeAddress_2(H,L,temp)
let incSP () = SP <- SP + 1us 
let incrementHL(inc:bool) = temp16 <- uint16 H <<< 8 ||| uint16 L ; (if inc then temp16 <- temp16 + 1us else temp16 <- temp16 - 1us) ; H <- byte ((temp16 &&& 0xFF00us) >>> 8) ;  L <- byte (temp16 &&& 0x00FFus)
let jp () = PC <- readAddress16(PC + 1us)
let jpHL () = PC <- uint16 H <<< 8 ||| uint16 L
let jr () = PC <- PC + 2us + uint16 (sbyte (readAddress(PC+1us)))
let orA (n:byte) = A <- A ||| n ; ZF <- (A = 0uy) ; NF <- false; HF <- false; CF <- false 
let pop (into:uint16 byref) = into <- ((uint16 memory.[int (SP+1us)] <<< 8) ||| uint16 memory.[int SP]) ; SP <- SP + 2us
let pop_2 (msb:byte byref, lsb:byte byref) = msb <- memory.[int (SP+1us)] ; lsb <- memory.[int SP] ; SP <- SP + 2us  
let popAF() = pop_2(&A,&F) ; ZF <- (F &&& (1uy <<< 7)) > 1uy ; NF <- (F &&& (1uy <<< 6)) > 1uy ; HF <- (F &&& (1uy <<< 5)) > 1uy ; CF <- (F &&& (1uy <<< 4)) > 1uy
let push (data:uint16) = SP <- SP - 2us ; memory.[int (SP+1us)] <- byte ((data &&& 0xFF00us) >>> 8); memory.[int SP] <- byte (data &&& 0x00FFus) 
let push_2 (msb:byte, lsb:byte) = SP <- SP - 2us ; memory.[int (SP+1us)] <- msb; memory.[int SP] <- lsb 
let res (b:int, reg:byte byref) = reg <- reg &&& ~~~(1uy <<< b)
let resHL(b:int) = temp <- readAddress_2(H,L) ; res(b, &temp) ; writeAddress_2(H,L,temp)
let ret () = pop(&PC)
let rl (reg:byte byref) = temp <- (if CF then 1uy else 0uy) ; CF <- (if reg &&& 0b10000000uy > 1uy then true else false) ; reg <- (reg <<< 1) ||| temp ; ZF <- reg = 0uy; NF <- false; HF <- false; 
let rlHL() = temp <- readAddress_2(H,L) ; rl(&temp); writeAddress_2(H,L, temp)
let rla () = temp <- (if CF then 1uy else 0uy) ; CF <- (if A &&& 0b10000000uy > 1uy then true else false) ; A <- (A <<< 1) ||| temp ; ZF <- A = 0uy; NF <- false; HF <- false;  
let rlc (reg:byte byref) = CF <- (if reg &&& 0b10000000uy > 1uy then true else false) ; reg <- (reg <<< 1) ||| (if CF then 1uy else 0uy) ; ZF <- reg = 0uy; NF <- false; HF <- false;  
let rlcHL () = temp <- readAddress_2(H,L) ; rlc(&temp); writeAddress_2(H,L, temp)
let rlca () = CF <- (if A &&& 0b10000000uy > 1uy then true else false) ; A <- (A <<< 1) ||| (if CF then 1uy else 0uy) ; ZF <- A = 0uy; NF <- false; HF <- false;  
let rr (reg:byte byref) = temp <- (if CF then 1uy else 0uy) ; CF <- (if reg &&& 1uy >= 1uy then true else false) ; reg <- (reg >>> 1) ||| (temp<<<7) ; ZF <- reg = 0uy; NF <- false; HF <- false; 
let rrHL() = temp <- readAddress_2(H,L) ; rr(&temp); writeAddress_2(H,L, temp)
let rra () = temp <- (if CF then 1uy else 0uy) ; CF <- (if A &&& 1uy >= 1uy then true else false) ; A <- (A >>> 1) ||| (temp<<<7) ; ZF <- A = 0uy; NF <- false; HF <- false; 
let rrc (reg:byte byref) = CF <- (if reg &&& 1uy >= 1uy then true else false) ; reg <- (reg >>> 1) ||| (if CF then (1uy<<<7) else 0uy) ; ZF <- reg = 0uy; NF <- false; HF <- false;  
let rrcHL () = temp <- readAddress_2(H,L) ; rrc(&temp); writeAddress_2(H,L, temp)
let rrca () = CF <- (if A &&& 1uy >= 1uy then true else false) ; A <- (A >>> 1) ||| (if CF then (1uy<<<7) else 0uy) ; ZF <- A = 0uy; NF <- false; HF <- false;  
let rst (n:uint16) = push(PC+1us); PC <- n
let sbcA (n:byte) = temp <- (if CF then 1uy else 0uy) ; NF <- true ; HF <- (A &&& 0x0Fuy) < ((n &&& 0x0Fuy)+temp) ; CF <- A < (n+temp); A <- A - n - temp ; ZF <- A = 0uy
let set (b:int, reg:byte byref) = reg <- reg ||| (1uy <<< b)
let setHL(b:int) = temp <- readAddress_2(H,L) ; set(b, &temp) ; writeAddress_2(H,L,temp)
let sla (reg:byte byref) = CF <- (if reg &&& 0b10000000uy > 1uy then true else false) ; reg <- reg <<< 1 ; ZF <- reg = 0uy; NF <- false ; HF <- false
let slaHL () = temp <- readAddress_2(H,L) ; sla(&temp); writeAddress_2(H,L, temp)
let sra (reg:byte byref) = CF <- (if reg &&& 1uy >= 1uy then true else false) ; reg <- (reg >>> 1) ||| (reg &&& 0b10000000uy); ZF <- reg = 0uy; NF <- false ; HF <- false
let sraHL () = temp <- readAddress_2(H,L) ; sra(&temp); writeAddress_2(H,L, temp)
let srl (reg:byte byref) = CF <- (if reg &&& 1uy >= 1uy then true else false) ; reg <- reg >>> 1 ; ZF <- reg = 0uy; NF <- false ; HF <- false
let srlHL () = temp <- readAddress_2(H,L) ; srl(&temp); writeAddress_2(H,L, temp)
let subA (n:byte) = NF <- true ; HF <- (A &&& 0x0Fuy) < (n &&& 0x0Fuy) ; CF <- A < n ; A <- A - n ; ZF <- A = 0uy
let swap (reg:byte byref) = reg <- (((reg &&& 0xF0uy) >>> 4) ||| ((reg &&& 0xFuy) <<< 4)); ZF <- (reg = 0uy) ; NF <- false ; HF <- false ; CF <- false
let swapHL () = temp <- readAddress_2(H, L) ; swap(&temp) ; writeAddress_2(H, L, temp)
let xorA (n:byte) = A <- A ^^^ n ; ZF <- (A = 0uy) ; NF <- false; HF <- false; CF <- false
let call () = push(PC+3us); jp()

opcodeHandlers.[0x00] <- (fun () -> PC <- PC + 1us; 1uy) //NOP
opcodeHandlers.[0x01] <- (fun () -> B <- readAddress(PC + 2us); C <- readAddress(PC + 1us); PC <- PC + 3us; 3uy) //LD BC,nn
opcodeHandlers.[0x02] <- (fun () -> writeAddress_2(B, C, A); PC <- PC + 1us; 2uy) //LD (BC), A
opcodeHandlers.[0x03] <- (fun () -> inc16(&B,&C);  PC <- PC + 1us; 2uy) //INC BC
opcodeHandlers.[0x04] <- (fun () -> inc(&B); PC <- PC + 1us; 1uy) //INC B
opcodeHandlers.[0x05] <- (fun () -> dec(&B); PC <- PC + 1us; 1uy) //DEC B
opcodeHandlers.[0x06] <- (fun () -> B <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD B,nn
opcodeHandlers.[0x07] <- (fun () -> rlca(); PC <- PC + 1us; 1uy) //RLCA
opcodeHandlers.[0x08] <- (fun () -> writeAddress16_2(readAddress(PC + 2us), readAddress(PC + 1us), SP); PC <- PC + 3us; 5uy) //LD (nn),SP
opcodeHandlers.[0x09] <- (fun () -> addHL(B,C);  PC <- PC + 1us; 2uy)  //ADD HL,BC 
opcodeHandlers.[0x0A] <- (fun () -> A <- readAddress_2(B, C); PC <- PC + 1us; 2uy) //LD A,(BC)
opcodeHandlers.[0x0B] <- (fun () -> dec16(&B,&C);  PC <- PC + 1us; 2uy) //DEC BC
opcodeHandlers.[0x0C] <- (fun () -> inc(&C); PC <- PC + 1us; 1uy) //INC C
opcodeHandlers.[0x0D] <- (fun () -> dec(&C); PC <- PC + 1us; 1uy) //DEC C
opcodeHandlers.[0x0E] <- (fun () -> C <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD C,nn
opcodeHandlers.[0x0F] <- (fun () -> rrca(); PC <- PC + 1us; 1uy) //RRCA
opcodeHandlers.[0x10] <- (fun () -> stopped <- true; MessageBox.Show("STOPPED"); PC <- PC + 2us; 1uy) //STOP
opcodeHandlers.[0x11] <- (fun () -> D <- readAddress(PC + 2us); E <- readAddress(PC + 1us); PC <- PC + 3us; 3uy) //LD DE,nn
opcodeHandlers.[0x12] <- (fun () -> writeAddress_2(D, E, A); PC <- PC + 1us; 2uy) //LD (DE), A
opcodeHandlers.[0x13] <- (fun () -> inc16(&D,&E);  PC <- PC + 1us; 2uy) //INC DE
opcodeHandlers.[0x14] <- (fun () -> inc(&D); PC <- PC + 1us; 1uy) //INC D
opcodeHandlers.[0x15] <- (fun () -> dec(&D); PC <- PC + 1us; 1uy) //DEC D
opcodeHandlers.[0x16] <- (fun () -> D <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD D,nn
opcodeHandlers.[0x17] <- (fun () -> rla(); PC <- PC + 1us; 1uy) //RLA
opcodeHandlers.[0x18] <- (fun () -> jr(); 3uy) //JR n
opcodeHandlers.[0x19] <- (fun () -> addHL(D,E);  PC <- PC + 1us; 2uy)  //ADD HL,DE 
opcodeHandlers.[0x1A] <- (fun () -> A <- readAddress_2(D, E); PC <- PC + 1us; 2uy) //LD A,(DE)
opcodeHandlers.[0x1B] <- (fun () -> dec16(&D,&E);  PC <- PC + 1us; 2uy) //DEC DE
opcodeHandlers.[0x1C] <- (fun () -> inc(&E); PC <- PC + 1us; 1uy) //INC E
opcodeHandlers.[0x1D] <- (fun () -> dec(&E); PC <- PC + 1us; 1uy) //DEC E
opcodeHandlers.[0x1E] <- (fun () -> E <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD E,nn
opcodeHandlers.[0x1F] <- (fun () -> rra(); PC <- PC + 1us; 1uy) //RRA
opcodeHandlers.[0x20] <- (fun () -> if ZF = false then jr(); 3uy; else PC <- PC + 2us; 2uy) //JR NZ,nn 
opcodeHandlers.[0x21] <- (fun () -> H <- readAddress(PC + 2us); L <- readAddress(PC + 1us); PC <- PC + 3us; 3uy) //LD HL,nn
opcodeHandlers.[0x22] <- (fun () -> writeAddress_2(H,L, A) ; incrementHL(true); PC <- PC + 1us ; 2uy) //LDI (HL),A
opcodeHandlers.[0x23] <- (fun () -> inc16(&H,&L);  PC <- PC + 1us; 2uy) //INC HL
opcodeHandlers.[0x24] <- (fun () -> inc(&H); PC <- PC + 1us; 1uy) //INC H
opcodeHandlers.[0x25] <- (fun () -> dec(&H); PC <- PC + 1us; 1uy) //DEC H
opcodeHandlers.[0x26] <- (fun () -> H <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD H,nn
opcodeHandlers.[0x27] <- (fun () -> daa() ; PC <- PC + 1us; 1uy)  //DAA
opcodeHandlers.[0x28] <- (fun () -> if ZF = true then jr(); 3uy; else PC <- PC + 2us; 2uy) //JR Z,nn 
opcodeHandlers.[0x29] <- (fun () -> addHL(H,L);  PC <- PC + 1us; 2uy)  //ADD HL,HL 
opcodeHandlers.[0x2A] <- (fun () -> A <- readAddress_2(H,L) ; incrementHL(true); PC <- PC + 1us ; 2uy) //LDI A,(HL)
opcodeHandlers.[0x2B] <- (fun () -> dec16(&H,&L);  PC <- PC + 1us; 2uy) //DEC HL
opcodeHandlers.[0x2C] <- (fun () -> inc(&L); PC <- PC + 1us; 1uy) //INC L
opcodeHandlers.[0x2D] <- (fun () -> dec(&L); PC <- PC + 1us; 1uy) //DEC L
opcodeHandlers.[0x2E] <- (fun () -> L <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD L,nn
opcodeHandlers.[0x2F] <- (fun () -> A <- ~~~A ; NF <- true; HF <- true; PC <- PC + 1us; 1uy) //CPL
opcodeHandlers.[0x30] <- (fun () -> if CF = false then jr(); 3uy; else PC <- PC + 2us; 2uy) //JR NC,nn 
opcodeHandlers.[0x31] <- (fun () -> SP <- readAddress16(PC + 1us); PC <- PC + 3us; 3uy) //LD SP, nn 
opcodeHandlers.[0x32] <- (fun () -> writeAddress_2(H,L, A) ; incrementHL(false); PC <- PC + 1us ; 2uy) //LDD (HL),A
opcodeHandlers.[0x33] <- (fun () -> incSP();  PC <- PC + 1us; 2uy) //INC SP
opcodeHandlers.[0x34] <- (fun () -> incHL(); PC <- PC + 1us; 3uy) //INC (HL)
opcodeHandlers.[0x35] <- (fun () -> decHL(); PC <- PC + 1us; 3uy) //DEC (HL)
opcodeHandlers.[0x36] <- (fun () -> writeAddress_2(H, L, readAddress(PC + 1us)); PC <- PC + 2us; 3uy) //LD (HL), n
opcodeHandlers.[0x37] <- (fun () -> NF <- false; HF <- false; CF <- true; PC <- PC + 1us; 1uy) //SCF
opcodeHandlers.[0x38] <- (fun () -> if CF = true then jr(); 3uy; else PC <- PC + 2us; 2uy) //JR C,nn 
opcodeHandlers.[0x39] <- (fun () -> addHLSP();  PC <- PC + 1us; 2uy)  //ADD HL,SP
opcodeHandlers.[0x3A] <- (fun () -> A <- readAddress_2(H,L) ; incrementHL(false); PC <- PC + 1us ; 2uy) //LDD A,(HL)
opcodeHandlers.[0x3B] <- (fun () -> decSP();  PC <- PC + 1us; 2uy) //DEC SP
opcodeHandlers.[0x3C] <- (fun () -> inc(&A); PC <- PC + 1us; 1uy) //INC A
opcodeHandlers.[0x3D] <- (fun () -> dec(&A); PC <- PC + 1us; 1uy) //DEC A
opcodeHandlers.[0x3E] <- (fun () -> A <- readAddress(PC + 1us); PC <- PC + 2us; 2uy) //LD A,n
opcodeHandlers.[0x3F] <- (fun () -> NF <- false; HF <- false; CF <- not CF ; PC <- PC + 1us; 1uy) //CCF
opcodeHandlers.[0x40] <- (fun () -> B <- B; PC <- PC + 1us; 1uy) //LD B,B
opcodeHandlers.[0x41] <- (fun () -> B <- C; PC <- PC + 1us; 1uy) //LD B,C
opcodeHandlers.[0x42] <- (fun () -> B <- D; PC <- PC + 1us; 1uy) //LD B,D
opcodeHandlers.[0x43] <- (fun () -> B <- E; PC <- PC + 1us; 1uy) //LD B,E
opcodeHandlers.[0x44] <- (fun () -> B <- H; PC <- PC + 1us; 1uy) //LD B,H
opcodeHandlers.[0x45] <- (fun () -> B <- L; PC <- PC + 1us; 1uy) //LD B,L
opcodeHandlers.[0x46] <- (fun () -> B <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD B,(HL)
opcodeHandlers.[0x47] <- (fun () -> B <- A; PC <- PC + 1us; 1uy) //LD B,A
opcodeHandlers.[0x48] <- (fun () -> C <- B; PC <- PC + 1us; 1uy) //LD C,B
opcodeHandlers.[0x49] <- (fun () -> C <- C; PC <- PC + 1us; 1uy) //LD C,C
opcodeHandlers.[0x4A] <- (fun () -> C <- D; PC <- PC + 1us; 1uy) //LD C,D
opcodeHandlers.[0x4B] <- (fun () -> C <- E; PC <- PC + 1us; 1uy) //LD C,E
opcodeHandlers.[0x4C] <- (fun () -> C <- H; PC <- PC + 1us; 1uy) //LD C,H
opcodeHandlers.[0x4D] <- (fun () -> C <- L; PC <- PC + 1us; 1uy) //LD C,L
opcodeHandlers.[0x4E] <- (fun () -> C <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD C,(HL)
opcodeHandlers.[0x4F] <- (fun () -> C <- A; PC <- PC + 1us; 1uy) //LD C,A
opcodeHandlers.[0x50] <- (fun () -> D <- B; PC <- PC + 1us; 1uy) //LD D,B
opcodeHandlers.[0x51] <- (fun () -> D <- C; PC <- PC + 1us; 1uy) //LD D,C
opcodeHandlers.[0x52] <- (fun () -> D <- D; PC <- PC + 1us; 1uy) //LD D,D
opcodeHandlers.[0x53] <- (fun () -> D <- E; PC <- PC + 1us; 1uy) //LD D,E
opcodeHandlers.[0x54] <- (fun () -> D <- H; PC <- PC + 1us; 1uy) //LD D,H
opcodeHandlers.[0x55] <- (fun () -> D <- L; PC <- PC + 1us; 1uy) //LD D,L
opcodeHandlers.[0x56] <- (fun () -> D <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD D,(HL)
opcodeHandlers.[0x57] <- (fun () -> D <- A; PC <- PC + 1us; 1uy) //LD D,A
opcodeHandlers.[0x58] <- (fun () -> E <- B; PC <- PC + 1us; 1uy) //LD E,B
opcodeHandlers.[0x59] <- (fun () -> E <- C; PC <- PC + 1us; 1uy) //LD E,C
opcodeHandlers.[0x5A] <- (fun () -> E <- D; PC <- PC + 1us; 1uy) //LD E,D
opcodeHandlers.[0x5B] <- (fun () -> E <- E; PC <- PC + 1us; 1uy) //LD E,E
opcodeHandlers.[0x5C] <- (fun () -> E <- H; PC <- PC + 1us; 1uy) //LD E,H
opcodeHandlers.[0x5D] <- (fun () -> E <- L; PC <- PC + 1us; 1uy) //LD E,L
opcodeHandlers.[0x5E] <- (fun () -> E <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD E,(HL)
opcodeHandlers.[0x5F] <- (fun () -> E <- A; PC <- PC + 1us; 1uy) //LD E,A
opcodeHandlers.[0x60] <- (fun () -> H <- B; PC <- PC + 1us; 1uy) //LD H,B
opcodeHandlers.[0x61] <- (fun () -> H <- C; PC <- PC + 1us; 1uy) //LD H,C
opcodeHandlers.[0x62] <- (fun () -> H <- D; PC <- PC + 1us; 1uy) //LD H,D
opcodeHandlers.[0x63] <- (fun () -> H <- E; PC <- PC + 1us; 1uy) //LD H,E
opcodeHandlers.[0x64] <- (fun () -> H <- H; PC <- PC + 1us; 1uy) //LD H,H
opcodeHandlers.[0x65] <- (fun () -> H <- L; PC <- PC + 1us; 1uy) //LD H,L
opcodeHandlers.[0x66] <- (fun () -> H <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD H,(HL)
opcodeHandlers.[0x67] <- (fun () -> H <- A; PC <- PC + 1us; 1uy) //LD H,A
opcodeHandlers.[0x68] <- (fun () -> L <- B; PC <- PC + 1us; 1uy) //LD L,B
opcodeHandlers.[0x69] <- (fun () -> L <- C; PC <- PC + 1us; 1uy) //LD L,C
opcodeHandlers.[0x6A] <- (fun () -> L <- D; PC <- PC + 1us; 1uy) //LD L,D
opcodeHandlers.[0x6B] <- (fun () -> L <- E; PC <- PC + 1us; 1uy) //LD L,E
opcodeHandlers.[0x6C] <- (fun () -> L <- H; PC <- PC + 1us; 1uy) //LD L,H
opcodeHandlers.[0x6D] <- (fun () -> L <- L; PC <- PC + 1us; 1uy) //LD L,L
opcodeHandlers.[0x6E] <- (fun () -> L <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD L,(HL)
opcodeHandlers.[0x6F] <- (fun () -> L <- A; PC <- PC + 1us; 1uy) //LD L,A
opcodeHandlers.[0x70] <- (fun () -> writeAddress_2(H, L, B); PC <- PC + 1us; 2uy) //LD (HL), B
opcodeHandlers.[0x71] <- (fun () -> writeAddress_2(H, L, C); PC <- PC + 1us; 2uy) //LD (HL), C
opcodeHandlers.[0x72] <- (fun () -> writeAddress_2(H, L, D); PC <- PC + 1us; 2uy) //LD (HL), D
opcodeHandlers.[0x73] <- (fun () -> writeAddress_2(H, L, E); PC <- PC + 1us; 2uy) //LD (HL), E
opcodeHandlers.[0x74] <- (fun () -> writeAddress_2(H, L, H); PC <- PC + 1us; 2uy) //LD (HL), H
opcodeHandlers.[0x75] <- (fun () -> writeAddress_2(H, L, L); PC <- PC + 1us; 2uy) //LD (HL), L
opcodeHandlers.[0x76] <- (fun () -> PC <- PC + 1us; 1uy) //HALT
opcodeHandlers.[0x77] <- (fun () -> writeAddress_2(H, L, A); PC <- PC + 1us; 2uy) //LD (HL), A
opcodeHandlers.[0x78] <- (fun () -> A <- B; PC <- PC + 1us; 1uy) //LD A,B
opcodeHandlers.[0x79] <- (fun () -> A <- C; PC <- PC + 1us; 1uy) //LD A,C
opcodeHandlers.[0x7A] <- (fun () -> A <- D; PC <- PC + 1us; 1uy) //LD A,D
opcodeHandlers.[0x7B] <- (fun () -> A <- E; PC <- PC + 1us; 1uy) //LD A,E
opcodeHandlers.[0x7C] <- (fun () -> A <- H; PC <- PC + 1us; 1uy) //LD A,H
opcodeHandlers.[0x7D] <- (fun () -> A <- L; PC <- PC + 1us; 1uy) //LD A,L
opcodeHandlers.[0x7E] <- (fun () -> A <- readAddress_2(H, L); PC <- PC + 1us; 2uy) //LD A,(HL)
opcodeHandlers.[0x7F] <- (fun () -> A <- A; PC <- PC + 1us; 1uy) //LD A,A
opcodeHandlers.[0x80] <- (fun () -> addA(B); PC <- PC + 1us; 1uy)  //ADD A,B 
opcodeHandlers.[0x81] <- (fun () -> addA(C); PC <- PC + 1us; 1uy)  //ADD A,C
opcodeHandlers.[0x82] <- (fun () -> addA(D); PC <- PC + 1us; 1uy)  //ADD A,D
opcodeHandlers.[0x83] <- (fun () -> addA(E); PC <- PC + 1us; 1uy)  //ADD A,E
opcodeHandlers.[0x84] <- (fun () -> addA(H); PC <- PC + 1us; 1uy)  //ADD A,H
opcodeHandlers.[0x85] <- (fun () -> addA(L); PC <- PC + 1us; 1uy)  //ADD A,L
opcodeHandlers.[0x86] <- (fun () -> addA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //ADD A,(HL)
opcodeHandlers.[0x87] <- (fun () -> addA(A); PC <- PC + 1us; 1uy)  //ADD A,A
opcodeHandlers.[0x88] <- (fun () -> adcA(B); PC <- PC + 1us; 1uy) //ADC A,B
opcodeHandlers.[0x89] <- (fun () -> adcA(C); PC <- PC + 1us; 1uy) //ADC A,C
opcodeHandlers.[0x8A] <- (fun () -> adcA(D); PC <- PC + 1us; 1uy) //ADC A,D
opcodeHandlers.[0x8B] <- (fun () -> adcA(E); PC <- PC + 1us; 1uy) //ADC A,E
opcodeHandlers.[0x8C] <- (fun () -> adcA(H); PC <- PC + 1us; 1uy) //ADC A,H
opcodeHandlers.[0x8D] <- (fun () -> adcA(L); PC <- PC + 1us; 1uy) //ADC A,L
opcodeHandlers.[0x8E] <- (fun () -> adcA(readAddress_2(H, L)); PC <- PC + 1us; 2uy)  //ADC A,(HL)
opcodeHandlers.[0x8F] <- (fun () -> adcA(A); PC <- PC + 1us; 1uy) //ADC A,A
opcodeHandlers.[0x90] <- (fun () -> subA(B); PC <- PC + 1us; 1uy) //SUB A,B
opcodeHandlers.[0x91] <- (fun () -> subA(C); PC <- PC + 1us; 1uy) //SUB A,C
opcodeHandlers.[0x92] <- (fun () -> subA(D); PC <- PC + 1us; 1uy) //SUB A,D
opcodeHandlers.[0x93] <- (fun () -> subA(E); PC <- PC + 1us; 1uy) //SUB A,E
opcodeHandlers.[0x94] <- (fun () -> subA(H); PC <- PC + 1us; 1uy) //SUB A,H
opcodeHandlers.[0x95] <- (fun () -> subA(L); PC <- PC + 1us; 1uy) //SUB A,L
opcodeHandlers.[0x96] <- (fun () -> subA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //SUB A,(HL)
opcodeHandlers.[0x97] <- (fun () -> subA(A); PC <- PC + 1us; 1uy) //SUB A,A
opcodeHandlers.[0x98] <- (fun () -> sbcA(B); PC <- PC + 1us; 1uy) //SBC A,B
opcodeHandlers.[0x99] <- (fun () -> sbcA(C); PC <- PC + 1us; 1uy) //SBC A,C
opcodeHandlers.[0x9A] <- (fun () -> sbcA(D); PC <- PC + 1us; 1uy) //SBC A,D
opcodeHandlers.[0x9B] <- (fun () -> sbcA(E); PC <- PC + 1us; 1uy) //SBC A,E
opcodeHandlers.[0x9C] <- (fun () -> sbcA(H); PC <- PC + 1us; 1uy) //SBC A,H
opcodeHandlers.[0x9D] <- (fun () -> sbcA(L); PC <- PC + 1us; 1uy) //SBC A,L
opcodeHandlers.[0x9E] <- (fun () -> sbcA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //SBC A,(HL)
opcodeHandlers.[0x9F] <- (fun () -> sbcA(A); PC <- PC + 1us; 1uy) //SBC A,A
opcodeHandlers.[0xA0] <- (fun () -> andA(B); PC <- PC + 1us; 1uy) //AND A,B
opcodeHandlers.[0xA1] <- (fun () -> andA(C); PC <- PC + 1us; 1uy) //AND A,C
opcodeHandlers.[0xA2] <- (fun () -> andA(D); PC <- PC + 1us; 1uy) //AND A,D
opcodeHandlers.[0xA3] <- (fun () -> andA(E); PC <- PC + 1us; 1uy) //AND A,E
opcodeHandlers.[0xA4] <- (fun () -> andA(H); PC <- PC + 1us; 1uy) //AND A,H 
opcodeHandlers.[0xA5] <- (fun () -> andA(L); PC <- PC + 1us; 1uy) //AND A,L
opcodeHandlers.[0xA6] <- (fun () -> andA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //AND A,(HL)  
opcodeHandlers.[0xA7] <- (fun () -> andA(A); PC <- PC + 1us; 1uy) //AND A,A
opcodeHandlers.[0xA8] <- (fun () -> xorA(B); PC <- PC + 1us; 1uy) //XOR A,B
opcodeHandlers.[0xA9] <- (fun () -> xorA(C); PC <- PC + 1us; 1uy) //XOR A,C
opcodeHandlers.[0xAA] <- (fun () -> xorA(D); PC <- PC + 1us; 1uy) //XOR A,D
opcodeHandlers.[0xAB] <- (fun () -> xorA(E); PC <- PC + 1us; 1uy) //XOR A,E
opcodeHandlers.[0xAC] <- (fun () -> xorA(H); PC <- PC + 1us; 1uy) //XOR A,H
opcodeHandlers.[0xAD] <- (fun () -> xorA(L); PC <- PC + 1us; 1uy) //XOR A,L
opcodeHandlers.[0xAE] <- (fun () -> xorA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //XOR A,(HL)  
opcodeHandlers.[0xAF] <- (fun () -> xorA(A); PC <- PC + 1us; 1uy) //XOR A,A
opcodeHandlers.[0xB0] <- (fun () -> orA(B); PC <- PC + 1us; 1uy) //OR A,B
opcodeHandlers.[0xB1] <- (fun () -> orA(C); PC <- PC + 1us; 1uy) //OR A,C
opcodeHandlers.[0xB2] <- (fun () -> orA(D); PC <- PC + 1us; 1uy) //OR A,D
opcodeHandlers.[0xB3] <- (fun () -> orA(E); PC <- PC + 1us; 1uy) //OR A,E
opcodeHandlers.[0xB4] <- (fun () -> orA(H); PC <- PC + 1us; 1uy) //OR A,H
opcodeHandlers.[0xB5] <- (fun () -> orA(L); PC <- PC + 1us; 1uy) //OR A,L
opcodeHandlers.[0xB6] <- (fun () -> orA(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //OR A,(HL)   
opcodeHandlers.[0xB7] <- (fun () -> orA(A); PC <- PC + 1us; 1uy) //OR A,A
opcodeHandlers.[0xB8] <- (fun () -> cp(B); PC <- PC + 1us; 1uy) //CP A,B
opcodeHandlers.[0xB9] <- (fun () -> cp(C); PC <- PC + 1us; 1uy) //CP A,C
opcodeHandlers.[0xBA] <- (fun () -> cp(D); PC <- PC + 1us; 1uy) //CP A,D
opcodeHandlers.[0xBB] <- (fun () -> cp(E); PC <- PC + 1us; 1uy) //CP A,E
opcodeHandlers.[0xBC] <- (fun () -> cp(H); PC <- PC + 1us; 1uy) //CP A,H
opcodeHandlers.[0xBD] <- (fun () -> cp(L); PC <- PC + 1us; 1uy) //CP A,L
opcodeHandlers.[0xBE] <- (fun () -> cp(readAddress_2(H, L)); PC <- PC + 1us; 2uy) //CP A,(HL)
opcodeHandlers.[0xBF] <- (fun () -> cp(A); PC <- PC + 1us; 1uy) //CP A,A
opcodeHandlers.[0xC0] <- (fun () -> if ZF = false then ret(); 2uy; else PC <- PC + 1us; 2uy) //RET NZ
opcodeHandlers.[0xC1] <- (fun () -> pop_2(&B,&C);  PC <- PC + 1us; 3uy) //POP BC
opcodeHandlers.[0xC2] <- (fun () -> if ZF = false then jp(); 3uy; else PC <- PC + 3us; 3uy) //JP NZ,nn
opcodeHandlers.[0xC3] <- (fun () -> jp(); 3uy) //JP nn
opcodeHandlers.[0xC4] <- (fun () -> if ZF = false then call(); 3uy; else PC <- PC + 3us; 3uy) //CALL NZ,nn
opcodeHandlers.[0xC5] <- (fun () -> push_2(B,C);  PC <- PC + 1us; 4uy) //PUSH BC
opcodeHandlers.[0xC6] <- (fun () -> addA(readAddress(PC+1us)); PC <- PC + 2us; 2uy)  //ADD A,n
opcodeHandlers.[0xC7] <- (fun () -> rst(0x0us); 8uy) //RST 0
opcodeHandlers.[0xC8] <- (fun () -> if ZF = true then ret(); 2uy; else PC <- PC + 1us; 2uy) //RET Z
opcodeHandlers.[0xC9] <- (fun () -> ret(); 2uy)  //RET
opcodeHandlers.[0xCA] <- (fun () -> if ZF = true then jp(); 3uy; else PC <- PC + 3us; 3uy) //JP Z,nn
opcodeHandlers.[0xCB] <- (fun () -> PC <- PC + 1us; cbOpCycles <- CBopcodeHandlers.[int (readAddress(PC))](); if cbOpCycles = 0uy then unhandledCBOpcode <- true; 0uy; else cbOpCycles) 
opcodeHandlers.[0xCC] <- (fun () -> if ZF = true then call(); 3uy; else PC <- PC + 3us; 3uy) //CALL Z,nn
opcodeHandlers.[0xCD] <- (fun () -> call(); 3uy)  //CALL nn
opcodeHandlers.[0xCE] <- (fun () -> adcA(readAddress(PC+1us)); PC <- PC + 2us; 2uy)  //ADC A,n
opcodeHandlers.[0xCF] <- (fun () -> rst(0x8us); 8uy) //RST 8
opcodeHandlers.[0xD0] <- (fun () -> if CF = false then ret(); 2uy; else PC <- PC + 1us; 2uy) //RET NC 
opcodeHandlers.[0xD1] <- (fun () -> pop_2(&D,&E);  PC <- PC + 1us; 3uy) //POP DE
opcodeHandlers.[0xD2] <- (fun () -> if CF = false then jp(); 3uy; else PC <- PC + 3us; 3uy) //JP NC,nn 
//opcodeHandlers.[0xD3] //Invalid opcode
opcodeHandlers.[0xD4] <- (fun () -> if CF = false then call(); 3uy; else PC <- PC + 3us; 3uy) //CALL NC,nn 
opcodeHandlers.[0xD5] <- (fun () -> push_2(D,E);  PC <- PC + 1us; 4uy) //PUSH DE
opcodeHandlers.[0xD6] <- (fun () -> subA(readAddress(PC+1us)); PC <- PC + 2us; 2uy) //SUB A,n
opcodeHandlers.[0xD7] <- (fun () -> rst(0x10us); 8uy) //RST 10
opcodeHandlers.[0xD8] <- (fun () -> if CF = true then ret(); 2uy; else PC <- PC + 1us; 2uy) // RET C 
opcodeHandlers.[0xD9] <- (fun () -> ret(); IME <- true; 2uy) //RETI
opcodeHandlers.[0xDA] <- (fun () -> if CF = true then jp(); 3uy; else PC <- PC + 3us; 3uy) //JP C,nn
//opcodeHandlers.[0xDB] //Invalid opcode
opcodeHandlers.[0xDC] <- (fun () -> if CF = true then call(); 3uy; else PC <- PC + 3us; 3uy) //CALL C,nn 
opcodeHandlers.[0xDE] <- (fun () -> sbcA(readAddress(PC+1us)); PC <- PC + 2us; 2uy) //SBC A,n
opcodeHandlers.[0xDF] <- (fun () -> rst(0x18us); 8uy) //RST 18
opcodeHandlers.[0xE0] <- (fun () -> writeAddress(0xFF00us + uint16 (readAddress(PC + 1us)), A); PC <- PC + 2us; 3uy) //LDH (FF00+n),A
opcodeHandlers.[0xE1] <- (fun () -> pop_2(&H,&L);  PC <- PC + 1us; 3uy) //POP HL
opcodeHandlers.[0xE2] <- (fun () -> writeAddress(0xFF00us + uint16 C, A); PC <- PC + 1us; 2uy) //LD (FF00+C),A
//opcodeHandlers.[0xE3] //Invalid opcode
//opcodeHandlers.[0xE4] //Invalid opcode
opcodeHandlers.[0xE5] <- (fun () -> push_2(H,L);  PC <- PC + 1us; 4uy) //PUSH HL
opcodeHandlers.[0xE6] <- (fun () -> andA(readAddress(PC+1us)); PC <- PC + 2us; 2uy)  //AND A,n
opcodeHandlers.[0xE7] <- (fun () -> rst(0x20us); 8uy) //RST 20 
opcodeHandlers.[0xE8] <- (fun () -> addSP();  PC <- PC + 2us; 4uy) //ADD SP,n
opcodeHandlers.[0xE9] <- (fun () -> jpHL(); 1uy) //JP (HL)
opcodeHandlers.[0xEA] <- (fun () -> writeAddress_2(readAddress(PC + 2us), readAddress(PC + 1us), A); PC <- PC + 3us; 4uy) //LD (nn), A
//opcodeHandlers.[0xEB] //Invalid opcode
//opcodeHandlers.[0xEC] //Invalid opcode
//opcodeHandlers.[0xED] //Invalid opcode
opcodeHandlers.[0xEE] <- (fun () -> xorA(readAddress(PC+1us)); PC <- PC + 2us; 2uy) //XOR A,n
opcodeHandlers.[0xEF] <- (fun () -> rst(0x28us); 8uy) //RST 28
opcodeHandlers.[0xF0] <- (fun () -> A <- readAddress(0xFF00us + uint16(readAddress(PC + 1us))); PC <- PC + 2us; 3uy) //LDH A,(FF00+n)
opcodeHandlers.[0xF1] <- (fun () -> popAF();  PC <- PC + 1us; 3uy) //POP AF
opcodeHandlers.[0xF2] <- (fun () -> A <- readAddress(0xFF00us + uint16 C); PC <- PC + 1us; 2uy) //LD A,(FF00+C)
opcodeHandlers.[0xF3] <- (fun () -> PC <- PC + 1us; IME <- false ; 1uy) //DI TODO: "Not immediatly"
//opcodeHandlers.[0xF4] //Invalid opcode
opcodeHandlers.[0xF5] <- (fun () -> push_2(A,FF());  PC <- PC + 1us; 4uy) //PUSH AF
opcodeHandlers.[0xF6] <- (fun () -> orA(readAddress(PC+1us)); PC <- PC + 2us; 2uy) //OR A,n
opcodeHandlers.[0xF7] <- (fun () -> rst(0x30us); 8uy) //RST 30
opcodeHandlers.[0xF8] <- (fun () -> H <- byte (((SP+ uint16 (readAddress(PC + 1us))) &&& 0xFF00us) >>> 8) ; L <- byte ((SP+ uint16 (readAddress(PC + 1us))) &&& 0xFFus) ; PC <- PC + 2us; 3uy) //LD HL,SP+n  //TODO: FLAGS
opcodeHandlers.[0xF9] <- (fun () -> SP <- (uint16 H <<< 8 ||| uint16 L); PC <- PC + 1us; 2uy) //LD SP,HL
opcodeHandlers.[0xFA] <- (fun () -> A <- readAddress_2(readAddress(PC + 2us), readAddress(PC + 1us)); PC <- PC + 3us; 4uy) //LD A,(nn)
opcodeHandlers.[0xFB] <- (fun () -> PC <- PC + 1us; IME <- true; 1uy) //EI TODO: "Not immediatly"
//opcodeHandlers.[0xFC] //Invalid opcode
//opcodeHandlers.[0xFD] //Invalid opcode
opcodeHandlers.[0xFE] <- (fun () -> cp(readAddress(PC + 1us)); PC <- PC + 2us; 2uy) //CP A,n
opcodeHandlers.[0xFF] <- (fun () -> rst(0x38us); 8uy) //RST 38

CBopcodeHandlers.[0x00] <- (fun () -> rlc(&B);    PC <- PC + 1us; 2uy) //RLC B 
CBopcodeHandlers.[0x01] <- (fun () -> rlc(&C);    PC <- PC + 1us; 2uy) //RLC C
CBopcodeHandlers.[0x02] <- (fun () -> rlc(&D);    PC <- PC + 1us; 2uy) //RLC D
CBopcodeHandlers.[0x03] <- (fun () -> rlc(&E);    PC <- PC + 1us; 2uy) //RLC E
CBopcodeHandlers.[0x04] <- (fun () -> rlc(&H);    PC <- PC + 1us; 2uy) //RLC H
CBopcodeHandlers.[0x05] <- (fun () -> rlc(&L);    PC <- PC + 1us; 2uy) //RLC L
CBopcodeHandlers.[0x06] <- (fun () -> rlcHL();    PC <- PC + 1us; 4uy) //RLC (HL)
CBopcodeHandlers.[0x07] <- (fun () -> rlc(&A);    PC <- PC + 1us; 2uy) //RLC A
CBopcodeHandlers.[0x08] <- (fun () -> rrc(&B);    PC <- PC + 1us; 2uy) //RRC B
CBopcodeHandlers.[0x09] <- (fun () -> rrc(&C);    PC <- PC + 1us; 2uy) //RRC C
CBopcodeHandlers.[0x0A] <- (fun () -> rrc(&D);    PC <- PC + 1us; 2uy) //RRC D
CBopcodeHandlers.[0x0B] <- (fun () -> rrc(&E);    PC <- PC + 1us; 2uy) //RRC E
CBopcodeHandlers.[0x0C] <- (fun () -> rrc(&H);    PC <- PC + 1us; 2uy) //RRC H
CBopcodeHandlers.[0x0D] <- (fun () -> rrc(&L);    PC <- PC + 1us; 2uy) //RRC L
CBopcodeHandlers.[0x0E] <- (fun () -> rrcHL();    PC <- PC + 1us; 4uy) //RRC HL
CBopcodeHandlers.[0x0F] <- (fun () -> rrc(&A);    PC <- PC + 1us; 2uy) //RRC A
CBopcodeHandlers.[0x10] <- (fun () -> rl(&B);     PC <- PC + 1us; 2uy) //RL B
CBopcodeHandlers.[0x11] <- (fun () -> rl(&C);     PC <- PC + 1us; 2uy) //RL C
CBopcodeHandlers.[0x12] <- (fun () -> rl(&D);     PC <- PC + 1us; 2uy) //RL D
CBopcodeHandlers.[0x13] <- (fun () -> rl(&E);     PC <- PC + 1us; 2uy) //RL E
CBopcodeHandlers.[0x14] <- (fun () -> rl(&H);     PC <- PC + 1us; 2uy) //RL H
CBopcodeHandlers.[0x15] <- (fun () -> rl(&L);     PC <- PC + 1us; 2uy) //RL L
CBopcodeHandlers.[0x16] <- (fun () -> rlHL();     PC <- PC + 1us; 4uy) //RL (HL)
CBopcodeHandlers.[0x17] <- (fun () -> rl(&A);     PC <- PC + 1us; 2uy) //RL A
CBopcodeHandlers.[0x18] <- (fun () -> rr(&B);     PC <- PC + 1us; 2uy) //RR B
CBopcodeHandlers.[0x19] <- (fun () -> rr(&C);     PC <- PC + 1us; 2uy) //RR C
CBopcodeHandlers.[0x1A] <- (fun () -> rr(&D);     PC <- PC + 1us; 2uy) //RR D
CBopcodeHandlers.[0x1B] <- (fun () -> rr(&E);     PC <- PC + 1us; 2uy) //RR E
CBopcodeHandlers.[0x1C] <- (fun () -> rr(&H);     PC <- PC + 1us; 2uy) //RR H
CBopcodeHandlers.[0x1D] <- (fun () -> rr(&L);     PC <- PC + 1us; 2uy) //RR L
CBopcodeHandlers.[0x1E] <- (fun () -> rrHL();     PC <- PC + 1us; 4uy) //RR (HL)
CBopcodeHandlers.[0x1F] <- (fun () -> rr(&A);     PC <- PC + 1us; 2uy) //RR A
CBopcodeHandlers.[0x20] <- (fun () -> sla(&B);    PC <- PC + 1us; 2uy) //SLA B
CBopcodeHandlers.[0x21] <- (fun () -> sla(&C);    PC <- PC + 1us; 2uy) //SLA C
CBopcodeHandlers.[0x22] <- (fun () -> sla(&D);    PC <- PC + 1us; 2uy) //SLA D
CBopcodeHandlers.[0x23] <- (fun () -> sla(&E);    PC <- PC + 1us; 2uy) //SLA E
CBopcodeHandlers.[0x24] <- (fun () -> sla(&H);    PC <- PC + 1us; 2uy) //SLA H
CBopcodeHandlers.[0x25] <- (fun () -> sla(&L);    PC <- PC + 1us; 2uy) //SLA L
CBopcodeHandlers.[0x26] <- (fun () -> slaHL();    PC <- PC + 1us; 4uy) //SLA (HL)
CBopcodeHandlers.[0x27] <- (fun () -> sla(&A);    PC <- PC + 1us; 2uy) //SLA A
CBopcodeHandlers.[0x28] <- (fun () -> sra(&B);    PC <- PC + 1us; 2uy) //SRA B
CBopcodeHandlers.[0x29] <- (fun () -> sra(&C);    PC <- PC + 1us; 2uy) //SRA C
CBopcodeHandlers.[0x2A] <- (fun () -> sra(&D);    PC <- PC + 1us; 2uy) //SRA D
CBopcodeHandlers.[0x2B] <- (fun () -> sra(&E);    PC <- PC + 1us; 2uy) //SRA E
CBopcodeHandlers.[0x2C] <- (fun () -> sra(&H);    PC <- PC + 1us; 2uy) //SRA H
CBopcodeHandlers.[0x2D] <- (fun () -> sra(&L);    PC <- PC + 1us; 2uy) //SRA L
CBopcodeHandlers.[0x2E] <- (fun () -> sraHL();    PC <- PC + 1us; 4uy) //SRA (HL)
CBopcodeHandlers.[0x2F] <- (fun () -> sra(&A);    PC <- PC + 1us; 2uy) //SRA A
CBopcodeHandlers.[0x30] <- (fun () -> swap(&B);   PC <- PC + 1us; 2uy) //SWAP B
CBopcodeHandlers.[0x31] <- (fun () -> swap(&C);   PC <- PC + 1us; 2uy) //SWAP C
CBopcodeHandlers.[0x32] <- (fun () -> swap(&D);   PC <- PC + 1us; 2uy) //SWAP D
CBopcodeHandlers.[0x33] <- (fun () -> swap(&E);   PC <- PC + 1us; 2uy) //SWAP E
CBopcodeHandlers.[0x34] <- (fun () -> swap(&H);   PC <- PC + 1us; 2uy) //SWAP H
CBopcodeHandlers.[0x35] <- (fun () -> swap(&L);   PC <- PC + 1us; 2uy) //SWAP L
CBopcodeHandlers.[0x36] <- (fun () -> swapHL();   PC <- PC + 1us; 4uy) //SWAP (HL)
CBopcodeHandlers.[0x37] <- (fun () -> swap(&A);   PC <- PC + 1us; 2uy) //SWAP A
CBopcodeHandlers.[0x38] <- (fun () -> srl(&B);    PC <- PC + 1us; 2uy) //SRL B
CBopcodeHandlers.[0x39] <- (fun () -> srl(&C);    PC <- PC + 1us; 2uy) //SRL C
CBopcodeHandlers.[0x3A] <- (fun () -> srl(&D);    PC <- PC + 1us; 2uy) //SRL D
CBopcodeHandlers.[0x3B] <- (fun () -> srl(&E);    PC <- PC + 1us; 2uy) //SRL E
CBopcodeHandlers.[0x3C] <- (fun () -> srl(&H);    PC <- PC + 1us; 2uy) //SRL H
CBopcodeHandlers.[0x3D] <- (fun () -> srl(&L);    PC <- PC + 1us; 2uy) //SRL L
CBopcodeHandlers.[0x3E] <- (fun () -> srlHL();    PC <- PC + 1us; 4uy) //SRL (HL)
CBopcodeHandlers.[0x3F] <- (fun () -> srl(&A);    PC <- PC + 1us; 2uy) //SRL A
CBopcodeHandlers.[0x40] <- (fun () -> bit(0, B);  PC <- PC + 1us; 2uy) //BIT 0,B
CBopcodeHandlers.[0x41] <- (fun () -> bit(0, C);  PC <- PC + 1us; 2uy) //BIT 0,C
CBopcodeHandlers.[0x42] <- (fun () -> bit(0, D);  PC <- PC + 1us; 2uy) //BIT 0,D
CBopcodeHandlers.[0x43] <- (fun () -> bit(0, E);  PC <- PC + 1us; 2uy) //BIT 0,E
CBopcodeHandlers.[0x44] <- (fun () -> bit(0, H);  PC <- PC + 1us; 2uy) //BIT 0,H
CBopcodeHandlers.[0x45] <- (fun () -> bit(0, L);  PC <- PC + 1us; 2uy) //BIT 0,L
CBopcodeHandlers.[0x46] <- (fun () -> bitHL(0);   PC <- PC + 1us; 4uy) //BIT 0,HL
CBopcodeHandlers.[0x47] <- (fun () -> bit(0, A);  PC <- PC + 1us; 2uy) //BIT 0,A
CBopcodeHandlers.[0x48] <- (fun () -> bit(1, B);  PC <- PC + 1us; 2uy) //BIT 1,B
CBopcodeHandlers.[0x49] <- (fun () -> bit(1, C);  PC <- PC + 1us; 2uy) //BIT 1,C
CBopcodeHandlers.[0x4A] <- (fun () -> bit(1, D);  PC <- PC + 1us; 2uy) //BIT 1,D
CBopcodeHandlers.[0x4B] <- (fun () -> bit(1, E);  PC <- PC + 1us; 2uy) //BIT 1,E
CBopcodeHandlers.[0x4C] <- (fun () -> bit(1, H);  PC <- PC + 1us; 2uy) //BIT 1,H
CBopcodeHandlers.[0x4D] <- (fun () -> bit(1, L);  PC <- PC + 1us; 2uy) //BIT 1,L
CBopcodeHandlers.[0x4E] <- (fun () -> bitHL(1);   PC <- PC + 1us; 4uy) //BIT 1,(HL)
CBopcodeHandlers.[0x4F] <- (fun () -> bit(1, A);  PC <- PC + 1us; 2uy) //BIT 1,A
CBopcodeHandlers.[0x50] <- (fun () -> bit(2, B);  PC <- PC + 1us; 2uy) //BIT 2,B
CBopcodeHandlers.[0x51] <- (fun () -> bit(2, C);  PC <- PC + 1us; 2uy) //BIT 2,C
CBopcodeHandlers.[0x52] <- (fun () -> bit(2, D);  PC <- PC + 1us; 2uy) //BIT 2,D
CBopcodeHandlers.[0x53] <- (fun () -> bit(2, E);  PC <- PC + 1us; 2uy) //BIT 2,E
CBopcodeHandlers.[0x54] <- (fun () -> bit(2, H);  PC <- PC + 1us; 2uy) //BIT 2,H
CBopcodeHandlers.[0x55] <- (fun () -> bit(2, L);  PC <- PC + 1us; 2uy) //BIT 2,L
CBopcodeHandlers.[0x56] <- (fun () -> bitHL(2);   PC <- PC + 1us; 4uy) //BIT 2,(HL)
CBopcodeHandlers.[0x57] <- (fun () -> bit(2, A);  PC <- PC + 1us; 2uy) //BIT 2,A
CBopcodeHandlers.[0x58] <- (fun () -> bit(3, B);  PC <- PC + 1us; 2uy) //BIT 3,B
CBopcodeHandlers.[0x59] <- (fun () -> bit(3, C);  PC <- PC + 1us; 2uy) //BIT 3,C
CBopcodeHandlers.[0x5A] <- (fun () -> bit(3, D);  PC <- PC + 1us; 2uy) //BIT 3,D
CBopcodeHandlers.[0x5B] <- (fun () -> bit(3, E);  PC <- PC + 1us; 2uy) //BIT 3,E
CBopcodeHandlers.[0x5C] <- (fun () -> bit(3, H);  PC <- PC + 1us; 2uy) //BIT 3,H
CBopcodeHandlers.[0x5D] <- (fun () -> bit(3, L);  PC <- PC + 1us; 2uy) //BIT 3,L
CBopcodeHandlers.[0x5E] <- (fun () -> bitHL(3);   PC <- PC + 1us; 4uy) //BIT 3,(HL)
CBopcodeHandlers.[0x5F] <- (fun () -> bit(3, A);  PC <- PC + 1us; 2uy) //BIT 3,A
CBopcodeHandlers.[0x60] <- (fun () -> bit(4, B);  PC <- PC + 1us; 2uy) //BIT 4,B
CBopcodeHandlers.[0x61] <- (fun () -> bit(4, C);  PC <- PC + 1us; 2uy) //BIT 4,C
CBopcodeHandlers.[0x62] <- (fun () -> bit(4, D);  PC <- PC + 1us; 2uy) //BIT 4,D
CBopcodeHandlers.[0x63] <- (fun () -> bit(4, E);  PC <- PC + 1us; 2uy) //BIT 4,E
CBopcodeHandlers.[0x64] <- (fun () -> bit(4, H);  PC <- PC + 1us; 2uy) //BIT 4,H
CBopcodeHandlers.[0x65] <- (fun () -> bit(4, L);  PC <- PC + 1us; 2uy) //BIT 4,L
CBopcodeHandlers.[0x66] <- (fun () -> bitHL(4);   PC <- PC + 1us; 4uy) //BIT 4,(HL)
CBopcodeHandlers.[0x67] <- (fun () -> bit(4, A);  PC <- PC + 1us; 2uy) //BIT 4,A
CBopcodeHandlers.[0x68] <- (fun () -> bit(5, B);  PC <- PC + 1us; 2uy) //BIT 5,B
CBopcodeHandlers.[0x69] <- (fun () -> bit(5, C);  PC <- PC + 1us; 2uy) //BIT 5,C
CBopcodeHandlers.[0x6A] <- (fun () -> bit(5, D);  PC <- PC + 1us; 2uy) //BIT 5,D
CBopcodeHandlers.[0x6B] <- (fun () -> bit(5, E);  PC <- PC + 1us; 2uy) //BIT 5,E
CBopcodeHandlers.[0x6C] <- (fun () -> bit(5, H);  PC <- PC + 1us; 2uy) //BIT 5,H
CBopcodeHandlers.[0x6D] <- (fun () -> bit(5, L);  PC <- PC + 1us; 2uy) //BIT 5,L
CBopcodeHandlers.[0x6E] <- (fun () -> bitHL(5);   PC <- PC + 1us; 4uy) //BIT 5,(HL)
CBopcodeHandlers.[0x6F] <- (fun () -> bit(5, A);  PC <- PC + 1us; 2uy) //BIT 5,A
CBopcodeHandlers.[0x70] <- (fun () -> bit(6, B);  PC <- PC + 1us; 2uy) //BIT 6,B
CBopcodeHandlers.[0x71] <- (fun () -> bit(6, C);  PC <- PC + 1us; 2uy) //BIT 6,C
CBopcodeHandlers.[0x72] <- (fun () -> bit(6, D);  PC <- PC + 1us; 2uy) //BIT 6,D
CBopcodeHandlers.[0x73] <- (fun () -> bit(6, E);  PC <- PC + 1us; 2uy) //BIT 6,E
CBopcodeHandlers.[0x74] <- (fun () -> bit(6, H);  PC <- PC + 1us; 2uy) //BIT 6,H
CBopcodeHandlers.[0x75] <- (fun () -> bit(6, L);  PC <- PC + 1us; 2uy) //BIT 6,L
CBopcodeHandlers.[0x76] <- (fun () -> bitHL(6);   PC <- PC + 1us; 4uy) //BIT 6,(HL)
CBopcodeHandlers.[0x77] <- (fun () -> bit(6, A);  PC <- PC + 1us; 2uy) //BIT 6,A
CBopcodeHandlers.[0x78] <- (fun () -> bit(7, B);  PC <- PC + 1us; 2uy) //BIT 7,B
CBopcodeHandlers.[0x79] <- (fun () -> bit(7, C);  PC <- PC + 1us; 2uy) //BIT 7,C
CBopcodeHandlers.[0x7A] <- (fun () -> bit(7, D);  PC <- PC + 1us; 2uy) //BIT 7,D
CBopcodeHandlers.[0x7B] <- (fun () -> bit(7, E);  PC <- PC + 1us; 2uy) //BIT 7,E
CBopcodeHandlers.[0x7C] <- (fun () -> bit(7, H);  PC <- PC + 1us; 2uy) //BIT 7,H
CBopcodeHandlers.[0x7D] <- (fun () -> bit(7, L);  PC <- PC + 1us; 2uy) //BIT 7,L
CBopcodeHandlers.[0x7E] <- (fun () -> bitHL(7);   PC <- PC + 1us; 4uy) //BIT 7,(HL)
CBopcodeHandlers.[0x7F] <- (fun () -> bit(7, A);  PC <- PC + 1us; 2uy) //BIT 7,A
CBopcodeHandlers.[0x80] <- (fun () -> res(0, &B); PC <- PC + 1us; 2uy) //RES 0,B
CBopcodeHandlers.[0x81] <- (fun () -> res(0, &C); PC <- PC + 1us; 2uy) //RES 0,C
CBopcodeHandlers.[0x82] <- (fun () -> res(0, &D); PC <- PC + 1us; 2uy) //RES 0,D
CBopcodeHandlers.[0x83] <- (fun () -> res(0, &E); PC <- PC + 1us; 2uy) //RES 0,E
CBopcodeHandlers.[0x84] <- (fun () -> res(0, &H); PC <- PC + 1us; 2uy) //RES 0,H
CBopcodeHandlers.[0x85] <- (fun () -> res(0, &L); PC <- PC + 1us; 2uy) //RES 0,L
CBopcodeHandlers.[0x86] <- (fun () -> resHL(0);   PC <- PC + 1us; 4uy) //RES 0,(HL)
CBopcodeHandlers.[0x87] <- (fun () -> res(0, &A); PC <- PC + 1us; 2uy) //RES 0,A
CBopcodeHandlers.[0x88] <- (fun () -> res(1, &B); PC <- PC + 1us; 2uy) //RES 1,B
CBopcodeHandlers.[0x89] <- (fun () -> res(1, &C); PC <- PC + 1us; 2uy) //RES 1,C
CBopcodeHandlers.[0x8A] <- (fun () -> res(1, &D); PC <- PC + 1us; 2uy) //RES 1,D
CBopcodeHandlers.[0x8B] <- (fun () -> res(1, &E); PC <- PC + 1us; 2uy) //RES 1,E
CBopcodeHandlers.[0x8C] <- (fun () -> res(1, &H); PC <- PC + 1us; 2uy) //RES 1,H
CBopcodeHandlers.[0x8D] <- (fun () -> res(1, &L); PC <- PC + 1us; 2uy) //RES 1,L
CBopcodeHandlers.[0x8E] <- (fun () -> resHL(1);   PC <- PC + 1us; 4uy) //RES 1,(HL)
CBopcodeHandlers.[0x8F] <- (fun () -> res(1, &A); PC <- PC + 1us; 2uy) //RES 1,A
CBopcodeHandlers.[0x90] <- (fun () -> res(2, &B); PC <- PC + 1us; 2uy) //RES 2,B
CBopcodeHandlers.[0x91] <- (fun () -> res(2, &C); PC <- PC + 1us; 2uy) //RES 2,C
CBopcodeHandlers.[0x92] <- (fun () -> res(2, &D); PC <- PC + 1us; 2uy) //RES 2,D
CBopcodeHandlers.[0x93] <- (fun () -> res(2, &E); PC <- PC + 1us; 2uy) //RES 2,E
CBopcodeHandlers.[0x94] <- (fun () -> res(2, &H); PC <- PC + 1us; 2uy) //RES 2,H
CBopcodeHandlers.[0x95] <- (fun () -> res(2, &L); PC <- PC + 1us; 2uy) //RES 2,L
CBopcodeHandlers.[0x96] <- (fun () -> resHL(2);   PC <- PC + 1us; 4uy) //RES 2,(HL)
CBopcodeHandlers.[0x97] <- (fun () -> res(2, &A); PC <- PC + 1us; 2uy) //RES 2,A
CBopcodeHandlers.[0x98] <- (fun () -> res(3, &B); PC <- PC + 1us; 2uy) //RES 3,B
CBopcodeHandlers.[0x99] <- (fun () -> res(3, &C); PC <- PC + 1us; 2uy) //RES 3,C
CBopcodeHandlers.[0x9A] <- (fun () -> res(3, &D); PC <- PC + 1us; 2uy) //RES 3,D
CBopcodeHandlers.[0x9B] <- (fun () -> res(3, &E); PC <- PC + 1us; 2uy) //RES 3,E
CBopcodeHandlers.[0x9C] <- (fun () -> res(3, &H); PC <- PC + 1us; 2uy) //RES 3,H
CBopcodeHandlers.[0x9D] <- (fun () -> res(3, &L); PC <- PC + 1us; 2uy) //RES 3,L
CBopcodeHandlers.[0x9E] <- (fun () -> resHL(3);   PC <- PC + 1us; 4uy) //RES 3,(HL)
CBopcodeHandlers.[0x9F] <- (fun () -> res(3, &A); PC <- PC + 1us; 2uy) //RES 3,A
CBopcodeHandlers.[0xA0] <- (fun () -> res(4, &B); PC <- PC + 1us; 2uy) //RES 4,B
CBopcodeHandlers.[0xA1] <- (fun () -> res(4, &C); PC <- PC + 1us; 2uy) //RES 4,C
CBopcodeHandlers.[0xA2] <- (fun () -> res(4, &D); PC <- PC + 1us; 2uy) //RES 4,D
CBopcodeHandlers.[0xA3] <- (fun () -> res(4, &E); PC <- PC + 1us; 2uy) //RES 4,E
CBopcodeHandlers.[0xA4] <- (fun () -> res(4, &H); PC <- PC + 1us; 2uy) //RES 4,H
CBopcodeHandlers.[0xA5] <- (fun () -> res(4, &L); PC <- PC + 1us; 2uy) //RES 4,L
CBopcodeHandlers.[0xA6] <- (fun () -> resHL(4);   PC <- PC + 1us; 4uy) //RES 4,(HL)
CBopcodeHandlers.[0xA7] <- (fun () -> res(4, &A); PC <- PC + 1us; 2uy) //RES 4,A
CBopcodeHandlers.[0xA8] <- (fun () -> res(5, &B); PC <- PC + 1us; 2uy) //RES 5,B
CBopcodeHandlers.[0xA9] <- (fun () -> res(5, &C); PC <- PC + 1us; 2uy) //RES 5,C
CBopcodeHandlers.[0xAA] <- (fun () -> res(5, &D); PC <- PC + 1us; 2uy) //RES 5,D
CBopcodeHandlers.[0xAB] <- (fun () -> res(5, &E); PC <- PC + 1us; 2uy) //RES 5,E
CBopcodeHandlers.[0xAC] <- (fun () -> res(5, &H); PC <- PC + 1us; 2uy) //RES 5,H
CBopcodeHandlers.[0xAD] <- (fun () -> res(5, &L); PC <- PC + 1us; 2uy) //RES 5,L
CBopcodeHandlers.[0xAE] <- (fun () -> resHL(5);   PC <- PC + 1us; 4uy) //RES 5,(HL)
CBopcodeHandlers.[0xAF] <- (fun () -> res(5, &A); PC <- PC + 1us; 2uy) //RES 5,A
CBopcodeHandlers.[0xB0] <- (fun () -> res(6, &B); PC <- PC + 1us; 2uy) //RES 6,B
CBopcodeHandlers.[0xB1] <- (fun () -> res(6, &C); PC <- PC + 1us; 2uy) //RES 6,C
CBopcodeHandlers.[0xB2] <- (fun () -> res(6, &D); PC <- PC + 1us; 2uy) //RES 6,D
CBopcodeHandlers.[0xB3] <- (fun () -> res(6, &E); PC <- PC + 1us; 2uy) //RES 6,E
CBopcodeHandlers.[0xB4] <- (fun () -> res(6, &H); PC <- PC + 1us; 2uy) //RES 6,H
CBopcodeHandlers.[0xB5] <- (fun () -> res(6, &L); PC <- PC + 1us; 2uy) //RES 6,L
CBopcodeHandlers.[0xB6] <- (fun () -> resHL(6);   PC <- PC + 1us; 4uy) //RES 6,(HL)
CBopcodeHandlers.[0xB7] <- (fun () -> res(6, &A); PC <- PC + 1us; 2uy) //RES 6,A
CBopcodeHandlers.[0xB8] <- (fun () -> res(7, &B); PC <- PC + 1us; 2uy) //RES 7,B
CBopcodeHandlers.[0xB9] <- (fun () -> res(7, &C); PC <- PC + 1us; 2uy) //RES 7,C
CBopcodeHandlers.[0xBA] <- (fun () -> res(7, &D); PC <- PC + 1us; 2uy) //RES 7,D
CBopcodeHandlers.[0xBB] <- (fun () -> res(7, &E); PC <- PC + 1us; 2uy) //RES 7,E
CBopcodeHandlers.[0xBC] <- (fun () -> res(7, &H); PC <- PC + 1us; 2uy) //RES 7,H
CBopcodeHandlers.[0xBD] <- (fun () -> res(7, &L); PC <- PC + 1us; 2uy) //RES 7,L
CBopcodeHandlers.[0xBE] <- (fun () -> resHL(7);   PC <- PC + 1us; 4uy) //RES 7,(HL)
CBopcodeHandlers.[0xBF] <- (fun () -> res(7, &A); PC <- PC + 1us; 2uy) //RES 7,A
CBopcodeHandlers.[0xC0] <- (fun () -> set(0, &B); PC <- PC + 1us; 2uy) //SET 0,B
CBopcodeHandlers.[0xC1] <- (fun () -> set(0, &C); PC <- PC + 1us; 2uy) //SET 0,C
CBopcodeHandlers.[0xC2] <- (fun () -> set(0, &D); PC <- PC + 1us; 2uy) //SET 0,D
CBopcodeHandlers.[0xC3] <- (fun () -> set(0, &E); PC <- PC + 1us; 2uy) //SET 0,E
CBopcodeHandlers.[0xC4] <- (fun () -> set(0, &H); PC <- PC + 1us; 2uy) //SET 0,H
CBopcodeHandlers.[0xC5] <- (fun () -> set(0, &L); PC <- PC + 1us; 2uy) //SET 0,L
CBopcodeHandlers.[0xC6] <- (fun () -> setHL(0);   PC <- PC + 1us; 4uy) //SET 0,(HL)
CBopcodeHandlers.[0xC7] <- (fun () -> set(0, &A); PC <- PC + 1us; 2uy) //SET 0,A
CBopcodeHandlers.[0xC8] <- (fun () -> set(1, &B); PC <- PC + 1us; 2uy) //SET 1,B
CBopcodeHandlers.[0xC9] <- (fun () -> set(1, &C); PC <- PC + 1us; 2uy) //SET 1,C
CBopcodeHandlers.[0xCA] <- (fun () -> set(1, &D); PC <- PC + 1us; 2uy) //SET 1,D
CBopcodeHandlers.[0xCB] <- (fun () -> set(1, &E); PC <- PC + 1us; 2uy) //SET 1,E
CBopcodeHandlers.[0xCC] <- (fun () -> set(1, &H); PC <- PC + 1us; 2uy) //SET 1,H
CBopcodeHandlers.[0xCD] <- (fun () -> set(1, &L); PC <- PC + 1us; 2uy) //SET 1,L
CBopcodeHandlers.[0xCE] <- (fun () -> setHL(1);   PC <- PC + 1us; 4uy) //SET 1,(HL)
CBopcodeHandlers.[0xCF] <- (fun () -> set(1, &A); PC <- PC + 1us; 2uy) //SET 1,A
CBopcodeHandlers.[0xD0] <- (fun () -> set(2, &B); PC <- PC + 1us; 2uy) //SET 2,B
CBopcodeHandlers.[0xD1] <- (fun () -> set(2, &C); PC <- PC + 1us; 2uy) //SET 2,C
CBopcodeHandlers.[0xD2] <- (fun () -> set(2, &D); PC <- PC + 1us; 2uy) //SET 2,D
CBopcodeHandlers.[0xD3] <- (fun () -> set(2, &E); PC <- PC + 1us; 2uy) //SET 2,E
CBopcodeHandlers.[0xD4] <- (fun () -> set(2, &H); PC <- PC + 1us; 2uy) //SET 2,H
CBopcodeHandlers.[0xD5] <- (fun () -> set(2, &L); PC <- PC + 1us; 2uy) //SET 2,L
CBopcodeHandlers.[0xD6] <- (fun () -> setHL(2);   PC <- PC + 1us; 4uy) //SET 2,(HL)
CBopcodeHandlers.[0xD7] <- (fun () -> set(2, &A); PC <- PC + 1us; 2uy) //SET 2,A
CBopcodeHandlers.[0xD8] <- (fun () -> set(3, &B); PC <- PC + 1us; 2uy) //SET 3,B
CBopcodeHandlers.[0xD9] <- (fun () -> set(3, &C); PC <- PC + 1us; 2uy) //SET 3,C
CBopcodeHandlers.[0xDA] <- (fun () -> set(3, &D); PC <- PC + 1us; 2uy) //SET 3,D
CBopcodeHandlers.[0xDB] <- (fun () -> set(3, &E); PC <- PC + 1us; 2uy) //SET 3,E
CBopcodeHandlers.[0xDC] <- (fun () -> set(3, &H); PC <- PC + 1us; 2uy) //SET 3,H
CBopcodeHandlers.[0xDD] <- (fun () -> set(3, &L); PC <- PC + 1us; 2uy) //SET 3,L
CBopcodeHandlers.[0xDE] <- (fun () -> setHL(3);   PC <- PC + 1us; 4uy) //SET 3,(HL)
CBopcodeHandlers.[0xDF] <- (fun () -> set(3, &A); PC <- PC + 1us; 2uy) //SET 3,A
CBopcodeHandlers.[0xE0] <- (fun () -> set(4, &B); PC <- PC + 1us; 2uy) //SET 4,B
CBopcodeHandlers.[0xE1] <- (fun () -> set(4, &C); PC <- PC + 1us; 2uy) //SET 4,C
CBopcodeHandlers.[0xE2] <- (fun () -> set(4, &D); PC <- PC + 1us; 2uy) //SET 4,D
CBopcodeHandlers.[0xE3] <- (fun () -> set(4, &E); PC <- PC + 1us; 2uy) //SET 4,E
CBopcodeHandlers.[0xE4] <- (fun () -> set(4, &H); PC <- PC + 1us; 2uy) //SET 4,H
CBopcodeHandlers.[0xE5] <- (fun () -> set(4, &L); PC <- PC + 1us; 2uy) //SET 4,L
CBopcodeHandlers.[0xE6] <- (fun () -> setHL(4);   PC <- PC + 1us; 4uy) //SET 4,(HL)
CBopcodeHandlers.[0xE7] <- (fun () -> set(4, &A); PC <- PC + 1us; 2uy) //SET 4,A
CBopcodeHandlers.[0xE8] <- (fun () -> set(5, &B); PC <- PC + 1us; 2uy) //SET 5,B
CBopcodeHandlers.[0xE9] <- (fun () -> set(5, &C); PC <- PC + 1us; 2uy) //SET 5,C
CBopcodeHandlers.[0xEA] <- (fun () -> set(5, &D); PC <- PC + 1us; 2uy) //SET 5,D
CBopcodeHandlers.[0xEB] <- (fun () -> set(5, &E); PC <- PC + 1us; 2uy) //SET 5,E
CBopcodeHandlers.[0xEC] <- (fun () -> set(5, &H); PC <- PC + 1us; 2uy) //SET 5,H
CBopcodeHandlers.[0xED] <- (fun () -> set(5, &L); PC <- PC + 1us; 2uy) //SET 5,L
CBopcodeHandlers.[0xEE] <- (fun () -> setHL(5);   PC <- PC + 1us; 4uy) //SET 5,(HL)
CBopcodeHandlers.[0xEF] <- (fun () -> set(5, &A); PC <- PC + 1us; 2uy) //SET 5,A
CBopcodeHandlers.[0xF0] <- (fun () -> set(6, &B); PC <- PC + 1us; 2uy) //SET 6,B
CBopcodeHandlers.[0xF1] <- (fun () -> set(6, &C); PC <- PC + 1us; 2uy) //SET 6,C
CBopcodeHandlers.[0xF2] <- (fun () -> set(6, &D); PC <- PC + 1us; 2uy) //SET 6,D
CBopcodeHandlers.[0xF3] <- (fun () -> set(6, &E); PC <- PC + 1us; 2uy) //SET 6,E
CBopcodeHandlers.[0xF4] <- (fun () -> set(6, &H); PC <- PC + 1us; 2uy) //SET 6,H
CBopcodeHandlers.[0xF5] <- (fun () -> set(6, &L); PC <- PC + 1us; 2uy) //SET 6,L
CBopcodeHandlers.[0xF6] <- (fun () -> setHL(6);   PC <- PC + 1us; 4uy) //SET 6,(HL)
CBopcodeHandlers.[0xF7] <- (fun () -> set(6, &A); PC <- PC + 1us; 2uy) //SET 6,A
CBopcodeHandlers.[0xF8] <- (fun () -> set(7, &B); PC <- PC + 1us; 2uy) //SET 7,B
CBopcodeHandlers.[0xF9] <- (fun () -> set(7, &C); PC <- PC + 1us; 2uy) //SET 7,C
CBopcodeHandlers.[0xFA] <- (fun () -> set(7, &D); PC <- PC + 1us; 2uy) //SET 7,D
CBopcodeHandlers.[0xFB] <- (fun () -> set(7, &E); PC <- PC + 1us; 2uy) //SET 7,E
CBopcodeHandlers.[0xFC] <- (fun () -> set(7, &H); PC <- PC + 1us; 2uy) //SET 7,H
CBopcodeHandlers.[0xFD] <- (fun () -> set(7, &L); PC <- PC + 1us; 2uy) //SET 7,L
CBopcodeHandlers.[0xFE] <- (fun () -> setHL(7);   PC <- PC + 1us; 4uy) //SET 7,(HL)
CBopcodeHandlers.[0xFF] <- (fun () -> set(7, &A); PC <- PC + 1us; 2uy) //SET 7,A


let screenBuffer = Array.create (SCREEN_WIDTH*SCREEN_HEIGHT) 0
        
let JumpToInterrupt (address:uint16, bit:int) = 
    if ((memory.[int IF] &&& (1uy <<< bit)) >= 1uy) && ((memory.[int IE] &&& (1uy <<< bit)) >= 1uy) then
        IME <- false ; lcdCycles <- lcdCycles + 32; memory.[int IF] <- memory.[int IF] &&& ~~~(1uy <<< bit); 
        push(PC) ; PC <- address ; true 
    else false

let SetInterrupt (bit:int) = memory.[int IF] <- memory.[int IF] ||| (1uy <<< bit)
let SetStatusInterruptIfModeBitSelected (bit:int) = if (memory.[int STAT] &&& (1uy <<< bit)) >= 1uy then SetInterrupt(LCD_STATUS_INT_BIT)
let SetStatMode (mode:byte) = 
    if memory.[int STAT] <> ((memory.[int STAT] &&& 0xFCuy) ||| mode) then  
        memory.[int STAT] <- (memory.[int STAT] &&& 0xFCuy) ||| mode ; true
    else false 

let incrementLY () =
    if memory.[int LYC] = memory.[int LY] then
        SetStatusInterruptIfModeBitSelected(STAT_LY_LYC_BIT) 
        memory.[int STAT] <- memory.[int STAT] ||| 0b100uy 
    else 
        memory.[int STAT] <- memory.[int STAT] &&& ~~~(0b100uy)
    memory.[int LY] <- memory.[int LY] + 1uy
    if memory.[int LY] = 154uy then 
        memory.[int LY] <- 0uy
    
let Loop  =
    async {
    while true do
        if not stopped then

            cycles <- opcodeHandlers.[int (readAddress(PC))]() * 4uy
            if cycles = 0uy then do
                MessageBox.Show(String.Format("Invalid Opcode {2}{0:X2} at 0x{1:X4}", readAddress(PC), (if unhandledCBOpcode then PC-1us else PC), if unhandledCBOpcode then "CB " else String.Empty)); 
                Environment.Exit(1)
            
            lcdCycles <- lcdCycles + int cycles

            if IME then
                if not (JumpToInterrupt(P10_P13_INT, P10_P13_INT_BIT)) then //priority 5
                    if not (JumpToInterrupt(TIMEROF_INT, TIMEROF_INT_BIT)) then //priority 3
                        if not (JumpToInterrupt(LCD_STATUS_INT, LCD_STATUS_INT_BIT)) then //priority 2
                            JumpToInterrupt(VBLANK_INT, VBLANK_INT_BIT)  //priority 1 

            //OAM (10) -> OAM&RAM (11) -> HBLANK (00) --(LY < 144)--> OAM (10) ...  
            //OAM (10) -> OAM&RAM (11) -> HBLANK (00) --(LY = 144)--> VBLANK(LY 144-154) (01) -> OAM (10) ...

            if memory.[int LY] < 144uy then
                //OAM&RAM (Mode 11, 169~175)
                if lcdCycles >= (80+172) then //OAM&RAM -> HBLANK
                    if SetStatMode(STAT_MODE_00_HBLANK) then SetStatusInterruptIfModeBitSelected(STAT_MODE_00_BIT)
                //OAM (Mode 10, 77~83 clks)
                else if lcdCycles >= 80 then //OAM -> OAM&RAM 
                    SetStatMode(STAT_MODE_11_OAM_RAM)

            
            //HBLANK. (Mode 00, 201~207 clks) A complete cycle through these states takes 456 clks.
            if lcdCycles >= (80+172+204) then  //456
                lcdCycles <- lcdCycles - 456
                let y = int memory.[int LY]
                if y < 144 then  //HBLANK --(LY < 144)--> OAM   
                    if y < 143 then
                        SetStatMode(STAT_MODE_10_OAM)
                        SetStatusInterruptIfModeBitSelected(STAT_MODE_10_BIT)   
                    for x in [0..SCREEN_WIDTH-1] do 
                        let tileOffset = (uint16 ((x + int (memory.[int SCROLLX]))/8) + uint16 (32*((y+int (memory.[int SCROLLY]))/8))) % 0x400us
                        let tilePixelX = uint16 ((x+int (memory.[int SCROLLX]))%8)
                        let tilePixelY = uint16 ((y+int (memory.[int SCROLLY]))%8)
                        let tileIndex = readAddress(BG_TILE_MAP_SEL + tileOffset)
                        let address = TILE_PATTERN_TABLE_SEL + uint16 (if TILE_PATTERN_TABLE_SEL = TILE_PATTERN_TABLE_1 then (0x800s + ((int16 (sbyte tileIndex)) * 16s)) else (int16 tileIndex*16s)) + (tilePixelY*2us)
                        screenBuffer.[(y*SCREEN_WIDTH) + x] <- (if readAddress(address) &&& (0b10000000uy >>> int tilePixelX) > 0uy then 1 else 0) ||| (if readAddress(address+1us) &&& (0b10000000uy >>> int tilePixelX) > 0uy then 0b10 else 0)
                    
                    for sprite in [(int (fst OAM))..4..(int (snd OAM))] do
                        let spx,spy,pattern,flipx,flipy = int memory.[sprite+1], int memory.[sprite], int memory.[sprite+2], int (if (memory.[sprite+3] &&& (1uy <<< 5)) > 0uy then 1uy else 0uy), int (if (memory.[sprite+3] &&& (1uy <<< 6)) > 0uy then 1uy else 0uy) 
                        if spx > 0 && spy > 0 && y >= (spy-16) && y < (spy-16+8) then
                            for tilePixelX in [0..7] do
                                let ftilePixelX = if flipx = 1 then 7-tilePixelX else tilePixelX
                                let address = TILE_PATTERN_TABLE_0 + uint16 ((pattern*16) + ((if flipy = 1 then (7-(y-(spy-16))) else y-(spy-16))*2))
                                let color = (if readAddress(address) &&& (0b10000000uy >>> ftilePixelX) > 0uy then 1 else 0) ||| (if readAddress(address+1us) &&& (0b10000000uy >>> ftilePixelX) > 0uy then 0b10 else 0)
                                if color > 0 then screenBuffer.[(y*SCREEN_WIDTH) + spx - 8 + tilePixelX] <- color
                                     
                incrementLY() //LY can go from 0 to 153 

                // VBLANK (144 -> 154). VBlank lasts 4560 clks (456 * (154 - 144))
                if memory.[int LY] = 144uy then //HBLANK --(LY = 144)--> VBLANK
                    SetStatMode(STAT_MODE_01_VBLANK)
                    SetStatusInterruptIfModeBitSelected(STAT_MODE_01_BIT)   
                    SetInterrupt(VBLANK_INT_BIT)
                    
                    // LCD ON
                    if (memory.[int LCDC] &&& 0b10000000uy) > 1uy then 
                         //BG ON
                        if (memory.[int LCDC] &&& 1uy) = 1uy then
                            form.Invalidate() 

                if memory.[int LY] = 0uy then //VBLANK -> OAM
                    //VBLANK END. A complete screen refresh occurs every 70224 clks (456*154).
                    frameCount <- frameCount + 1
                    SetStatMode(STAT_MODE_10_OAM)
                    SetStatusInterruptIfModeBitSelected(STAT_MODE_10_BIT) 

            //TAC TIMER
            if memory.[int TAC] &&& (1uy <<< TAC_TIMER_STOP_BIT) > 1uy then 
                timerCycles <- timerCycles + int cycles
                if timerCycles >= timerOverflow then
                    timerCycles <- timerCycles - timerOverflow
                    memory.[int TIMA] <- memory.[int TIMA] + 1uy;
                    if memory.[int TIMA] = 0uy then
                        memory.[int TIMA] <- memory.[int TMA]
                        SetInterrupt(TIMEROF_INT_BIT)

            //DIV
            divCycles <- divCycles + int cycles
            if divCycles > 256 then
                divCycles <- divCycles - 256
                memory.[int DIV] <- memory.[int DIV] + 1uy
    }

let fpsBrush = new SolidBrush(Color.Yellow)
let brushes = [| new SolidBrush(Color.FromArgb(223, 253, 234)); new SolidBrush(Color.FromArgb(181, 227, 198)); new SolidBrush(Color.FromArgb(162, 206, 178));  new SolidBrush(Color.FromArgb(3, 36, 15)) |]
let Draw (args:PaintEventArgs) =
    for y in [0..SCREEN_HEIGHT-1] do
        for x in [0..SCREEN_WIDTH-1] do
            args.Graphics.FillRectangle(brushes.[screenBuffer.[(y*SCREEN_WIDTH) + x]], x * SCALE, y * SCALE, SCALE, SCALE)
    args.Graphics.DrawString(String.Format("FPS: {0}", fps), new Font("Arial", 12.0f), fpsBrush, 0.0f,0.0f)

//for the TileViewer
let DrawTile (graphics:Graphics, address:uint16, x:int, y:int, scale:int) =
    let mutable tileY = 0
    for i in [address..2us..(address+0xFus)] do
        for tileX in [0..7] do
            let bitToTest = byte (0b10000000 >>> tileX)
            let color = int (((memory.[int i] &&& bitToTest) <<< 1) ||| (memory.[int i+1] &&& bitToTest))
            let brush = new SolidBrush(Color.FromArgb(0xFF000000 ||| (color * 0x555555)))
            graphics.FillRectangle(brush, (x*scale) + (tileX*scale),(y*scale) + (tileY*scale),scale,scale)
            brush.Dispose()
        tileY <- tileY + 1

let DrawTiles (args:PaintEventArgs) =
    let mutable x = 0
    let mutable y = 0
    let pen = new Pen(Color.White)
    pen.Width <- 0.5f
    for i in [0x8000us..0x10us..0x97F0us] do
        DrawTile(args.Graphics, i, x*8, y*8, 3)
        x <- x + 1
        if x = 16 then
            x <- 0
            y <- y + 1
    for v in [0..16] do
        args.Graphics.DrawLine(pen, v*8*3, 0, v*8*3, 24*8*3) 
    for h in [0..24] do
        args.Graphics.DrawLine(pen, 0, h*8*3, 16*8*3, h*8*3)
    pen.Dispose()

//for the MapViewer
let DrawMap (args:PaintEventArgs) =
    let mutable x = 0
    let mutable y = 0
    for i in [BG_TILE_MAP_SEL..(BG_TILE_MAP_SEL+0x3FFus)] do
        DrawTile(args.Graphics, TILE_PATTERN_TABLE_SEL + (uint16 memory.[int i] * 16us), x*8, y*8, 2)
        x <- x + 1
        if x = 32 then
            x <- 0
            y <- y + 1
    let pen = new Pen(Color.White)
    pen.Width <- 0.5f
    for v in [0..32] do
        args.Graphics.DrawLine(pen, v*8*2, 0, v*8*2, 32*8*2) 
    for h in [0..32] do
        args.Graphics.DrawLine(pen, 0, h*8*2, 32*8*2, h*8*2)
    pen.Dispose()

let FPSLoop  =
    async {
       while true do
            Thread.Sleep(1000)
            fps <- frameCount
            frameCount <- 0
    }

form.ClientSize <- new System.Drawing.Size(SCREEN_WIDTH * SCALE, SCREEN_HEIGHT * SCALE)
form.Load.Add(fun e -> form.BackColor <- Color.Black ; Async.Start(Loop) ; Async.Start(FPSLoop))
form.KeyDown.Add(fun e -> match e.KeyCode with
                        | Keys.Right -> SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 &&& ~~~0b0001uy //RIGHT
                        | Keys.Left ->  SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 &&& ~~~0b0010uy //LEFT
                        | Keys.Up ->    SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 &&& ~~~0b0100uy //UP
                        | Keys.Down ->  SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 &&& ~~~0b1000uy //DOWN
                        | Keys.Z ->     SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 &&& ~~~0b0001uy //A
                        | Keys.X ->     SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 &&& ~~~0b0010uy //B
                        | Keys.Space -> SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 &&& ~~~0b0100uy //SELECT
                        | Keys.Enter -> SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 &&& ~~~0b1000uy //START
                        | _ -> ())
form.KeyUp.Add(fun e -> stopped <- false
                        match e.KeyCode with
                        | Keys.Right -> SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 ||| 0b0001uy //RIGHT
                        | Keys.Left ->  SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 ||| 0b0010uy //LEFT
                        | Keys.Up ->    SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 ||| 0b0100uy //UP
                        | Keys.Down ->  SetInterrupt(P10_P13_INT_BIT) ; P14 <- P14 ||| 0b1000uy //DOWN
                        | Keys.Z ->     SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 ||| 0b0001uy //A
                        | Keys.X ->     SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 ||| 0b0010uy //B
                        | Keys.Space -> SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 ||| 0b0100uy //SELECT
                        | Keys.Enter -> SetInterrupt(P10_P13_INT_BIT) ; P15 <- P15 ||| 0b1000uy //START
                        | _ -> ())

let mutable mapViewer,tileViewer = new Form(),new Form()
let mapViewerMenuItem,tileViewerMenuItem = new MenuItem("Map Viewer"), new MenuItem("Tile Viewer")     
  
mapViewerMenuItem.Click.Add(fun e -> if mapViewer.IsDisposed then mapViewer <- new Form()
                                     mapViewer.Text <- "FunBoy - Map Viewer"
                                     mapViewer.ClientSize <- new System.Drawing.Size(32 * 2 * 8, 32 * 2 * 8)
                                     mapViewer.Paint.Add(DrawMap)  
                                     mapViewer.MaximizeBox <- false
                                     mapViewer.FormBorderStyle <- FormBorderStyle.FixedSingle
                                     mapViewer.Show())
tileViewerMenuItem.Click.Add(fun e -> if tileViewer.IsDisposed then tileViewer <- new Form()
                                      tileViewer.Text <- "FunBoy - Tile Viewer"
                                      tileViewer.Paint.Add(DrawTiles) 
                                      tileViewer.MaximizeBox <- false
                                      tileViewer.ClientSize <- new System.Drawing.Size(16 * 3 * 8, 24 * 3*8) 
                                      tileViewer.FormBorderStyle <- FormBorderStyle.FixedSingle
                                      tileViewer.Show())

form.ContextMenu <- new ContextMenu([| mapViewerMenuItem ; tileViewerMenuItem |])

form.Paint.Add(Draw)
form.Closed.Add(fun e -> fpsBrush.Dispose() ; Array.ForEach(brushes,(fun e -> e.Dispose()))) 
form.Text <- String.Concat("FunBoy - ", ASCIIEncoding.ASCII.GetString(memory.[0x0134..0x0142]))
form.MaximizeBox <- false
form.FormBorderStyle <- FormBorderStyle.FixedSingle
Application.Run(form)