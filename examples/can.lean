-- CAN 2.0 Frame Parser (ISO 11898 / Bosch CAN 2.0) in pure Lean 4 for bare-metal RISC-V
--
-- Parses the MCP2515 CAN controller SPI receive buffer format (13 bytes).
-- Supports CAN 2.0A (11-bit standard ID) and CAN 2.0B (29-bit extended ID).
-- Includes CRC-15/CAN computation per Bosch spec.
--
-- This file is the single source of truth for the CAN implementation.
-- examples/can_proof.lean imports it via `import can`, so the formal
-- proofs apply to this exact code.

-- RISC-V cycle counter (implemented in lean_rt.c)
@[extern "lean_cycles_now"]
opaque cyclesNow : IO UInt64

def getU8 (a : Array UInt8) (i : Nat) : UInt8 := a.getD i 0

/-! ## Data types -/

structure CanFrame where
  id       : UInt32      -- 11-bit or 29-bit, zero-extended
  extended : Bool        -- true = CAN 2.0B, false = CAN 2.0A
  rtr      : Bool        -- remote transmission request
  dlc      : UInt8       -- data length code (0-8, clamped)
  data     : Array UInt8 -- always 8 bytes (padded with 0x00)
  deriving Inhabited

/-! ## MCP2515 byte layout (13 bytes)
    Byte 0 (SIDH):  SID[10:3]
    Byte 1 (SIDL):  SID[2:0] bits 7:5, IDE bit 3, EID[17:16] bits 1:0
    Byte 2 (EID8):  EID[15:8]
    Byte 3 (EID0):  EID[7:0]
    Byte 4 (DLC):   RTR bit 6, DLC[3:0] bits 3:0
    Bytes 5-12:     Data[0..7] -/

@[inline] def extractStdId (buf : Array UInt8) : UInt32 :=
  let sidh := (getU8 buf 0).toUInt32
  let sidl := (getU8 buf 1).toUInt32
  (sidh <<< 3) ||| (sidl >>> 5)

@[inline] def extractExtId (buf : Array UInt8) : UInt32 :=
  let sidh := (getU8 buf 0).toUInt32
  let sidl := (getU8 buf 1).toUInt32
  let eid8 := (getU8 buf 2).toUInt32
  let eid0 := (getU8 buf 3).toUInt32
  (sidh <<< 21) ||| ((sidl &&& 0xE0) <<< 13) ||| ((sidl &&& 0x03) <<< 16) ||| (eid8 <<< 8) ||| eid0

@[inline] def isExtended (buf : Array UInt8) : Bool :=
  ((getU8 buf 1) &&& 0x08) != 0

@[inline] def extractRtr (buf : Array UInt8) : Bool :=
  ((getU8 buf 4) &&& 0x40) != 0

@[inline] def clampDlc (raw : UInt8) : UInt8 :=
  let dlc := raw &&& 0x0F
  if dlc > 8 then 8 else dlc

@[inline] def extractDlc (buf : Array UInt8) : UInt8 :=
  clampDlc (getU8 buf 4)

def extractData (buf : Array UInt8) (i : Nat) (acc : Array UInt8) : Array UInt8 :=
  if i >= 8 then acc
  else extractData buf (i + 1) (acc.push (getU8 buf (5 + i)))
termination_by 8 - i

def parseMcp2515 (buf : Array UInt8) : CanFrame :=
  let ext := isExtended buf
  let id := if ext then extractExtId buf else extractStdId buf
  { id       := id
    extended := ext
    rtr      := extractRtr buf
    dlc      := extractDlc buf
    data     := extractData buf 0 #[] }

/-! ## Encoder (for roundtrip proofs) -/

def encodeMcp2515 (f : CanFrame) : Array UInt8 :=
  let sidh : UInt8 := if f.extended then
    (f.id >>> 21).toUInt8 &&& 0xFF
  else
    (f.id >>> 3).toUInt8 &&& 0xFF
  let sidl : UInt8 := if f.extended then
    (((f.id >>> 18).toUInt8 &&& 0x07) <<< 5) ||| (0x08 : UInt8) |||
    ((f.id >>> 16).toUInt8 &&& 0x03)
  else
    ((f.id.toUInt8 &&& 0x07) <<< 5)
  let eid8 : UInt8 := if f.extended then (f.id >>> 8).toUInt8 else 0
  let eid0 : UInt8 := if f.extended then f.id.toUInt8 else 0
  let dlcByte : UInt8 := (if f.rtr then 0x40 else 0x00) ||| (f.dlc &&& 0x0F)
  #[sidh, sidl, eid8, eid0, dlcByte,
    getU8 f.data 0, getU8 f.data 1, getU8 f.data 2, getU8 f.data 3,
    getU8 f.data 4, getU8 f.data 5, getU8 f.data 6, getU8 f.data 7]

/-! ## CRC-15/CAN (Bosch spec)
    Polynomial: x^15 + x^14 + x^10 + x^8 + x^7 + x^4 + x^3 + 1 (0x4599)
    Init: 0x0000, MSB-first, no reflection, no final XOR -/

@[inline] def crc15Bit (crc : UInt16) (bit : UInt16) : UInt16 :=
  let xorIn := ((crc >>> 14) ^^^ bit) &&& 1
  let shifted := (crc <<< 1) &&& 0x7FFF
  if xorIn == 1 then shifted ^^^ 0x4599 else shifted

def crc15Byte (crc : UInt16) (byte : UInt8) (bitIdx : Nat) : UInt16 :=
  if bitIdx >= 8 then crc
  else
    let bit := ((byte.toUInt16 >>> (7 - bitIdx).toUInt16) &&& 1)
    crc15Byte (crc15Bit crc bit) byte (bitIdx + 1)
termination_by 8 - bitIdx

def crc15Loop (data : Array UInt8) (i : Nat) (crc : UInt16) : UInt16 :=
  if i >= data.size then crc
  else crc15Loop data (i + 1) (crc15Byte crc (getU8 data i) 0)
termination_by data.size - i

def crc15 (data : Array UInt8) : UInt16 :=
  crc15Loop data 0 0x0000

/-! ## Hex output helpers -/

def nibbleToHex (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (0x30 + n.toNat)
  else Char.ofNat (0x61 + n.toNat - 10)

def uint8ToHex (v : UInt8) : String :=
  let s := String.push "" (nibbleToHex ((v >>> 4) &&& 0x0F))
  String.push s (nibbleToHex (v &&& 0x0F))

def uint16ToHex (v : UInt16) : String :=
  let s := String.push "" (nibbleToHex ((v >>> 12).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 8).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 4).toUInt8 &&& 0x0F))
  String.push s (nibbleToHex (v.toUInt8 &&& 0x0F))

def uint32ToHex (v : UInt32) : String :=
  let s := String.push "" (nibbleToHex ((v >>> 28).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 24).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 20).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 16).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 12).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 8).toUInt8 &&& 0x0F))
  let s := String.push s (nibbleToHex ((v >>> 4).toUInt8 &&& 0x0F))
  String.push s (nibbleToHex (v.toUInt8 &&& 0x0F))

def dataToHex (d : Array UInt8) : String :=
  uint8ToHex (getU8 d 0) ++ "," ++
  uint8ToHex (getU8 d 1) ++ "," ++
  uint8ToHex (getU8 d 2) ++ "," ++
  uint8ToHex (getU8 d 3) ++ "," ++
  uint8ToHex (getU8 d 4) ++ "," ++
  uint8ToHex (getU8 d 5) ++ "," ++
  uint8ToHex (getU8 d 6) ++ "," ++
  uint8ToHex (getU8 d 7)

def frameToHex (f : CanFrame) : String :=
  let idStr := if f.extended then "ext" else "std"
  let rtrStr := if f.rtr then " RTR" else ""
  s!"ID=0x{uint32ToHex f.id} ({idStr}){rtrStr} DLC={f.dlc.toNat} data=[{dataToHex f.data}]"

/-! ## Main -/

-- Wrapping arrays in IO prevents the Lean compiler from constant-folding
-- the entire computation at module initialization time (which causes string
-- corruption in the bare-metal runtime's pre-computed closures).
@[noinline] def mkBuf (bytes : Array UInt8) : IO (Array UInt8) := pure bytes

def main : IO Unit := do
  IO.println "=== CAN 2.0 Frame Parser (MCP2515) ==="

  -- Test vector 1: Standard frame, ID=0x123, DLC=4, data=0xDE 0xAD 0xBE 0xEF
  -- SIDH = 0x123 >>> 3 = 0x24, SIDL = (0x123 &&& 0x07) <<< 5 = 0x60
  let buf1 ← mkBuf #[0x24, 0x60, 0x00, 0x00, 0x04,
                      0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00]
  let t0 ← cyclesNow
  let frame1 := parseMcp2515 buf1
  let t1 ← cyclesNow
  IO.println s!"Frame 1: {frameToHex frame1}"
  IO.println s!"  cycles: {t1 - t0}"

  -- Test vector 2: Extended frame, ID=0x12345678, DLC=8, data=0x01..0x08
  -- SIDH = bits[28:21] = 0x91
  -- SIDL = bits[20:18] in [7:5] = 0xA0, IDE=0x08, bits[17:16] in [1:0] = 0x00 → 0xA8
  -- EID8 = bits[15:8] = 0x56
  -- EID0 = bits[7:0] = 0x78
  let buf2 ← mkBuf #[0x91, 0xA8, 0x56, 0x78, 0x08,
                      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
  let frame2 := parseMcp2515 buf2
  IO.println s!"Frame 2: {frameToHex frame2}"

  -- Test vector 3: Standard frame with RTR, ID=0x7FF, DLC=0
  let buf3 ← mkBuf #[0xFF, 0xE0, 0x00, 0x00, 0x40,
                      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let frame3 := parseMcp2515 buf3
  IO.println s!"Frame 3: {frameToHex frame3}"

  -- CRC-15 check value: CRC-15("123456789") = 0x059E
  let crcInput ← mkBuf #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]
  let crcVal := crc15 crcInput
  IO.println s!"CRC-15(\"123456789\") = 0x{uint16ToHex crcVal}"
