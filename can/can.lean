-- CAN 2.0 Frame Parser — bare-metal entry point
--
-- All CAN library code lives in can_lib.lean. This file re-exports it
-- and adds the main function for bare-metal execution on QEMU.

import can_lib

-- RISC-V cycle counter (implemented in lean_rt.c)
@[extern "lean_cycles_now"]
opaque cyclesNow : IO UInt64

/-! ## Main -/

-- Wrapping arrays in IO prevents the Lean compiler from constant-folding
-- the entire computation at module initialization time (which causes string
-- corruption in the bare-metal runtime's pre-computed closures).
@[noinline] def mkBuf (bytes : Array UInt8) : IO (Array UInt8) := pure bytes

def main : IO Unit := do
  IO.println "=== CAN 2.0 Frame Parser (MCP2515) ==="
  IO.println ""
  IO.println "Parses MCP2515 CAN controller SPI receive buffers into CAN 2.0 frames."
  IO.println "Handles standard (11-bit) and extended (29-bit) IDs, RTR, and CRC-15."
  IO.println "Proven correct: parseMcp2515 (encodeMcp2515 f) = f for well-formed frames."
  IO.println ""

  -- Test vector 1: Standard frame, ID=0x123, DLC=4, data=0xDE 0xAD 0xBE 0xEF
  -- SIDH = 0x123 >>> 3 = 0x24, SIDL = (0x123 &&& 0x07) <<< 5 = 0x60
  IO.println "Test 1: Standard frame, ID=0x123, DLC=4, data=DEADBEEF"
  let buf1 ← mkBuf #[0x24, 0x60, 0x00, 0x00, 0x04,
                      0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00]
  let t0 ← cyclesNow
  let frame1 := parseMcp2515 buf1
  let t1 ← cyclesNow
  IO.println s!"  -> {frameToHex frame1}"
  IO.println s!"  cycles: {t1 - t0}"
  IO.println ""

  -- Test vector 2: Extended frame, ID=0x12345678, DLC=8, data=0x01..0x08
  -- SIDH = bits[28:21] = 0x91
  -- SIDL = bits[20:18] in [7:5] = 0xA0, IDE=0x08, bits[17:16] in [1:0] = 0x00 → 0xA8
  -- EID8 = bits[15:8] = 0x56
  -- EID0 = bits[7:0] = 0x78
  IO.println "Test 2: Extended frame, ID=0x12345678, DLC=8"
  let buf2 ← mkBuf #[0x91, 0xA8, 0x56, 0x78, 0x08,
                      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
  let frame2 := parseMcp2515 buf2
  IO.println s!"  -> {frameToHex frame2}"
  IO.println ""

  -- Test vector 3: Standard frame with RTR, ID=0x7FF, DLC=0
  IO.println "Test 3: Standard frame with RTR, ID=0x7FF"
  let buf3 ← mkBuf #[0xFF, 0xE0, 0x00, 0x00, 0x40,
                      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let frame3 := parseMcp2515 buf3
  IO.println s!"  -> {frameToHex frame3}"
  IO.println ""

  -- CRC-15 check value: CRC-15("123456789") = 0x059E
  let crcInput ← mkBuf #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]
  let crcVal := crc15 crcInput
  IO.println s!"CRC-15 check value: CRC-15(\"123456789\") = 0x{uint16ToHex crcVal}"
  IO.println ""
  IO.println "can-parser ok"
