-- Formal verification of CAN 2.0 Frame Parser (ISO 11898 / Bosch CAN 2.0) in Lean 4
--
-- This file imports examples/can_lib.lean (`import can_lib`), so every theorem
-- below is proven against the exact code that runs on bare metal.
-- If someone changes can_lib.lean, these proofs must still typecheck or
-- the build fails — the Lean kernel enforces the guarantee.
--
-- What this file proves (universally quantified unless noted):
--   1. Bit extraction (ID shifts/masks) matches MCP2515 spec
--   2. Test vectors verified at COMPILE TIME via `native_decide` (concrete)
--   3. Structural properties: id bounds, dlc ≤ 8, data.size = 8
--   4. Roundtrip: parseMcp2515 (encodeMcp2515 f) = f for 7 concrete frames
--      (universal roundtrip infeasible via bv_decide on 13-byte structures)
--   5. CRC-15: byte processing = 8× bit steps (universal)
--   6. CRC-15: loop equivalence (universal)
--   7. Parser well-formedness: parseMcp2515 always produces a well-formed frame
--   8. End-to-end: implementation = reference specification (universal)
--
-- Trust model:
--   Trusted: Lean kernel, lean -c compiler, GCC cross-compiler, freestanding runtime
--   Proven:  Bit extraction correct, test vectors match, structural properties universal

import can_lib
import bitfield
import Std.Tactic.BVDecide

-- DecidableEq is needed for native_decide on CanFrame equality,
-- but we keep it out of can.lean to avoid pulling library code into the binary.
deriving instance DecidableEq for CanFrame

/-! ## Section 1: CAN 2.0 / MCP2515 reference spec

    The MCP2515 receive buffer is 13 bytes:
      Byte 0 (SIDH):  SID[10:3]
      Byte 1 (SIDL):  SID[2:0] bits 7:5, IDE bit 3, EID[17:16] bits 1:0
      Byte 2 (EID8):  EID[15:8]
      Byte 3 (EID0):  EID[7:0]
      Byte 4 (DLC):   RTR bit 6, DLC[3:0] bits 3:0
      Bytes 5-12:     Data[0..7]

    Standard ID (CAN 2.0A): 11 bits = SIDH[7:0] ++ SIDL[7:5]
    Extended ID (CAN 2.0B): 29 bits = SIDH[7:0] ++ SIDL[7:5] ++ SIDL[1:0] ++ EID8[7:0] ++ EID0[7:0]

    CRC-15/CAN polynomial: x^15 + x^14 + x^10 + x^8 + x^7 + x^4 + x^3 + 1 (0x4599)
    Init: 0x0000, MSB-first, no reflection, no final XOR -/

-- Reference spec: standard ID extraction (BitVec level)
def spec_extractStdId (sidh sidl : BitVec 8) : BitVec 32 :=
  (sidh.zeroExtend 32 <<< 3) ||| (sidl.zeroExtend 32 >>> 5)

-- Reference spec: extended ID extraction (BitVec level)
def spec_extractExtId (sidh sidl eid8 eid0 : BitVec 8) : BitVec 32 :=
  (sidh.zeroExtend 32 <<< 21) |||
  ((sidl.zeroExtend 32 &&& 0xE0) <<< 13) |||
  ((sidl.zeroExtend 32 &&& 0x03) <<< 16) |||
  (eid8.zeroExtend 32 <<< 8) |||
  eid0.zeroExtend 32

/-! ## Section 2: Bit extraction proofs via `bv_decide`

    These are universally quantified — proven for ALL possible 8-bit inputs,
    not just test cases. Each theorem states that our shift-based implementation
    equals the MCP2515 spec operation. -/

-- Standard ID: (sidh <<< 3) ||| (sidl >>> 5) yields an 11-bit value (< 2048)
theorem std_id_bounded (sidh sidl : BitVec 8) :
    ((sidh.zeroExtend 32 <<< 3) ||| (sidl.zeroExtend 32 >>> 5)) < 2048 := by bv_decide

-- Extended ID: the full construction yields a 29-bit value (< 2^29)
theorem ext_id_bounded (sidh sidl eid8 eid0 : BitVec 8) :
    ((sidh.zeroExtend 32 <<< 21) |||
     ((sidl.zeroExtend 32 &&& 0xE0) <<< 13) |||
     ((sidl.zeroExtend 32 &&& 0x03) <<< 16) |||
     (eid8.zeroExtend 32 <<< 8) |||
     eid0.zeroExtend 32) < (1 <<< 29 : BitVec 32) := by bv_decide

-- IDE bit: bit 3 of SIDL is the extended frame flag
theorem ide_bit_isolate (sidl : BitVec 8) :
    ((sidl &&& 0x08) != 0) = (sidl.getLsbD 3) := by bv_decide

-- RTR bit: bit 6 of DLC byte is the remote transmission request flag
theorem rtr_bit_isolate (dlcByte : BitVec 8) :
    ((dlcByte &&& 0x40) != 0) = (dlcByte.getLsbD 6) := by bv_decide

-- DLC mask: low 4 bits are extracted correctly
theorem dlc_mask_correct (dlcByte : BitVec 8) :
    (dlcByte &&& 0x0F) = (dlcByte.zeroExtend 8 % 16) := by bv_decide

-- Standard ID reconstruction: encoding then re-extracting standard ID is identity
theorem std_id_roundtrip (id : BitVec 32) (h : id < 2048) :
    ((((id >>> 3).truncate 8).zeroExtend 32 <<< 3) |||
     ((((id.truncate 8) &&& 0x07) <<< 5).zeroExtend 32 >>> 5)) = id := by bv_decide

/-! ## Section 3: Test vectors via `native_decide`

    These theorems are verified at COMPILE TIME. If this file typechecks,
    the CAN parser produces the correct results for all test vectors.
    The Lean kernel itself is the verifier. -/

-- Vector 1: Minimum standard frame — Std ID 0x000, DLC=0
theorem parse_std_min :
    parseMcp2515 #[0x00, 0x00, 0x00, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
    { id := 0x000, extended := false, rtr := false, dlc := 0,
      data := #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } := by native_decide

-- Vector 2: Maximum standard frame — Std ID 0x7FF, DLC=8, data=0xFF
theorem parse_std_max :
    parseMcp2515 #[0xFF, 0xE0, 0x00, 0x00, 0x08,
                   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] =
    { id := 0x7FF, extended := false, rtr := false, dlc := 8,
      data := #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] } := by native_decide

-- Vector 3: Minimum extended frame — Ext ID 0x00000000, DLC=0
theorem parse_ext_min :
    parseMcp2515 #[0x00, 0x08, 0x00, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
    { id := 0x00000000, extended := true, rtr := false, dlc := 0,
      data := #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } := by native_decide

-- Vector 4: Maximum extended frame — Ext ID 0x1FFFFFFF, DLC=8
theorem parse_ext_max :
    parseMcp2515 #[0xFF, 0xEB, 0xFF, 0xFF, 0x08,
                   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] =
    { id := 0x1FFFFFFF, extended := true, rtr := false, dlc := 8,
      data := #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] } := by native_decide

-- Vector 5: Standard frame with RTR set — Std ID 0x7FF, DLC=0
theorem parse_std_rtr :
    parseMcp2515 #[0xFF, 0xE0, 0x00, 0x00, 0x40,
                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
    { id := 0x7FF, extended := false, rtr := true, dlc := 0,
      data := #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } := by native_decide

-- Vector 6: DLC saturation — DLC=15 in raw byte, clamped to 8
theorem parse_dlc_clamp :
    parseMcp2515 #[0x00, 0x00, 0x00, 0x00, 0x0F,
                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
    { id := 0x000, extended := false, rtr := false, dlc := 8,
      data := #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } := by native_decide

-- Vector 7: Data content — Std ID 0x100, DLC=8, data=0x01..0x08
theorem parse_data_content :
    parseMcp2515 #[0x20, 0x00, 0x00, 0x00, 0x08,
                   0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] =
    { id := 0x100, extended := false, rtr := false, dlc := 8,
      data := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] } := by native_decide

-- Vector 8: Extended frame with mixed SIDL bits — Ext ID 0x12345678
-- SIDH=0x91, SIDL=0xA8 (bits[20:18]=5→[7:5], IDE=0x08, bits[17:16]=0→[1:0])
theorem parse_ext_mixed :
    parseMcp2515 #[0x91, 0xA8, 0x56, 0x78, 0x08,
                   0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] =
    { id := 0x12345678, extended := true, rtr := false, dlc := 8,
      data := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] } := by native_decide

-- Vector 9: Standard frame from main — Std ID 0x123, DLC=4
theorem parse_std_0x123 :
    parseMcp2515 #[0x24, 0x60, 0x00, 0x00, 0x04,
                   0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00] =
    { id := 0x123, extended := false, rtr := false, dlc := 4,
      data := #[0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00] } := by native_decide

-- Vector 10: Empty buffer (all zeros, short) — tests getU8 default behavior
theorem parse_empty_buf :
    parseMcp2515 #[] =
    { id := 0x000, extended := false, rtr := false, dlc := 0,
      data := #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } := by native_decide

/-! ## Section 4: Structural properties (universal) -/

-- extractData always returns exactly 8 elements
theorem extractData_size (buf : Array UInt8) (i : Nat) (acc : Array UInt8) (hi : i ≤ 8) :
    (extractData buf i acc).size = acc.size + (8 - i) := by
  unfold extractData
  split
  · omega
  · rw [extractData_size _ _ _ (by omega), Array.size_push]; omega
termination_by 8 - i

-- parseMcp2515 always produces data of size 8
theorem parseMcp2515_data_size (buf : Array UInt8) :
    (parseMcp2515 buf).data.size = 8 := by
  unfold parseMcp2515
  simp only []
  have := extractData_size buf 0 #[] (by omega)
  simpa using this

-- clampDlc always returns a value ≤ 8
theorem clampDlc_le_8 (raw : UInt8) : (clampDlc raw).toNat ≤ 8 := by
  show (if (raw &&& 0x0F) > 8 then (8 : UInt8) else (raw &&& 0x0F)).toNat ≤ 8
  split
  · decide
  · rename_i h
    have : ¬ (8 < (raw &&& 0x0F).toNat) := h
    omega

-- extractDlc always returns a value ≤ 8
theorem extractDlc_le_8 (buf : Array UInt8) : (extractDlc buf).toNat ≤ 8 := by
  unfold extractDlc
  exact clampDlc_le_8 _

-- parseMcp2515 DLC is always ≤ 8
theorem parseMcp2515_dlc_le_8 (buf : Array UInt8) :
    (parseMcp2515 buf).dlc.toNat ≤ 8 := by
  unfold parseMcp2515
  simp only []
  exact extractDlc_le_8 _

/-! ## Section 5: Helper lemmas (getU8) -/

-- getU8 bridges getD to getElem
theorem getU8_eq (xs : Array UInt8) (i : Nat) (h : i < xs.size) :
    getU8 xs i = xs[i] := by
  unfold getU8 Array.getD; split
  · rfl
  · contradiction

theorem getU8_default (xs : Array UInt8) (i : Nat) (h : ¬(i < xs.size)) :
    getU8 xs i = 0 := by
  unfold getU8 Array.getD; split
  · contradiction
  · rfl

theorem getU8_push_lt (xs : Array UInt8) (v : UInt8) (i : Nat) (h : i < xs.size) :
    getU8 (xs.push v) i = getU8 xs i := by
  rw [getU8_eq (xs.push v) i (by rw [Array.size_push]; omega),
      getU8_eq xs i h, Array.getElem_push_lt]

theorem getU8_push_eq (xs : Array UInt8) (v : UInt8) :
    getU8 (xs.push v) xs.size = v := by
  rw [getU8_eq (xs.push v) xs.size (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_eq

/-! ## Section 6: ID reconstruction content proofs -/

-- extractStdId unfolds to the shift/OR formula
theorem extractStdId_eq (buf : Array UInt8) :
    extractStdId buf =
    ((getU8 buf 0).toUInt32 <<< 3) ||| ((getU8 buf 1).toUInt32 >>> 5) := by
  unfold extractStdId; rfl

-- extractExtId unfolds to the full formula
theorem extractExtId_eq (buf : Array UInt8) :
    extractExtId buf =
    ((getU8 buf 0).toUInt32 <<< 21) |||
    (((getU8 buf 1).toUInt32 &&& 0xE0) <<< 13) |||
    (((getU8 buf 1).toUInt32 &&& 0x03) <<< 16) |||
    ((getU8 buf 2).toUInt32 <<< 8) |||
    (getU8 buf 3).toUInt32 := by
  unfold extractExtId; rfl

-- isExtended unfolds to IDE bit check
theorem isExtended_eq (buf : Array UInt8) :
    isExtended buf = (((getU8 buf 1) &&& 0x08) != 0) := by
  unfold isExtended; rfl

/-! ## Section 7: DLC and RTR extraction proofs -/

-- extractRtr unfolds to bit 6 of byte 4
theorem extractRtr_eq (buf : Array UInt8) :
    extractRtr buf = (((getU8 buf 4) &&& 0x40) != 0) := by
  unfold extractRtr; rfl

-- extractDlc unfolds to clampDlc of byte 4
theorem extractDlc_eq (buf : Array UInt8) :
    extractDlc buf = clampDlc (getU8 buf 4) := by
  unfold extractDlc; rfl

-- clampDlc identity for valid DLC values (0-8)
theorem clampDlc_identity (raw : UInt8) (h : (raw &&& 0x0F).toNat ≤ 8) :
    clampDlc raw = raw &&& 0x0F := by
  show (if (raw &&& 0x0F) > 8 then (8 : UInt8) else (raw &&& 0x0F)) = raw &&& 0x0F
  split
  · rename_i h'
    have : (raw &&& 0x0F).toNat > 8 := h'
    omega
  · rfl

-- clampDlc saturation for invalid DLC values (9-15)
theorem clampDlc_saturate (raw : UInt8) (h : (raw &&& 0x0F).toNat > 8) :
    clampDlc raw = 8 := by
  show (if (raw &&& 0x0F) > 8 then (8 : UInt8) else (raw &&& 0x0F)) = 8
  split
  · rfl
  · rename_i h'
    exfalso
    have : ¬ (8 < (raw &&& 0x0F).toNat) := h'
    omega

/-! ## Section 8: Data extraction proofs -/

-- extractData preserves existing accumulator elements
theorem extractData_preserves_acc (buf : Array UInt8) (i : Nat) (acc : Array UInt8)
    (hi : i ≤ 8) (k : Nat) (hk : k < acc.size) :
    getU8 (extractData buf i acc) k = getU8 acc k := by
  unfold extractData; split
  case isTrue => rfl
  case isFalse hlt =>
    rw [extractData_preserves_acc buf (i + 1) _ (by omega) k
        (by rw [Array.size_push]; omega)]
    exact getU8_push_lt acc _ k hk
termination_by 8 - i

-- extractData: element at position k where k ≥ i
theorem extractData_at_inv (buf : Array UInt8) (i : Nat) (acc : Array UInt8)
    (hi : i ≤ 8) (hw : acc.size = i) (k : Nat) (hk_lb : i ≤ k) (hk_ub : k < 8) :
    getU8 (extractData buf i acc) k = getU8 buf (5 + k) := by
  unfold extractData; split
  case isTrue hge => omega
  case isFalse hlt =>
    by_cases hki : k = i
    · rw [hki]
      rw [extractData_preserves_acc buf (i + 1) _ (by omega) i
          (by rw [Array.size_push]; omega)]
      rw [← hw, getU8_push_eq]
    · exact extractData_at_inv buf (i + 1) _ (by omega)
          (by rw [Array.size_push, hw]) k (by omega) hk_ub
termination_by 8 - i

-- extractData from 0 with empty acc: output[k] = buf[5+k]
theorem extractData_content (buf : Array UInt8) (k : Nat) (hk : k < 8) :
    getU8 (extractData buf 0 #[]) k = getU8 buf (5 + k) := by
  exact extractData_at_inv buf 0 #[] (by omega) rfl k (by omega) hk

/-! ## Section 9: Encoder + roundtrip -/

-- Well-formedness predicate for CAN frames
def CanFrame.wellFormed (f : CanFrame) : Prop :=
  f.data.size = 8
  ∧ f.dlc.toNat ≤ 8
  ∧ (if f.extended then f.id.toNat < 2^29 else f.id.toNat < 2048)

-- encodeMcp2515 always produces 13 bytes
theorem encodeMcp2515_size (f : CanFrame) :
    (encodeMcp2515 f).size = 13 := by
  unfold encodeMcp2515; rfl

-- Roundtrip test frames
private def rt_std_min : CanFrame :=
  ⟨0x000, false, false, 0, #[0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]⟩
private def rt_std_max : CanFrame :=
  ⟨0x7FF, false, false, 8, #[0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF]⟩
private def rt_std_123 : CanFrame :=
  ⟨0x123, false, false, 4, #[0xDE,0xAD,0xBE,0xEF,0x00,0x00,0x00,0x00]⟩
private def rt_ext_min : CanFrame :=
  ⟨0x00000000, true, false, 0, #[0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]⟩
private def rt_ext_max : CanFrame :=
  ⟨0x1FFFFFFF, true, false, 8, #[0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF]⟩
private def rt_ext_mixed : CanFrame :=
  ⟨0x12345678, true, false, 8, #[0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08]⟩
private def rt_std_rtr : CanFrame :=
  ⟨0x7FF, false, true, 0, #[0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]⟩

-- Roundtrip proofs: parse(encode(frame)) = frame
theorem roundtrip_std_min : parseMcp2515 (encodeMcp2515 rt_std_min) = rt_std_min := by
  native_decide
theorem roundtrip_std_max : parseMcp2515 (encodeMcp2515 rt_std_max) = rt_std_max := by
  native_decide
theorem roundtrip_std_123 : parseMcp2515 (encodeMcp2515 rt_std_123) = rt_std_123 := by
  native_decide
theorem roundtrip_ext_min : parseMcp2515 (encodeMcp2515 rt_ext_min) = rt_ext_min := by
  native_decide
theorem roundtrip_ext_max : parseMcp2515 (encodeMcp2515 rt_ext_max) = rt_ext_max := by
  native_decide
theorem roundtrip_ext_mixed : parseMcp2515 (encodeMcp2515 rt_ext_mixed) = rt_ext_mixed := by
  native_decide
theorem roundtrip_std_rtr : parseMcp2515 (encodeMcp2515 rt_std_rtr) = rt_std_rtr := by
  native_decide

/-! ## Section 10: CRC-15 reference spec (bit-at-a-time)

    The CRC-15/CAN uses polynomial 0x4599 with MSB-first processing.
    The reference spec processes one bit at a time using a shift register. -/

-- Reference spec: CRC-15 single bit step (same as implementation, used as spec anchor)
def spec_crc15Step (crc : UInt16) (bit : UInt16) : UInt16 :=
  let xorIn := ((crc >>> 14) ^^^ bit) &&& 1
  let shifted := (crc <<< 1) &&& 0x7FFF
  if xorIn == 1 then shifted ^^^ 0x4599 else shifted

-- Reference spec: process 8 bits of a byte MSB-first (using crc15Bit)
def spec_crc15ByteBits (crc : UInt16) (byte : UInt8) : UInt16 :=
  let b := byte.toUInt16
  let crc := crc15Bit crc ((b >>> 7) &&& 1)
  let crc := crc15Bit crc ((b >>> 6) &&& 1)
  let crc := crc15Bit crc ((b >>> 5) &&& 1)
  let crc := crc15Bit crc ((b >>> 4) &&& 1)
  let crc := crc15Bit crc ((b >>> 3) &&& 1)
  let crc := crc15Bit crc ((b >>> 2) &&& 1)
  let crc := crc15Bit crc ((b >>> 1) &&& 1)
  crc15Bit crc (b &&& 1)

/-! ## Section 11: CRC-15 byte = 8x bit step -/

-- crc15Bit = spec_crc15Step (definitional)
theorem crc15Bit_eq_spec (crc bit : UInt16) :
    crc15Bit crc bit = spec_crc15Step crc bit := by
  unfold crc15Bit spec_crc15Step; rfl

-- crc15Byte at bitIdx=8 is identity
theorem crc15Byte_done (crc : UInt16) (byte : UInt8) :
    crc15Byte crc byte 8 = crc := by
  unfold crc15Byte; simp

-- crc15Byte = spec_crc15ByteBits (universal — for ALL crc and byte values)
-- Proof: unfold the 8-step recursion; each step matches the corresponding crc15Bit call.
theorem crc15Byte_eq_spec (crc : UInt16) (byte : UInt8) :
    crc15Byte crc byte 0 = spec_crc15ByteBits crc byte := by
  unfold spec_crc15ByteBits
  simp [crc15Byte]

/-! ## Section 12: CRC-15 test vectors -/

-- Canonical check value: CRC-15("123456789") = 0x059E
theorem crc15_check_value :
    crc15 #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0x059E := by
  native_decide

-- Empty input: CRC-15 of empty array = 0x0000 (init value)
theorem crc15_empty :
    crc15 #[] = 0x0000 := by native_decide

-- Single byte: CRC-15(0xD3)
theorem crc15_single_byte :
    crc15 #[0xD3] = (crc15Byte 0x0000 0xD3 0) := by native_decide

-- Single byte 0x00
theorem crc15_zero_byte :
    crc15 #[0x00] = (crc15Byte 0x0000 0x00 0) := by native_decide

-- Two bytes
theorem crc15_two_bytes :
    crc15 #[0xAB, 0xCD] =
    (crc15Byte (crc15Byte 0x0000 0xAB 0) 0xCD 0) := by native_decide

/-! ## Section 13: CRC-15 loop equivalence (universal) -/

-- Reference spec: CRC-15 loop using spec_crc15ByteBits
def spec_crc15Loop (data : Array UInt8) (i : Nat) (crc : UInt16) : UInt16 :=
  if i ≥ data.size then crc
  else spec_crc15Loop data (i + 1) (spec_crc15ByteBits crc (getU8 data i))
termination_by data.size - i

-- crc15Loop = spec_crc15Loop (universal — for ALL arrays, indices, and CRC values)
theorem crc15Loop_eq_spec (data : Array UInt8) (i : Nat) (crc : UInt16) :
    crc15Loop data i crc = spec_crc15Loop data i crc := by
  unfold crc15Loop spec_crc15Loop
  split
  · rfl
  · rw [crc15Byte_eq_spec]
    exact crc15Loop_eq_spec data (i + 1) _
termination_by data.size - i

-- crc15 = spec_crc15Loop from 0 (universal)
theorem crc15_eq_spec_full (data : Array UInt8) :
    crc15 data = spec_crc15Loop data 0 0x0000 := by
  unfold crc15
  exact crc15Loop_eq_spec data 0 0x0000

/-! ## Section 14: Implementation = spec equivalence (parser)

    The spec below uses BitVec field extraction (extractLsb', getLsbD, ++)
    matching MCP2515 datasheet bit positions, so the bridge proof between
    the implementation's shift-mask formulas and the spec requires real
    work (bv_decide), not just rfl. -/

-- Bridge lemmas: each proves the implementation's shift-mask formula
-- equals the spec's BitVec operation.

-- Standard ID: shift-OR = concat+zeroExtend (by bv_decide, 2^16 cases)
private theorem std_id_bridge (sidh sidl : UInt8) :
    (sidh.toUInt32 <<< 3) ||| (sidl.toUInt32 >>> 5) =
    ⟨(sidh.toBitVec ++ sidl.toBitVec.extractLsb' 5 3 : BitVec 11).setWidth 32⟩ := by
  bv_decide

-- Extended ID: shift-OR = concat+zeroExtend (by bv_decide, 2^32 cases)
private theorem ext_id_bridge (sidh sidl eid8 eid0 : UInt8) :
    (sidh.toUInt32 <<< 21) ||| ((sidl.toUInt32 &&& 0xE0) <<< 13) |||
    ((sidl.toUInt32 &&& 0x03) <<< 16) ||| (eid8.toUInt32 <<< 8) ||| eid0.toUInt32 =
    ⟨(sidh.toBitVec ++ sidl.toBitVec.extractLsb' 5 3 ++
     sidl.toBitVec.extractLsb' 0 2 ++
     eid8.toBitVec ++ eid0.toBitVec : BitVec 29).setWidth 32⟩ := by
  bv_decide

-- DLC: mask 0x0F = extractLsb' 0 4 (by bv_decide)
private theorem dlc_bridge (dlcByte : UInt8) :
    dlcByte &&& 0x0F =
    ⟨(dlcByte.toBitVec.extractLsb' 0 4 : BitVec 4).setWidth 8⟩ := by bv_decide

-- Data: extractData from 0 equals flat array literal
private theorem extractData_eq_literal (buf : Array UInt8) :
    extractData buf 0 #[] = #[getU8 buf 5, getU8 buf 6, getU8 buf 7, getU8 buf 8,
                               getU8 buf 9, getU8 buf 10, getU8 buf 11, getU8 buf 12] := by
  simp [extractData]

-- Reference specification for the full parser (BitVec field extraction
-- matching MCP2515 datasheet bit positions)
def spec_parseMcp2515 (buf : Array UInt8) : CanFrame :=
  let sidh := getU8 buf 0
  let sidl := getU8 buf 1
  let eid8 := getU8 buf 2
  let eid0 := getU8 buf 3
  let dlcByte := getU8 buf 4
  let ext := sidl.toBitVec.getLsbD 3
  let id : UInt32 := if ext then
    ⟨(sidh.toBitVec ++ sidl.toBitVec.extractLsb' 5 3 ++
     sidl.toBitVec.extractLsb' 0 2 ++
     eid8.toBitVec ++ eid0.toBitVec : BitVec 29).setWidth 32⟩
  else
    ⟨(sidh.toBitVec ++ sidl.toBitVec.extractLsb' 5 3 : BitVec 11).setWidth 32⟩
  let rtr := dlcByte.toBitVec.getLsbD 6
  let rawDlc : UInt8 := ⟨(dlcByte.toBitVec.extractLsb' 0 4 : BitVec 4).setWidth 8⟩
  let dlc := if rawDlc > 8 then 8 else rawDlc
  { id := id, extended := ext, rtr := rtr, dlc := dlc,
    data := #[getU8 buf 5, getU8 buf 6, getU8 buf 7, getU8 buf 8,
              getU8 buf 9, getU8 buf 10, getU8 buf 11, getU8 buf 12] }

-- parseMcp2515 = spec_parseMcp2515
theorem parseMcp2515_eq_spec (buf : Array UInt8) :
    parseMcp2515 buf = spec_parseMcp2515 buf := by
  unfold parseMcp2515 spec_parseMcp2515
  unfold isExtended extractStdId extractExtId extractRtr extractDlc clampDlc
  simp only [uint8_bit3, uint8_bit6, dlc_bridge, std_id_bridge, ext_id_bridge,
             extractData_eq_literal]

-- crc15 = crc15Loop from 0
theorem crc15_eq (data : Array UInt8) :
    crc15 data = crc15Loop data 0 0x0000 := by
  unfold crc15; rfl

/-! ## Section 15: Well-formedness -/

-- Standard ID is always < 2048 (11-bit bound) — via bv_decide on UInt operations
-- Note: use < on UInt32 (= BitVec 32) which bv_decide supports; this is
-- definitionally equivalent to .toNat < 2048 since UInt32.lt = Nat.lt on .toNat.
private theorem extractStdId_lt_2048 (a b : UInt8) :
    ((a.toUInt32 <<< 3) ||| (b.toUInt32 >>> 5)) < (2048 : UInt32) := by bv_decide

theorem extractStdId_bounded (buf : Array UInt8) :
    (extractStdId buf).toNat < 2048 := by
  unfold extractStdId
  exact extractStdId_lt_2048 (getU8 buf 0) (getU8 buf 1)

-- Extended ID is always < 2^29 — via bv_decide on UInt operations
private theorem extractExtId_lt_2_29 (a b c d : UInt8) :
    ((a.toUInt32 <<< 21) ||| ((b.toUInt32 &&& 0xE0) <<< 13) |||
     ((b.toUInt32 &&& 0x03) <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32)
    < (536870912 : UInt32) := by bv_decide

theorem extractExtId_bounded (buf : Array UInt8) :
    (extractExtId buf).toNat < 2 ^ 29 := by
  unfold extractExtId
  exact extractExtId_lt_2_29 (getU8 buf 0) (getU8 buf 1) (getU8 buf 2) (getU8 buf 3)

-- parseMcp2515 always produces a well-formed frame (universal)
theorem parseMcp2515_wellFormed (buf : Array UInt8) :
    CanFrame.wellFormed (parseMcp2515 buf) := by
  unfold CanFrame.wellFormed
  refine ⟨parseMcp2515_data_size buf, parseMcp2515_dlc_le_8 buf, ?_⟩
  unfold parseMcp2515 isExtended
  simp only []
  split
  · exact extractExtId_bounded buf
  · exact extractStdId_bounded buf

/-! ## Section 16: Capstone `can_parser_correct` theorem -/

/-- Full pipeline correctness for the CAN 2.0 frame parser.

    All conjuncts below are universally quantified (proven for ALL inputs).

    1. Output structure: data is always 8 bytes, DLC ≤ 8
    2. Parser = reference specification (parseMcp2515 = spec_parseMcp2515)
    3. Encoder always produces 13 bytes
    4. Data extraction: output[k] = buf[5+k] for k < 8
    5. CRC-15 byte = 8× bit step (universal)
    6. CRC-15 loop equivalence (universal)
    7. Well-formedness: std ID < 2048, ext ID < 2^29

    NOT included (proven separately):
    - Roundtrip parse(encode(f)) = f: 7 concrete frames via native_decide (Section 9).
      Universal roundtrip is infeasible via bv_decide on 13-byte structures.
    - CRC-15 test vectors: concrete values via native_decide (Section 12). -/
theorem can_parser_correct (buf : Array UInt8) :
    -- 1. Data is always 8 bytes
    (parseMcp2515 buf).data.size = 8
    -- 2. DLC is always ≤ 8
    ∧ (parseMcp2515 buf).dlc.toNat ≤ 8
    -- 3. Parser = spec
    ∧ parseMcp2515 buf = spec_parseMcp2515 buf
    -- 4. Encoder produces 13 bytes
    ∧ (∀ f : CanFrame, (encodeMcp2515 f).size = 13)
    -- 5. extractData content: output[k] = buf[5+k]
    ∧ (∀ (b : Array UInt8) (k : Nat), k < 8 →
        getU8 (extractData b 0 #[]) k = getU8 b (5 + k))
    -- 6. CRC-15 byte = 8× bit step (universal)
    ∧ (∀ (crc : UInt16) (byte : UInt8), crc15Byte crc byte 0 = spec_crc15ByteBits crc byte)
    -- 7. CRC-15 loop equivalence (universal)
    ∧ (∀ (data : Array UInt8) (i : Nat) (crc : UInt16),
        crc15Loop data i crc = spec_crc15Loop data i crc)
    -- 8. Well-formedness: ID bounds always hold
    ∧ CanFrame.wellFormed (parseMcp2515 buf) := by
  exact ⟨parseMcp2515_data_size buf,
         parseMcp2515_dlc_le_8 buf,
         parseMcp2515_eq_spec buf,
         encodeMcp2515_size,
         fun b k hk => extractData_content b k hk,
         fun crc byte => crc15Byte_eq_spec crc byte,
         fun data i crc => crc15Loop_eq_spec data i crc,
         parseMcp2515_wellFormed buf⟩
