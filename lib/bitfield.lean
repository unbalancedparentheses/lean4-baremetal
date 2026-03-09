-- Reusable UInt8 single-bit isolation lemmas
--
-- Each theorem proves: ((b &&& mask) != 0) = b.toBitVec.getLsbD n
-- for all 8 bit positions. These are used by can_proof.lean and torque_proof.lean
-- to bridge between shift-mask implementations and BitVec specifications.

import Std.Tactic.BVDecide

theorem uint8_bit0 (b : UInt8) :
    ((b &&& 0x01) != 0) = b.toBitVec.getLsbD 0 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit1 (b : UInt8) :
    ((b &&& 0x02) != 0) = b.toBitVec.getLsbD 1 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit2 (b : UInt8) :
    ((b &&& 0x04) != 0) = b.toBitVec.getLsbD 2 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit3 (b : UInt8) :
    ((b &&& 0x08) != 0) = b.toBitVec.getLsbD 3 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit4 (b : UInt8) :
    ((b &&& 0x10) != 0) = b.toBitVec.getLsbD 4 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit5 (b : UInt8) :
    ((b &&& 0x20) != 0) = b.toBitVec.getLsbD 5 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit6 (b : UInt8) :
    ((b &&& 0x40) != 0) = b.toBitVec.getLsbD 6 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide

theorem uint8_bit7 (b : UInt8) :
    ((b &&& 0x80) != 0) = b.toBitVec.getLsbD 7 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]; bv_decide
