-- Formal verification of the Automotive Torque-Enable / Drive-Authority Gate in Lean 4
--
-- This file imports examples/torque.lean (`import torque`), so every theorem
-- below is proven against the exact code that runs on bare metal.

import torque
import Std.Tactic.BVDecide

/-! ## Section 1: Safety predicate properties -/

theorem safetyOk_all_true :
    safetyOk ⟨true, true, true, true, true, true⟩ = true := by decide

theorem safetyOk_brake_false (g m b e en : Bool) :
    safetyOk ⟨false, g, m, b, e, en⟩ = false := by
  unfold safetyOk; simp

theorem safetyOk_gear_false (br m b e en : Bool) :
    safetyOk ⟨br, false, m, b, e, en⟩ = false := by
  unfold safetyOk; cases br <;> simp

theorem safetyOk_temp_false (br g b e en : Bool) :
    safetyOk ⟨br, g, false, b, e, en⟩ = false := by
  unfold safetyOk; cases br <;> cases g <;> simp

theorem safetyOk_battery_false (br g m e en : Bool) :
    safetyOk ⟨br, g, m, false, e, en⟩ = false := by
  unfold safetyOk; cases br <;> cases g <;> cases m <;> simp

theorem safetyOk_estop_false (br g m b en : Bool) :
    safetyOk ⟨br, g, m, b, false, en⟩ = false := by
  unfold safetyOk; cases br <;> cases g <;> cases m <;> cases b <;> simp

/-! ## Section 2: Core safety guarantee — torque → safety -/

-- THE critical safety property: if torque is allowed, all safety conditions held
theorem torque_implies_safety (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    safetyOk inp = true ∧ st.faulted = false := by
  unfold evalTorqueGate
  cases st.faulted <;> simp
  split <;> simp_all

/-! ## Section 3: Fault denial -/

theorem faulted_denies_torque (inp : DriveInputs) (st : DriveState)
    (hf : st.faulted = true) :
    (evalTorqueGate inp st).1.torque_allowed = false := by
  unfold evalTorqueGate; simp [hf]

/-! ## Section 4: Enable request required -/

theorem no_request_no_torque (inp : DriveInputs) (st : DriveState)
    (hne : inp.enable_request = false) :
    (evalTorqueGate inp st).1.torque_allowed = false := by
  unfold evalTorqueGate safetyOk
  cases st.faulted <;> simp
  split <;> simp_all

/-! ## Section 5: Safety violation latches fault -/

theorem unsafe_latches_fault (inp : DriveInputs) (st : DriveState)
    (hok : st.faulted = false) (hunsafe : safetyOk inp = false) :
    (evalTorqueGate inp st).2.faulted = true := by
  unfold evalTorqueGate; simp [hok, hunsafe]

/-! ## Section 6: Fault persistence -/

theorem fault_persists (inp : DriveInputs) (st : DriveState)
    (hf : st.faulted = true) :
    (evalTorqueGate inp st).2.faulted = true := by
  unfold evalTorqueGate; simp [hf]

/-! ## Section 7: No backdoor -/

theorem no_backdoor (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    inp.enable_request = true := by
  unfold evalTorqueGate safetyOk
  cases st.faulted <;> simp
  split <;> simp_all
  split <;> simp_all

/-! ## Section 8: Bit extraction bridge (bv_decide) -/

private theorem brake_bit_bridge (b : UInt8) :
    ((b &&& 0x01) != 0) = b.toBitVec.getLsbD 0 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

private theorem gear_bit_bridge (b : UInt8) :
    ((b &&& 0x02) != 0) = b.toBitVec.getLsbD 1 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

private theorem temp_bit_bridge (b : UInt8) :
    ((b &&& 0x04) != 0) = b.toBitVec.getLsbD 2 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

private theorem battery_bit_bridge (b : UInt8) :
    ((b &&& 0x08) != 0) = b.toBitVec.getLsbD 3 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

private theorem estop_bit_bridge (b : UInt8) :
    ((b &&& 0x10) != 0) = b.toBitVec.getLsbD 4 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

private theorem enable_bit_bridge (b : UInt8) :
    ((b &&& 0x20) != 0) = b.toBitVec.getLsbD 5 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

theorem extractDriveInputs_bits (frame : CanFrame) :
    let b := getU8 frame.data 0
    let inp := extractDriveInputs frame
    inp.brake_pressed  = (b.toBitVec.getLsbD 0)
    ∧ inp.gear_valid     = (b.toBitVec.getLsbD 1)
    ∧ inp.motor_temp_ok  = (b.toBitVec.getLsbD 2)
    ∧ inp.battery_ok     = (b.toBitVec.getLsbD 3)
    ∧ inp.estop_clear    = (b.toBitVec.getLsbD 4)
    ∧ inp.enable_request = (b.toBitVec.getLsbD 5) := by
  unfold extractDriveInputs
  simp only []
  exact ⟨brake_bit_bridge _, gear_bit_bridge _, temp_bit_bridge _,
         battery_bit_bridge _, estop_bit_bridge _, enable_bit_bridge _⟩

/-! ## Section 9: Test vectors (native_decide) -/

private def mkTestBuf (cmd : UInt8) : Array UInt8 :=
  #[0x20, 0x00, 0x00, 0x00, 0x01,
    cmd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem test_all_ok :
    processDriveCommand (mkTestBuf 0x3F) ⟨false, false⟩ =
    (⟨true, true, .ok⟩, ⟨false, true⟩) := by native_decide

theorem test_estop :
    processDriveCommand (mkTestBuf 0x2F) ⟨false, true⟩ =
    (⟨false, false, .estopActive⟩, ⟨true, false⟩) := by native_decide

theorem test_fault_latched :
    processDriveCommand (mkTestBuf 0x3F) ⟨true, false⟩ =
    (⟨false, false, .faultLatched⟩, ⟨true, false⟩) := by native_decide

theorem test_reset_reenable :
    processDriveCommand (mkTestBuf 0x3F) resetDriveState =
    (⟨true, true, .ok⟩, ⟨false, true⟩) := by native_decide

theorem test_no_enable :
    processDriveCommand (mkTestBuf 0x1F) ⟨false, false⟩ =
    (⟨false, false, .noEnable⟩, ⟨false, false⟩) := by native_decide

/-! ## Section 10: End-to-end CAN → torque safety -/

theorem can_to_torque_safety (buf : Array UInt8) (st : DriveState) :
    (processDriveCommand buf st).1.torque_allowed = true →
    safetyOk (extractDriveInputs (parseMcp2515 buf)) = true
    ∧ st.faulted = false := by
  unfold processDriveCommand
  exact torque_implies_safety _ _

/-! ## Section 11: Well-formedness / output consistency -/

theorem torque_implies_enabled (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    (evalTorqueGate inp st).1.drive_enabled = true := by
  unfold evalTorqueGate
  cases st.faulted <;> simp
  split <;> simp_all
  split <;> simp_all

theorem enabled_implies_torque (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.drive_enabled = true →
    (evalTorqueGate inp st).1.torque_allowed = true := by
  unfold evalTorqueGate
  cases st.faulted <;> simp
  split <;> simp_all
  split <;> simp_all

theorem reason_ok_iff_torque (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.reason = .ok ↔
    (evalTorqueGate inp st).1.torque_allowed = true := by
  unfold evalTorqueGate
  cases st.faulted <;> simp
  constructor
  · intro h
    split at h <;> simp_all
    · split at h <;> simp_all
      split at h <;> simp_all
      split at h <;> simp_all
      split at h <;> simp_all
    · split at h <;> simp_all
  · intro h
    split at h <;> simp_all
    split at h <;> simp_all

/-! ## Section 12: Capstone theorem -/

theorem torque_gate_correct (buf : Array UInt8) (st : DriveState) :
    ((processDriveCommand buf st).1.torque_allowed = true →
      safetyOk (extractDriveInputs (parseMcp2515 buf)) = true ∧ st.faulted = false)
    ∧ (st.faulted = true → (processDriveCommand buf st).1.torque_allowed = false)
    ∧ ((processDriveCommand buf st).1.torque_allowed = true →
        (extractDriveInputs (parseMcp2515 buf)).enable_request = true)
    ∧ (st.faulted = false →
        safetyOk (extractDriveInputs (parseMcp2515 buf)) = false →
        (processDriveCommand buf st).2.faulted = true)
    ∧ (st.faulted = true → (processDriveCommand buf st).2.faulted = true) := by
  unfold processDriveCommand
  exact ⟨torque_implies_safety _ _,
         faulted_denies_torque _ _,
         no_backdoor _ _,
         unsafe_latches_fault _ _,
         fault_persists _ _⟩
