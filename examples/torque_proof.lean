-- Formal verification of the Automotive Torque-Enable / Drive-Authority Gate in Lean 4
--
-- This file imports examples/torque.lean (`import torque`), so every theorem
-- below is proven against the exact code that runs on bare metal.
-- If someone changes torque.lean, these proofs must still typecheck or
-- the build fails — the Lean kernel enforces the guarantee.
--
-- What this file proves (universally quantified unless noted):
--   1. Safety predicate properties (safetyOk)
--   2. Core safety guarantee: torque → all safety conditions held
--   3. Fault denial: faulted state always denies torque
--   4. Enable request required: no request → no torque
--   5. Safety violation latches fault
--   6. Fault persistence (latching)
--   7. No backdoor: torque requires enable_request
--   8. Bit extraction bridge (bv_decide)
--   9. Test vectors (native_decide)
--  10. End-to-end CAN → torque safety
--  11. Well-formedness / output consistency
--  12. Capstone theorem
--
-- Trust model:
--   Trusted: Lean kernel, lean -c compiler, GCC cross-compiler, freestanding runtime
--   Proven:  Safety invariants, fault latching, bit extraction, test vectors

import torque
import Std.Tactic.BVDecide

/-! ## Section 1: Safety predicate properties -/

-- All inputs true → safetyOk = true
theorem safetyOk_all_true :
    safetyOk ⟨true, true, true, true, true, true⟩ = true := by decide

-- Each individual false input → safetyOk = false
theorem safetyOk_brake_false (g m b e en : Bool) :
    safetyOk ⟨false, g, m, b, e, en⟩ = false := by decide

theorem safetyOk_gear_false (br m b e en : Bool) :
    safetyOk ⟨br, false, m, b, e, en⟩ = false := by
  simp [safetyOk, Bool.and_eq_true]; tauto

theorem safetyOk_temp_false (br g b e en : Bool) :
    safetyOk ⟨br, g, false, b, e, en⟩ = false := by
  simp [safetyOk, Bool.and_eq_true]; tauto

theorem safetyOk_battery_false (br g m e en : Bool) :
    safetyOk ⟨br, g, m, false, e, en⟩ = false := by
  simp [safetyOk, Bool.and_eq_true]; tauto

theorem safetyOk_estop_false (br g m b en : Bool) :
    safetyOk ⟨br, g, m, b, false, en⟩ = false := by
  simp [safetyOk, Bool.and_eq_true]; tauto

/-! ## Section 2: Core safety guarantee — torque → safety -/

-- THE critical safety property: if torque is allowed, all safety conditions held
theorem torque_implies_safety (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    safetyOk inp = true ∧ st.faulted = false := by
  unfold evalTorqueGate
  split <;> simp_all [safetyOk]

/-! ## Section 3: Fault denial — faulted state always denies torque -/

theorem faulted_denies_torque (inp : DriveInputs) (st : DriveState)
    (hf : st.faulted = true) :
    (evalTorqueGate inp st).1.torque_allowed = false := by
  unfold evalTorqueGate; simp [hf]

/-! ## Section 4: Enable request required -/

theorem no_request_no_torque (inp : DriveInputs) (st : DriveState)
    (hne : inp.enable_request = false) :
    (evalTorqueGate inp st).1.torque_allowed = false := by
  unfold evalTorqueGate
  simp_all [safetyOk]
  split <;> simp_all
  split <;> simp_all

/-! ## Section 5: Safety violation latches fault -/

theorem unsafe_latches_fault (inp : DriveInputs) (st : DriveState)
    (hok : st.faulted = false) (hunsafe : safetyOk inp = false) :
    (evalTorqueGate inp st).2.faulted = true := by
  unfold evalTorqueGate; simp [hok, hunsafe]

/-! ## Section 6: Fault persistence (latching) -/

theorem fault_persists (inp : DriveInputs) (st : DriveState)
    (hf : st.faulted = true) :
    (evalTorqueGate inp st).2.faulted = true := by
  unfold evalTorqueGate; simp [hf]

/-! ## Section 7: No backdoor — torque requires enable_request -/

theorem no_backdoor (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    inp.enable_request = true := by
  unfold evalTorqueGate
  split <;> simp_all [safetyOk]

/-! ## Section 8: Bit extraction bridge (bv_decide) -/

-- Each DriveInputs field extraction from UInt8 byte matches getLsbD at the correct bit position

-- brake_pressed: bit 0
private theorem brake_bit_bridge (b : UInt8) :
    ((b &&& 0x01) != 0) = b.toBitVec.getLsbD 0 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- gear_valid: bit 1
private theorem gear_bit_bridge (b : UInt8) :
    ((b &&& 0x02) != 0) = b.toBitVec.getLsbD 1 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- motor_temp_ok: bit 2
private theorem temp_bit_bridge (b : UInt8) :
    ((b &&& 0x04) != 0) = b.toBitVec.getLsbD 2 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- battery_ok: bit 3
private theorem battery_bit_bridge (b : UInt8) :
    ((b &&& 0x08) != 0) = b.toBitVec.getLsbD 3 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- estop_clear: bit 4
private theorem estop_bit_bridge (b : UInt8) :
    ((b &&& 0x10) != 0) = b.toBitVec.getLsbD 4 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- enable_request: bit 5
private theorem enable_bit_bridge (b : UInt8) :
    ((b &&& 0x20) != 0) = b.toBitVec.getLsbD 5 := by
  simp only [bne, BEq.beq, UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and]
  bv_decide

-- extractDriveInputs uses the correct bit positions
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

-- Helper: build a CAN buffer for standard frame ID=0x100, DLC=1, data[0]=cmd
private def mkTestBuf (cmd : UInt8) : Array UInt8 :=
  #[0x20, 0x00, 0x00, 0x00, 0x01,
    cmd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

-- Scenario 1: All conditions met → torque allowed
theorem test_all_ok :
    processDriveCommand (mkTestBuf 0x3F) ⟨false, false⟩ =
    (⟨true, true, .ok⟩, ⟨false, true⟩) := by native_decide

-- Scenario 2: E-stop active → denied, fault latched
theorem test_estop :
    processDriveCommand (mkTestBuf 0x2F) ⟨false, true⟩ =
    (⟨false, false, .estopActive⟩, ⟨true, false⟩) := by native_decide

-- Scenario 3: After fault latch → still denied (fault persistence)
theorem test_fault_latched :
    processDriveCommand (mkTestBuf 0x3F) ⟨true, false⟩ =
    (⟨false, false, .faultLatched⟩, ⟨true, false⟩) := by native_decide

-- Scenario 4: Reset then re-enable → torque allowed
theorem test_reset_reenable :
    processDriveCommand (mkTestBuf 0x3F) resetDriveState =
    (⟨true, true, .ok⟩, ⟨false, true⟩) := by native_decide

-- Scenario 5: No enable request → safe idle (no torque, no fault)
theorem test_no_enable :
    processDriveCommand (mkTestBuf 0x1F) ⟨false, false⟩ =
    (⟨false, false, .noEnable⟩, ⟨false, false⟩) := by native_decide

/-! ## Section 10: End-to-end CAN → torque safety -/

-- If processDriveCommand allows torque, the raw CAN byte had all safety bits set
theorem can_to_torque_safety (buf : Array UInt8) (st : DriveState) :
    (processDriveCommand buf st).1.torque_allowed = true →
    safetyOk (extractDriveInputs (parseMcp2515 buf)) = true
    ∧ st.faulted = false := by
  unfold processDriveCommand
  exact torque_implies_safety _ _

/-! ## Section 11: Well-formedness / output consistency -/

-- torque_allowed → drive_enabled
theorem torque_implies_enabled (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.torque_allowed = true →
    (evalTorqueGate inp st).1.drive_enabled = true := by
  unfold evalTorqueGate
  split <;> simp_all [safetyOk]

-- drive_enabled → torque_allowed
theorem enabled_implies_torque (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.drive_enabled = true →
    (evalTorqueGate inp st).1.torque_allowed = true := by
  unfold evalTorqueGate
  split <;> simp_all [safetyOk]
  split <;> simp_all
  split <;> simp_all

-- Reason code = .ok iff torque_allowed = true
theorem reason_ok_iff_torque (inp : DriveInputs) (st : DriveState) :
    (evalTorqueGate inp st).1.reason = .ok ↔
    (evalTorqueGate inp st).1.torque_allowed = true := by
  unfold evalTorqueGate
  constructor
  · split <;> simp_all [safetyOk]
    split <;> simp_all
    split <;> simp_all
  · split <;> simp_all [safetyOk]

/-! ## Section 12: Capstone theorem -/

/-- Full pipeline correctness for the torque-enable gate.

    All conjuncts below are universally quantified (proven for ALL inputs).

    1. Torque → all safety conditions
    2. Faulted → no torque
    3. Torque → enable requested
    4. Unsafe → fault latches
    5. Fault persists -/
theorem torque_gate_correct (buf : Array UInt8) (st : DriveState) :
    -- 1. Torque → all safety conditions
    ((processDriveCommand buf st).1.torque_allowed = true →
      safetyOk (extractDriveInputs (parseMcp2515 buf)) = true ∧ st.faulted = false)
    -- 2. Faulted → no torque
    ∧ (st.faulted = true → (processDriveCommand buf st).1.torque_allowed = false)
    -- 3. Torque → enable requested
    ∧ ((processDriveCommand buf st).1.torque_allowed = true →
        (extractDriveInputs (parseMcp2515 buf)).enable_request = true)
    -- 4. Unsafe → fault latches
    ∧ (st.faulted = false →
        safetyOk (extractDriveInputs (parseMcp2515 buf)) = false →
        (processDriveCommand buf st).2.faulted = true)
    -- 5. Fault persists
    ∧ (st.faulted = true → (processDriveCommand buf st).2.faulted = true) := by
  unfold processDriveCommand
  exact ⟨torque_implies_safety _ _,
         faulted_denies_torque _ _,
         no_backdoor _ _,
         unsafe_latches_fault _ _,
         fault_persists _ _⟩
