-- Formal verification of the Automotive Torque-Enable / Drive-Authority Gate in Lean 4
--
-- This file imports examples/torque.lean (`import torque`), so every theorem
-- below is proven against the exact code that runs on bare metal.

import torque
import bitfield
import Std.Tactic.BVDecide

-- DecidableEq is needed for native_decide on equality tests,
-- but we keep it out of torque.lean to avoid pulling library code into the binary.
deriving instance DecidableEq for ReasonCode
deriving instance DecidableEq for DriveInputs
deriving instance DecidableEq for DriveState
deriving instance DecidableEq for DriveOutput

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

/-! ## Section 8: Bit extraction bridge (uses shared bitfield library) -/

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
  exact ⟨uint8_bit0 _, uint8_bit1 _, uint8_bit2 _,
         uint8_bit3 _, uint8_bit4 _, uint8_bit5 _⟩

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

-- Wrong CAN ID (0x200): SIDH=0x40, SIDL=0x00 → ID = (0x40 << 3) | 0 = 0x200
private def mkWrongIdBuf (cmd : UInt8) : Array UInt8 :=
  #[0x40, 0x00, 0x00, 0x00, 0x01,
    cmd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem test_wrong_id_rejected :
    processDriveCommand (mkWrongIdBuf 0x3F) ⟨false, false⟩ =
    (⟨false, false, .frameRejected⟩, ⟨false, false⟩) := by native_decide

-- RTR frame: DLC byte = 0x41 (RTR bit set + DLC=1)
private def mkRtrBuf (cmd : UInt8) : Array UInt8 :=
  #[0x20, 0x00, 0x00, 0x00, 0x41,
    cmd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem test_rtr_rejected :
    processDriveCommand (mkRtrBuf 0x3F) ⟨false, false⟩ =
    (⟨false, false, .frameRejected⟩, ⟨false, false⟩) := by native_decide

/-! ## Section 10: Frame admissibility -/

-- Inadmissible frames are always denied torque
theorem inadmissible_denies_torque (buf : Array UInt8) (st : DriveState)
    (h : frameAdmissible (parseMcp2515 buf) = false) :
    (processDriveCommand buf st).1.torque_allowed = false := by
  unfold processDriveCommand; simp [h]

-- Inadmissible frames leave state unchanged
theorem inadmissible_preserves_state (buf : Array UInt8) (st : DriveState)
    (h : frameAdmissible (parseMcp2515 buf) = false) :
    (processDriveCommand buf st).2 = st := by
  unfold processDriveCommand; simp [h]

-- Torque authorization requires an admissible frame
theorem torque_requires_admissible (buf : Array UInt8) (st : DriveState) :
    (processDriveCommand buf st).1.torque_allowed = true →
    frameAdmissible (parseMcp2515 buf) = true := by
  unfold processDriveCommand
  split
  · simp
  · intro; simp_all

/-! ## Section 11: End-to-end CAN → torque safety -/

theorem can_to_torque_safety (buf : Array UInt8) (st : DriveState) :
    (processDriveCommand buf st).1.torque_allowed = true →
    safetyOk (extractDriveInputs (parseMcp2515 buf)) = true
    ∧ st.faulted = false := by
  unfold processDriveCommand
  split
  · simp
  · exact torque_implies_safety _ _

/-! ## Section 12: Well-formedness / output consistency -/

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

/-! ## Section 13: Capstone theorem -/

theorem torque_gate_correct (buf : Array UInt8) (st : DriveState) :
    -- 1. Torque allowed → safety ok and not faulted
    ((processDriveCommand buf st).1.torque_allowed = true →
      safetyOk (extractDriveInputs (parseMcp2515 buf)) = true ∧ st.faulted = false)
    -- 2. Faulted → torque denied
    ∧ (st.faulted = true → (processDriveCommand buf st).1.torque_allowed = false)
    -- 3. Torque allowed → enable requested
    ∧ ((processDriveCommand buf st).1.torque_allowed = true →
        (extractDriveInputs (parseMcp2515 buf)).enable_request = true)
    -- 4. Admissible + not faulted + unsafe → fault latched
    ∧ (frameAdmissible (parseMcp2515 buf) = true →
        st.faulted = false →
        safetyOk (extractDriveInputs (parseMcp2515 buf)) = false →
        (processDriveCommand buf st).2.faulted = true)
    -- 5. Faulted → fault persists (even for inadmissible frames)
    ∧ (st.faulted = true → (processDriveCommand buf st).2.faulted = true) := by
  unfold processDriveCommand
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- 1. torque allowed → safety ∧ not faulted
  · split
    · simp
    · exact torque_implies_safety _ _
  -- 2. faulted → torque denied
  · split
    · simp
    · exact faulted_denies_torque _ _
  -- 3. torque → enable requested
  · split
    · simp
    · exact no_backdoor _ _
  -- 4. admissible + not faulted + unsafe → fault latched
  · split
    · intro h; simp_all
    · intro _ h1 h2; exact unsafe_latches_fault _ _ h1 h2
  -- 5. faulted → fault persists
  · split
    · intro h; exact h
    · exact fault_persists _ _
