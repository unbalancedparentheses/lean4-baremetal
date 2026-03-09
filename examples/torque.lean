-- Automotive Torque-Enable / Drive-Authority Gate in pure Lean 4 for bare-metal RISC-V
--
-- Reads a CAN command frame (data byte 0 = bit-packed safety inputs),
-- evaluates safety conditions, and outputs a torque authorization decision
-- with a reason code. Fault latching ensures that once a fault is detected,
-- the system stays in a safe state until explicitly reset.
--
-- This file is the single source of truth for the torque gate implementation.
-- examples/torque_proof.lean imports it via `import torque`, so the formal
-- proofs apply to this exact code.

import can_lib

/-! ## Data types -/

-- CAN command frame data byte 0 bit layout:
--   bit 0: brake_pressed
--   bit 1: gear_valid
--   bit 2: motor_temp_ok
--   bit 3: battery_ok
--   bit 4: estop_clear    (emergency stop NOT pressed)
--   bit 5: enable_request (driver wants torque)
--   bit 6: reserved
--   bit 7: reserved
structure DriveInputs where
  brake_pressed  : Bool
  gear_valid     : Bool
  motor_temp_ok  : Bool
  battery_ok     : Bool
  estop_clear    : Bool
  enable_request : Bool
  deriving Inhabited, DecidableEq, Repr

-- Persistent state across CAN cycles
structure DriveState where
  faulted       : Bool   -- latched fault flag
  drive_enabled : Bool   -- drive currently authorized
  deriving Inhabited, DecidableEq, Repr

-- Reason codes for torque denial
inductive ReasonCode where
  | ok           : ReasonCode   -- torque allowed
  | noEnable     : ReasonCode   -- driver didn't request enable
  | brakeNotSet  : ReasonCode   -- brake not pressed during enable
  | gearInvalid  : ReasonCode   -- gear position invalid
  | overTemp     : ReasonCode   -- motor over temperature
  | batteryFault : ReasonCode   -- battery fault
  | estopActive  : ReasonCode   -- emergency stop active
  | faultLatched : ReasonCode   -- previous fault still latched
  deriving Inhabited, DecidableEq, Repr

structure DriveOutput where
  torque_allowed : Bool
  drive_enabled  : Bool
  reason         : ReasonCode
  deriving Inhabited, DecidableEq, Repr

/-! ## Core logic -/

-- Safety predicate: all hardware conditions must be satisfied
@[inline] def safetyOk (inp : DriveInputs) : Bool :=
  inp.brake_pressed && inp.gear_valid && inp.motor_temp_ok &&
  inp.battery_ok && inp.estop_clear

-- Main gate evaluation (pure function, no IO)
def evalTorqueGate (inp : DriveInputs) (st : DriveState) : DriveOutput × DriveState :=
  if st.faulted then
    -- Fault latched: deny everything, keep faulted
    (⟨false, false, .faultLatched⟩, st)
  else if !safetyOk inp then
    -- Safety violation: deny, latch fault, disable drive
    let reason := if !inp.estop_clear then .estopActive
      else if !inp.battery_ok then .batteryFault
      else if !inp.motor_temp_ok then .overTemp
      else if !inp.gear_valid then .gearInvalid
      else .brakeNotSet
    (⟨false, false, reason⟩, ⟨true, false⟩)
  else if !inp.enable_request then
    -- Safe but driver doesn't want torque
    (⟨false, false, .noEnable⟩, ⟨false, false⟩)
  else
    -- All clear: authorize torque
    (⟨true, true, .ok⟩, ⟨false, true⟩)

-- Reset from latched fault (e.g., after operator clears fault)
def resetDriveState : DriveState := ⟨false, false⟩

/-! ## CAN integration -/

-- Extract DriveInputs from CAN frame data byte 0 via bit masking
def extractDriveInputs (frame : CanFrame) : DriveInputs :=
  let b := getU8 frame.data 0
  { brake_pressed  := (b &&& 0x01) != 0
    gear_valid     := (b &&& 0x02) != 0
    motor_temp_ok  := (b &&& 0x04) != 0
    battery_ok     := (b &&& 0x08) != 0
    estop_clear    := (b &&& 0x10) != 0
    enable_request := (b &&& 0x20) != 0 }

-- Full pipeline: CAN buffer → parse → extract inputs → evaluate gate
def processDriveCommand (buf : Array UInt8) (st : DriveState) : DriveOutput × DriveState :=
  let frame := parseMcp2515 buf
  let inputs := extractDriveInputs frame
  evalTorqueGate inputs st

/-! ## Hex/display helpers -/

def reasonToString : ReasonCode → String
  | .ok           => "ok"
  | .noEnable     => "no-enable"
  | .brakeNotSet  => "brake-not-set"
  | .gearInvalid  => "gear-invalid"
  | .overTemp     => "over-temp"
  | .batteryFault => "battery-fault"
  | .estopActive  => "estop-active"
  | .faultLatched => "fault-latched"

def outputToString (out : DriveOutput) : String :=
  s!"torque={out.torque_allowed} enabled={out.drive_enabled} reason={reasonToString out.reason}"

/-! ## Main — 5 scenarios for bare-metal test -/

-- Wrapping arrays in IO prevents the Lean compiler from constant-folding
-- the entire computation at module initialization time.
@[noinline] def mkTorqueBuf (bytes : Array UInt8) : IO (Array UInt8) := pure bytes

def main : IO Unit := do
  IO.println "=== Torque-Enable Gate ==="

  -- Build a CAN buffer: standard frame ID=0x100, DLC=1, data byte 0 = command bits
  -- MCP2515 layout: SIDH=0x20, SIDL=0x00, EID8=0x00, EID0=0x00, DLC=0x01, data[0]=cmd
  let mkCmdBuf (cmd : UInt8) : IO (Array UInt8) :=
    mkTorqueBuf #[0x20, 0x00, 0x00, 0x00, 0x01,
                  cmd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

  -- Scenario 1: All conditions met (brake=1, gear=1, temp=1, batt=1, estop=1, enable=1)
  -- cmd = 0x3F = 0b00111111
  let buf1 ← mkCmdBuf 0x3F
  let st0 : DriveState := ⟨false, false⟩
  let (out1, st1) := processDriveCommand buf1 st0
  IO.println s!"1: {outputToString out1}"  -- torque=true enabled=true reason=ok

  -- Scenario 2: E-stop active (estop_clear=0) — cmd = 0x2F = 0b00101111
  let buf2 ← mkCmdBuf 0x2F
  let (out2, st2) := processDriveCommand buf2 st1
  IO.println s!"2: {outputToString out2}"  -- torque=false enabled=false reason=estop-active

  -- Scenario 3: After fault latch — even with all-ok input, still denied
  let buf3 ← mkCmdBuf 0x3F
  let (out3, _st3) := processDriveCommand buf3 st2
  IO.println s!"3: {outputToString out3}"  -- torque=false enabled=false reason=fault-latched

  -- Scenario 4: Reset then re-enable — torque allowed again
  let st4 := resetDriveState
  let buf4 ← mkCmdBuf 0x3F
  let (out4, _st4') := processDriveCommand buf4 st4
  IO.println s!"4: {outputToString out4}"  -- torque=true enabled=true reason=ok

  -- Scenario 5: No enable request (enable=0) — cmd = 0x1F = 0b00011111
  let buf5 ← mkCmdBuf 0x1F
  let st5 : DriveState := ⟨false, false⟩
  let (out5, _st5') := processDriveCommand buf5 st5
  IO.println s!"5: {outputToString out5}"  -- torque=false enabled=false reason=no-enable

  IO.println "torque-gate ok"
