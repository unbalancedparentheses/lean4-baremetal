import Lake
open Lake DSL

package sha256Baremetal

-- The SHA-256 implementation (also used as bare-metal entry point via `lean -c`)
lean_lib sha256 where
  srcDir := "examples"
  roots := #[`sha256]

-- Formal proofs — imports sha256, so proofs apply to the exact same code
@[default_target]
lean_lib sha256_proof where
  srcDir := "examples"
  roots := #[`sha256_proof]

-- CAN 2.0 library (types, parser, encoder, CRC — no main)
lean_lib can_lib where
  srcDir := "examples"
  roots := #[`can_lib]

-- The CAN 2.0 frame parser entry point (imports can_lib, adds main)
lean_lib can where
  srcDir := "examples"
  roots := #[`can]

-- Formal proofs — imports can_lib, so proofs apply to the exact same code
@[default_target]
lean_lib can_proof where
  srcDir := "examples"
  roots := #[`can_proof]

-- The torque-enable gate (also used as bare-metal entry point via `lean -c`)
lean_lib torque where
  srcDir := "examples"
  roots := #[`torque]

-- Formal proofs — imports torque, so proofs apply to the exact same code
@[default_target]
lean_lib torque_proof where
  srcDir := "examples"
  roots := #[`torque_proof]

-- Runtime coverage test (bare-metal entry point via `lean -c`)
lean_exe runtime_test where
  srcDir := "examples"
  root := `runtime_test
