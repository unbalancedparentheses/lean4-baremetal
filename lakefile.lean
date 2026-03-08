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
