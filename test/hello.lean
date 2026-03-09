def main : IO Unit := do
  IO.println "=== Lean 4 on Bare-Metal RISC-V ==="
  IO.println ""
  IO.println "No OS, no libc -- pure Lean compiled to C, running directly on hardware."
  IO.println "This is the simplest possible bare-metal Lean program."
  IO.println ""
  IO.println "Hello from bare-metal Lean!"
