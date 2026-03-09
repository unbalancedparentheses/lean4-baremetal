def main : IO Unit := do
  IO.println "about to raise expected io error"
  throw <| IO.userError "expected runtime error"
