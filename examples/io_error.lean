def main : IO Unit := do
  IO.println "=== IO Error Handling Test ==="
  IO.println ""
  IO.println "Tests that the bare-metal runtime correctly handles IO.userError exceptions."
  IO.println "The runtime should catch the error and print the message."
  IO.println ""
  IO.println "Raising expected IO error..."
  throw <| IO.userError "expected runtime error"
