def buildChunk (round : Nat) : Array UInt32 := Id.run do
  let mut xs : Array UInt32 := #[]
  for i in [:512] do
    xs := xs.push (UInt32.ofNat (round * 512 + i))
  return xs

def main : IO Unit := do
  let mut lastMsg := ""
  for round in [:64] do
    let xs := buildChunk round
    let ys := xs.map (fun x => x + 1)
    let msg := s!"round={round} size={ys.size}"
    if ys.size != 512 then
      throw <| IO.userError s!"unexpected chunk size: {ys.size}"
    lastMsg := msg
  IO.println "alloc-stress ok"
  IO.println lastMsg
