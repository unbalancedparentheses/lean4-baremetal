-- Runtime coverage test for bare-metal Lean 4

def check (name : String) (ok : Bool) : IO Unit := do
  if ok then
    IO.println s!"  PASS  {name}"
  else
    IO.println s!"  FAIL  {name}"
    throw (IO.userError s!"sub-test failed: {name}")

@[noinline] def mkVal (v : α) : IO α := pure v

def main : IO Unit := do
  IO.println "=== Runtime Coverage Test ==="

  -- 1. Thunk forcing (lean_mk_thunk, lean_thunk_get_core)
  let t : Thunk Nat := Thunk.mk (fun _ => 42)
  let v := t.get
  check "Thunk forcing" (v == 42)

  -- 2. Closure partial application (lean_closure_call under-application)
  let add3 := fun (a b c : Nat) => a + b + c
  let add3_1 := add3 10
  let add3_2 := add3_1 20
  let result := add3_2 30
  check "Closure partial application" (result == 60)

  -- 3. Shared array copy (lean_array_push non-exclusive path)
  let arr ← mkVal #[1, 2, 3]
  let arr2 := arr
  let arr3 := arr2.push 4
  check "Shared array copy" (arr.size == 3 && arr3.size == 4)
  check "Shared array content" (arr3[3]! == 4)

  -- 4. ST ref create/set/get
  let r ← IO.mkRef (10 : Nat)
  let v0 ← r.get
  check "ST ref initial" (v0 == 10)
  r.set 99
  let v1 ← r.get
  check "ST ref after set" (v1 == 99)

  -- 5. String.toList + String.ofList roundtrip
  let s ← mkVal "hello"
  let chars := s.toList
  let s2 := String.ofList chars
  check "String roundtrip" (s == s2)

  -- 6. ByteArray push
  let mut ba : ByteArray := ⟨#[]⟩
  ba := ByteArray.push ba 0xDE
  ba := ByteArray.push ba 0xAD
  ba := ByteArray.push ba 0xBE
  ba := ByteArray.push ba 0xEF
  check "ByteArray push" (ByteArray.size ba == 4)

  IO.println "runtime-test ok"
