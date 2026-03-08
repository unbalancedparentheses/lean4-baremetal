-- SHA-256 (FIPS 180-4) in pure Lean 4 for bare-metal RISC-V

-- RISC-V cycle counter (implemented in lean_rt.c)
@[extern "lean_cycles_now"]
opaque cyclesNow : IO UInt64

-- SHA-256 round constants
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Initial hash values
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

-- Unchecked array access helper
@[inline] def getU32 (a : Array UInt32) (i : Nat) : UInt32 :=
  a.getD i 0
@[inline] def getU8 (a : Array UInt8) (i : Nat) : UInt8 :=
  a.getD i 0

-- Bitwise operations
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

@[inline] def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] def bigSigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

@[inline] def bigSigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

@[inline] def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

@[inline] def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

-- Build message schedule: 16 words from block, expand to 64
def messageSchedule (block : Array UInt8) : Array UInt32 :=
  -- Parse 16 big-endian UInt32 words from 64-byte block
  let w : Array UInt32 := Id.run do
    let mut w : Array UInt32 := #[]
    for i in [:16] do
      let b0 := (getU8 block (i * 4)).toUInt32
      let b1 := (getU8 block (i * 4 + 1)).toUInt32
      let b2 := (getU8 block (i * 4 + 2)).toUInt32
      let b3 := (getU8 block (i * 4 + 3)).toUInt32
      w := w.push ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
    return w
  -- Expand to 64 words
  Id.run do
    let mut w := w
    for i in [16:64] do
      let s0 := smallSigma0 (getU32 w (i - 15))
      let s1 := smallSigma1 (getU32 w (i - 2))
      let val := getU32 w (i - 16) + s0 + getU32 w (i - 7) + s1
      w := w.push val
    return w

-- Compression: 64 rounds
structure HashState where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

def compress (hash : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let init : HashState := {
    a := getU32 hash 0, b := getU32 hash 1,
    c := getU32 hash 2, d := getU32 hash 3,
    e := getU32 hash 4, f := getU32 hash 5,
    g := getU32 hash 6, h := getU32 hash 7
  }
  let st := Id.run do
    let mut st := init
    for i in [:64] do
      let t1 := st.h + bigSigma1 st.e + ch st.e st.f st.g +
                getU32 K i + getU32 w i
      let t2 := bigSigma0 st.a + maj st.a st.b st.c
      st := {
        a := t1 + t2
        b := st.a
        c := st.b
        d := st.c
        e := st.d + t1
        f := st.e
        g := st.f
        h := st.g
      }
    return st
  #[getU32 hash 0 + st.a, getU32 hash 1 + st.b,
    getU32 hash 2 + st.c, getU32 hash 3 + st.d,
    getU32 hash 4 + st.e, getU32 hash 5 + st.f,
    getU32 hash 6 + st.g, getU32 hash 7 + st.h]

-- Padding: append 0x80, zeros to 56 mod 64, then 64-bit BE length
def pad (msg : Array UInt8) : Array UInt8 :=
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  -- Append 0x80 and pad with zeros until length ≡ 56 (mod 64)
  let padded := Id.run do
    let mut p := msg.push 0x80
    while p.size % 64 != 56 do
      p := p.push 0x00
    return p
  -- Append 64-bit big-endian bit length
  let padded := padded.push (bitLen >>> 56).toUInt8
  let padded := padded.push (bitLen >>> 48).toUInt8
  let padded := padded.push (bitLen >>> 40).toUInt8
  let padded := padded.push (bitLen >>> 32).toUInt8
  let padded := padded.push (bitLen >>> 24).toUInt8
  let padded := padded.push (bitLen >>> 16).toUInt8
  let padded := padded.push (bitLen >>> 8).toUInt8
  padded.push bitLen.toUInt8

-- SHA-256 hash function
def sha256 (msg : Array UInt8) : Array UInt32 :=
  let padded := pad msg
  let numBlocks := padded.size / 64
  Id.run do
    let mut hash := H0
    for i in [:numBlocks] do
      let block : Array UInt8 := Id.run do
        let mut b : Array UInt8 := #[]
        for j in [:64] do
          b := b.push (getU8 padded (i * 64 + j))
        return b
      let w := messageSchedule block
      hash := compress hash w
    return hash

-- Hex output
def nibbleToHex (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (0x30 + n.toNat)
  else Char.ofNat (0x61 + n.toNat - 10)

def uint32ToHex (v : UInt32) : String :=
  let s := String.push "" (nibbleToHex ((v >>> 28).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 24).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 20).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 16).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 12).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 8).toUInt8 &&& 0x0f))
  let s := String.push s (nibbleToHex ((v >>> 4).toUInt8 &&& 0x0f))
  String.push s (nibbleToHex (v.toUInt8 &&& 0x0f))

def hashToHex (hash : Array UInt32) : String :=
  Id.run do
    let mut s := ""
    for i in [:hash.size] do
      s := s ++ uint32ToHex (getU32 hash i)
    return s

-- Main
def main : IO Unit := do
  let msg : Array UInt8 := #[0x61, 0x62, 0x63]  -- "abc"
  let t0 ← cyclesNow
  let digest := sha256 msg
  let t1 ← cyclesNow
  IO.println (hashToHex digest)
  IO.println s!"cycles: {t1 - t0}"
