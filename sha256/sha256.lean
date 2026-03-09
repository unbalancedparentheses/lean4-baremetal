-- SHA-256 (FIPS 180-4) in pure Lean 4 for bare-metal RISC-V
--
-- This file is the single source of truth for the SHA-256 implementation.
-- examples/sha256_proof.lean imports it via `import sha256`, so the formal
-- proofs (bv_decide, native_decide) apply to this exact code.

-- C-timed Lean SHA-256: calls l_sha256 with rdcycle in C so the Lean compiler
-- can't reorder the pure computation outside the timing window.
-- Returns (digest, cycles).
@[extern "lean_sha256_timed"]
opaque sha256Timed : Array UInt8 → IO (Array UInt32 × UInt64)

-- C reference SHA-256 benchmarks (implemented in sha256_ref.c)
-- Each hashes a hardcoded message, prints result via UART, returns cycle count.
@[extern "lean_c_sha256_bench_3"]
opaque cSha256Bench3 : IO UInt64
@[extern "lean_c_sha256_bench_64"]
opaque cSha256Bench64 : IO UInt64
@[extern "lean_c_sha256_bench_256"]
opaque cSha256Bench256 : IO UInt64

def getU32 (a : Array UInt32) (i : Nat) : UInt32 := a.getD i 0
def getU8 (a : Array UInt8) (i : Nat) : UInt8 := a.getD i 0

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

def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def parseWords (block : Array UInt8) (i : Nat) (acc : Array UInt32) : Array UInt32 :=
  if i >= 16 then acc
  else
    let b0 := (getU8 block (i * 4)).toUInt32
    let b1 := (getU8 block (i * 4 + 1)).toUInt32
    let b2 := (getU8 block (i * 4 + 2)).toUInt32
    let b3 := (getU8 block (i * 4 + 3)).toUInt32
    parseWords block (i + 1) (acc.push ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3))
termination_by 16 - i

def expandWords (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i >= 64 then w
  else
    let s0 := smallSigma0 (getU32 w (i - 15))
    let s1 := smallSigma1 (getU32 w (i - 2))
    let val := getU32 w (i - 16) + s0 + getU32 w (i - 7) + s1
    expandWords (w.push val) (i + 1)
termination_by 64 - i

def messageSchedule (block : Array UInt8) : Array UInt32 :=
  expandWords (parseWords block 0 #[]) 16

structure HashState where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
  deriving DecidableEq, Repr

def compressRounds (w : Array UInt32) (st : HashState) (i : Nat) : HashState :=
  if i >= 64 then st
  else
    let t1 := st.h + bigSigma1 st.e + ch st.e st.f st.g + getU32 K i + getU32 w i
    let t2 := bigSigma0 st.a + maj st.a st.b st.c
    compressRounds w { a := t1 + t2, b := st.a, c := st.b, d := st.c,
                       e := st.d + t1, f := st.e, g := st.f, h := st.g } (i + 1)
termination_by 64 - i

def compress (hash : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let init : HashState := {
    a := getU32 hash 0, b := getU32 hash 1, c := getU32 hash 2, d := getU32 hash 3,
    e := getU32 hash 4, f := getU32 hash 5, g := getU32 hash 6, h := getU32 hash 7
  }
  let st := compressRounds w init 0
  #[getU32 hash 0 + st.a, getU32 hash 1 + st.b,
    getU32 hash 2 + st.c, getU32 hash 3 + st.d,
    getU32 hash 4 + st.e, getU32 hash 5 + st.f,
    getU32 hash 6 + st.g, getU32 hash 7 + st.h]

def appendZeros (p : Array UInt8) : Nat → Array UInt8
  | 0 => p
  | n + 1 => appendZeros (p.push 0x00) n

def padMsg (msg : Array UInt8) : Array UInt8 :=
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let p := msg.push 0x80
  let padLen := (119 - msg.size % 64) % 64
  let p := appendZeros p padLen
  let p := p.push (bitLen >>> 56).toUInt8
  let p := p.push (bitLen >>> 48).toUInt8
  let p := p.push (bitLen >>> 40).toUInt8
  let p := p.push (bitLen >>> 32).toUInt8
  let p := p.push (bitLen >>> 24).toUInt8
  let p := p.push (bitLen >>> 16).toUInt8
  let p := p.push (bitLen >>> 8).toUInt8
  p.push bitLen.toUInt8

def extractBlock (padded : Array UInt8) (off : Nat) (j : Nat) (acc : Array UInt8) : Array UInt8 :=
  if j >= 64 then acc
  else extractBlock padded off (j + 1) (acc.push (getU8 padded (off + j)))
termination_by 64 - j

def sha256Loop (padded : Array UInt8) (numBlocks : Nat) (i : Nat) (hash : Array UInt32) : Array UInt32 :=
  if i >= numBlocks then hash
  else
    let block := extractBlock padded (i * 64) 0 #[]
    let w := messageSchedule block
    sha256Loop padded numBlocks (i + 1) (compress hash w)
termination_by numBlocks - i

def sha256 (msg : Array UInt8) : Array UInt32 :=
  let padded := padMsg msg
  sha256Loop padded (padded.size / 64) 0 H0

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

-- Build an array [0x00, 0x01, ..., n-1]
def mkSeqBytes (n : Nat) : Array UInt8 :=
  Id.run do
    let mut a : Array UInt8 := #[]
    for i in [:n] do
      a := a.push (i % 256).toUInt8
    return a

-- Print ratio as "N.Nx" using integer arithmetic
def printRatio (leanCycles cCycles : UInt64) : IO Unit := do
  if cCycles == 0 then
    IO.println "Ratio:    N/A (C cycles = 0)"
  else
    let tenths := leanCycles * 10 / cCycles
    let whole := tenths / 10
    let frac := tenths % 10
    IO.println s!"Ratio:    {whole}.{frac}x (Lean / C)"

-- Run one benchmark: Lean hash + C ref hash, print comparison
def runBench (label : String) (msg : Array UInt8) (expected : String)
    (cBench : IO UInt64) : IO Unit := do
  IO.println s!"--- {label} ---"
  IO.println ""
  -- Lean (timing done in C via sha256Timed to prevent reordering)
  let (digest, leanCycles) ← sha256Timed msg
  IO.println s!"Expected: {expected}"
  IO.println s!"Lean:     {hashToHex digest}"
  IO.println s!"  cycles: {leanCycles}"
  -- C reference (prints its own "C ref: ..." line via UART)
  let cCycles ← cBench
  IO.println ""
  printRatio leanCycles cCycles
  IO.println ""

-- Main
def main : IO Unit := do
  IO.println "=== SHA-256 (FIPS 180-4) Benchmark ==="
  IO.println ""
  IO.println "Compares Lean SHA-256 vs C reference (same FIPS 180-4 algorithm, same -O2)."
  IO.println "Lean implementation is proven correct: sha256 msg = spec_sha256 msg for all inputs."
  IO.println ""
  -- 3-byte input: "abc" (1 block)
  let msg3 : Array UInt8 := #[0x61, 0x62, 0x63]
  runBench "3 bytes (\"abc\", 1 block)" msg3
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    cSha256Bench3
  -- 64-byte input: 0x00..0x3f (2 blocks)
  let msg64 := mkSeqBytes 64
  runBench "64 bytes (0x00..0x3f, 2 blocks)" msg64
    "fdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108"
    cSha256Bench64
  -- 256-byte input: 0x00..0xff (5 blocks)
  let msg256 := mkSeqBytes 256
  runBench "256 bytes (0x00..0xff, 5 blocks)" msg256
    "40aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880"
    cSha256Bench256
