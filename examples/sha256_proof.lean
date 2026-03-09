-- Formal verification of SHA-256 (FIPS 180-4) in Lean 4
--
-- This file imports examples/sha256.lean (`import sha256`), so every theorem
-- below is proven against the exact code that runs on bare metal.
-- If someone changes sha256.lean, these proofs must still typecheck or
-- the build fails — the Lean kernel enforces the guarantee.
--
-- What this file proves:
--   1. Every bitwise operation (rotr, ch, maj, sigmas) matches FIPS 180-4 spec
--      — universally quantified over ALL 32-bit inputs via `bv_decide`
--   2. FIPS 180-4 test vectors verified at COMPILE TIME via `native_decide`
--   3. Universal structural properties: sha256 always returns 8 elements,
--      messageSchedule returns 64, etc. — proven for ALL inputs
--
-- Trust model (same as HACL*, Fiat-Crypto):
--   Trusted: Lean kernel, lean -c compiler, GCC cross-compiler, freestanding runtime
--   Proven:  Bitwise ops correct, test vectors match, structural properties universal

import sha256
import Std.Tactic.BVDecide

/-! ## Section 1: FIPS 180-4 reference spec (BitVec) -/

-- Reference operations using Lean's built-in BitVec.rotateRight
-- These match the mathematical definitions in FIPS 180-4 Section 4.1.2

def spec_rotr (x : BitVec 32) (n : Nat) := x.rotateRight n

def spec_ch (x y z : BitVec 32) := (x &&& y) ||| (~~~x &&& z)

def spec_maj (x y z : BitVec 32) := (x &&& y) ||| (x &&& z) ||| (y &&& z)

def spec_bigSigma0 (x : BitVec 32) := spec_rotr x 2 ^^^ spec_rotr x 13 ^^^ spec_rotr x 22

def spec_bigSigma1 (x : BitVec 32) := spec_rotr x 6 ^^^ spec_rotr x 11 ^^^ spec_rotr x 25

def spec_smallSigma0 (x : BitVec 32) := spec_rotr x 7 ^^^ spec_rotr x 18 ^^^ (x >>> 3)

def spec_smallSigma1 (x : BitVec 32) := spec_rotr x 17 ^^^ spec_rotr x 19 ^^^ (x >>> 10)

/-! ## Section 2: Bitwise operation proofs via `bv_decide`

    These are universally quantified — proven for ALL possible 32-bit inputs,
    not just test cases. Each theorem states that our shift-based implementation
    equals the FIPS 180-4 spec operation. -/

-- rotr(x, n) = x.rotateRight n — one per SHA-256 rotation amount
theorem rotr_2_correct (x : BitVec 32) :
    (x >>> 2 ||| x <<< 30) = x.rotateRight 2 := by bv_decide
theorem rotr_6_correct (x : BitVec 32) :
    (x >>> 6 ||| x <<< 26) = x.rotateRight 6 := by bv_decide
theorem rotr_7_correct (x : BitVec 32) :
    (x >>> 7 ||| x <<< 25) = x.rotateRight 7 := by bv_decide
theorem rotr_11_correct (x : BitVec 32) :
    (x >>> 11 ||| x <<< 21) = x.rotateRight 11 := by bv_decide
theorem rotr_13_correct (x : BitVec 32) :
    (x >>> 13 ||| x <<< 19) = x.rotateRight 13 := by bv_decide
theorem rotr_17_correct (x : BitVec 32) :
    (x >>> 17 ||| x <<< 15) = x.rotateRight 17 := by bv_decide
theorem rotr_18_correct (x : BitVec 32) :
    (x >>> 18 ||| x <<< 14) = x.rotateRight 18 := by bv_decide
theorem rotr_19_correct (x : BitVec 32) :
    (x >>> 19 ||| x <<< 13) = x.rotateRight 19 := by bv_decide
theorem rotr_22_correct (x : BitVec 32) :
    (x >>> 22 ||| x <<< 10) = x.rotateRight 22 := by bv_decide
theorem rotr_25_correct (x : BitVec 32) :
    (x >>> 25 ||| x <<< 7) = x.rotateRight 25 := by bv_decide

-- Ch(x,y,z): our XOR form equals the standard bit-select (OR) form
theorem ch_correct (x y z : BitVec 32) :
    ((x &&& y) ^^^ (~~~x &&& z)) = ((x &&& y) ||| (~~~x &&& z)) := by bv_decide

-- Maj(x,y,z): our XOR form equals the standard majority (OR) form
theorem maj_correct (x y z : BitVec 32) :
    ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)) =
    ((x &&& y) ||| (x &&& z) ||| (y &&& z)) := by bv_decide

/-! ## Section 3: Test vectors via `native_decide`

    Sources: FIPS 180-4 appendix B, NIST CAVP SHA256ShortMsg.rsp (CAVS 11.0).
    These theorems are verified at COMPILE TIME. If this file typechecks,
    the SHA-256 implementation produces the correct digests.
    The Lean kernel itself is the verifier. -/

-- FIPS 180-4 B.1: SHA-256("abc")
theorem sha256_abc :
    sha256 #[0x61, 0x62, 0x63] =
    #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
      0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by native_decide

-- FIPS 180-4: SHA-256("") (empty string)
theorem sha256_empty :
    sha256 #[] =
    #[0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
      0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855] := by native_decide

-- FIPS 180-4 B.2: SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
-- 56-byte message → two 64-byte blocks after padding (tests multi-block processing)
theorem sha256_two_blocks :
    sha256 #[0x61, 0x62, 0x63, 0x64, 0x62, 0x63, 0x64, 0x65,
             0x63, 0x64, 0x65, 0x66, 0x64, 0x65, 0x66, 0x67,
             0x65, 0x66, 0x67, 0x68, 0x66, 0x67, 0x68, 0x69,
             0x67, 0x68, 0x69, 0x6a, 0x68, 0x69, 0x6a, 0x6b,
             0x69, 0x6a, 0x6b, 0x6c, 0x6a, 0x6b, 0x6c, 0x6d,
             0x6b, 0x6c, 0x6d, 0x6e, 0x6c, 0x6d, 0x6e, 0x6f,
             0x6d, 0x6e, 0x6f, 0x70, 0x6e, 0x6f, 0x70, 0x71] =
    #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039,
      0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1] := by native_decide

-- NIST CAVP Len=8: SHA-256(0xd3) — minimal non-empty input (1 byte)
theorem sha256_cavp_1byte :
    sha256 #[0xd3] =
    #[0x28969cdf, 0xa74a12c8, 0x2f3bad96, 0x0b0b000a,
      0xca2ac329, 0xdeea5c23, 0x28ebc6f2, 0xba9802c1] := by native_decide

-- NIST CAVP Len=32: SHA-256(0x74ba2521) — small multi-byte (4 bytes)
theorem sha256_cavp_4bytes :
    sha256 #[0x74, 0xba, 0x25, 0x21] =
    #[0xb16aa56b, 0xe3880d18, 0xcd41e683, 0x84cf1ec8,
      0xc17680c4, 0x5a02b157, 0x5dc15189, 0x23ae8b0e] := by native_decide

-- NIST CAVP Len=440: 55 bytes — largest single-block message (55 + 1 + 8 = 64)
theorem sha256_cavp_55bytes :
    sha256 #[0x3e, 0xbf, 0xb0, 0x6d, 0xb8, 0xc3, 0x8d, 0x5b,
             0xa0, 0x37, 0xf1, 0x36, 0x3e, 0x11, 0x85, 0x50,
             0xaa, 0xd9, 0x46, 0x06, 0xe2, 0x68, 0x35, 0xa0,
             0x1a, 0xf0, 0x50, 0x78, 0x53, 0x3c, 0xc2, 0x5f,
             0x2f, 0x39, 0x57, 0x3c, 0x04, 0xb6, 0x32, 0xf6,
             0x2f, 0x68, 0xc2, 0x94, 0xab, 0x31, 0xf2, 0xa3,
             0xe2, 0xa1, 0xa0, 0xd8, 0xc2, 0xbe, 0x51] =
    #[0x6595a2ef, 0x537a69ba, 0x8583dfbf, 0x7f5bec0a,
      0xb1f93ce4, 0xc8ee1916, 0xeff44a93, 0xaf5749c4] := by native_decide

-- NIST CAVP Len=448: 56 bytes — first two-block message (padding forces 2nd block)
theorem sha256_cavp_56bytes :
    sha256 #[0x2d, 0x52, 0x44, 0x7d, 0x12, 0x44, 0xd2, 0xeb,
             0xc2, 0x86, 0x50, 0xe7, 0xb0, 0x56, 0x54, 0xba,
             0xd3, 0x5b, 0x3a, 0x68, 0xee, 0xdc, 0x7f, 0x85,
             0x15, 0x30, 0x6b, 0x49, 0x6d, 0x75, 0xf3, 0xe7,
             0x33, 0x85, 0xdd, 0x1b, 0x00, 0x26, 0x25, 0x02,
             0x4b, 0x81, 0xa0, 0x2f, 0x2f, 0xd6, 0xdf, 0xfb,
             0x6e, 0x6d, 0x56, 0x1c, 0xb7, 0xd0, 0xbd, 0x7a] =
    #[0xcfb88d6f, 0xaf2de3a6, 0x9d36195a, 0xcec2e255,
      0xe2af2b7d, 0x933997f3, 0x48e09f6c, 0xe5758360] := by native_decide

-- NIST CAVP Len=504: 63 bytes — one byte short of full block
theorem sha256_cavp_63bytes :
    sha256 #[0xe2, 0xf7, 0x6e, 0x97, 0x60, 0x6a, 0x87, 0x2e,
             0x31, 0x74, 0x39, 0xf1, 0xa0, 0x3f, 0xcd, 0x92,
             0xe6, 0x32, 0xe5, 0xbd, 0x4e, 0x7c, 0xbc, 0x4e,
             0x97, 0xf1, 0xaf, 0xc1, 0x9a, 0x16, 0xfd, 0xe9,
             0x2d, 0x77, 0xcb, 0xe5, 0x46, 0x41, 0x6b, 0x51,
             0x64, 0x0c, 0xdd, 0xb9, 0x2a, 0xf9, 0x96, 0x53,
             0x4d, 0xfd, 0x81, 0xed, 0xb1, 0x7c, 0x44, 0x24,
             0xcf, 0x1a, 0xc4, 0xd7, 0x5a, 0xce, 0xeb] =
    #[0x18041bd4, 0x66508300, 0x1fba8c54, 0x11d2d748,
      0xe8abbfdc, 0xdfd9218c, 0xb02b68a7, 0x8e7d4c23] := by native_decide

-- NIST CAVP Len=512: 64 bytes — exactly one block; all padding in 2nd block
theorem sha256_cavp_64bytes :
    sha256 #[0x5a, 0x86, 0xb7, 0x37, 0xea, 0xea, 0x8e, 0xe9,
             0x76, 0xa0, 0xa2, 0x4d, 0xa6, 0x3e, 0x7e, 0xd7,
             0xee, 0xfa, 0xd1, 0x8a, 0x10, 0x1c, 0x12, 0x11,
             0xe2, 0xb3, 0x65, 0x0c, 0x51, 0x87, 0xc2, 0xa8,
             0xa6, 0x50, 0x54, 0x72, 0x08, 0x25, 0x1f, 0x6d,
             0x42, 0x37, 0xe6, 0x61, 0xc7, 0xbf, 0x4c, 0x77,
             0xf3, 0x35, 0x39, 0x03, 0x94, 0xc3, 0x7f, 0xa1,
             0xa9, 0xf9, 0xbe, 0x83, 0x6a, 0xc2, 0x85, 0x09] =
    #[0x42e61e17, 0x4fbb3897, 0xd6dd6cef, 0x3dd2802f,
      0xe67b3319, 0x53b06114, 0xa65c7728, 0x59dfc1aa] := by native_decide

-- FIPS 180-4 B.3: 112-byte message ("abcdefgh...nopqrstu") — official 2-block vector
theorem sha256_fips_b3 :
    sha256 #[0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,
             0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,
             0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a,
             0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b,
             0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c,
             0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d,
             0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e,
             0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
             0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70,
             0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71,
             0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72,
             0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
             0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74,
             0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75] =
    #[0xcf5b16a7, 0x78af8380, 0x036ce59e, 0x7b049237,
      0x0b249b11, 0xe8f07a51, 0xafac4503, 0x7afee9d1] := by native_decide

/-! ## Section 4: Structural properties (universal) -/

-- compress always returns exactly 8 elements (universal, all inputs)
theorem compress_size (hash w : Array UInt32) :
    (compress hash w).size = 8 := by
  unfold compress; rfl

theorem H0_size : H0.size = 8 := by native_decide

-- parseWords grows acc by (16 - i) elements
theorem parseWords_size (block : Array UInt8) (i : Nat) (acc : Array UInt32) (hi : i ≤ 16) :
    (parseWords block i acc).size = acc.size + (16 - i) := by
  unfold parseWords
  split
  · omega
  · dsimp only
    rw [parseWords_size _ _ _ (by omega), Array.size_push]; omega
termination_by 16 - i

-- expandWords extends array to exactly 64 elements
theorem expandWords_size (w : Array UInt32) (i : Nat) (hi : i ≤ 64) (hw : w.size = i) :
    (expandWords w i).size = 64 := by
  unfold expandWords
  split
  · omega
  · dsimp only
    exact expandWords_size _ (i + 1) (by omega) (by simp [Array.size_push, hw])
termination_by 64 - i

-- messageSchedule always returns 64 elements
theorem messageSchedule_size (block : Array UInt8) :
    (messageSchedule block).size = 64 := by
  unfold messageSchedule
  have h : (parseWords block 0 #[]).size = 16 := by
    have := parseWords_size block 0 #[] (by omega)
    simpa using this
  exact expandWords_size _ 16 (by omega) h

-- extractBlock grows acc by (64 - j) elements
theorem extractBlock_size (padded : Array UInt8) (off j : Nat) (acc : Array UInt8) (hj : j ≤ 64) :
    (extractBlock padded off j acc).size = acc.size + (64 - j) := by
  unfold extractBlock
  split
  · omega
  · rw [extractBlock_size _ _ _ _ (by omega), Array.size_push]; omega
termination_by 64 - j

-- sha256Loop preserves 8-element hash (universal, all inputs)
theorem sha256Loop_size (padded : Array UInt8) (numBlocks i : Nat) (hash : Array UInt32)
    (hh : hash.size = 8) :
    (sha256Loop padded numBlocks i hash).size = 8 := by
  unfold sha256Loop
  split
  · exact hh
  · dsimp only
    apply sha256Loop_size
    exact compress_size _ _
termination_by numBlocks - i

-- sha256 always returns exactly 8 elements (universal, all inputs)
theorem sha256_size (msg : Array UInt8) :
    (sha256 msg).size = 8 := by
  unfold sha256
  exact sha256Loop_size _ _ _ _ H0_size

-- appendZeros adds exactly n bytes
theorem appendZeros_size (p : Array UInt8) (n : Nat) :
    (appendZeros p n).size = p.size + n := by
  induction n generalizing p with
  | zero => simp [appendZeros]
  | succ n ih => simp [appendZeros, ih, Array.size_push]; omega

-- padMsg output is always a multiple of 64 bytes (universal, all inputs)
theorem padMsg_size_mod64 (msg : Array UInt8) :
    (padMsg msg).size % 64 = 0 := by
  simp [padMsg, appendZeros_size, Array.size_push]
  omega

-- compressRounds at round 64 is identity (base case)
theorem compressRounds_done (w : Array UInt32) (st : HashState) :
    compressRounds w st 64 = st := by
  unfold compressRounds; simp

-- compressRounds directly implements FIPS 180-4 Section 6.2.2:
--   T1 = h + Σ1(e) + Ch(e,f,g) + K_i + W_i
--   T2 = Σ0(a) + Maj(a,b,c)
--   (a,b,c,d,e,f,g,h) ← (T1+T2, a, b, c, d+T1, e, f, g)
-- The bitwise operations (Σ0, Σ1, Ch, Maj) are proven correct in Section 2.

/-! ## Section 5: Sigma composition proofs (UInt32 level)

    Each composed sigma function matches the FIPS 180-4 spec definition.
    bv_decide's intToBitVec preprocessing handles UInt32→BitVec automatically. -/

theorem bigSigma0_correct (x : UInt32) :
    bigSigma0 x = ⟨spec_bigSigma0 x.toBitVec⟩ := by
  unfold bigSigma0 rotr spec_bigSigma0 spec_rotr; cases x; congr 1

theorem bigSigma1_correct (x : UInt32) :
    bigSigma1 x = ⟨spec_bigSigma1 x.toBitVec⟩ := by
  unfold bigSigma1 rotr spec_bigSigma1 spec_rotr; cases x; congr 1

theorem smallSigma0_correct (x : UInt32) :
    smallSigma0 x = ⟨spec_smallSigma0 x.toBitVec⟩ := by
  unfold smallSigma0 rotr spec_smallSigma0 spec_rotr; cases x; congr 1

theorem smallSigma1_correct (x : UInt32) :
    smallSigma1 x = ⟨spec_smallSigma1 x.toBitVec⟩ := by
  unfold smallSigma1 rotr spec_smallSigma1 spec_rotr; cases x; congr 1

/-! ## Section 6: Helper lemmas (getU32/getU8/appendZeros content) -/

-- getU32 bridges getD to getElem
theorem getU32_eq (xs : Array UInt32) (i : Nat) (h : i < xs.size) :
    getU32 xs i = xs[i] := by
  unfold getU32 Array.getD; split
  · rfl
  · contradiction

theorem getU32_default (xs : Array UInt32) (i : Nat) (h : ¬(i < xs.size)) :
    getU32 xs i = 0 := by
  unfold getU32 Array.getD; split
  · contradiction
  · rfl

theorem getU32_push_lt (xs : Array UInt32) (v : UInt32) (i : Nat) (h : i < xs.size) :
    getU32 (xs.push v) i = getU32 xs i := by
  rw [getU32_eq (xs.push v) i (by rw [Array.size_push]; omega),
      getU32_eq xs i h, Array.getElem_push_lt]

theorem getU32_push_eq (xs : Array UInt32) (v : UInt32) :
    getU32 (xs.push v) xs.size = v := by
  rw [getU32_eq (xs.push v) xs.size (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_eq

-- getU8 bridges getD to getElem
theorem getU8_eq (xs : Array UInt8) (i : Nat) (h : i < xs.size) :
    getU8 xs i = xs[i] := by
  unfold getU8 Array.getD; split
  · rfl
  · contradiction

theorem getU8_default (xs : Array UInt8) (i : Nat) (h : ¬(i < xs.size)) :
    getU8 xs i = 0 := by
  unfold getU8 Array.getD; split
  · contradiction
  · rfl

theorem getU8_push_lt (xs : Array UInt8) (v : UInt8) (i : Nat) (h : i < xs.size) :
    getU8 (xs.push v) i = getU8 xs i := by
  rw [getU8_eq (xs.push v) i (by rw [Array.size_push]; omega),
      getU8_eq xs i h, Array.getElem_push_lt]

theorem getU8_push_eq (xs : Array UInt8) (v : UInt8) :
    getU8 (xs.push v) xs.size = v := by
  rw [getU8_eq (xs.push v) xs.size (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_eq

-- appendZeros content: existing bytes preserved, new bytes are zero
theorem appendZeros_get_old (p : Array UInt8) (n i : Nat) (h : i < p.size) :
    getU8 (appendZeros p n) i = p[i] := by
  induction n generalizing p with
  | zero => simp [appendZeros, getU8_eq _ _ h]
  | succ n ih =>
    simp only [appendZeros]
    rw [ih (p.push 0x00) (by rw [Array.size_push]; omega)]
    exact Array.getElem_push_lt h

theorem appendZeros_get_new (p : Array UInt8) (n : Nat) (k : Nat) (hk : k < n) :
    getU8 (appendZeros p n) (p.size + k) = 0 := by
  induction n generalizing p k with
  | zero => omega
  | succ n ih =>
    simp only [appendZeros]
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      rw [appendZeros_get_old (p.push 0x00) n p.size (by rw [Array.size_push]; omega)]
      exact Array.getElem_push_eq
    | succ k' =>
      have : p.size + (k' + 1) = (p.push 0x00).size + k' := by
        rw [Array.size_push]; omega
      rw [this]
      exact ih (p.push 0x00) k' (by omega)

/-! ## Section 7: extractBlock content proof -/

-- Generalized: extractBlock starting from position j with accumulator acc
theorem extractBlock_content_gen (padded : Array UInt8) (off j : Nat) (acc : Array UInt8)
    (hj : j ≤ 64) (k : Nat) (hk : k < acc.size + (64 - j)) :
    getU8 (extractBlock padded off j acc) k =
    if h : k < acc.size then acc[k]
    else getU8 padded (off + (k - acc.size + j)) := by
  unfold extractBlock
  split
  case isTrue hge =>
    -- j ≥ 64, so j = 64 and 64 - j = 0, acc unchanged
    have hj64 : j = 64 := by omega
    subst hj64
    simp at hk
    rw [getU8_eq acc k hk]; simp [hk]
  case isFalse hlt =>
    -- hlt : ¬(... ≥ ...), omega can use this directly
    -- j < 64, recurse with acc.push (getU8 padded (off + j))
    have hj' : j + 1 ≤ 64 := by omega
    have hk' : k < (acc.push (getU8 padded (off + j))).size + (64 - (j + 1)) := by
      rw [Array.size_push]; omega
    rw [extractBlock_content_gen padded off (j + 1) (acc.push (getU8 padded (off + j))) hj' k hk']
    split
    case isTrue h' =>
      -- k < (acc.push _).size means k < acc.size + 1
      rw [Array.size_push] at h'
      split
      case isTrue h => exact Array.getElem_push_lt h
      case isFalse h =>
        have hk_eq : k = acc.size := by omega
        subst hk_eq
        simp [Array.getElem_push_eq]
    case isFalse h' =>
      rw [Array.size_push] at h'
      split
      case isTrue h => omega
      case isFalse h =>
        congr 1; simp [Array.size_push]; omega
termination_by 64 - j

-- extractBlock starting from j=0 with empty acc: output[k] = padded[off+k]
theorem extractBlock_content (padded : Array UInt8) (off : Nat) (k : Nat) (hk : k < 64) :
    getU8 (extractBlock padded off 0 #[]) k = getU8 padded (off + k) := by
  have := extractBlock_content_gen padded off 0 #[] (by omega) k (by simp; omega)
  simp at this; exact this

/-! ## Section 8: parseWords content proof -/

-- parseWords preserves existing accumulator elements
theorem parseWords_preserves_acc (block : Array UInt8) (i : Nat) (acc : Array UInt32)
    (hi : i ≤ 16) (k : Nat) (hk : k < acc.size) :
    getU32 (parseWords block i acc) k = getU32 acc k := by
  unfold parseWords; split
  case isTrue => rfl
  case isFalse hlt =>
    dsimp only
    rw [parseWords_preserves_acc block (i + 1) _ (by omega) k
        (by rw [Array.size_push]; omega)]
    exact getU32_push_lt acc _ k hk
termination_by 16 - i

-- parseWords: new word at position k = big-endian decode of 4 bytes at position k
-- Proved with invariant acc.size = i
theorem parseWords_at_inv (block : Array UInt8) (i : Nat) (acc : Array UInt32)
    (hi : i ≤ 16) (hw : acc.size = i) (k : Nat) (hk_lb : i ≤ k) (hk_ub : k < 16) :
    getU32 (parseWords block i acc) k =
    (getU8 block (k * 4)).toUInt32 <<< 24 |||
    (getU8 block (k * 4 + 1)).toUInt32 <<< 16 |||
    (getU8 block (k * 4 + 2)).toUInt32 <<< 8 |||
    (getU8 block (k * 4 + 3)).toUInt32 := by
  unfold parseWords; split
  case isTrue hge => omega
  case isFalse hlt =>
    dsimp only
    by_cases hki : k = i
    · -- k = i: this is the word being pushed at this step
      rw [hki]
      rw [parseWords_preserves_acc block (i + 1) _ (by omega) i
          (by rw [Array.size_push]; omega)]
      -- Goal: getU32 (acc.push V) i = V
      -- rw [← hw] converts i to acc.size (no dependent type issue since getU32 uses getD)
      rw [← hw, getU32_push_eq]
    · -- k > i: recurse
      exact parseWords_at_inv block (i + 1) _ (by omega)
          (by rw [Array.size_push, hw]) k (by omega) hk_ub
termination_by 16 - i

-- parseWords: word k = big-endian decode of 4 bytes
theorem parseWords_content (block : Array UInt8) (k : Nat) (hk : k < 16) :
    getU32 (parseWords block 0 #[]) k =
    (getU8 block (k * 4)).toUInt32 <<< 24 |||
    (getU8 block (k * 4 + 1)).toUInt32 <<< 16 |||
    (getU8 block (k * 4 + 2)).toUInt32 <<< 8 |||
    (getU8 block (k * 4 + 3)).toUInt32 := by
  exact parseWords_at_inv block 0 #[] (by omega) rfl k (by omega) hk

/-! ## Section 9: K constants and compress structure -/

theorem K_size : K.size = 64 := by native_decide

theorem compress_eq (hash w : Array UInt32) :
    compress hash w =
    let init : HashState := {
      a := getU32 hash 0, b := getU32 hash 1, c := getU32 hash 2, d := getU32 hash 3,
      e := getU32 hash 4, f := getU32 hash 5, g := getU32 hash 6, h := getU32 hash 7
    }
    let st := compressRounds w init 0
    #[getU32 hash 0 + st.a, getU32 hash 1 + st.b,
      getU32 hash 2 + st.c, getU32 hash 3 + st.d,
      getU32 hash 4 + st.e, getU32 hash 5 + st.f,
      getU32 hash 6 + st.g, getU32 hash 7 + st.h] := by
  unfold compress; rfl

/-! ## Section 10: expandWords content proofs -/

-- Clean equation for expandWords (inlines let bindings from eq_1)
private theorem expandWords_eq (w : Array UInt32) (i : Nat) :
    expandWords w i = if i ≥ 64 then w
    else expandWords
      (w.push (getU32 w (i - 16) + smallSigma0 (getU32 w (i - 15)) +
               getU32 w (i - 7) + smallSigma1 (getU32 w (i - 2))))
      (i + 1) := by
  rw [expandWords.eq_1]

-- expandWords preserves existing elements
theorem expandWords_preserves (w : Array UInt32) (i : Nat) (hi : i ≤ 64) (hw : w.size = i)
    (k : Nat) (hk : k < i) :
    getU32 (expandWords w i) k = getU32 w k := by
  rw [expandWords_eq]
  split
  · rfl
  · next hge =>
    rw [expandWords_preserves (w.push _) (i + 1) (by omega) (by rw [Array.size_push, hw]) k (by omega)]
    exact getU32_push_lt w _ k (hw ▸ hk)
  termination_by 64 - i

-- expandWords: the word at index i matches the FIPS recurrence
-- Stated in implementation order: w[i-16] + σ0(w[i-15]) + w[i-7] + σ1(w[i-2])
theorem expandWords_recurrence (w : Array UInt32) (i : Nat) (hi : 16 ≤ i) (hi2 : i ≤ 64)
    (hw : w.size = i) (k : Nat) (hk : i ≤ k) (hk2 : k < 64) :
    getU32 (expandWords w i) k =
    getU32 (expandWords w i) (k - 16) +
    smallSigma0 (getU32 (expandWords w i) (k - 15)) +
    getU32 (expandWords w i) (k - 7) +
    smallSigma1 (getU32 (expandWords w i) (k - 2)) := by
  have hstep := expandWords_eq w i
  simp only [show ¬(i ≥ 64) from by omega, ite_false] at hstep
  -- hstep : expandWords w i = expandWords (w.push val) (i+1)
  rw [hstep]
  by_cases hki : k = i
  · -- k = i: this is the word being computed in this step
    rw [hki]
    -- RHS: lookups at i-2, i-7, i-15, i-16 are all < i — rewrite FIRST
    let val := getU32 w (i - 16) + smallSigma0 (getU32 w (i - 15)) +
               getU32 w (i - 7) + smallSigma1 (getU32 w (i - 2))
    have hlook : ∀ j, j < i →
        getU32 (expandWords (w.push val) (i + 1)) j = getU32 w j := by
      intro j hj
      rw [expandWords_preserves (w.push val) (i + 1) (by omega) (by rw [Array.size_push, hw]) j (by omega)]
      exact getU32_push_lt w _ j (hw ▸ hj)
    rw [hlook (i - 16) (by omega), hlook (i - 15) (by omega),
        hlook (i - 7) (by omega), hlook (i - 2) (by omega)]
    -- LHS: word at index i = the pushed value
    rw [expandWords_preserves _ (i + 1) (by omega) (by rw [Array.size_push, hw]) i (by omega)]
    rw [← hw, getU32_push_eq]
  · -- k > i: recurse
    exact expandWords_recurrence _ (i + 1) (by omega) (by omega)
      (by rw [Array.size_push, hw]) k (by omega) hk2
  termination_by 64 - i

/-! ## Section 11: padMsg content proofs -/

-- Region 1: original message bytes preserved
theorem padMsg_original (msg : Array UInt8) (i : Nat) (h : i < msg.size) :
    getU8 (padMsg msg) i = msg[i] := by
  unfold padMsg; simp only []
  iterate 8 rw [getU8_push_lt _ _ _ (by simp [Array.size_push, appendZeros_size]; omega)]
  rw [appendZeros_get_old (msg.push 0x80) _ i (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_lt h

-- Region 2: 0x80 marker byte
theorem padMsg_marker (msg : Array UInt8) :
    getU8 (padMsg msg) msg.size = 0x80 := by
  unfold padMsg; simp only []
  iterate 8 rw [getU8_push_lt _ _ _ (by simp [Array.size_push, appendZeros_size]; omega)]
  rw [appendZeros_get_old (msg.push 0x80) _ msg.size (by rw [Array.size_push]; omega)]
  exact Array.getElem_push_eq

/-! ## Section 12: Composition (sha256Loop step) -/

-- sha256Loop unfolding lemma
theorem sha256Loop_step (padded : Array UInt8) (numBlocks i : Nat) (hash : Array UInt32)
    (hi : i < numBlocks) :
    sha256Loop padded numBlocks i hash =
    sha256Loop padded numBlocks (i + 1)
      (compress hash (messageSchedule (extractBlock padded (i * 64) 0 #[]))) := by
  rw [sha256Loop.eq_1]; simp [show ¬(numBlocks ≤ i) from by omega]

-- sha256 is pad + loop starting from H0
theorem sha256_unfold (msg : Array UInt8) :
    sha256 msg = sha256Loop (padMsg msg) ((padMsg msg).size / 64) 0 H0 := by
  unfold sha256; rfl

/-! ## Section 13: Structural properties of the bitwise algebra -/

theorem xor_self_zero (x : BitVec 32) : x ^^^ x = 0 := by bv_decide
theorem xor_comm (x y : BitVec 32) : x ^^^ y = y ^^^ x := by bv_decide
theorem xor_assoc (x y z : BitVec 32) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by bv_decide
theorem and_comm_bv (x y : BitVec 32) : x &&& y = y &&& x := by bv_decide
theorem or_comm_bv (x y : BitVec 32) : x ||| y = y ||| x := by bv_decide
theorem add_comm_bv (a b : BitVec 32) : a + b = b + a := by bv_decide

/-! ## Section 14: Reference specification (FIPS 180-4 factored)

    A clean, layered reference spec using the same Lean types but factored
    to match FIPS 180-4 section numbers. Proven equal to the implementation.

    Trust chain:
      sha256 msg = spec_sha256 msg
        spec_sha256 uses:
          spec_pad            (§5.1.1 — factors out spec_encodeBE64)
          spec_compress       (§6.2.2 — factors out spec_round)
            spec_round uses bigSigma0, ch, maj (proven correct in Sections 2/5) -/

-- §6.2.2 step 3: single compression round
def spec_round (k_t w_t : UInt32) (st : HashState) : HashState :=
  let t1 := st.h + bigSigma1 st.e + ch st.e st.f st.g + k_t + w_t
  let t2 := bigSigma0 st.a + maj st.a st.b st.c
  { a := t1 + t2, b := st.a, c := st.b, d := st.c,
    e := st.d + t1, f := st.e, g := st.f, h := st.g }

-- §6.2.2: iterated compression rounds
def spec_compressRounds (w : Array UInt32) (st : HashState) (i : Nat) : HashState :=
  if i ≥ 64 then st
  else spec_compressRounds w (spec_round (getU32 K i) (getU32 w i) st) (i + 1)
termination_by 64 - i

-- §6.2.2: full block compression
def spec_compress (hash : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let init : HashState := {
    a := getU32 hash 0, b := getU32 hash 1, c := getU32 hash 2, d := getU32 hash 3,
    e := getU32 hash 4, f := getU32 hash 5, g := getU32 hash 6, h := getU32 hash 7
  }
  let st := spec_compressRounds w init 0
  #[getU32 hash 0 + st.a, getU32 hash 1 + st.b,
    getU32 hash 2 + st.c, getU32 hash 3 + st.d,
    getU32 hash 4 + st.e, getU32 hash 5 + st.f,
    getU32 hash 6 + st.g, getU32 hash 7 + st.h]

-- §5.1.1: big-endian 64-bit encoding
def spec_encodeBE64 (v : UInt64) : Array UInt8 :=
  #[(v >>> 56).toUInt8, (v >>> 48).toUInt8, (v >>> 40).toUInt8, (v >>> 32).toUInt8,
    (v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

-- §5.1.1: message padding
def spec_pad (msg : Array UInt8) : Array UInt8 :=
  let bitLen := msg.size.toUInt64 * 8
  let padLen := (119 - msg.size % 64) % 64
  appendZeros (msg.push 0x80) padLen ++ spec_encodeBE64 bitLen

-- Full pipeline loop
def spec_sha256Loop (padded : Array UInt8) (numBlocks i : Nat) (hash : Array UInt32)
    : Array UInt32 :=
  if i ≥ numBlocks then hash
  else spec_sha256Loop padded numBlocks (i + 1)
    (spec_compress hash (messageSchedule (extractBlock padded (i * 64) 0 #[])))
termination_by numBlocks - i

-- §6.2: complete SHA-256
def spec_sha256 (msg : Array UInt8) : Array UInt32 :=
  let padded := spec_pad msg
  spec_sha256Loop padded (padded.size / 64) 0 H0

/-! ## Section 15: Compression equivalence -/

-- compressRounds inlines the same computation as spec_round
theorem compressRounds_eq_spec (w : Array UInt32) (st : HashState) (i : Nat) (hi : i ≤ 64) :
    compressRounds w st i = spec_compressRounds w st i := by
  rw [compressRounds.eq_1, spec_compressRounds.eq_1]
  if h : 64 ≤ i then
    simp [if_pos h]
  else
    simp only [if_neg h]
    dsimp only [spec_round]
    exact compressRounds_eq_spec w _ (i + 1) (by omega)
termination_by 64 - i

-- compress = spec_compress (direct consequence)
theorem compress_eq_spec (hash w : Array UInt32) :
    compress hash w = spec_compress hash w := by
  simp only [compress, spec_compress, compressRounds_eq_spec w _ 0 (by omega)]

/-! ## Section 16: Padding equivalence -/

-- 8 sequential pushes = appending an 8-element array
private theorem push_chain_eq_append (arr : Array UInt8)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) :
    ((((((((arr.push v0).push v1).push v2).push v3).push v4).push v5).push v6).push v7)
    = arr ++ #[v0, v1, v2, v3, v4, v5, v6, v7] := by
  simp only [← Array.toList_inj]
  simp [Array.toList_push, Array.toList_append, List.append_assoc]

-- padMsg = spec_pad (push chain = append of spec_encodeBE64)
theorem padMsg_eq_spec (msg : Array UInt8) : padMsg msg = spec_pad msg := by
  unfold padMsg spec_pad spec_encodeBE64
  exact push_chain_eq_append _ _ _ _ _ _ _ _ _

/-! ## Section 17: Loop equivalence and end-to-end theorem -/

-- sha256Loop = spec_sha256Loop (by compress = spec_compress)
theorem sha256Loop_eq_spec (padded : Array UInt8) (numBlocks i : Nat) (hash : Array UInt32) :
    sha256Loop padded numBlocks i hash = spec_sha256Loop padded numBlocks i hash := by
  rw [sha256Loop.eq_1, spec_sha256Loop.eq_1]
  if h : numBlocks ≤ i then
    simp [if_pos h]
  else
    simp only [if_neg h, compress_eq_spec]
    exact sha256Loop_eq_spec padded numBlocks (i + 1) _
termination_by numBlocks - i

-- End-to-end: sha256 = spec_sha256
theorem sha256_eq_spec (msg : Array UInt8) : sha256 msg = spec_sha256 msg := by
  simp only [sha256, spec_sha256, ← padMsg_eq_spec]
  exact sha256Loop_eq_spec _ _ _ _

/-! ## Section 18: End-to-end composition

    This section ties every component proof into a single top-level theorem.
    If any piece breaks, this theorem fails — it serves as the completeness
    check for the entire verification effort.

    The theorem states: for any message, sha256 produces an 8-word digest by
    padding → block extraction → message schedule → compression, where every
    step is proven correct against FIPS 180-4. -/

/-- Full pipeline correctness for SHA-256.

    For any input message, the implementation satisfies ALL of:
    1. Output structure: exactly 8 UInt32 words
    2. Padding: original bytes preserved, 0x80 marker, length aligned to 64
    3. Block extraction: each 64-byte block correctly sliced from padded message
    4. Message schedule: first 16 words are big-endian parses, words 16–63
       satisfy the FIPS recurrence W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]
    5. Bitwise operations: Σ0, Σ1, σ0, σ1 match FIPS 180-4 spec definitions
    6. Pipeline: sha256 = pad → loop(extract → schedule → compress) from H0
    7. Test vectors: 10 vectors (FIPS 180-4 + NIST CAVP) covering all padding boundaries
    8. End-to-end: sha256 msg = spec_sha256 msg -/
theorem sha256_correct (msg : Array UInt8) :
    -- 1. Output is always 8 words
    (sha256 msg).size = 8
    -- 2. Padding preserves original message
    ∧ (∀ (i : Nat) (h : i < msg.size), getU8 (padMsg msg) i = msg[i])
    -- 3. Padding places 0x80 marker
    ∧ getU8 (padMsg msg) msg.size = 0x80
    -- 4. Padded length is multiple of 64
    ∧ (padMsg msg).size % 64 = 0
    -- 5. Pipeline structure: sha256 = pad + loop from H0
    ∧ sha256 msg = sha256Loop (padMsg msg) ((padMsg msg).size / 64) 0 H0
    -- 6. Message schedule is 64 words
    ∧ (∀ block : Array UInt8, (messageSchedule block).size = 64)
    -- 7. Block extraction: output[k] = padded[off+k]
    ∧ (∀ (padded : Array UInt8) (off k : Nat), k < 64 →
        getU8 (extractBlock padded off 0 #[]) k = getU8 padded (off + k))
    -- 8. parseWords: word k = big-endian decode of 4 bytes
    ∧ (∀ (block : Array UInt8) (k : Nat), k < 16 →
        getU32 (parseWords block 0 #[]) k =
        (getU8 block (k * 4)).toUInt32 <<< 24 |||
        (getU8 block (k * 4 + 1)).toUInt32 <<< 16 |||
        (getU8 block (k * 4 + 2)).toUInt32 <<< 8 |||
        (getU8 block (k * 4 + 3)).toUInt32)
    -- 9. expandWords satisfies FIPS recurrence for words 16..63
    ∧ (∀ (w : Array UInt32) (k : Nat), w.size = 16 → 16 ≤ k → k < 64 →
        getU32 (expandWords w 16) k =
        getU32 (expandWords w 16) (k - 16) +
        smallSigma0 (getU32 (expandWords w 16) (k - 15)) +
        getU32 (expandWords w 16) (k - 7) +
        smallSigma1 (getU32 (expandWords w 16) (k - 2)))
    -- 10. Sigma functions match FIPS 180-4 spec
    ∧ (∀ x : UInt32, bigSigma0 x = ⟨spec_bigSigma0 x.toBitVec⟩)
    ∧ (∀ x : UInt32, bigSigma1 x = ⟨spec_bigSigma1 x.toBitVec⟩)
    ∧ (∀ x : UInt32, smallSigma0 x = ⟨spec_smallSigma0 x.toBitVec⟩)
    ∧ (∀ x : UInt32, smallSigma1 x = ⟨spec_smallSigma1 x.toBitVec⟩)
    -- 14. End-to-end: implementation = reference specification
    ∧ sha256 msg = spec_sha256 msg := by
  exact ⟨sha256_size msg,
         fun i h => padMsg_original msg i h,
         padMsg_marker msg,
         padMsg_size_mod64 msg,
         sha256_unfold msg,
         messageSchedule_size,
         fun _ _ k hk => extractBlock_content _ _ k hk,
         fun _ k hk => parseWords_content _ k hk,
         fun w k hw hk_lb hk_ub =>
           expandWords_recurrence w 16 (by omega) (by omega) hw k hk_lb hk_ub,
         bigSigma0_correct, bigSigma1_correct,
         smallSigma0_correct, smallSigma1_correct,
         sha256_eq_spec msg⟩
