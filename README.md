# lean4-baremetal

Run Lean 4 programs directly on bare-metal hardware with no operating system.

Lean 4 compiles to C, but its runtime depends on libc, GMP, pthreads, libuv, and C++ exceptions. This project provides a **freestanding replacement runtime** (~1000 lines of C) that removes all those dependencies, enabling Lean programs to run on raw hardware.

## Quick start

```bash
nix develop                     # enter dev environment
make nix-run                    # hello world on bare-metal RISC-V
make EXAMPLE=sha256 nix-run     # formally verified SHA-256 on bare-metal
make nix-test                   # run all tests, check expected output
make nix-verify                 # typecheck formal proofs via lake
```

## What this does

```
examples/sha256.lean            (Lean 4 source + formal proofs)
        │
        ▼  lean -c
   build/sha256.c               (Lean compiler emits C)
        │
        ▼  riscv64-elf-gcc -ffreestanding -nostdlib
   build/kernel.elf             (cross-compiled with freestanding runtime)
        │
        ▼  qemu-system-riscv64 -machine virt -bios none
   ba7816bf8f01cfea...          (SHA-256 of "abc", correct)
```

The SHA-256 implementation is formally verified: `sha256_proof.lean` imports `sha256.lean` and proves bitwise operations match FIPS 180-4 (universal, via `bv_decide`) and test vectors are correct (compile-time, via `native_decide`). If someone changes `sha256.lean` and breaks a proof, `make verify` fails.

## Why this matters

Lean 4 produces machine-checkable proofs about programs. Bare-metal Lean means formally verified code for avionics (DO-178C), medical devices (IEC 62304), automotive (ISO 26262), embedded systems, and RTOS kernels.

## What we replaced

| Dependency | Original | Replacement |
|-----------|----------|-------------|
| libc | glibc/musl | `libc_min.c` — memcpy, memset, strlen, abort |
| Allocator | mimalloc | Slab allocator — 8 size classes, free lists, O(1) alloc/free |
| GMP | libgmp | Panic on overflow (fixed-width integers only) |
| pthreads | libpthread | No-op stubs (single-threaded) |
| C++ runtime | libstdc++ | Rewritten in C, exceptions → panic + halt |
| stdio | printf/fprintf | `uart.c` — NS16550A UART driver |

## Project structure

```
boot.S              RISC-V entry: disable interrupts, zero BSS, set stack, call main
linker.ld           Memory layout at 0x80000000 (QEMU virt)
lean_rt.c/h         Freestanding Lean 4 runtime (slab allocator, refcounting, strings, arrays)
uart.c/h            NS16550A UART driver for QEMU virt
libc_min.c          Minimal libc stubs
main.c              C entry point: init UART, init Lean runtime, call Lean main
lakefile.lean       Lake project (proof file imports implementation)
lean-toolchain      Lean 4.28.0
flake.nix           Nix flake for reproducible dev environment
examples/
  hello.lean        Hello world
  sha256.lean       SHA-256 (FIPS 180-4) — single source of truth
  sha256_proof.lean Formal proofs — imports sha256.lean
```

## Formal verification

`sha256_proof.lean` imports `sha256.lean` via lake. The proofs are about the exact code that runs on bare metal — one source of truth.

What's proven:
- **Bitwise operations** match FIPS 180-4 spec — universal over all 32-bit inputs (`bv_decide`)
- **Test vectors** — SHA-256("abc"), SHA-256(""), and the 56-byte two-block FIPS B.2 vector verified at compile time (`native_decide`)
- **Structural properties (universal)** — `sha256` always returns 8 elements, `messageSchedule` returns 64, `padMsg` output is a multiple of 64 bytes, `compress` preserves array length 8 — all proven for ALL inputs
- **Algebraic properties** — XOR commutativity/associativity, AND/OR commutativity

What's not yet proven:
- Full functional correctness for all inputs (requires complete FIPS 180-4 reference spec — comparable in scope to HACL*/Fiat-Crypto)

## Slab allocator

8 size classes (32, 48, 64, 80, 112, 144, 272, 544 bytes) with per-class free lists. Freed blocks return to their class in O(1). Objects >544B fall back to bump allocation. All in `lean_rt.c`.

## Roadmap

- [x] Hello World — `IO.println` on bare-metal
- [x] SHA-256 — real computation with cycle timing
- [x] Formal verification — proofs import implementation via lake
- [x] Slab allocator — real memory reuse
- [ ] Nat/Int bignum support (port `mpn.cpp` to C)
- [ ] Interrupts and basic hardware interaction
- [ ] Real hardware (SiFive, StarFive)
- [ ] Formally verified device drivers in Lean

## Future work

### Near-term (weeks)

- **Verified state machine on real hardware (SiFive / StarFive RISC-V board)** — Port from QEMU to a $15 board. A Lean-proven-correct protocol parser (e.g. CAN bus message decoder for automotive) running on actual silicon.

- **More crypto primitives** — ChaCha20, HMAC-SHA256, or AES. Same approach: implement in Lean, prove correct, compile to bare-metal. Compares to HACL* (F\*), Fiat-Crypto (Coq), Jasmin — but with Lean's ergonomics.

### Medium-term (months)

- **Bare-metal Lean RTOS microkernel** — Task switching, priority queues, timer interrupts — all in Lean with proofs about scheduling properties (no priority inversion, bounded latency). The seL4 story but in a language that's pleasant to write.

- **Verified sensor fusion / flight controller** — Kalman filter with proven numerical stability bounds, running on bare-metal reading IMU data. Targets DO-178C (avionics).

- **Verified bootloader** — RISC-V bootloader that loads and verifies a signed kernel image. Proof that it never executes unsigned code.

## Target

RISC-V 64-bit on QEMU `virt` machine. Open ISA, excellent QEMU support. All tools provided by `nix develop`.

## Project Ideas

Here are some projects that leverage the "verified + bare metal" combination:

### Verified Bootloader + Secure Boot Chain 🔐
A RISC-V bootloader that loads and verifies kernel images, with proofs that it never executes unsigned code and correctly validates signatures (Ed25519). **Why**: Bootloaders are the root of trust—bugs here compromise everything above.

### Deterministic CAN Bus Protocol Parser 🚗
A verified parser for automotive CAN bus messages running on real hardware (e.g., StarFive VisionFive 2). Prove the parser is total (never crashes), handles framing correctly, and has no integer overflows. **Why**: Automotive ECUs often have parser bugs that cause safety issues.

### Minimal Verified RTOS Microkernel ⏱️
Task scheduler + priority queue with proofs of no priority inversion and bounded latency. The kernel itself is written in Lean and proven correct. **Why**: seL4 proved this is possible in C—Lean could make it more ergonomic.

### Constant-Time Cryptographic Primitives 🔑
ChaCha20, AES-GCM, or HMAC-SHA256 with functional correctness proofs AND constant-time proofs (no timing side channels). **Why**: Traditional C crypto is riddled with timing attacks.

### Sensor Fusion with Numerical Bounds 🛩️
Kalman filter for IMU data on a drone controller. Proofs: numerical stability (no NaN), quaternion normalization stays valid, angle estimates stay bounded. **Why**: Flight controllers need guarantees about numerical behavior.

### Memory-Safe DMA Driver 🚀
Direct Memory Access driver with proofs that transfers never overlap kernel memory, buffer bounds are respected, and no use-after-free occurs. **Why**: DMA bugs corrupt memory silently and are notoriously hard to debug.

### Verified Space Protocol Parser 🛰️
CCSDS packet parser for spacecraft communication. Prove no packet can cause out-of-bounds access. **Why**: Spacecraft software can't be patched—verification matters.

---

### 🌟 Recommended First Project

**Verified Protocol Parser for a Hardware Bus (I2C/SPI/CAN)**

**Why this first:**
- Fits current constraints (no bignums needed, single-threaded is fine)
- Can run on real $15 hardware (StarFive VisionFive 2)
- Solves a real, common problem (parser bugs are frequent in embedded)
- Clear success criteria: parse correctly + proofs of totality + no overflows
- Good showcase for the "same code for proof and runtime" approach

**Example target**: Parse MPU-6050/9250 IMU data over I2C with proofs that:
1. Parser terminates on any input (totality)
2. No out-of-bounds array access
3. Checksum validation is correct
4. Sensor values are within physically possible ranges
