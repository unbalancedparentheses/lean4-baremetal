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
- **Test vectors** — SHA-256("abc") and SHA-256("") produce correct digests at compile time (`native_decide`)
- **Algebraic properties** — XOR commutativity/associativity, AND/OR commutativity

What's not yet proven:
- Correctness for all inputs (not just test vectors)
- `padMsg` follows FIPS 180-4 padding spec
- Structural properties (e.g. `compress` preserves array length 8)

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
