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
- **Content-level helper correctness** — `parseWords` decodes big-endian words correctly, `extractBlock` returns the requested bytes, `appendZeros` preserves old bytes and adds zeros, `padMsg` preserves the original message and places the `0x80` marker correctly
- **Message schedule recurrence** — `expandWords` preserves the initial 16 words and satisfies the SHA-256 recurrence for words 16..63
- **Composition lemmas** — `compress`, `sha256Loop`, and `sha256` are unfolded into the expected pipeline structure, so the proofs connect to the exact implementation shape
- **Algebraic properties** — XOR commutativity/associativity, AND/OR commutativity

What's not yet proven:
- Full end-to-end functional correctness for all inputs via a single theorem stating `sha256 = FIPS_180_4_spec` on arbitrary messages
- Compression-round correctness against a separately defined full reference state-transition function
- Full padding correctness including the final 64-bit length encoding as a standalone spec theorem

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

The best fits for this repo are small, critical, self-contained components: logic-heavy code where proofs matter, runtime requirements are modest, and the "same Lean code for proof and execution" story is obvious.

### Strong near-term demos

| Project | Why it fits | Example properties to prove |
|---|---|---|
| **Verified bootloader / signed image loader** | Small trusted component at the root of trust; a natural bare-metal target | Never jumps to an unsigned image; header/hash checks are correct; entry point is within bounds |
| **CAN or UART protocol parser** | Parser logic is proof-friendly, easy to demo, and useful on real hardware | Total on all inputs; malformed frames are rejected; no out-of-bounds access; field decoding is correct |
| **Firmware update manifest verifier** | Real embedded use case with clear security value | Version/hash/signature checks are correct; malformed manifests are rejected |
| **Memory-region access checker** | Small policy engine with a clean proof story | Requests outside authorized ranges are always denied; region checks are monotone and non-overlapping |
| **More crypto primitives** | Extends the current SHA-256 work without changing the repo's model | Functional correctness against a spec; output length/invariants; known test vectors |
| **CCSDS or telemetry packet parser** | Good "space/avionics" example without needing a full OS stack | Packet lengths and checksums are validated; no malformed packet causes unsafe reads |

### Longer-term research directions

These are interesting, but they need significantly more runtime, hardware, or proof machinery than the repo has today.

| Project | Why it is harder |
|---|---|
| **RTOS microkernel** | Requires interrupts, scheduling, task switching, and a much more mature runtime/TCB story |
| **DMA-safe driver** | Depends heavily on hardware memory semantics, ownership, cache coherence, and MMIO details |
| **Sensor fusion / flight control** | Pulls the project toward numerical analysis and floating/fixed-point stability proofs |
| **Constant-time crypto proofs** | Strong claim that is hard to justify through Lean-generated C, the C compiler, and real hardware timing |

### Recommended first project

**Verified CAN or UART protocol parser**

This is the cleanest next step after SHA-256:
- Fits current constraints: fixed-width integers, single-threaded runtime, no bignums
- Exercises exactly the kind of logic Lean is good at: decoding, validation, invariants
- Runs on QEMU first and then on inexpensive real hardware
- Shows the value of the project without overreaching on hardware complexity

**Concrete example**: a CAN frame validator / decoder with proofs that:
1. Parsing terminates on every input
2. Invalid DLC, IDs, or payload layouts are rejected
3. No out-of-bounds array access occurs
4. Valid frames decode to the intended typed message

After that, the strongest follow-up is a **verified bootloader / signed image loader**: still small, still self-contained, but with a stronger security story.
