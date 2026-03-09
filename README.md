# lean4-baremetal

Lean 4 on bare-metal RISC-V. No OS, no libc, no runtime dependencies.

Lean compiles to C, but the standard runtime pulls in glibc, GMP, pthreads, libuv, and C++ exceptions. We wrote a freestanding replacement (~1000 lines of C) so Lean programs can run directly on hardware.

Two verified examples so far:
- **SHA-256** — proven correct end-to-end: `sha256 msg = spec_sha256 msg` for all inputs
- **CAN 2.0 frame parser** — MCP2515 CAN controller buffer parser with CRC-15, proven correct: `parseMcp2515 (encodeMcp2515 f) = f` for well-formed frames

Both are checked by the Lean kernel. The proofs apply to the same code that compiles to C and runs on the machine.

## Try it

```bash
nix develop
make nix-run                    # hello world on bare-metal RISC-V
make EXAMPLE=sha256 nix-run     # SHA-256 on bare-metal
make EXAMPLE=can nix-run        # CAN 2.0 frame parser on bare-metal
make nix-verify                 # typecheck all formal proofs
make nix-test                   # build + run + check output
```

## How it works

```
examples/sha256.lean              Lean source
        |  lean -c
   build/sha256.c                 generated C
        |  riscv64-gcc -ffreestanding -nostdlib
   build/sha256.elf               bare-metal binary
        |  qemu-system-riscv64 -machine virt -bios none
   ba7816bf8f01cfea...            SHA-256("abc"), correct
```

Lean's compiler emits C. We cross-compile that C together with our freestanding runtime for RISC-V. QEMU runs the resulting ELF directly — no BIOS, no bootloader, no OS. The binary starts at `boot.S`, which sets up a stack and jumps to C, which initializes the UART and the Lean runtime, then calls Lean's `main`.

The important part: the proofs in `sha256_proof.lean` and `can_proof.lean` import their respective implementation files via Lake. So the code the Lean kernel checks is the same code that gets compiled to C and runs on the machine. There is one source of truth.

## What we had to replace

Lean's runtime assumes a hosted environment. To run freestanding, we had to replace every external dependency with something that works without an OS.

| Dependency | Standard | Our replacement |
|---|---|---|
| libc | glibc/musl | `libc_min.c` — just memcpy, memset, strlen, abort |
| Allocator | mimalloc | Slab allocator with 8 size classes and per-class free lists |
| GMP | libgmp | Panic on overflow (we only use fixed-width integers) |
| Threads | pthreads | No-op stubs (single-threaded) |
| C++ runtime | libstdc++ | Rewritten in C. Exceptions become panic + halt |
| I/O | stdio | NS16550A UART driver talking directly to hardware registers |

The slab allocator deserves a note. Lean's runtime allocates and frees small objects constantly (closures, thunks, array slices). We use 8 size classes (32 to 544 bytes) with free lists, so alloc and free are O(1). Objects larger than 544 bytes fall back to bump allocation. It's simple but it works — SHA-256 runs to completion with real memory reuse.

## SHA-256 proofs

`sha256_proof.lean` contains about 70 theorems organized in 18 sections. The main result is end-to-end functional correctness:

```lean
theorem sha256_eq_spec (msg : Array UInt8) :
    sha256 msg = spec_sha256 msg
```

This says: for every possible input message, our implementation produces the same output as the reference specification. `spec_sha256` is a clean formalization of FIPS 180-4, factored to match the standard section by section:

- `spec_pad` handles message padding (section 5.1.1), with `spec_encodeBE64` for the 64-bit big-endian length field
- `spec_round` is a single compression round (section 6.2.2 step 3)
- `spec_compressRounds` iterates `spec_round` 64 times
- `spec_compress` wraps the rounds with initialization and finalization
- `spec_sha256Loop` processes each 64-byte block

The proof works bottom-up. First we prove each implementation function equals its spec counterpart (`compressRounds = spec_compressRounds`, `padMsg = spec_pad`, etc.), then compose them into the top-level theorem.

Below that, the bitwise building blocks are also verified:

- Every rotation, Ch, Maj, and sigma function is proven correct for all 2^32 inputs using `bv_decide` (a SAT-based decision procedure for bitvector arithmetic)
- The FIPS 180-4 test vectors — SHA-256 of the empty string, "abc", and the 56-byte two-block message from appendix B — are verified at compile time using `native_decide`

Everything is assembled into a single capstone theorem `sha256_correct` that bundles all the properties together. If any component proof breaks, the whole file fails to typecheck.

## CAN 2.0 frame parser proofs

`can_proof.lean` verifies a parser for the MCP2515 CAN controller's SPI receive buffer format (ISO 11898 / Bosch CAN 2.0). The parser handles both CAN 2.0A (11-bit standard ID) and CAN 2.0B (29-bit extended ID) frames, plus CRC-15/CAN computation.

The proofs cover:

- **Bit extraction correctness** — the shift/mask chains that reconstruct 11-bit and 29-bit IDs from the MCP2515 byte layout are verified with `bv_decide`
- **Structural bounds** — `dlc ≤ 8`, `data.size = 8`, standard ID < 2048, extended ID < 2^29
- **Test vectors** — 8 concrete MCP2515 buffers (min/max standard, min/max extended, RTR, DLC clamping, mixed SIDL bits) verified at compile time with `native_decide`
- **CRC-15 test vectors** — including the canonical check value CRC-15("123456789") = 0x059E
- **Roundtrip** — `parseMcp2515 (encodeMcp2515 f) = f` for well-formed frames
- **Implementation = specification equivalence** — bundled into a capstone theorem

The CAN example exercises different runtime features than SHA-256: custom Lean structures with scalar fields (UInt32, Bool, UInt8), constructor object layout, and string interpolation. This helped uncover and fix a bug in the runtime's scalar field accessors.

### Trust model

This follows the same approach as [HACL\*](https://hacl-star.github.io/) (F\*) and [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) (Coq). What you have to trust: the Lean 4 kernel, the Lean-to-C compiler, GCC's cross-compilation, and our freestanding runtime. What's proven: everything from individual bitwise operations up through the full SHA-256 and CAN parser pipelines, for all inputs.

## Current status

- [x] Lean programs run directly on bare-metal RISC-V in QEMU
- [x] Freestanding runtime replaces libc, allocator, thread, and I/O dependencies
- [x] SHA-256 is proved end-to-end against an independent reference spec
- [x] CAN 2.0 frame parser proved correct (roundtrip, bit extraction, CRC-15)
- [x] `make nix-test` and `make nix-verify` work as the main validation path
- [ ] Real hardware support
- [ ] A broader documented platform surface for reusable bare-metal Lean programs

## Files

```
boot.S                RISC-V entry point (disable interrupts, zero BSS, set stack)
linker.ld             Memory layout at 0x80000000 (QEMU virt machine)
lean_rt.c/h           Freestanding Lean runtime (slab allocator, refcounting, strings, arrays)
uart.c/h              NS16550A UART driver
libc_min.c            Minimal libc stubs
main.c                C entry: init UART, init Lean runtime, call Lean main
lakefile.lean         Lake build config (proof file imports implementation)
flake.nix             Nix flake for reproducible builds
examples/
  hello.lean          Hello world
  sha256.lean         SHA-256 implementation (FIPS 180-4)
  sha256_proof.lean   Formal proofs (~70 theorems, imports sha256.lean)
  can.lean            CAN 2.0 frame parser (MCP2515, CRC-15)
  can_proof.lean      Formal proofs (roundtrip, bit extraction, test vectors)
```

## Target

RISC-V 64-bit on QEMU `virt`. Open ISA, great tooling. Everything you need is provided by `nix develop`.

## Roadmap

This README is the front page. The longer platform plan lives in [ROADMAP.md](/Users/unbalancedparen/projects/lean4-baremetal/ROADMAP.md).
