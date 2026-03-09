# lean4-baremetal

Lean 4 on bare-metal RISC-V. No OS, no libc, no runtime dependencies.

Lean compiles to C, but the standard runtime pulls in glibc, GMP, pthreads, libuv, and C++ exceptions. We wrote a freestanding replacement (~3200 lines of C and assembly) so Lean programs can run directly on hardware.

Three verified subsystems so far:
- **SHA-256** — proven correct end-to-end: `sha256 msg = spec_sha256 msg` for all inputs
- **CAN 2.0 frame parser** — MCP2515 buffer parser with verified bit extraction, structural bounds, CRC-15, test vectors, and roundtrip: `parseMcp2515 (encodeMcp2515 f) = f` for well-formed frames
- **Torque-enable gate** — automotive drive-authority gate that processes CAN frames to decide whether an electric motor may produce torque. Formally proven: torque is never granted unless all safety conditions hold, faults latch and persist, and there is no backdoor past the enable request

All three are checked by the Lean kernel — 167 theorems total across four proof files. The proofs apply to the same code that compiles to C and runs on the machine. This is no longer just a crypto demo: it now includes a reusable protocol layer and a real safety-critical authority gate built on top of it.

## Try it

```bash
make run                        # hello world on bare-metal RISC-V
make EXAMPLE=sha256 run         # SHA-256 with benchmarks
make EXAMPLE=can run            # CAN 2.0 frame parser
make EXAMPLE=torque run         # torque-enable gate
make verify                     # typecheck all formal proofs
make test                       # build + run + check all runnable examples and runtime tests
```

Requires [Nix](https://nixos.org/). `make` auto-delegates to Nix builds.

## How it works

```
sha256/sha256.lean                Lean source
        |  lean -c
   build/sha256.c                 generated C
        |  riscv64-gcc -ffreestanding -nostdlib
   build/sha256.elf               bare-metal binary
        |  qemu-system-riscv64 -machine virt -bios none
   ba7816bf8f01cfea...            SHA-256("abc"), correct
```

Lean's compiler emits C. We cross-compile that C together with our freestanding runtime for RISC-V. QEMU runs the resulting ELF directly — no BIOS, no bootloader, no OS. The binary starts at `platform/boot.S`, which sets up a stack and jumps to C `main`, which initializes the runtime and calls Lean's entry point.

The important part: the proofs in `sha256/sha256_proof.lean`, `can/can_proof.lean`, and `torque/torque_proof.lean` import their respective implementation files via Lake. So the code the Lean kernel checks is the same code that gets compiled to C and runs on the machine. There is one source of truth.

## Trust model

This follows the same approach as [HACL\*](https://hacl-star.github.io/) (F\*) and [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) (Coq).

**What you trust:**
- The Lean 4 kernel (proof verification engine)
- `lean -c` (Lean-to-C compiler)
- GCC cross-compilation (`riscv64-unknown-elf-gcc`)
- Our freestanding runtime (`platform/` + `runtime/`)

**What's proven:**
- SHA-256: end-to-end functional correctness (`sha256 msg = spec_sha256 msg` for all inputs)
- CAN 2.0 parser: bit extraction, structural bounds, CRC-15, roundtrip, and parser = reference spec equivalence
- Torque-enable gate: torque implies all safety conditions, fault latching and persistence, no backdoor, frame admissibility filtering

The trusted base is small and explicit. Everything above the runtime boundary is verified by the Lean kernel.

## Verified subsystems

### SHA-256 (72 theorems)

`sha256_proof.lean` — 18 sections. The main result is end-to-end functional correctness:

```lean
theorem sha256_eq_spec (msg : Array UInt8) :
    sha256 msg = spec_sha256 msg
```

For every possible input message, our implementation produces the same output as the reference specification. `spec_sha256` is a clean formalization of FIPS 180-4, factored to match the standard section by section:

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

**Benchmarks:** The SHA-256 example includes cycle-count benchmarks comparing Lean-generated code against a C reference implementation (`runtime/sha256_ref.c`) at three input sizes (3, 64, and 256 bytes), measured via RISC-V `rdcycle`.

### CAN 2.0 frame parser (59 theorems)

`can_proof.lean` verifies a parser for the MCP2515 CAN controller's SPI receive buffer format (ISO 11898 / Bosch CAN 2.0). The parser handles both CAN 2.0A (11-bit standard ID) and CAN 2.0B (29-bit extended ID) frames, plus CRC-15/CAN computation.

The proofs cover:

- **Bit extraction correctness** — the shift/mask chains that reconstruct 11-bit and 29-bit IDs from the MCP2515 byte layout are verified with `bv_decide`
- **Structural bounds** — `dlc ≤ 8`, `data.size = 8`, standard ID < 2048, extended ID < 2^29
- **Test vectors** — 10 concrete MCP2515 buffers (min/max standard, min/max extended, RTR, DLC clamping, mixed SIDL bits, data content, empty buffer) verified at compile time with `native_decide`
- **CRC-15 test vectors** — 5 vectors including the canonical check value CRC-15("123456789") = 0x059E
- **Roundtrip** — `parseMcp2515 (encodeMcp2515 f) = f` for 7 well-formed frame configurations
- **Parser = reference spec** — `parseMcp2515 buf = spec_parseMcp2515 buf`, where the spec uses BitVec field extraction matching MCP2515 datasheet bit positions, connected via bridge lemmas (`std_id_bridge`, `ext_id_bridge`, `dlc_bridge`)

### Torque-enable gate (28 theorems)

`torque_proof.lean` verifies an automotive torque-enable / drive-authority gate. The gate reads a CAN frame with bit-packed safety inputs (brake, gear position, motor temperature, battery status, emergency stop) and a driver enable request, then decides whether an electric motor may produce torque.

The key safety properties, all universally quantified:

- **Torque implies safety** — if torque is granted, every safety input was true and no fault was latched
- **Fault denial** — a faulted system never grants torque, regardless of inputs
- **No backdoor** — torque always requires an explicit enable request from the driver
- **Fault latching** — any safety violation immediately latches a persistent fault
- **Fault persistence** — once latched, a fault survives across CAN cycles until explicitly reset
- **Frame admissibility** — inadmissible frames (wrong CAN ID, extended/RTR frame type, or short DLC) are always denied and leave state unchanged; torque authorization requires an admissible frame

Additional proofs cover bit extraction correctness (each CAN byte bit maps to the right DriveInputs field via `bv_decide`), 7 concrete test vectors via `native_decide`, and output consistency (torque_allowed ↔ drive_enabled, reason `.ok` ↔ torque granted).

The torque gate imports verified CAN parsing (`can_lib`), demonstrating composable verified subsystems.

### Shared proof library

`bitfield.lean` provides 8 reusable UInt8 single-bit isolation lemmas, each proving that shift-mask extraction `(b &&& mask) != 0` equals BitVec bit access `b.toBitVec.getLsbD n` for all UInt8 inputs via `bv_decide`. Used by both CAN and torque proofs.

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

## Project structure

The project is organized by role:

- **`platform/`** — Hardware-specific code that changes per board: boot sequence, linker script, board config, UART driver. To port to new hardware, you replace or add files here. Nothing in `platform/` knows about Lean's object model.

- **`runtime/`** — Lean freestanding runtime that is board-independent: the slab allocator, refcounting, string/array operations, libc stubs, and the `lean/lean.h` shim. This code implements the interface that Lean's generated C expects. It talks to hardware only through `platform/` headers (`uart.h`, `board.h`).

- **`sha256/`**, **`can/`**, **`torque/`** — Verified subsystems. Each directory contains the implementation and its formal proofs.

- **`lib/`** — Shared proof libraries used across subsystems.

- **`test/`** — Test and demo programs (hello world, allocator stress test, IO error handling, runtime coverage).

This separation means porting to a new board is a `platform/`-only change, and runtime bug fixes don't touch hardware code.

## Files

```
platform/
  boot.S              RISC-V entry point (disable interrupts, zero BSS, set stack)
  linker.ld           Memory layout at 0x80000000 (QEMU virt machine)
  board.c/h           Board-specific config (UART base, early init, halt)
  uart.c/h            NS16550A UART driver
runtime/
  lean_rt.c/h         Freestanding Lean runtime (slab allocator, refcounting, strings, arrays)
  libc_min.c          Minimal libc stubs
  main.c              C entry: init UART, init Lean runtime, call Lean main
  sha256_ref.c        C reference SHA-256 for benchmarking (FIPS 180-4)
  lean/lean.h         Shim header replacing <lean/lean.h> for freestanding builds
sha256/
  sha256.lean         SHA-256 implementation (FIPS 180-4) with benchmarks
  sha256_proof.lean   Formal proofs (72 theorems, imports sha256.lean)
can/
  can_lib.lean        CAN 2.0 library (types, parser, encoder, CRC-15)
  can.lean            CAN 2.0 bare-metal entry point (imports can_lib)
  can_proof.lean      Formal proofs (59 theorems: roundtrip, bit extraction, test vectors)
torque/
  torque.lean         Torque-enable gate (imports can_lib)
  torque_proof.lean   Formal proofs (28 theorems: safety invariants, fault latching, admissibility)
lib/
  bitfield.lean       Reusable UInt8 bit isolation lemmas (shared proof library)
test/
  hello.lean          Hello world
  alloc_stress.lean   Allocator stress test
  io_error.lean       IO error handling test
  runtime_test.lean   Runtime feature coverage test
lakefile.lean         Lake build config (proof file imports implementation)
flake.nix             Nix flake for reproducible builds
```

## Target

RISC-V 64-bit on QEMU `virt`. Open ISA, great tooling. Everything you need is provided by Nix.

## Current status

- [x] Lean programs run directly on bare-metal RISC-V in QEMU
- [x] Freestanding runtime replaces libc, allocator, thread, and I/O dependencies
- [x] SHA-256 proved end-to-end (72 theorems) with cycle-count benchmarks
- [x] CAN 2.0 frame parser proved correct (59 theorems: roundtrip, bit extraction, CRC-15, parser = spec)
- [x] Torque-enable gate proved safe (28 theorems: torque → all conditions, fault latching, no backdoor, frame admissibility)
- [x] Shared proof library: `bitfield.lean` (8 lemmas shared by CAN and torque proofs)
- [x] `platform/` vs `runtime/` split — clean porting boundary
- [x] `make test` and `make verify` work as the main validation path
- [ ] Real hardware support

## Roadmap

See [ROADMAP.md](ROADMAP.md).
Near-term direction: finish the automotive authority-gate path, then apply the same verified policy pattern to a hardware-near finance order admission / pre-trade risk gate.
