# lean4-baremetal

Run Lean 4 programs directly on bare-metal hardware with no operating system.

Lean 4 compiles to C, but its runtime depends on libc, GMP, pthreads, libuv, and C++ exceptions. This project provides a **freestanding replacement runtime** (~1000 lines of C) that removes all those dependencies, enabling Lean programs to run on raw hardware.

**This is the first known freestanding Lean 4 runtime.** Nobody has done this before.

## Why this matters

Lean 4 produces machine-checkable proofs about programs. Bare-metal Lean means formally verified code for:

- **Avionics** (DO-178C)
- **Medical devices** (IEC 62304)
- **Automotive** (ISO 26262)
- **Embedded systems** and **RTOS kernels**

## Target

RISC-V 64-bit on QEMU `virt` machine. Simplest bare-metal target available — open ISA spec, excellent QEMU support.

## Quick start

```bash
# Enter the dev environment (provides lean4, riscv64 cross-compiler, qemu)
nix develop

# Build and run
make
make run
# You should see: "Hello from bare-metal Lean!"
# Press Ctrl-A X to exit QEMU
```

## How it works

```
examples/hello.lean
        │
        ▼  lean -c
   build/hello.c         (Lean compiler emits C)
        │
        ▼  riscv64-elf-gcc -ffreestanding -nostdlib
   build/kernel.elf      (cross-compiled with our runtime)
        │
        ▼  qemu-system-riscv64 -machine virt -bios none
   UART output            (runs directly on virtual hardware)
```

### Build pipeline

1. `lean examples/hello.lean -c build/hello.c` — Lean to C
2. Cross-compile `boot.S` + `lean_rt.c` + `uart.c` + `libc_min.c` + `main.c` + `build/hello.c`
3. Link with `linker.ld` (RAM at 0x80000000, QEMU virt memory map)
4. Run on QEMU RISC-V 64-bit virt machine

### What we replaced

| Dependency | Original | Our replacement |
|-----------|----------|-----------------|
| libc | glibc/musl | `libc_min.c` — memcpy, memset, strlen, abort (~80 lines) |
| Memory allocator | mimalloc | Bump allocator in `lean_rt.c` (~30 lines) |
| GMP | libgmp | Panic on overflow (fixed-width integers only) |
| pthreads | libpthread | No-op stubs (single-threaded) |
| libuv | libuv | Not needed |
| C++ runtime | libstdc++ | Rewritten in C, exceptions → panic + halt |
| stdio | printf/fprintf | `uart.c` — NS16550A UART driver (~60 lines) |

## Project structure

```
boot.S          RISC-V entry point: disable interrupts, zero BSS, set stack, call main
linker.ld       Memory layout: text/rodata/data/bss/heap/stack at 0x80000000
uart.c/h        NS16550A UART driver for QEMU virt (0x10000000)
lean_rt.c/h     Freestanding Lean 4 runtime (~1000 lines of C)
libc_min.c      Minimal libc: memcpy, memset, memmove, memcmp, strlen, abort
main.c          Initializes runtime, calls Lean main
Makefile        Build system
flake.nix       Nix flake for reproducible dev environment
examples/       Lean source files
```

## Key technical decisions

- **C, not C++** — The original Lean runtime is C++ but we rewrote the needed parts in C to avoid needing C++ exceptions and standard library on bare-metal.
- **Bump allocator** — Simplest possible (increment pointer, never free). Good enough for short-lived programs. Will upgrade to slab allocator for real use.
- **No GMP** — Only fixed-width integers (UInt32/UInt64). Bignum operations panic. Phase 2 will add the built-in mpn fallback.
- **Single-threaded** — All threading primitives are no-ops or globals. No atomics needed.
- **RISC-V 64-bit** — Simplest ISA, best QEMU support, fully open specification.

## Roadmap

- [x] Phase 1: Hello World — `IO.println` working on bare-metal
- [ ] Phase 2: Nat/Int bignum support (port `mpn.cpp` to C)
- [ ] Phase 3: Slab allocator (real memory reuse)
- [ ] Phase 4: Interrupts and basic hardware interaction
- [ ] Phase 5: Real hardware (SiFive, StarFive, etc.)
- [ ] Phase 6: Formally verified device drivers written in Lean

## Allocator roadmap: bump → slab

Phase 1 uses a **bump allocator**: a single pointer that increments on every allocation and never frees. This is ~10 lines of code and sufficient to prove the concept, but any long-running program will exhaust memory.

Phase 3 will replace it with a **slab allocator**. A slab allocator pre-allocates pools of fixed-size memory blocks — one pool for 16-byte objects, another for 32-byte, another for 64-byte, etc. This matches how Lean's own runtime works internally (8-byte granularity slots up to 4096 bytes, larger objects go to a general allocator).

Benefits of slab allocation for Lean:
- **O(1) alloc/free** — just pop/push from a free list per size class
- **No fragmentation** within a size class (all blocks same size)
- **Cache-friendly** — objects of the same size are contiguous in memory
- **Matches Lean's allocation patterns** — Lean objects are small and frequently allocated/freed via reference counting

The slab allocator will be ~300-500 lines of C. For bare-metal use, it will manage pages carved from a static memory region (no `mmap`/`sbrk`).

## Requirements

- Lean 4 (tested with v4.x)
- RISC-V 64-bit cross-compiler (`riscv64-elf-gcc` or `riscv64-unknown-elf-gcc`)
- QEMU with RISC-V support (`qemu-system-riscv64`)
- GNU Make

All provided by `nix develop` if you use the flake.
