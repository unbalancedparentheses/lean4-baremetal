# Makefile — Build system for lean4-baremetal
#
# Pipeline:
#   1. lean examples/$(EXAMPLE).lean -c build/$(EXAMPLE).c    (Lean → C)
#   2. riscv64 cross-compile all C + assembly                  (C → ELF)
#   3. qemu-system-riscv64 runs the binary                     (ELF → bare-metal)

# Tools
LEAN      ?= lean
QEMU      ?= qemu-system-riscv64
PYTHON    ?= python3

# Cross-compiler: detect riscv64 gcc variant (nix sets CC=clang, so we
# must explicitly search for the cross-compiler by name)
CROSS_CC  := $(shell command -v riscv64-unknown-linux-gnu-gcc 2>/dev/null || \
                     command -v riscv64-elf-gcc 2>/dev/null || \
                     command -v riscv64-unknown-elf-gcc 2>/dev/null || \
                     command -v riscv64-none-elf-gcc 2>/dev/null || \
                     command -v riscv64-linux-gnu-gcc 2>/dev/null)

# Flags
CFLAGS    := -ffreestanding -nostdlib -nostartfiles \
             -mcmodel=medany -march=rv64imac_zicsr -mabi=lp64 \
             -O2 -Wall -Wextra -Wno-unused-parameter \
             -I. \
             -fno-stack-protector \
             -DLEAN_FREESTANDING=1
LDFLAGS   := -T linker.ld -nostdlib -static
QEMUFLAGS := -machine virt -bios none -nographic -serial mon:stdio
TEST_TIMEOUT ?= 10

# Directories
BUILDDIR  := build

# Example selection (override with: make EXAMPLE=sha256)
EXAMPLE   ?= hello

# Sources
LEAN_SRC  := examples/$(EXAMPLE).lean
LEAN_C    := $(BUILDDIR)/$(EXAMPLE).c

ASM_SRC   := boot.S
C_SRCS    := lean_rt.c uart.c libc_min.c
C_SRCS    += board.c

# Object files
ASM_OBJ   := $(BUILDDIR)/boot.o
C_OBJS    := $(patsubst %.c,$(BUILDDIR)/%.o,$(C_SRCS))
LEAN_OBJ  := $(BUILDDIR)/$(EXAMPLE)_lean.o

ALL_OBJS  := $(ASM_OBJ) $(C_OBJS) $(LEAN_OBJ)

# Output (example-specific to avoid stale cross-example artifacts)
KERNEL    := $(BUILDDIR)/$(EXAMPLE).elf

.PHONY: all clean run lean-c objdump verify test help \
	        nix-build nix-run nix-clean nix-verify nix-test

# ---- Nix wrappers (run everything inside nix develop) ----

NIX := nix --extra-experimental-features 'nix-command flakes'

nix-build:
	$(NIX) develop --command make EXAMPLE=$(EXAMPLE) all

nix-run:
	$(NIX) develop --command make EXAMPLE=$(EXAMPLE) run

nix-clean:
	$(NIX) develop --command make clean

nix-verify:
	$(NIX) develop --command make verify

nix-test:
	$(NIX) develop --command make test

# ---- Build targets ----

all: $(KERNEL)

# Compile Lean to C
lean-c: $(LEAN_C)

$(LEAN_C): $(LEAN_SRC) | $(BUILDDIR)
	@echo "  LEAN    $< -> $@"
	$(LEAN) $< -c $@

# Compile assembly
$(ASM_OBJ): $(ASM_SRC) | $(BUILDDIR)
	@echo "  AS      $<"
	$(CROSS_CC) $(CFLAGS) -c $< -o $@

# Compile C sources
$(BUILDDIR)/%.o: %.c lean_rt.h uart.h | $(BUILDDIR)
	@echo "  CC      $<"
	$(CROSS_CC) $(CFLAGS) -c $< -o $@

# Compile Lean-generated C
$(LEAN_OBJ): $(LEAN_C) lean_rt.h | $(BUILDDIR)
	@echo "  CC      $< (lean-generated)"
	$(CROSS_CC) $(CFLAGS) -Wno-unused-function -Wno-missing-field-initializers -c $< -o $@

# Link
$(KERNEL): $(ALL_OBJS)
	@echo "  LD      $@"
	$(CROSS_CC) $(LDFLAGS) $(ALL_OBJS) -o $@
	@size=$$(stat -f%z $@ 2>/dev/null || stat -c%s $@); echo "  Built $(KERNEL) ($$size bytes)"

# ---- Run / test / verify ----

define run_with_timeout
if command -v timeout >/dev/null 2>&1; then \
	timeout $(TEST_TIMEOUT) $(1); \
elif command -v gtimeout >/dev/null 2>&1; then \
	gtimeout $(TEST_TIMEOUT) $(1); \
elif command -v $(PYTHON) >/dev/null 2>&1; then \
	$(PYTHON) -c 'import os, signal, subprocess, sys; \
timeout = int(sys.argv[1]); \
proc = subprocess.Popen(sys.argv[2:], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True); \
signal.signal(signal.SIGALRM, lambda *_: proc.kill()); \
signal.alarm(timeout); \
out, _ = proc.communicate(); \
sys.stdout.write(out); \
sys.exit(0 if proc.returncode in (0, -signal.SIGKILL) else proc.returncode)' \
	$(TEST_TIMEOUT) $(1); \
else \
	echo "No timeout runner found (need timeout, gtimeout, or $(PYTHON))" >&2; \
	exit 1; \
fi
endef

run: $(KERNEL)
	@echo "  QEMU    $(KERNEL)"
	@echo "  (Press Ctrl-A X to exit QEMU)"
	$(QEMU) $(QEMUFLAGS) -kernel $(KERNEL)

# Formal verification: sha256_proof imports sha256 via lake.
# If sha256.lean changes and breaks a proof, this fails.
verify:
	@echo "  VERIFY  examples/sha256_proof.lean (via lake build)"
	lake build sha256_proof
	@echo "  VERIFY  examples/can_proof.lean (via lake build)"
	lake build can_proof

# Automated test: build, run on QEMU, check expected output
test:
	@echo "  TEST    hello"
	@$(MAKE) --no-print-directory EXAMPLE=hello all
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/hello.elf)); \
	if echo "$$output" | grep -q "Hello from bare-metal Lean!"; then \
		echo "  PASS    hello"; \
	else \
		echo "  FAIL    hello"; echo "$$output"; exit 1; \
	fi
	@$(MAKE) --no-print-directory EXAMPLE=sha256 all
	@echo "  TEST    sha256"
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/sha256.elf)); \
	if echo "$$output" | grep -q "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"; then \
		echo "  PASS    sha256"; \
	else \
		echo "  FAIL    sha256"; echo "$$output"; exit 1; \
	fi
	@$(MAKE) --no-print-directory EXAMPLE=alloc_stress all
	@echo "  TEST    alloc_stress"
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/alloc_stress.elf)); \
	if echo "$$output" | grep -q "alloc-stress ok"; then \
		echo "  PASS    alloc_stress"; \
	else \
		echo "  FAIL    alloc_stress"; echo "$$output"; exit 1; \
	fi
	@$(MAKE) --no-print-directory EXAMPLE=io_error all
	@echo "  TEST    io_error"
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/io_error.elf)); \
	if echo "$$output" | grep -q "\\[lean\\] IO error: expected runtime error"; then \
		echo "  PASS    io_error"; \
	else \
		echo "  FAIL    io_error"; echo "$$output"; exit 1; \
	fi
	@$(MAKE) --no-print-directory EXAMPLE=can all
	@echo "  TEST    can"
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/can.elf)); \
	if echo "$$output" | grep -q "CRC-15" && echo "$$output" | grep -q "059e"; then \
		echo "  PASS    can"; \
	else \
		echo "  FAIL    can"; echo "$$output"; exit 1; \
	fi
	@$(MAKE) --no-print-directory EXAMPLE=runtime_test all
	@echo "  TEST    runtime_test"
	@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/runtime_test.elf)); \
	if echo "$$output" | grep -q "runtime-test ok"; then \
		echo "  PASS    runtime_test"; \
	else \
		echo "  FAIL    runtime_test"; echo "$$output"; exit 1; \
	fi
	@echo "  ALL TESTS PASSED"

# ---- Utilities ----

objdump: $(KERNEL)
	$(subst gcc,objdump,$(CROSS_CC)) -d $(KERNEL) | head -100

$(BUILDDIR):
	mkdir -p $(BUILDDIR)

clean:
	rm -rf $(BUILDDIR) .lake

help:
	@echo "Usage: make [TARGET] [EXAMPLE=hello|sha256]"
	@echo ""
	@echo "Build targets:"
	@echo "  all          Build kernel ELF (default)"
	@echo "  run          Build and run on QEMU"
	@echo "  test         Build both examples, run, check expected output"
	@echo "  verify       Typecheck formal proofs via lake"
	@echo "  lean-c       Compile Lean to C only"
	@echo "  objdump      Disassemble kernel ELF"
	@echo "  clean        Remove build artifacts"
	@echo ""
	@echo "Nix wrappers (no manual nix develop needed):"
	@echo "  nix-build    make all inside nix develop"
	@echo "  nix-run      make run inside nix develop"
	@echo "  nix-test     make test inside nix develop"
	@echo "  nix-verify   make verify inside nix develop"
	@echo "  nix-clean    make clean inside nix develop"
	@echo ""
	@echo "Examples:"
	@echo "  make nix-run                   # build and run hello (default)"
	@echo "  make EXAMPLE=sha256 nix-run    # build and run sha256"
	@echo "  make EXAMPLE=alloc_stress nix-run"
	@echo "  make EXAMPLE=io_error nix-run"
	@echo "  make nix-test                  # run all tests"
	@echo "  make nix-verify                # check formal proofs"
