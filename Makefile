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
             -Iruntime -Iplatform \
             -fno-stack-protector \
             -DLEAN_FREESTANDING=1
LDFLAGS   := -T platform/linker.ld -nostdlib -static
QEMUFLAGS := -machine virt -bios none -nographic -serial mon:stdio
TEST_TIMEOUT ?= 10

# Directories
BUILDDIR  := build

# Example selection (override with: make EXAMPLE=sha256)
EXAMPLE   ?= hello

# Examples that import project modules and need lake for LEAN_PATH.
# Each such example lists its Lean module dependencies below.
LAKE_EXAMPLES := can torque
LEAN_DEPS_can     := can_lib
LEAN_DEPS_torque  := can_lib

# Sources
LEAN_SRC  := examples/$(EXAMPLE).lean
LEAN_C    := $(BUILDDIR)/$(EXAMPLE).c

ASM_SRC   := platform/boot.S
C_SRCS    := runtime/lean_rt.c platform/uart.c runtime/libc_min.c
C_SRCS    += platform/board.c

# Object files
ASM_OBJ   := $(BUILDDIR)/boot.o
C_OBJS    := $(BUILDDIR)/lean_rt.o $(BUILDDIR)/uart.o $(BUILDDIR)/libc_min.o \
             $(BUILDDIR)/board.o
LEAN_OBJ  := $(BUILDDIR)/$(EXAMPLE)_lean.o

# Dependency objects (empty for standalone examples, populated for lake examples)
LEAN_DEP_OBJS := $(patsubst %,$(BUILDDIR)/%_lean.o,$(LEAN_DEPS_$(EXAMPLE)))

ALL_OBJS  := $(ASM_OBJ) $(C_OBJS) $(LEAN_OBJ) $(LEAN_DEP_OBJS)

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

# Compile Lean to C.
# - Standalone examples: plain `lean -c`
# - Lake examples (import project modules): `lake build` generates C for all
#   modules, then copy to build/.
lean-c: $(LEAN_C)

$(LEAN_C): $(LEAN_SRC) | $(BUILDDIR)
	@echo "  LEAN    $< -> $@"
	@if echo "$(LAKE_EXAMPLES)" | grep -qw "$(EXAMPLE)"; then \
		lake build $(EXAMPLE) >/dev/null 2>&1; \
		cp .lake/build/ir/$(EXAMPLE).c $@; \
		for dep in $(LEAN_DEPS_$(EXAMPLE)); do \
			cp .lake/build/ir/$$dep.c $(BUILDDIR)/$$dep.c; \
		done; \
	else \
		$(LEAN) $< -c $@; \
	fi

# Dependency C files are generated as a side effect of the main lean-c step
$(foreach dep,$(LEAN_DEPS_$(EXAMPLE)),$(eval $(BUILDDIR)/$(dep).c: $(LEAN_C)))

# Compile assembly
$(ASM_OBJ): $(ASM_SRC) | $(BUILDDIR)
	@echo "  AS      $<"
	$(CROSS_CC) $(CFLAGS) -c $< -o $@

# Compile C sources (explicit rules per source directory)
$(BUILDDIR)/%.o: runtime/%.c | $(BUILDDIR)
	@echo "  CC      $<"
	$(CROSS_CC) $(CFLAGS) -c $< -o $@

$(BUILDDIR)/%.o: platform/%.c | $(BUILDDIR)
	@echo "  CC      $<"
	$(CROSS_CC) $(CFLAGS) -c $< -o $@

# Compile Lean-generated C (main example + any dependencies)
$(BUILDDIR)/%_lean.o: $(BUILDDIR)/%.c runtime/lean_rt.h | $(BUILDDIR)
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

# run_test: build example, run on QEMU, grep for expected output
# $(1) = example name, $(2) = grep pattern
define run_test
@$(MAKE) --no-print-directory EXAMPLE=$(1) all
@echo "  TEST    $(1)"
@output=$$($(call run_with_timeout,$(QEMU) $(QEMUFLAGS) -kernel $(BUILDDIR)/$(1).elf)); \
if echo "$$output" | grep -q $(2); then \
	echo "  PASS    $(1)"; \
else \
	echo "  FAIL    $(1)"; echo "$$output"; exit 1; \
fi
endef

run: $(KERNEL)
	@echo "  QEMU    $(KERNEL)"
	@echo "  (Press Ctrl-A X to exit QEMU)"
	$(QEMU) $(QEMUFLAGS) -kernel $(KERNEL)

# Formal verification: proof libs import the implementation via lake.
# If the implementation changes and breaks a proof, this fails.
verify:
	@echo "  VERIFY  sha256_proof"
	@lake build sha256_proof
	@echo "  VERIFY  can_proof"
	@lake build can_proof
	@echo "  VERIFY  torque_proof"
	@lake build torque_proof
	@echo "  ALL PROOFS VERIFIED"

# Automated test: build each example, run on QEMU, check expected output
test:
	$(call run_test,hello,"Hello from bare-metal Lean!")
	$(call run_test,sha256,"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
	$(call run_test,alloc_stress,"alloc-stress ok")
	$(call run_test,io_error,"IO error: expected runtime error")
	$(call run_test,can,"059e")
	$(call run_test,torque,"torque-gate ok")
	$(call run_test,runtime_test,"runtime-test ok")
	@echo "  ALL TESTS PASSED"

# ---- Utilities ----

objdump: $(KERNEL)
	$(subst gcc,objdump,$(CROSS_CC)) -d $(KERNEL) | head -100

$(BUILDDIR):
	mkdir -p $(BUILDDIR)

clean:
	rm -rf $(BUILDDIR) .lake

help:
	@echo "Usage: make [TARGET] [EXAMPLE=name]"
	@echo ""
	@echo "Build targets:"
	@echo "  all          Build kernel ELF (default)"
	@echo "  run          Build and run on QEMU"
	@echo "  test         Build all examples, run, check expected output"
	@echo "  verify       Typecheck all formal proofs via lake"
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
	@echo "Examples: hello sha256 alloc_stress io_error can torque runtime_test"
	@echo ""
	@echo "  make EXAMPLE=torque nix-run     # build and run torque gate"
	@echo "  make nix-test                   # run all tests"
	@echo "  make nix-verify                 # check formal proofs"
