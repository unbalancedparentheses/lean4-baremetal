# Makefile — Build system for lean4-baremetal
#
# Pipeline:
#   1. lean examples/hello.lean -c build/hello.c    (Lean → C)
#   2. riscv64 cross-compile all C + assembly        (C → ELF)
#   3. qemu-system-riscv64 runs the binary           (ELF → bare-metal)

# Tools
LEAN      ?= lean
CC        ?= riscv64-elf-gcc
OBJCOPY   ?= riscv64-elf-objcopy
OBJDUMP   ?= riscv64-elf-objdump
QEMU      ?= qemu-system-riscv64

# If riscv64-elf-gcc is not found, try riscv64-unknown-elf-gcc or
# riscv64-linux-gnu-gcc (Nix often provides riscv64-none-elf-gcc)
CC_ALT1   := riscv64-unknown-elf-gcc
CC_ALT2   := riscv64-none-elf-gcc
CC_ALT3   := riscv64-linux-gnu-gcc

# Flags
CFLAGS    := -ffreestanding -nostdlib -nostartfiles \
             -mcmodel=medany -march=rv64imac_zicsr -mabi=lp64 \
             -O2 -Wall -Wextra -Wno-unused-parameter \
             -I. \
             -fno-stack-protector \
             -DLEAN_FREESTANDING=1
LDFLAGS   := -T linker.ld -nostdlib -static
QEMUFLAGS := -machine virt -bios none -nographic -serial mon:stdio

# Directories
BUILDDIR  := build

# Sources
LEAN_SRC  := examples/hello.lean
LEAN_C    := $(BUILDDIR)/hello.c

ASM_SRC   := boot.S
C_SRCS    := lean_rt.c uart.c libc_min.c main.c

# Object files
ASM_OBJ   := $(BUILDDIR)/boot.o
C_OBJS    := $(patsubst %.c,$(BUILDDIR)/%.o,$(C_SRCS))
LEAN_OBJ  := $(BUILDDIR)/hello_lean.o

ALL_OBJS  := $(ASM_OBJ) $(C_OBJS) $(LEAN_OBJ)

# Output
KERNEL    := $(BUILDDIR)/kernel.elf

# Detect which cross-compiler is available
REAL_CC := $(shell command -v $(CC) 2>/dev/null || \
                   command -v $(CC_ALT1) 2>/dev/null || \
                   command -v $(CC_ALT2) 2>/dev/null || \
                   command -v $(CC_ALT3) 2>/dev/null)

.PHONY: all clean run lean-c objdump nix-build nix-run nix-clean

# Nix wrappers — run everything inside nix develop, no manual shell needed
NIX := nix --extra-experimental-features 'nix-command flakes'

nix-build:
	$(NIX) develop --command make all

nix-run:
	$(NIX) develop --command make run

nix-clean:
	$(NIX) develop --command make clean

all: $(KERNEL)

# Step 1: Compile Lean to C
lean-c: $(LEAN_C)

$(LEAN_C): $(LEAN_SRC) | $(BUILDDIR)
	@echo "  LEAN    $< -> $@"
	$(LEAN) $< -c $@

# Step 2: Compile assembly
$(ASM_OBJ): $(ASM_SRC) | $(BUILDDIR)
	@echo "  AS      $<"
	$(REAL_CC) $(CFLAGS) -c $< -o $@

# Step 3: Compile C sources
$(BUILDDIR)/%.o: %.c lean_rt.h uart.h | $(BUILDDIR)
	@echo "  CC      $<"
	$(REAL_CC) $(CFLAGS) -c $< -o $@

# Step 4: Compile Lean-generated C (needs special include handling)
$(LEAN_OBJ): $(LEAN_C) lean_rt.h | $(BUILDDIR)
	@echo "  CC      $< (lean-generated)"
	$(REAL_CC) $(CFLAGS) -Wno-unused-function -Wno-missing-field-initializers -c $< -o $@

# Step 5: Link
$(KERNEL): $(ALL_OBJS)
	@echo "  LD      $@"
	$(REAL_CC) $(LDFLAGS) $(ALL_OBJS) -o $@
	@echo "  Built $(KERNEL) ($(shell stat -f%z $@ 2>/dev/null || stat -c%s $@) bytes)"

# Run on QEMU
run: $(KERNEL)
	@echo "  QEMU    $(KERNEL)"
	@echo "  (Press Ctrl-A X to exit QEMU)"
	$(QEMU) $(QEMUFLAGS) -kernel $(KERNEL)

# Useful for debugging
objdump: $(KERNEL)
	$(REAL_CC:gcc=objdump) -d $(KERNEL) | head -100

$(BUILDDIR):
	mkdir -p $(BUILDDIR)

clean:
	rm -rf $(BUILDDIR)
