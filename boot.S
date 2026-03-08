# boot.S — RISC-V 64-bit entry point for QEMU virt machine
#
# On entry from QEMU -bios none -kernel:
#   - Hart 0 is the boot hart
#   - PC = 0x80000000 (start of RAM)
#   - a0 = hartid, a1 = device tree pointer

.section .text.boot
.globl _start
_start:
    # Disable interrupts
    csrw    mie, zero
    csrw    mstatus, zero

    # Park all harts except hart 0
    csrr    t0, mhartid
    bnez    t0, .park

    # Zero BSS section
    la      t0, _bss_start
    la      t1, _bss_end
.zero_bss:
    bgeu    t0, t1, .bss_done
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       .zero_bss
.bss_done:

    # Set up stack pointer (stack grows downward)
    la      sp, _stack_top

    # Call C main
    call    main

    # If main returns, halt
.park:
    wfi
    j       .park
