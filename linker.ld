/* linker.ld — Memory layout for QEMU virt machine (RISC-V 64-bit)
 *
 * QEMU virt RAM starts at 0x80000000.
 * We place code at the start, then data, then BSS, then a 64KB stack.
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS
{
    . = 0x80000000;

    .text : {
        *(.text.boot)
        *(.text .text.*)
    } > RAM

    .rodata : {
        *(.rodata .rodata.*)
    } > RAM

    .data : {
        *(.data .data.*)
    } > RAM

    . = ALIGN(8);
    _bss_start = .;
    .bss : {
        *(.bss .bss.*)
        *(COMMON)
    } > RAM
    . = ALIGN(8);
    _bss_end = .;

    /* Heap: 16MB after BSS */
    . = ALIGN(16);
    _heap_start = .;
    . = . + 16M;
    _heap_end = .;

    /* Stack: 64KB, grows downward */
    . = ALIGN(16);
    _stack_bottom = .;
    . = . + 64K;
    _stack_top = .;
}
