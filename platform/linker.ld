/* linker.ld — Memory layout for QEMU virt machine (RISC-V 64-bit)
 *
 * QEMU virt RAM starts at 0x80000000.
 * We place code at the start, then data, then BSS, then heap and stack.
 *
 * Program headers separate code (RX) from data (RW) to avoid
 * the "LOAD segment with RWX permissions" linker warning.
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

PHDRS
{
    text PT_LOAD FLAGS(5);   /* PF_R | PF_X */
    data PT_LOAD FLAGS(6);   /* PF_R | PF_W */
}

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
    } > RAM :text

    .rodata : {
        *(.rodata .rodata.*)
    } > RAM :text

    .data : {
        *(.data .data.*)
    } > RAM :data

    . = ALIGN(8);
    _bss_start = .;
    .bss : {
        *(.bss .bss.*)
        *(COMMON)
    } > RAM :data
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
