#include "board.h"

#if BOARD_TARGET == BOARD_QEMU_VIRT

const char *board_name(void)
{
    return "qemu-virt";
}

uintptr_t board_uart_base(void)
{
    return 0x10000000UL;
}

void board_early_init(void)
{
    /* QEMU virt entered via -bios none needs no extra early board init here. */
}

void board_halt(void)
{
    for (;;)
        __asm__ volatile("wfi");
}

#else
#error "Unsupported BOARD_TARGET"
#endif
