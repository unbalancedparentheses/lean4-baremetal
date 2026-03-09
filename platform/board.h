#ifndef BOARD_H
#define BOARD_H

#include <stdint.h>

/* Supported board targets. Start with QEMU virt and keep the interface small
 * so real hardware ports only need to fill in this boundary. */
#define BOARD_QEMU_VIRT 1

#ifndef BOARD_TARGET
#define BOARD_TARGET BOARD_QEMU_VIRT
#endif

const char *board_name(void);
uintptr_t board_uart_base(void);
void board_early_init(void);
void board_halt(void) __attribute__((noreturn));

#endif
