#ifndef UART_H
#define UART_H

/* NS16550A UART driver for QEMU virt machine.
 * UART0 is memory-mapped at 0x10000000. */

void uart_init(void);
void uart_putc(char c);
void uart_puts(const char *s);
void uart_put_hex(unsigned long val);
void uart_put_dec(long val);

#endif
