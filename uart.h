#ifndef UART_H
#define UART_H

/* NS16550A UART driver using the active board's MMIO configuration. */

void uart_init(void);
void uart_putc(char c);
void uart_puts(const char *s);
void uart_put_hex(unsigned long val);
void uart_put_dec(long val);

#endif
