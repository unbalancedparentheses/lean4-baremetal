#include "uart.h"

/* NS16550A UART registers (QEMU virt: base 0x10000000) */
#define UART0_BASE  0x10000000UL

#define UART_THR    0   /* Transmit Holding Register (write) */
#define UART_RBR    0   /* Receive Buffer Register (read) */
#define UART_IER    1   /* Interrupt Enable Register */
#define UART_FCR    2   /* FIFO Control Register (write) */
#define UART_LCR    3   /* Line Control Register */
#define UART_LSR    5   /* Line Status Register */

#define UART_LCR_8N1       0x03    /* 8 data bits, no parity, 1 stop bit */
#define UART_LCR_DLAB      0x80    /* Divisor Latch Access Bit */
#define UART_FCR_FIFO_EN   0x01    /* Enable FIFOs */
#define UART_FCR_CLEAR     0x06    /* Clear RX and TX FIFOs */
#define UART_LSR_TX_EMPTY  0x20    /* Transmit holding register empty */

static volatile unsigned char *const uart = (unsigned char *)UART0_BASE;

void uart_init(void)
{
    /* Disable interrupts */
    uart[UART_IER] = 0x00;

    /* Enable DLAB to set baud rate divisor */
    uart[UART_LCR] = UART_LCR_DLAB;

    /* Set divisor to 1 (115200 baud with 1.8432 MHz clock) */
    uart[0] = 0x01;  /* DLL */
    uart[1] = 0x00;  /* DLM */

    /* 8 data bits, no parity, 1 stop bit; clear DLAB */
    uart[UART_LCR] = UART_LCR_8N1;

    /* Enable and clear FIFOs */
    uart[UART_FCR] = UART_FCR_FIFO_EN | UART_FCR_CLEAR;
}

void uart_putc(char c)
{
    /* Wait for transmit holding register to be empty */
    while ((uart[UART_LSR] & UART_LSR_TX_EMPTY) == 0)
        ;
    uart[UART_THR] = (unsigned char)c;
}

void uart_puts(const char *s)
{
    while (*s) {
        if (*s == '\n')
            uart_putc('\r');
        uart_putc(*s);
        s++;
    }
}

void uart_put_hex(unsigned long val)
{
    static const char hex[] = "0123456789abcdef";
    uart_puts("0x");
    for (int i = 60; i >= 0; i -= 4)
        uart_putc(hex[(val >> i) & 0xf]);
}

void uart_put_dec(long val)
{
    char buf[21];
    int neg = 0;
    unsigned long u;

    if (val < 0) {
        neg = 1;
        u = (unsigned long)(-(val + 1)) + 1;
    } else {
        u = (unsigned long)val;
    }

    int i = 0;
    do {
        buf[i++] = '0' + (char)(u % 10);
        u /= 10;
    } while (u > 0);

    if (neg)
        uart_putc('-');
    while (i > 0)
        uart_putc(buf[--i]);
}
