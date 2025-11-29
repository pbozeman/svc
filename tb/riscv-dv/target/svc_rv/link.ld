/* SVC RISC-V Linker Script for riscv-dv tests
 *
 * Memory layout for SVC processor:
 * - Instruction memory: 0x00010000 (64KB, starts at 64KB offset)
 * - Data memory:        0x00010000 (same, separate Harvard)
 * - MMIO:               0x80000000+ (bit 31 set)
 *
 * Note: Program starts at 0x10000 because Spike ISS doesn't support
 * memory at address 0x0. Both Spike and RTL use the same addresses.
 *
 * tohost/fromhost: HTIF interface at 0x80001000 for test termination
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x00010000, LENGTH = 64K
    MMIO (rw) : ORIGIN = 0x80001000, LENGTH = 4K
}

SECTIONS
{
    . = 0x00010000;

    .text : {
        *(.text.init)
        *(.text)
        *(.text.*)
    } > RAM

    . = ALIGN(4);

    .rodata : {
        *(.rodata)
        *(.rodata.*)
    } > RAM

    . = ALIGN(4);

    .data : {
        *(.data)
        *(.data.*)
        *(.sdata)
        *(.sdata.*)
    } > RAM

    . = ALIGN(4);

    .bss : {
        __bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
        __bss_end = .;
    } > RAM

    . = ALIGN(4);

    /* Stack at top of RAM */
    __stack_top = ORIGIN(RAM) + LENGTH(RAM);

    /* HTIF tohost/fromhost for test termination - placed in MMIO region */
    .tohost (NOLOAD) : {
        . = ALIGN(64);
        tohost = .;
        . += 8;
        . = ALIGN(64);
        fromhost = .;
        . += 8;
    } > MMIO
}
