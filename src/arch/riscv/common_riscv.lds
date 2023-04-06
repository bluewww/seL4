/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2015, 2016 Hesham Almatary <heshamelmatary@gmail.com>
 * Copyright 2021, HENSOLDT Cyber
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

#include <config.h>
#define __ASSEMBLER__
#include <hardware.h>
#include <sel4/plat/api/constants.h>
#include <plat/machine/devices_gen.h>

KERNEL_OFFSET = KERNEL_ELF_BASE - KERNEL_ELF_PADDR_BASE;

SECTIONS
{
    . = KERNEL_ELF_BASE;

    ki_boot_start = .;

    .boot.text . : AT(ADDR(.boot.text) - KERNEL_OFFSET)
    {
        *(.boot.text)
    }
    .boot.rodata . : AT(ADDR(.boot.rodata) - KERNEL_OFFSET)
    {
        *(.boot.rodata)
    }
    .boot.data . : AT(ADDR(.boot.data) - KERNEL_OFFSET)
    {
        *(.boot.data)
    }
    .boot.bss . : AT(ADDR(.boot.bss) - KERNEL_OFFSET)
    {
        *(.boot.bss)
    }
    . = ALIGN(4K);

    ki_boot_end = .;

    ki_start = .;
    ki_elf_start = .;
    ki_text_start = .;

    .text . : AT(ADDR(.text) - KERNEL_OFFSET)
    {
        . = ALIGN(4K);


        /* Standard kernel */
        *(.text)

        ki_text_end = .;

        /* Kernel image switch code */
        . = ALIGN(4K);
        ki_switch_start = .;
        *(.text.switch)
        ki_switch_end = .;
    }

    ki_private_start = .;

    /* Start of data section */
    _sdata = .;
    .small : {
        /* Small data that should be accessed relative to gp.  ld has trouble
           with the relaxation if they are not in a single section. */
        __global_pointer$ = . + 0x800;
        *(.srodata*)
        *(.sdata*)
    }

    .rodata . : AT(ADDR(.rodata) - KERNEL_OFFSET)
    {
        *(.rodata)
        *(.rodata.*)
    }

    .data . : AT(ADDR(.data) - KERNEL_OFFSET)
    {
        *(.data)
    }

    /* The kernel's idle thread section contains no code or data. */
    ._idle_thread . (NOLOAD): AT(ADDR(._idle_thread) - KERNEL_OFFSET)
    {
        *(._idle_thread)
    }

    .bss . (NOLOAD): AT(ADDR(.bss) - KERNEL_OFFSET)
    {
        /* node-local bss regions, not modified after boot */
        *(.bss.node_local)
        ki_private_end = .;

        /* per-image idle thread TCBs */
        . = ALIGN(4K);
        ki_idle_thread_start = .;
        *(.bss.idle_thread)
        ki_idle_thread_end = .;

        /* shared BSS data */
        ki_shared_start = .;

        *(.bss)
        *(.sbss)
        *(COMMON) /* fallback in case '-fno-common' is not used */

        /* 4k breakpoint stack */
        _breakpoint_stack_bottom = .;
        . = . + 4K;
        _breakpoint_stack_top = .;

        /* large data such as the globals frame and global PD */
        *(.bss.aligned)
    }

    . = ALIGN(4K);
    ki_shared_end = .;
    ki_elf_end = .;

    /* Region for kernel image clones */
    ._clone_mem . (NOLOAD): AT(ADDR(._clone_mem) - KERNEL_OFFSET)
    {
        ki_clone_mem_start = .;
        . = . + 16M; /* TODO: determine an actual reasonable size */
        ki_clone_mem_end = .;
        *(._clone_mem)
    }

    . = ALIGN(4K);
    ki_end = .;

    /* The start of the physically mapped free memory */
    ki_freemem_start = .;
}
