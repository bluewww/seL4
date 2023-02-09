/*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

#pragma once

#include <plat/machine.h>
#include <machine/registerset.h>
#include <hardware.h>

/* When translating a physical address into an address accessible to the
 * kernel via virtual addressing we always use the mapping of the memory
 * into the physical memory window, even if the mapping originally
 * referred to a kernel virtual address. */
static inline void *CONST ptrFromPAddr(paddr_t paddr)
{
    return (void *)(paddr + PPTR_BASE_OFFSET);
}

/* When obtaining a physical address from a reference to any object in
 * the physical mapping window, this function must be used. */
static inline paddr_t CONST addrFromPPtr(const void *pptr)
{
    return (paddr_t)pptr - PPTR_BASE_OFFSET;
}

/* When obtaining a physical address from a reference to an address from
 * the kernel ELF mapping, this function must be used. */
static inline paddr_t CONST addrFromKPPtr(const void *pptr)
{
    assert((paddr_t)pptr >= KERNEL_ELF_BASE);
    assert((paddr_t)pptr <= KERNEL_ELF_TOP);
    return (paddr_t)pptr - KERNEL_ELF_BASE_OFFSET;
}

#ifdef CONFIG_KERNEL_IMAGES
/* Function for addresses in the kernel image clone memory region. */
static inline paddr_t CONST addrFromKCMPtr(const void *pptr)
{
    assert((paddr_t)pptr >= KERNEL_CLONE_MEM_BASE);
    assert((paddr_t)pptr <= KERNEL_CLONE_MEM_TOP);
    return (paddr_t)pptr - KERNEL_ELF_BASE_OFFSET;
}
#endif

#define paddr_to_pptr(x)   ptrFromPAddr(x)
#define pptr_to_paddr(x)   addrFromPPtr(x)
#define kpptr_to_paddr(x)  addrFromKPPtr(x)
#ifdef CONFIG_KERNEL_IMAGES
#define kcmptr_to_paddr(x)  addrFromKCMPtr(x)
#endif

static inline region_t CONST paddr_to_pptr_reg(const p_region_t p_reg)
{
    return (region_t) {
        .start = (paddr_t)paddr_to_pptr(p_reg.start),
        .end   = (paddr_t)paddr_to_pptr(p_reg.end)
    };
}

static inline p_region_t CONST pptr_to_paddr_reg(const region_t reg)
{
    return (p_region_t) {
        .start = pptr_to_paddr((const void *)reg.start),
        .end   = pptr_to_paddr((const void *)reg.end),
    };
}


#include <mode/machine.h>
