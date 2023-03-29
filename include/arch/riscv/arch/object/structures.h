/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2015, 2016 Hesham Almatary <heshamelmatary@gmail.com>
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

#pragma once

#ifndef __ASSEMBLER__
#include <config.h>
#include <assert.h>
#include <util.h>
#include <api/types.h>
#include <arch/types.h>
#include <arch/object/structures_gen.h>
#include <arch/machine/hardware.h>
#include <arch/machine/registerset.h>
#include <mode/object/structures.h>

#define tcbArchCNodeEntries tcbCNodeEntries

struct asid_pool {
    pte_t *array[BIT(asidLowBits)];
};

typedef struct asid_pool asid_pool_t;

#define ASID_POOL_PTR(r)    ((asid_pool_t*)r)
#define ASID_POOL_REF(p)    ((word_t)p)
#define ASID_BITS           (asidHighBits + asidLowBits)
#ifdef CONFIG_KERNEL_IMAGES
/* These are the *allocatable* ASID pools. */
#define nASIDPools          (BIT(asidHighBits) - 1)
/* The highest, unallocatable, ASID pool we reserve for the kernel images. */
#define KIASIDPool          MASK(asidHighBits)
#else
#define nASIDPools          BIT(asidHighBits)
#endif
#define ASID_LOW(a)         (a & MASK(asidLowBits))
#define ASID_HIGH(a)        ((a >> asidLowBits) & MASK(asidHighBits))

typedef struct arch_tcb {
    user_context_t tcbContext;
} arch_tcb_t;

enum vm_rights {
    VMKernelOnly = 1,
    VMReadOnly = 2,
    VMReadWrite = 3
};
typedef word_t vm_rights_t;

typedef pte_t vspace_root_t;

#ifdef CONFIG_KERNEL_IMAGES
typedef pte_t kernel_image_root_t;
#endif /* CONFIG_KERNEL_IMAGES */

/* Generic fastpath.c code expects pde_t for stored_hw_asid
 * that's a workaround in the time being.
 */
typedef pte_t pde_t;

#define VSPACE_PTR(r)       ((vspace_root_t *)(r))

#define PTE_PTR(r) ((pte_t *)(r))
#define PTE_REF(p) ((word_t)(p))

#define PT_SIZE_BITS 12
#define PT_PTR(r) ((pte_t *)(r))
#define PT_REF(p) ((word_t)(p))

#define PTE_SIZE_BITS   seL4_PageTableEntryBits
#define PT_INDEX_BITS   seL4_PageTableIndexBits

#define WORD_BITS   (8 * sizeof(word_t))
#define WORD_PTR(r) ((word_t *)(r))

#ifdef CONFIG_KERNEL_IMAGES
struct kernel_image {
    /* The virtual ASID used to identify the image. */
    asid_t kiASID;

    /* The number of KernelMemory objects already mapped into the image. */
    word_t kiMemoriesMapped;

    /* The root of the virtual address space. */
    kernel_image_root_t *kiRoot;

    /* A bitmap of which nodes have ever executed using this image. */
    word_t kiNodesExecuted[BITS_TO_TYPE(CONFIG_MAX_NUM_NODES, word_t)];

#if 0
    /* TODO: Figure out how to make the maxIRQ symbol visible here for
     * arm and riscv without intorducing circular dependencies in
     * headers */
    /* A bitmap of which IRQs have been unmasked under this image. */
    word_t kiIRQsUnmasked[BITS_TO_TYPE(maxIRQ, word_t)];
#endif

    /* Whether it is valid to run a thread in this image.
     *
     * When invalidating the image, this is set to false before
     * triggering other cores to reschedule. This ensures that after all
     * other cores have rescheduled none will be running threads in this
     * image and it is safe to remove all mappings. */
    bool_t kiRunnable;

    /* Whether the kernel data has been copied. */
    bool_t kiCopied;

    /* Whether the kernel stack has been initialised properly for this image.
     * This should take place immediately prior to the initial switch to it. */
    bool_t kiStackInitted;

    /* The sp value to restore on switching back to this image. */
    vptr_t kiStackPointer;
};
typedef struct kernel_image kernel_image_t;

#endif

static inline bool_t CONST cap_get_archCapIsPhysical(cap_t cap)
{
    cap_tag_t ctag;

    ctag = cap_get_capType(cap);

    switch (ctag) {

    case cap_frame_cap:
        return true;

    case cap_page_table_cap:
        return true;

    case cap_asid_control_cap:
        return false;

    case cap_asid_pool_cap:
        return true;

    default:
        /* unreachable */
        return false;
    }
}

static inline word_t CONST cap_get_archCapSizeBits(cap_t cap)
{
    cap_tag_t ctag;

    ctag = cap_get_capType(cap);

    switch (ctag) {
    case cap_frame_cap:
        return pageBitsForSize(cap_frame_cap_get_capFSize(cap));

    case cap_page_table_cap:
        return PT_SIZE_BITS;

    case cap_asid_control_cap:
        return 0;

    case cap_asid_pool_cap:
        return seL4_ASIDPoolBits;

    default:
        assert(!"Unknown cap type");
        /* Unreachable, but GCC can't figure that out */
        return 0;
    }
}

static inline void *CONST cap_get_archCapPtr(cap_t cap)
{
    cap_tag_t ctag;

    ctag = cap_get_capType(cap);

    switch (ctag) {

    case cap_frame_cap:
        return (void *)(cap_frame_cap_get_capFBasePtr(cap));

    case cap_page_table_cap:
        return PT_PTR(cap_page_table_cap_get_capPTBasePtr(cap));

    case cap_asid_control_cap:
        return NULL;

    case cap_asid_pool_cap:
        return ASID_POOL_PTR(cap_asid_pool_cap_get_capASIDPool(cap));

    default:
        assert(!"Unknown cap type");
        /* Unreachable, but GCC can't figure that out */
        return NULL;
    }
}

static inline bool_t CONST Arch_isCapRevocable(cap_t derivedCap, cap_t srcCap)
{
    return false;
}

#endif /* !__ASSEMBLER__  */

