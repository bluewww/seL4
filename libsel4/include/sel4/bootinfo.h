/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#ifdef HAVE_AUTOCONF
#include <autoconf.h>
#endif

#include <sel4/types.h>
#include <sel4/bootinfo_types.h>
#include <sel4/macros.h>
#include <sel4/sel4_arch/constants.h>

void seL4_InitBootInfo(seL4_BootInfo *bi)
SEL4_DEPRECATED("libsel4 management of bootinfo is deprecated, see the BootInfo Frame section of the manual");
seL4_BootInfo *seL4_GetBootInfo(void)
SEL4_DEPRECATED("libsel4 management of bootinfo is deprecated, see the BootInfo Frame section of the manual");

#ifdef CONFIG_KERNEL_IMAGES
/** Static array describing the kernel image level sizes in bits */
extern seL4_Word __sel4_kernel_image_level_size_bits[seL4_KernelImageNumLevels];

/**
 * Get the size of KernelMemory obects at each level of the kernel image
 * virtual address space in bits starting from the topmost level.
 *
 * @param level  The level of the kernel image address space. Must be
 *               less than seL4_KernelImageNumLevels;
 * @returns      The size, in bits, for each KernelMemory at the
 *               specified level of the address space.
 */
static inline seL4_Word seL4_GetKernelImageLevelSizeBits(seL4_Word level)
{
    if (level < seL4_KernelImageNumLevels) {
        return __sel4_kernel_image_level_size_bits[level];
    } else {
        return 0;
    }
}

/** Static array describing the kernel image level index bits */
extern seL4_Word __sel4_kernel_image_level_index_bits[seL4_KernelImageNumLevels];

/**
 * Get the number of bits indexed at each level of the kernel image
 * virtual address space starting from the topmost level.
 *
 * @param level  The level of the kernel image address space. Must be
 *               less than seL4_KernelImageNumLevels;
 * @returns      The number of bits resolved in a virtual address by
 *               that level of the virtual address space.
 */
static inline seL4_Word seL4_GetKernelImageLevelIndexBits(seL4_Word level)
{
    if (level < seL4_KernelImageNumLevels) {
        return __sel4_kernel_image_level_index_bits[level];
    } else {
        return 0;
    }
}
#endif

