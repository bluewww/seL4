/*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 */

#ifndef __ARCH_OBJECT_KERNEL_IMAGE_H
#define __ARCH_OBJECT_KERNEL_IMAGE_H

#include <types.h>
#include <object/structures.h>
#include <api/failures.h>
#include <mode/object/kernelimage.h>

/* Map the provided memory with the given mapping parameters */
exception_t Arch_kernelMemoryMap(kernel_image_t *image, ki_mapping_t *mapping, paddr_t memory_addr);

/* Clone the entry at the specified address and depth between the
 * address spaces */
exception_t Arch_kernelImageCloneEntry(kernel_image_root_t *dest, kernel_image_root_t *src, vptr_t clone_addr,
                                       word_t depth, bool_t duplicate);

/* Update the kernel image virtual address space with the given root.
 *
 * Will also set the user address space to empty if shared with kernel.  */
void Arch_setKernelImage(kernel_image_root_t *root);

#endif /* __ARCH_OBJECT_KERNEL_IMAGE_H */
