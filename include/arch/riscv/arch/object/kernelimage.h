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
void Arch_setKernelImage(kernel_image_t *image);

/* Get the physical address associated with the virtual address in a kernel image. */
static inline paddr_t Arch_kernelImagePaddr(kernel_image_root_t *root, vptr_t vaddr)
{
    lookupPTSlot_ret_t ret = lookupPTSlot(root, vaddr);
    assert(pte_ptr_get_valid(ret.ptSlot) && !isPTEPageTable(ret.ptSlot));

    pptr_t pptr1 = (pptr_t)(getPPtrFromHWPTE(ret.ptSlot));
    pptr_t pptr2 = (pptr1 + (vaddr & MASK(ret.ptBitsLeft)));
    paddr_t paddr = pptr_to_paddr((void *) pptr2);
    //printf("0x%lx: 0x%lx -> 0x%lx (0x%lx)\n", vaddr, pptr1, pptr2, paddr);

    return paddr;
}

#endif /* __ARCH_OBJECT_KERNEL_IMAGE_H */
