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

#include <util.h>
#include <kernel/vspace.h>
#include <object/kernelimage.h>

extern void set_sp(vptr_t sp_val);

static inline void *Arch_kiGetPPtrFromHWPTE(pte_t *pte)
{
    return PTE_PTR(ptrFromPAddr(pte_ptr_get_ppn(pte) << seL4_PageTableBits));
}

static inline lookupPTSlot_ret_t Arch_kiLookupPTSlot(pte_t *lvl1pt, vptr_t vptr, word_t depth)
{
    lookupPTSlot_ret_t ret;
    /* this is how many bits we potentially have left to decode. Initially we have the
     * full address space to decode, and every time we walk this will be reduced. The
     * final value of this after the walk is the size of the frame that can be inserted,
     * or already exists, in ret.ptSlot */
    ret.ptBitsLeft = PT_INDEX_BITS * CONFIG_PT_LEVELS + seL4_PageBits;
    ret.ptSlot = NULL;

    pte_t *pt = lvl1pt;
    do {
        ret.ptBitsLeft -= PT_INDEX_BITS;
        word_t index = (vptr >> ret.ptBitsLeft) & MASK(PT_INDEX_BITS);
        ret.ptSlot = pt + index;
        pt = getPPtrFromHWPTE(ret.ptSlot);
        /* stop when we find something that isn't a page table - either a mapped frame or
         * an empty slot */
        depth -= 1;
    } while (isPTEPageTable(ret.ptSlot) && depth > 0);

    return ret;
}

exception_t Arch_kernelMemoryMap(kernel_image_t *image, ki_mapping_t *mapping, paddr_t memory_addr)
{
    assert(mapping->kimRegion < KINumRegions);
    assert(mapping->kimLevel < seL4_KernelImageNumLevels);

    if (mapping->kimLevel == 0) {
        assert(image->kiRoot == NULL);
        image->kiRoot = PTE_PTR(paddr_to_pptr(memory_addr));
        return EXCEPTION_NONE;
    }

    assert(image->kiRoot != NULL);

    bool_t last_level = (mapping->kimLevel == seL4_KernelImageNumLevels - 1);

    /* Get PT slot to install the address in */
    lookupPTSlot_ret_t pt_ret = lookupPTSlot(image->kiRoot, mapping->kimMapAddr);

    assert(!pte_ptr_get_valid(pt_ret.ptSlot));
    assert(pt_ret.ptBitsLeft == kernelImageUntranslatedBits(mapping->kimLevel));

    /* Insert the mapping
     *
     * The mapping is inserted with global permissions as the mappings
     * are shared between multiple ASIDs in the kernel image and all
     * translation caches are fully flushed on a kernel image switch */
    *pt_ret.ptSlot = pte_new(
                         (memory_addr >> seL4_PageBits),
                         0, /* sw */
                         1, /* dirty */
                         1, /* accessed */
                         last_level,  /* global */
                         0,  /* user */
                         last_level,  /* execute */
                         last_level,  /* write */
                         last_level,  /* read */
                         1 /* valid */
                     );

    return EXCEPTION_NONE;
}

static inline pte_t Arch_kiPTMapping(kernel_image_root_t *image, vptr_t addr, word_t depth)
{
    lookupPTSlot_ret_t slot = Arch_kiLookupPTSlot(image, addr, depth);
    if (slot.ptBitsLeft > kernelImageUntranslatedBits(depth)) {
        /* Superpage mapping was used, need to generate page mapping */
        pte_t entry = *slot.ptSlot;
        word_t ppn = pte_get_ppn(entry);
        /* Calculate offset of page within the given superpage */
        word_t offset = addr & MASK(slot.ptBitsLeft);
        offset = offset & ~MASK(kernelImageUntranslatedBits(depth));
        offset = offset >> seL4_PageBits;
        /* Get the ppn of the page */
        ppn += offset;
        pte_ptr_set_ppn(&entry, ppn);
        return entry;
    } else {
        assert(slot.ptBitsLeft == kernelImageUntranslatedBits(depth));
        /* Correct page mapping used */
        return *slot.ptSlot;
    }
}

static inline void *Arch_kiPagePPtr(kernel_image_root_t *image, vptr_t addr, word_t depth)
{
    pte_t mapping = Arch_kiPTMapping(image, addr, depth);
    return Arch_kiGetPPtrFromHWPTE(&mapping);
}

exception_t Arch_kernelImageCloneEntry(kernel_image_root_t *dest, kernel_image_root_t *src, vptr_t clone_addr,
                                       word_t depth, ki_map_strategy_t strategy)
{
    /* Don't clone the root */
    assert(depth > 0);
    /* The last level doesn't translate to further levels */
    assert(depth < seL4_KernelImageNumLevels);

    /* Find the page table slot for the destination */
    lookupPTSlot_ret_t dest_slot = Arch_kiLookupPTSlot(dest, clone_addr, depth);
    assert(dest_slot.ptBitsLeft == kernelImageUntranslatedBits(depth));

    if (strategy == KIMapCopied) {
        assert(pte_ptr_get_valid(dest_slot.ptSlot));
        assert(pte_ptr_get_global(dest_slot.ptSlot));
        const unsigned char *src_data = Arch_kiPagePPtr(src, clone_addr, depth);
        unsigned char *dest_data = Arch_kiGetPPtrFromHWPTE(dest_slot.ptSlot);
        assert(dest_data != NULL);
        assert(src_data != NULL);
        memcpy(dest_data, src_data, BIT(kernelImageUntranslatedBits(depth)));
    } else {
        /* Share the page by copying the entry */
        assert(pte_ptr_get_ppn(dest_slot.ptSlot) == 0);
        assert(!pte_ptr_get_valid(dest_slot.ptSlot));
        *dest_slot.ptSlot = Arch_kiPTMapping(src, clone_addr, depth);
    }

    return EXCEPTION_NONE;
}

void Arch_setKernelImage(kernel_image_t *image)
{
    //vptr_t ret_p, s_p;
    vptr_t s_p;
    /* Copy the stack into the given addres space */
    /* Set the kernel address space to the given root */
    /* If vspace shared with user, set user to empty vspace */

    //printf("    Arch_setKernelImage: BEGIN for image %p (from ksCurKernelImage %p)\n", image, NODE_STATE(ksCurKernelImage));

    assert(image != NODE_STATE(ksCurKernelImage));

    /* The global kimage used for ASID 0 is in the ELF mapping */
    paddr_t kiRootPAddr = image->kiASID ?
        addrFromPPtr(image->kiRoot) : addrFromKPPtr(image->kiRoot);

#if 0
    asm volatile(
        "ld %[ret_p], 72(sp)\n"
        "mv %[s_p], sp\n"
        : [ret_p] "=r" (ret_p), [s_p] "=r" (s_p));
    printf("    Arch_setKernelImage: ra is %p, sp is %p\n", (void *)ret_p, (void *)s_p);
#endif
    asm volatile(
        "mv %[s_p], sp\n"
        : [s_p] "=r" (s_p));
    ksCurKernelImage->kiStackPointer = s_p;
    asm volatile("fence\n");

    if (!image->kiStackInitted) {
        /* The only kernel images with uninitialised stacks should be clones */
        assert(image->kiASID != 0);

        vptr_t stack_p = kernelStackBase();
        /* This is necessary because the stack base virtual address is at the
         * beginning of the KIRegionShared, which is mapped differently to
         * where the rest of the stack actually resides. Decrementing this
         * pointer puts us just before the end of the KIRegionPrivate, which
         * for each kernel image is instead mapped to where its stack is
         * actually meant to reside. */
        vptr_t image_p = kernelImageVPtr(image->kiRoot, stack_p - 1) + 1;

        //printf("    Arch_setKernelImage: Copying stack from base %p -> %p, switching vspace root to %lx (from %p), asid %lu.\n", (void *)stack_p, (void *)image_p, addrFromPPtr(image->kiRoot), image->kiRoot, image->kiASID);

        asm volatile(
            /* Copy stack */
            "1: \n"
            // while (stack_p != sp) {
            "beq %[stack_p], sp, 1f\n"
            "li t1, 8\n"
            // stack_p -= 8;
            "sub %[stack_p], %[stack_p], t1\n"
            // image_p -= 8:
            "sub %[image_p], %[image_p], t1\n"
            // *image_p = *stack_p;
            "ld t1, (%[stack_p])\n"
            "sd t1, (%[image_p])\n"
            // }
            "j 1b\n"
            "1: \n"
            "fence\n"
            : [stack_p] "+r" (stack_p), [image_p] "+r" (image_p)
            : "[stack_p]" (stack_p), "[image_p]" (image_p)
            : "t1", "memory"
        );

        image->kiStackPointer = ksCurKernelImage->kiStackPointer;
        image->kiStackInitted = true;
        asm volatile("fence\n");
    }

    //printf("    Arch_setKernelImage: Calling setVSpaceRoot for %lx (from %p), asid %lu.\n", kiRootPAddr, image->kiRoot, image->kiASID);
    setVSpaceRoot(kiRootPAddr, image->kiASID);
    //printf("    Arch_setKernelImage: Returned from setVSpaceRoot for %lx (from %p), asid %lu.\n", kiRootPAddr, image->kiRoot, image->kiASID);

    //printf("    Arch_setKernelImage: Setting sp to %lx\n", image->kiStackPointer);
    set_sp(image->kiStackPointer);

    //printf("    Arch_setKernelImage: END for image %p (from ksCurKernelImage %p)\n", image, NODE_STATE(ksCurKernelImage));

    NODE_STATE(ksCurKernelImage) = image;

#if 0
    asm volatile(
        "ld %[ret_p], 72(sp)\n"
        "mv %[s_p], sp\n"
        : [ret_p] "=r" (ret_p), [s_p] "=r" (s_p));
    printf("    Arch_setKernelImage: ra is %p, sp is %p\n", (void *)ret_p, (void *)s_p);
#endif
}
