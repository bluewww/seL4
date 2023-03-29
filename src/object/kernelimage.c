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

#include <types.h>
#include <assert.h>
#include <util.h>
#include <object/kernelimage.h>
#include <kernel/vspace.h>
#include <api/types.h>
#include <sel4/sel4_arch/constants.h>

/* The number of kernel memories needed for each level of the virtual
 * address space */
word_t kernel_image_level_count[seL4_KernelImageNumLevels];

/** The bits resolved by each level of the kernel image virtual address space */
const word_t kernel_image_level_index_bits[seL4_KernelImageNumLevels] = SEL4_KERNEL_IMAGE_LEVEL_INDEX_BITS;

/** The size in bits of each level of the kernel image virtual address space */
const word_t kernel_image_level_size_bits[seL4_KernelImageNumLevels] = SEL4_KERNEL_IMAGE_LEVEL_SIZE_BITS;

const ki_region_range_t kernel_image_regions[KINumRegions] = {
    [KIRegionElf] = {
        KI_ELF_REGION(ki_elf),
        .kirStrategy = KIMapNone,
        .kirRights = VMKernelOnly,
    },
    [KIRegionText] = {
        KI_ELF_REGION(ki_text),
        .kirStrategy = KIMapCopied,
        .kirRights = VMReadOnly,
    },
    [KIRegionSwitch] = {
        KI_ELF_REGION(ki_switch),
        .kirStrategy = KIMapShared,
        .kirRights = VMReadOnly,
    },
    [KIRegionPrivate] = {
        KI_ELF_REGION(ki_private),
        .kirStrategy = KIMapCopied,
        .kirRights = VMReadWrite,
    },
    [KIRegionIdleThread] = {
        KI_ELF_REGION(ki_idle_thread),
        .kirStrategy = KIMapCopied,
        .kirRights = VMReadWrite,
    },
    [KIRegionShared] = {
        KI_ELF_REGION(ki_shared),
        .kirStrategy = KIMapShared,
        .kirRights = VMReadWrite,
    },
    [KIRegionPhysPtr] = {
        .kirStart = KI_PPTR_START,
        .kirEnd = KI_PPTR_END,
        .kirStrategy = KIMapPhysPtr,
        .kirRights = VMReadWrite,
    },
    [KIRegionDevice] = {
        .kirStart = KI_DEVICE_START,
        .kirEnd = KI_DEVICE_END,
        .kirStrategy = KIMapDevice,
        .kirRights = VMReadWrite,
    },
    [KIRegionKernelWindow] = {
        .kirStart = KI_WINDOW_START,
        .kirEnd = KI_WINDOW_END,
        .kirStrategy = KIMapNone,
        .kirRights = VMKernelOnly,
    },
};

/* Find the number of kernel image memories needed to fill the space
 * between two addresses */
static inline word_t countKernelImageSpanMemories(vptr_t start_addr, vptr_t end_addr, word_t unresolved_bits)
{
    word_t memories = 0;

    if (end_addr & MASK(unresolved_bits)) {
        memories += 1;
    }

    if (unresolved_bits >= seL4_WordBits) {
        /* Left shift >= WORD_BITS on a word is UB */
        return memories;
    }

    word_t start = start_addr >> unresolved_bits;
    word_t end = end_addr >> unresolved_bits;
    printf("%p => %p (%p)\n", (void *)start_addr, (void *)end_addr, (void *)MASK(unresolved_bits));

    if (end >= start) {
        memories += end - start;
        return memories;
    } else {
        return 0;
    }
}

/* Find the number of memories needed to resolve the address up to the unresolve bits */
static inline word_t countKernelImageMemories(const ki_region_range_t *region, word_t unresolved_bits)
{
    return countKernelImageSpanMemories(region->kirStart, region->kirEnd, unresolved_bits);
}

/* Count the number of kernel memories in the intersection of two regions */
static inline word_t countIntersectingKernelImageMemories(const ki_region_range_t *region_a, const ki_region_range_t *region_b, word_t unresolved_bits)
{
    vptr_t start = region_a->kirStart;
    if (region_a->kirStart < region_b->kirStart) {
        start = region_b->kirStart;
    }

    vptr_t end = region_b->kirEnd;
    if (region_a->kirEnd < region_b->kirEnd) {
        end = region_a->kirEnd;
    }

    return countKernelImageSpanMemories(start, end, unresolved_bits);
}

/* Clone the region at the specified depth */
static exception_t kernelImageCloneRegion(kernel_image_t *dest, kernel_image_t *src, const ki_region_range_t *region,
                                          word_t depth)
{
    word_t untranslated_bits = kernelImageUntranslatedBits(depth);

    /* Find the number of entries to translate */
    word_t entries = ((word_t)region->kirEnd - (word_t)region->kirStart) >> untranslated_bits;
    if ((word_t)region->kirEnd & MASK(untranslated_bits)) {
        entries += 1;
    }

    /* Find the address of the first entry */
    vptr_t clone_addr = (word_t)region->kirStart & ~(MASK(untranslated_bits));
    for (word_t idx = 0; idx < entries; idx += 1) {

        printf(
            "%s %p at level %lu of %s\n",
            kernel_image_strategy_name(region->kirStrategy),
            (void *)clone_addr,
            depth,
            kernel_image_region_name(region - kernel_image_regions)
        );

        exception_t err = Arch_kernelImageCloneEntry(dest->kiRoot, src->kiRoot, clone_addr, depth, region->kirStrategy);
        if (err == EXCEPTION_LOOKUP_FAULT && region->kirStrategy == KIMapDevice) {
            /* Lookup fault indicates end of device region */
            break;
        } else if (err != EXCEPTION_NONE) {
            return err;
        }

        /* Address for next entry */
        clone_addr +=  BIT(untranslated_bits);
    }

    return EXCEPTION_NONE;
}

void initKernelImageLevelCount(void)
{
    dump_kernel_image_regions();

    /* Count the number of intermediary mapping memories needed */
    word_t unresolved_bits = seL4_KernelImageTranslationBits;
    word_t level = 0;
    while (level < seL4_KernelImageNumLevels - 1) {
        /* Static mapping levels */
        /* Physical memory mapping levels */
        if (level >= KI_MAP_PPTR_DEPTH) {
            const ki_region_range_t *elf_region = &kernel_image_regions[KIRegionElf];

            kernel_image_level_count[level] = countKernelImageMemories(elf_region, unresolved_bits);

            if (level < KI_MAP_DEVICE_DEPTH) {
                /* Kernel image device region requires at least one
                 * mapping object at every level except the last */
                const ki_region_range_t *device_region = &kernel_image_regions[KIRegionDevice];
                kernel_image_level_count[level] += 1;
                kernel_image_level_count[level] -= countIntersectingKernelImageMemories(elf_region, device_region, unresolved_bits);
            }
        } else {
            const ki_region_range_t *region = &kernel_image_regions[KIRegionKernelWindow];
            kernel_image_level_count[level] = countKernelImageMemories(region, unresolved_bits);
        }

        printf(
            "Level %lu: %lu mapping objects\n",
            level,
            kernel_image_level_count[level]
        );

        unresolved_bits -= kernelImageLevelIndexBits(level);
        level += 1;
    }

    /* Count the number of duplicate pages needed */
    word_t duplicate_pages = 0;
    for (ki_region_t r = 0; r < KINumRegions; r += 1) {
        const ki_region_range_t *region = &kernel_image_regions[r];

        if (region->kirStrategy == KIMapCopied) {
            duplicate_pages += countKernelImageMemories(region, unresolved_bits);
            assert(
                countKernelImageMemories(region, unresolved_bits) ==
                kernelImagePagesCopied(r)
            );
        }
    }
    kernel_image_level_count[level] = duplicate_pages;

    printf(
        "Level %lu: %lu mapping objects\n",
        level,
        kernel_image_level_count[level]
    );
}

ki_mapping_t locateNextKernelMemory(kernel_image_t *image)
{
    assert(image->kiMemoriesMapped < kernelImageRequiredMemories());

    word_t next_memory = image->kiMemoriesMapped;

    /* Find the index and level at which to map the memory */
    word_t level = 0;
    word_t level_index = next_memory;
    word_t unresolved_bits = seL4_KernelImageTranslationBits;
    assert(level < seL4_KernelImageNumLevels);
    while (level_index >= kernel_image_level_count[level]) {
        level_index -= kernel_image_level_count[level];
        level += 1;
        unresolved_bits -= kernelImageLevelIndexBits(level);

        /* This loop won't exceed the total number of levels if the next
         * memory to be mapped is strictly less then the sum of all
         * memories on every level */
        assert(level < seL4_KernelImageNumLevels);
    }

    /* Find the region into which the memory will be mapped */
    ki_region_t region;
    word_t region_index = level_index;
    if (level < KI_MAP_PPTR_DEPTH) {
        /* Mapping region is 'all regions' */
        region = KIRegionKernelWindow;
    } else if (level < KI_MAP_DEVICE_DEPTH) {
        const ki_region_range_t *elf_region = &kernel_image_regions[KIRegionElf];
        word_t elf_memories = countKernelImageMemories(elf_region, unresolved_bits);
        if (region_index < elf_memories) {
            region = KIRegionElf;
        } else {
            region = KIRegionDevice;
            region_index -= elf_memories;
        }
    } else if (level < KI_MAP_ELF_DEPTH) {
        /* Mapping only non-physical regions */
        region = KIRegionElf;
    } else {
        /* Mapping a duplicated region */
        region = 0;
        while (region < KINumRegions && region_index >= kernelImagePagesCopied(region)) {
            region_index -= kernelImagePagesCopied(region);
            region += 1;

            assert(region < KINumRegions);
        }
    }

    /* Find the address at which the memory should be mapped */
    word_t shift_bits = kernelImageUntranslatedBits(level);
    vptr_t map_addr = (vptr_t)(kernel_image_regions[region].kirStart);
    map_addr &= ~(MASK(shift_bits));
    map_addr += region_index << shift_bits;

    ki_mapping_t ret = {
        .kimLevel = level,
        .kimMapAddr = map_addr,
        .kimRegion = region,
    };

    return ret;
}

exception_t kernelMemoryMap(kernel_image_t *image, ki_mapping_t *mapping, void *memory_pptr)
{
    assert(image->kiMemoriesMapped < kernelImageRequiredMemories());

    /* Zero out the entire region */
    memzero(memory_pptr, BIT(kernelImageLevelSizeBits(mapping->kimLevel)));

    printf(
        "Mapping %p at %p at level %lu of %s\n",
        (void *)addrFromPPtr(memory_pptr),
        (void *)mapping->kimMapAddr,
        mapping->kimLevel,
        kernel_image_region_name(mapping->kimRegion)
    );

    /* Map the memory into the image and update the idle root if
     * necessary */
    exception_t err = Arch_kernelMemoryMap(image, mapping, pptr_to_paddr(memory_pptr));
    if (err != EXCEPTION_NONE) {
        return err;
    }

    image->kiMemoriesMapped += 1;

    return EXCEPTION_NONE;
}

exception_t kernelImageClone(kernel_image_t *dest, kernel_image_t *src)
{
    /* Both images must be fully mapped */
    assert(dest->kiMemoriesMapped == kernelImageRequiredMemories());
    assert(src->kiMemoriesMapped == kernelImageRequiredMemories());

    /* The source must be copied and the destination must not be */
    assert(!dest->kiRunnable);
    assert(src->kiRunnable);
    assert(!dest->kiCopied);
    assert(src->kiCopied);
    assert(dest->kiRoot != NULL);
    assert(src->kiRoot != NULL);

    for (ki_region_t r = 0; r < KINumRegions; r += 1) {
        const ki_region_range_t *region = &kernel_image_regions[r];

        if (region->kirStrategy == KIMapNone) {
            continue;
        }

        /* Depth at which to index pages */
        word_t depth;
        switch (region->kirStrategy) {
        case KIMapPhysPtr:
            depth = KI_MAP_PPTR_DEPTH;
            break;
        case KIMapDevice:
            depth = KI_MAP_DEVICE_DEPTH;
            break;
        default:
            depth = KI_MAP_ELF_DEPTH;
            break;
        }

        exception_t err = kernelImageCloneRegion(dest, src, region, depth);

        if (err != EXCEPTION_NONE) {
            return err;
        }
    }

    dest->kiCopied = true;
    dest->kiRunnable = true;

    return EXCEPTION_NONE;
}

exception_t kernelImageBindVSpace(kernel_image_t *image, asid_t vspace_asid)
{
    /* Copy the root-level mappings shared between the kernel and the
     * user virtual address space. */

    findVSpaceForASID_ret_t find_ret = findVSpaceForASID(vspace_asid);
    if (unlikely(find_ret.status != EXCEPTION_NONE)) {
        printf("kernelImageBindVSpace: ASID lookup failed with exception %lu", find_ret.status);
        return find_ret.status;
    }
    vspace_root_t *vspace_root = find_ret.vspace_root;

    /* If the kernel user share mappings, the root objects should have the
     * same size and type */
    assert(seL4_VSpaceBits == kernelImageLevelSizeBits(0));

    /* Find the number of bits needed to isolate the root index */
    word_t shift_bits = kernelImageUntranslatedBits(1);
    word_t index_bits = kernelImageLevelIndexBits(0);

    /* We use a base index and a number of entries here so that the
     * condition has an upper bound that won't be missed by means of
     * integer overflow.  The KI_WINDOW_END refers to the last entry, so
     * the range must be inclusive of it */
    word_t base_index = (KI_WINDOW_START >> shift_bits) & MASK(index_bits);
    word_t num_entries = (((KI_WINDOW_END - KI_WINDOW_START) >> shift_bits) & MASK(index_bits)) + 1;

    for (word_t entry = 0; entry < num_entries; entry += 1) {
        /* XXX: printf("copying entry %lu\n", base_index + entry); */
        vspace_root[base_index + entry] = image->kiRoot[base_index + entry];
    }

    printf("kernelImageBindVSpace: Completed for image %p, asid %lu.\nThe asid points to vspace_root %p, which we think should be the same as %p.\n",
        image, vspace_asid, vspace_root, riscvKSASIDTable[vspace_asid >> asidLowBits]->array[vspace_asid & MASK(asidLowBits)]);

    return EXCEPTION_NONE;
}
