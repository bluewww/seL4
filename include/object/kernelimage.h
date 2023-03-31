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

#include <object/structures.h>

#ifndef __OBJECT_KERNEL_IMAGE_H
#define __OBJECT_KERNEL_IMAGE_H

#include <stdint.h>
#include <types.h>
#include <util.h>
#include <api/failures.h>
#include <kernel/vspace.h>
#include <kernel/stack.h>
#include <sel4/sel4_arch/constants.h>
#include <object/structures.h>

/*
 * The kernel mapping is laid out in the following set of regions with
 * differing mapping requirements.
 *
 *      +-------------------+ 0x00000000
 *      |                   |
 *      | Userspace         |
 *      |                   |
 *      +- USER_TOP --------+
 *      +- KI_KERNEL_START -+
 *      |                   |
 *      | PPTR window       | <- G+R+W
 *      |                   |
 *      +- KI_ELF_START ----+ ki_text_start
 *      | .text             | <- X+R
 *      +-------------------+ ki_text_end / ki_switch_start
 *      | .text.switch      | <- G+X+R
 *      +-------------------+ ki_switch_end / ki_private_start
 *      | .rodata           |
 *      | .data             | <- R+W
 *      | .bss.node_local   |
 *      +-------------------+ ki_private_end / ki_private_start
 *      | .bss.idle_thread  |
 *      +-------------------+ ki_private_end / ki_shared_start
 *      | .bss              |
 *      | .bss.aligned      | <- G+R+W
 *      |                   |
 *      +- KI_ELF_END ------+ ki_shared_end
 *      |                   |
 *      +- KI_DEVICE_START -+
 *      |                   |
 *      |  Device mapping   |
 *      |                   |
 *      +- KI_KERNEL_END ---+
 *
 * This effectively breaks up the kernel's static virtual memory into 6
 * sections: boot, text, switch, private, idle thread, and shared.
 *
 * The boot section is completely discarded and the memory repurposed as
 * untyped memory after boot.
 *
 * The text section is copied for each kernel image with identical
 * contents in each copy which are never modified. Similarly, the
 * private section is copied between each image as, after boot and
 * initialisation, the contents are never changed.
 *
 * The switch section is marked as a global mapping and shared between
 * every image. It contains a minimal amount of code to completely
 * switch between images. (on arm this operation is non-atomic as it the
 * ASID and VSpace root are switched separately)
 *
 * The idle thread section contains the idle thread context for each
 * node for a given kernel image. These are never modified once
 * configured at boot except to save and restore context, thus they can
 * be copied in the same manner as the private section.
 *
 * The shared section contains all the dynamic global state for the
 * kernel and is mapped global and shared across all images.
 *
 * The freemem area maps all physical memory that backs non-device
 * untypeds and is also mapped globally into every image. These regions
 * are usually mapped using larger pages (1MiB, 4MiB, or 1GiB) and so do
 * not require a full set of intermediary mappings.
 */

#define KI_MAP_ELF_DEPTH       (seL4_KernelImageNumLevels - 1)

#define KI_ELF_REGION_ADDR(r) (vptr_t)(r)
#define KI_ELF_REGION(r) \
    .kirStart = KI_ELF_REGION_ADDR(r##_start), \
    .kirEnd   = KI_ELF_REGION_ADDR(r##_end)

extern const unsigned char ki_elf_start[], ki_elf_end[];
extern const unsigned char ki_text_start[], ki_text_end[];
extern const unsigned char ki_switch_start[], ki_switch_end[];
extern const unsigned char ki_private_start[], ki_private_end[];
extern const unsigned char ki_idle_thread_start[], ki_idle_thread_end[];
extern const unsigned char ki_shared_start[], ki_shared_end[];

/* Kernel region identifiers */
enum ki_region {
    /* Addresses in the statically mapped region (not freemem) */
    KIRegionElf = 0,
    KIRegionText = 1,
    KIRegionSwitch = 2,
    KIRegionPrivate = 3,
    KIRegionIdleThread = 4,
    KIRegionShared = 5,
    /* Continuous physical memory region */
    KIRegionPhysPtr = 6,
    /* Device mappings */
    KIRegionDevice = 7,
    /* All kernel memory regions (static + freemem) */
    KIRegionKernelWindow = 8,
    KINumRegions = 9,
};
typedef word_t ki_region_t;

static inline char *kernel_image_region_name(ki_region_t region)
{
    switch (region) {
    case KIRegionElf: return "KIRegionElf";
    case KIRegionText: return "KIRegionText";
    case KIRegionSwitch: return "KIRegionSwitch";
    case KIRegionPrivate: return "KIRegionPrivate";
    case KIRegionIdleThread: return "KIRegionIdleThread";
    case KIRegionShared: return "KIRegionShared";
    case KIRegionPhysPtr: return "KIRegionPhysPtr";
    case KIRegionDevice: return "KIRegionDevice";
    case KIRegionKernelWindow: return "KIRegionKernelWindow";
    default: return "(unknown region)";
    }
}

enum ki_map_strategy {
    KIMapNone,
    KIMapShared,
    KIMapCopied,
    KIMapPhysPtr,
    KIMapDevice,
};
typedef word_t ki_map_strategy_t;

static inline char *kernel_image_strategy_name(ki_map_strategy_t strategy)
{
    switch (strategy) {
    case KIMapNone: return "KIMapNone";
    case KIMapShared: return "KIMapShared";
    case KIMapCopied: return "KIMapCopied";
    case KIMapPhysPtr: return "KIMapPhysPtr";
    case KIMapDevice: return "KIMapDevice";
    default: return "(unknown strategy)";
    }
}

/* A bounds and size of a particular region */
struct ki_region_range {
    /* The first address in the region */
    vptr_t kirStart;

    /* The address immediately after the end of the region */
    vptr_t kirEnd;

    /* The strategy used to map the region */
    ki_map_strategy_t kirStrategy;

    /* Rights to use when mapping */
    vm_rights_t kirRights;
};
typedef struct ki_region_range ki_region_range_t;

/* Specification for mapping of a single memory for a kernel image */
typedef struct {
    word_t kimLevel;
    vptr_t kimMapAddr;
    ki_region_t kimRegion;
} ki_mapping_t;

#include <arch/object/kernelimage.h>

/* Descriptors of every kernel image region */
extern const ki_region_range_t kernel_image_regions[KINumRegions];

/* The number of kernel memories needed for each level of the virtual
 * address space */
extern word_t kernel_image_level_count[seL4_KernelImageNumLevels];

/** Static array describing the kernel image level sizes in bits */
extern const word_t kernel_image_level_size_bits[seL4_KernelImageNumLevels];

/** Static array describing the kernel image level index bits */
extern const word_t kernel_image_level_index_bits[seL4_KernelImageNumLevels];

static inline void dump_kernel_image_regions(void)
{
    for (int region = 0; region < KINumRegions; region += 1) {
        const ki_region_range_t *range = &kernel_image_regions[region];
        printf(
            "%20s (%14s; %6p): %16p -> %16p\n",
            kernel_image_region_name(region),
            kernel_image_strategy_name(range->kirStrategy),
            (void *)range->kirRights,
            (void *)range->kirStart,
            (void *)range->kirEnd
        );
    }
}

/**
 * Get the size of KernelMemory obects at each level of the kernel image
 * virtual address space in bits starting from the topmost level.
 */
static inline word_t kernelImageLevelSizeBits(seL4_Word level)
{
    if (level < seL4_KernelImageNumLevels) {
        return kernel_image_level_size_bits[level];
    } else {
        return 0;
    }
}

/**
 * Get the number of bits indexed at each level of the kernel image
 * virtual address space starting from the topmost level.
 */
static inline word_t kernelImageLevelIndexBits(seL4_Word level)
{
    if (level < seL4_KernelImageNumLevels) {
        return kernel_image_level_index_bits[level];
    } else {
        return 0;
    }
}

/**
 * Get the number of bits left untranslated at a given level of the
 * kernel image.
 */
static inline word_t kernelImageUntranslatedBits(seL4_Word level)
{
    assert(level < seL4_KernelImageNumLevels);

    word_t shift_bits = seL4_KernelImageTranslationBits;
    for (word_t l = 0; l < level; l += 1) {
        shift_bits -= kernelImageLevelIndexBits(l);
    }
    return shift_bits;
}

static inline word_t kernelImageRequiredMemories(void)
{
    word_t kernel_image_required_memories = 0;
    for (word_t level = 0; level < seL4_KernelImageNumLevels; level += 1) {
        kernel_image_required_memories += kernel_image_level_count[level];
    }
    return kernel_image_required_memories;
}

static inline word_t kernelImagePagesCopied(ki_region_t region)
{
    if (region > KINumRegions) {
        return 0;
    } else if (kernel_image_regions[region].kirStrategy != KIMapCopied) {
        return 0;
    } else {
        const ki_region_range_t *range = &kernel_image_regions[region];
        word_t start = range->kirStart & ~MASK(seL4_PageBits);
        word_t pages = (range->kirEnd - start) >> seL4_PageBits;
        if ((word_t)(range->kirEnd) & MASK(seL4_PageBits)) {
            pages += 1;
        }
        return pages;
    }
}

/* Initialise the number of memories needed to map each level of the
 * kernel virtual address space. */
void initKernelImageLevelCount(void);

/** Copy the level count to the boot info frame */
static inline void copyKernelImageLevelCount(word_t bootinfo_count[seL4_KernelImageNumLevels])
{
    for (word_t level = 0; level < seL4_KernelImageNumLevels; level += 1) {
        bootinfo_count[level] = kernel_image_level_count[level];
    }
}

/* Switch to the given kernel image if it is valid.
 *
 * When chaning kernel images in a configuration where the kernel and
 * user share a single virtual address space this will also switch to a
 * virtual address space with no user-level mappings. */
static inline exception_t setKernelImage(kernel_image_t *image)
{
    assert(image != NULL);

    if (likely(image->kiRunnable)) {
        if (unlikely(image != NODE_STATE(ksCurKernelImage))) {
            //printf("   setKernelImage: Calling Arch_setKernelImage for image %p (root %p, asid %lu)\n", image, image->kiRoot, image->kiASID);
            /* Note: Arch_setKernelImage is responsible for setting
             * ksCurKernelImage to the new image. */
            Arch_setKernelImage(image);
            //printf("   setKernelImage: Returned from Arch_setKernelImage for image %p (root %p, asid %lu)\n", image, image->kiRoot, image->kiASID);
        }
        return EXCEPTION_NONE;
    } else {
        return EXCEPTION_FAULT;
    }
}

/* Switch to the global user address space with no user-level mappings
 * and the initial kernel image. */
static inline void switchToIdleKernelImage(void)
{
    exception_t status;
    //printf("  switchToIdleKernelImage: Calling setKernelImage for domain %lu's image %p (root %p, asid %lu)\n", ksDomScheduleIdx, &ksDomKernelImage[ksDomScheduleIdx], ksDomKernelImage[ksDomScheduleIdx].kiRoot, ksDomKernelImage[ksDomScheduleIdx].kiASID);
    status = setKernelImage(&ksDomKernelImage[ksDomScheduleIdx]);
    //printf("  switchToIdleKernelImage: Returned from setKernelImage for domain %lu's image %p (root %p, asid %lu)\n", ksDomScheduleIdx, &ksDomKernelImage[ksDomScheduleIdx], ksDomKernelImage[ksDomScheduleIdx].kiRoot, ksDomKernelImage[ksDomScheduleIdx].kiASID);
    assert(status == EXCEPTION_NONE);
}

/* Get the base address of the kernel stack for the current node */
static inline vptr_t kernelStackBase(void)
{
    return (vptr_t)(&kernel_stack_alloc[CURRENT_CPU_INDEX()][BIT(CONFIG_KERNEL_STACK_BITS)]);
}

/* Get a virtual address to a virtual address in another kernel image */
static inline vptr_t kernelImageVPtr(kernel_image_root_t *root, vptr_t addr)
{
    paddr_t paddr = Arch_kernelImagePaddr(root, addr);
    return (vptr_t)(ptrFromPAddr(paddr));
}

/* Identify the start of the next page of the numbered colour. */
static inline paddr_t locateNextPageOfColour(int i, paddr_t memory_addr)
{
    /* The colour bits are the first n page bits */
    assert(i < BIT(CONFIG_NUM_COLOUR_BITS));

    /* Ensure we're in the right colour.
     * Note this is will just use one colour per domain, meaning any colours
     * greater than the number of domains will be wasted. However, on L2 cache
     * hardware with more colours than domains, one can avoid wasting space by
     * configuring a smaller NUM_COLOUR_BITS to reduce the number of actual
     * hardware colour bits used to partition the L2 cache for each domain. */
    /* avoid skipping page if at beginning of next group of (2^n + 1) pages */
    memory_addr -= 1;
    memory_addr &= ~MASK(PAGE_BITS + CONFIG_NUM_COLOUR_BITS);
    memory_addr |= i << PAGE_BITS;

    /* Advance to the next page of this colour. */
    return memory_addr + BIT(PAGE_BITS + CONFIG_NUM_COLOUR_BITS);
}

/* Return whether the memory region at the given address of the given size lies
 * wholly within the same page of the numbered colour. */
static inline bool_t inPageOfColour(int i, paddr_t memory_addr, paddr_t size)
{
    assert(i < BIT(CONFIG_NUM_COLOUR_BITS));
    assert(size > 0);

    /* region starts in a page of the numbered colour */
    if ((i << PAGE_BITS) !=
        (memory_addr & MASK(PAGE_BITS + CONFIG_NUM_COLOUR_BITS) &
            ~MASK(PAGE_BITS))) {
        return false;
    }

    /* region is wholly in the same page */
    return (memory_addr & ~MASK(PAGE_BITS)) ==
        ((memory_addr + size - 1) & ~MASK(PAGE_BITS));
}

/* Find the level and virtual address at which the next memory should be
 * mapped */
ki_mapping_t locateNextKernelMemory(kernel_image_t *image);

/* Map a given kernel memory into the specified location in the image
 *
 * This should be passed a kernel image with a memory of sufficient size
 * for the given level and addres without a mapping at the specified
 * level or address.
 */
exception_t kernelMemoryMap(kernel_image_t *image, ki_mapping_t *mapping, void *memory_addr);

/**
 * Copy all of the duplicated data and shared mappings from a source
 * kernel image to a writeable destination image.
 */
exception_t kernelImageClone(kernel_image_t *dest, kernel_image_t *src);

/* Bind a kernel image to a given vspace */
exception_t kernelImageBindVSpace(kernel_image_t *image, asid_t vspace_asid);

#endif /* __OBJECT_KERNEL_IMAGE_H */
