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

#ifndef __MODE_OBJECT_KERNEL_IMAGE_H
#define __MODE_OBJECT_KERNEL_IMAGE_H

/* First address of the kernel window */
#define KI_WINDOW_START  PPTR_BASE
/* Last address of the kernel window */
#define KI_WINDOW_END    0xFFFFFFFFFFFFFFFF
/* First address of the PPTR window (within kernel window) */
#define KI_PPTR_START    PPTR_BASE
/* Last address of the PPTR window */
#define KI_PPTR_END      PPTR_TOP
/* First address of the kernel device mapping window (within kernel window) */
#define KI_DEVICE_START  KDEV_BASE
/* Last addres of the kernel device mapping window */
#define KI_DEVICE_END    KI_WINDOW_END

/* Number of levels of mapping objects for PPTR region */
/* Physically mapped pages are mapped using 1GiB pages */
#define KI_MAP_PPTR_DEPTH    1lu
/* Number of levels of mapping objects for kernel device region */
/* Devices are mapped using 1GiB pages */
#define KI_MAP_DEVICE_DEPTH  KI_MAP_PPTR_DEPTH

#endif /* __MODE_OBJECT_KERNEL_IMAGE_H */
