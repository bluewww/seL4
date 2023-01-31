/*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

#pragma once

#include <util.h>
#include <arch/linker.h>

/* code that is only used during kernel bootstrapping */
#define BOOT_CODE SECTION(".boot.text")

/* read-only data only used during kernel bootstrapping */
#define BOOT_RODATA SECTION(".boot.rodata")

/* read/write data only used during kernel bootstrapping */
#define BOOT_DATA SECTION(".boot.data")

/* node-local bss data that is only used during kernel bootstrapping */
#define BOOT_BSS SECTION(".boot.bss")

/* data will be aligned to n bytes in a special BSS section */
#define ALIGN_BSS(n) ALIGN(n) SECTION(".bss.aligned")

/* non-shared bss data that is not shared between multiple kernel images*/
#define KERNEL_NODE_LOCAL SECTION(".bss.node_local")

/* the idle thread TCB block*/
#define KERNEL_IDLE_THREAD SECTION(".bss.idle_thread")

/* globally mapped code for switching kernel address space */
#define KERNEL_CODE_SWITCH SECTION(".text.switch")

/* data that will be mapped into and permitted to be used in the restricted SKIM
 * address space */
#define SKIM_DATA SECTION(".skim.data")

/* bss data that is permitted to be used in the restricted SKIM address space */
#define SKIM_BSS SECTION(".skim.bss")


