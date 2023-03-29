/*
 * Copyright 2023, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

.section .text

.global set_sp

set_sp:
  mv sp, a0
  ret
