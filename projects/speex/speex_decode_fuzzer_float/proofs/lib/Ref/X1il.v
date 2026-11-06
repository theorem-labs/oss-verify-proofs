(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition A_ogg_page_eos            : Z := 0x28b4c.
Definition A_ogg_page_granulepos     : Z := 0x28b5c.
Definition A_ogg_page_serialno       : Z := 0x28bbc.
Definition A_ogg_page_packets        : Z := 0x28bec.
Definition A_ogg_stream_init         : Z := 0x28c2c.
Definition A_ogg_stream_clear        : Z := 0x28ce4.
Definition A_ogg_page_checksum_set   : Z := 0x28d40.
Definition A_os_update_crc           : Z := 0x28dd4.
Definition A_os_body_expand          : Z := 0x28f30.
Definition A_os_lacing_expand        : Z := 0x28fdc.
Definition A_ogg_sync_init           : Z := 0x290a0.
Definition A_ogg_sync_clear          : Z := 0x290bc.
Definition A_ogg_sync_buffer         : Z := 0x29100.
Definition A_ogg_sync_wrote          : Z := 0x291ec.
Definition A_ogg_sync_pageseek       : Z := 0x29214.
Definition A_ogg_sync_pageout        : Z := 0x29428.
Definition A_ogg_stream_pagein       : Z := 0x29494.
Definition A_ogg_stream_reset_serialno : Z := 0x29878.
Definition A_ogg_stream_packetout    : Z := 0x298c4.
Definition A_packetout               : Z := 0x298e0.

Definition A_malloc                  : Z := 0x2a634.
Definition A_free                    : Z := 0x2a4f4.
Definition A_realloc                 : Z := 0x2bea0.
Definition A_memchr                  : Z := 0x32650.
Definition A_memcmp                  : Z := 0x3271c.
Definition A_memcpy                  : Z := 0x3274c.
Definition A_memmove                 : Z := 0x32b50.

Definition A_crc_lookup              : Z := 0x138f4.
