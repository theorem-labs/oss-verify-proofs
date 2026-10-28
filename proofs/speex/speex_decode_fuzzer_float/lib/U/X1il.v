(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition A_ogg_page_eos            : Z := 0x2ff18.
Definition A_ogg_page_granulepos     : Z := 0x2ff28.
Definition A_ogg_page_serialno       : Z := 0x2ff88.
Definition A_ogg_page_packets        : Z := 0x2ffb8.
Definition A_ogg_stream_init         : Z := 0x2fff8.
Definition A_ogg_stream_clear        : Z := 0x300b0.
Definition A_ogg_page_checksum_set   : Z := 0x3010c.
Definition A_os_update_crc           : Z := 0x301a0.
Definition A_os_body_expand          : Z := 0x302fc.
Definition A_os_lacing_expand        : Z := 0x303a8.
Definition A_ogg_sync_init           : Z := 0x3046c.
Definition A_ogg_sync_clear          : Z := 0x30488.
Definition A_ogg_sync_buffer         : Z := 0x304cc.
Definition A_ogg_sync_wrote          : Z := 0x305b8.
Definition A_ogg_sync_pageseek       : Z := 0x305e0.
Definition A_ogg_sync_pageout        : Z := 0x307f4.
Definition A_ogg_stream_pagein       : Z := 0x30860.
Definition A_ogg_stream_reset_serialno : Z := 0x30c44.
Definition A_ogg_stream_packetout    : Z := 0x30c90.
Definition A_packetout               : Z := 0x30cac.

Definition A_malloc                  : Z := 0x31a00.
Definition A_free                    : Z := 0x318c0.
Definition A_realloc                 : Z := 0x3326c.
Definition A_memchr                  : Z := 0x39b60.
Definition A_memcmp                  : Z := 0x39c2c.
Definition A_memcpy                  : Z := 0x39c5c.
Definition A_memmove                 : Z := 0x3a060.

Definition A_crc_lookup              : Z := 0x138ec.
