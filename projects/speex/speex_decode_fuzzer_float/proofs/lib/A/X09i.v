(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.

Module B_TWIN.

Open Scope Z_scope.

Definition A_ogg_page_eos            : Z := 0xc10fc.
Definition A_ogg_page_granulepos     : Z := 0xc110c.
Definition A_ogg_page_serialno       : Z := 0xc116c.
Definition A_ogg_page_packets        : Z := 0xc119c.
Definition A_ogg_stream_init         : Z := 0xc11dc.
Definition A_ogg_stream_clear        : Z := 0xc1294.
Definition A_ogg_page_checksum_set   : Z := 0xc12f0.
Definition A_os_update_crc           : Z := 0xc1384.
Definition A_os_body_expand          : Z := 0xc14e0.
Definition A_os_lacing_expand        : Z := 0xc158c.
Definition A_ogg_sync_init           : Z := 0xc1650.
Definition A_ogg_sync_clear          : Z := 0xc166c.
Definition A_ogg_sync_buffer         : Z := 0xc16b0.
Definition A_ogg_sync_wrote          : Z := 0xc179c.
Definition A_ogg_sync_pageseek       : Z := 0xc17c4.
Definition A_ogg_sync_pageout        : Z := 0xc19d8.
Definition A_ogg_stream_pagein       : Z := 0xc1a44.
Definition A_ogg_stream_reset_serialno : Z := 0xc1e28.
Definition A_ogg_stream_packetout    : Z := 0xc1e74.
Definition A_packetout               : Z := 0xc1e90.

Definition oe_malloc                 : Z := 0x67f84.
Definition oe_free                   : Z := 0x67f80.
Definition oe_realloc                : Z := 0x67f8c.
Definition oe_memchr                 : Z := 0x56ce4.
Definition oe_memcpy                 : Z := 0x663fc.
Definition oe_memmove                : Z := 0x663f8.
Definition oe_memset                 : Z := 0x663f4.

Definition A_crc_lookup              : Z := 0x279d0.
End B_TWIN.

Open Scope Z_scope.

Definition A_ogg_page_eos            : Z := 0xb89cc.
Definition A_ogg_page_granulepos     : Z := 0xb89dc.
Definition A_ogg_page_serialno       : Z := 0xb8a3c.
Definition A_ogg_page_packets        : Z := 0xb8a6c.
Definition A_ogg_stream_init         : Z := 0xb8aac.
Definition A_ogg_stream_clear        : Z := 0xb8b64.
Definition A_ogg_page_checksum_set   : Z := 0xb8bc0.
Definition A_os_update_crc           : Z := 0xb8c54.
Definition A_os_body_expand          : Z := 0xb8db0.
Definition A_os_lacing_expand        : Z := 0xb8e5c.
Definition A_ogg_sync_init           : Z := 0xb8f20.
Definition A_ogg_sync_clear          : Z := 0xb8f3c.
Definition A_ogg_sync_buffer         : Z := 0xb8f80.
Definition A_ogg_sync_wrote          : Z := 0xb906c.
Definition A_ogg_sync_pageseek       : Z := 0xb9094.
Definition A_ogg_sync_pageout        : Z := 0xb92a8.
Definition A_ogg_stream_pagein       : Z := 0xb9314.
Definition A_ogg_stream_reset_serialno : Z := 0xb96f8.
Definition A_ogg_stream_packetout    : Z := 0xb9744.
Definition A_packetout               : Z := 0xb9760.

Definition oe_malloc                 : Z := 0x67e98.
Definition oe_free                   : Z := 0x67e94.
Definition oe_realloc                : Z := 0x67ea0.
Definition oe_memchr                 : Z := 0x56bf8.
Definition oe_memcpy                 : Z := 0x66310.
Definition oe_memmove                : Z := 0x6630c.
Definition oe_memset                 : Z := 0x66308.

Definition A_crc_lookup              : Z := 0x279d0.
