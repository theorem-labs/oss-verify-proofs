(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's asan-ubsan image by atable.py (frozen 6a35bb77e745, start-up tool set of commit 4453a719871) from fuzz_codec.asan-ubsan and its unstripped twin: image fields from the program headers (img_lo / img_hi written as lib/AU/YImgTopU's IMG_LO / IMG_TOP, each checked by reflexivity against the image's value), code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's YB12.v at commit 25e3d17bdb50 gives the text only. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libdiginet/fuzz_codec/lib/AU/YB12.v, with its module paths, addresses and numbers changed. *)
(* Generated for libdiginet/fuzz_transport's asan-ubsan image by atable.py (frozen e88affcf0526, start-up tool set of commit f1417943331) from fuzz_transport.asan-ubsan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's YB12.v at commit 25e3d17bdb50 gives the text only. *)
(* Read from: fuzz_transport.asan-ubsan (libdiginet/fuzz_transport asan-ubsan) sha256 41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4; unstripped twin sha256 e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x616000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3112c; rw_lo := 0xa5000; rw_len := 0x571000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64778; x_imemcpy := 0x646fc; x_memset := 0x9d270; x_memcpy := 0x9ce6c; x_memiszero := 0x64ca8;
x_istrncpy := 0x64ba4; x_sealed := 0x1184c; x_popfree := 0x37518;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x92c70; x_envscan_k := 0x92c7c; x_pnscan := 0x92d34; x_pnscan_k := 0x92d40;
stops_more := [0x3518c; 0x367b0; 0x54a84; 0x5ae3c; 0x5ae50; 0x5ae64; 0x607f4; 0x608c4; 0x6ddf0; 0x6ecfc; 0x6ee8c; 0x78be4; 0x6effc]
|}.
Definition TFIB_TEXT_LO : Z := 0x3112c.
Definition TFIB_TEXT_N : nat := 115998.
