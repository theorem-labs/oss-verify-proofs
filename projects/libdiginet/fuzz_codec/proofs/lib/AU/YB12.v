(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's asan-ubsan image by atable.py (frozen 6a35bb77e745, start-up tool set of commit 4453a719871) from fuzz_codec.asan-ubsan and its unstripped twin: image fields from the program headers (img_lo / img_hi written as lib/AU/YImgTopU's IMG_LO / IMG_TOP, each checked by reflexivity against the image's value), code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's YB12.v at commit 25e3d17bdb50 gives the text only. *)
(* Read from: fuzz_codec.asan-ubsan (libdiginet/fuzz_codec asan-ubsan) sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3; unstripped twin sha256 43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266 *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fc000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30c84; rw_lo := 0xa0000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63e74; x_imemcpy := 0x63df8; x_memset := 0x97834; x_memcpy := 0x97430; x_memiszero := 0x643a4;
x_istrncpy := 0x642a0; x_sealed := 0x11825; x_popfree := 0x37070;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8d234; x_envscan_k := 0x8d240; x_pnscan := 0x8d2f8; x_pnscan_k := 0x8d304;
stops_more := [0x34ce4; 0x36308; 0x54180; 0x5a538; 0x5a54c; 0x5a560; 0x5fef0; 0x5ffc0; 0x6d4ec; 0x6e3f8; 0x6e588; 0x782e0; 0x6e6f8]
|}.
Definition TFIB_TEXT_LO : Z := 0x30c84.
Definition TFIB_TEXT_N : nat := 110521.
