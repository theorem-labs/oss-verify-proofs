(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_segconf image B by atable.py e88affcf0526 (the start-up tool set of record at tools commit f1417943331) from fuzz_segconf.asan-ubsan and its unstripped twin; TFIB_TEXT_N covers this image's own whole .text (0x31f60, 113453 words); stops_more is the image's 13 self-loops; module paths changed. *)
(* Read from: fuzz_segconf.asan-ubsan (reac-pw/fuzz_segconf asan-ubsan) sha256 c3796c0b38f3666f32a3ecff43c9fdb55ead356833af6013a07c404bd0254509; unstripped twin sha256 80e82127e8ca1e8b2ee142f113e0e529fd7b8052d654e8dfc120fd8d4ae40a21 *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x602000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x31f60; rw_lo := 0xa4000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x68298; x_imemcpy := 0x6821c; x_memset := 0x9afd4; x_memcpy := 0x9aba0; x_memiszero := 0x687c8;
x_istrncpy := 0x686c4; x_sealed := 0x11840; x_popfree := 0x3842c;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x909a4; x_envscan_k := 0x909b0; x_pnscan := 0x90a68; x_pnscan_k := 0x90a74;
stops_more := [0x360a0; 0x376c4; 0x58240; 0x5e848; 0x5e85c; 0x5e870; 0x64314; 0x643e4; 0x71910; 0x7281c; 0x729ac; 0x7c704; 0x72b1c]
|}.
Definition TFIB_TEXT_LO : Z := 0x31f60.
Definition TFIB_TEXT_N : nat := 113453.
