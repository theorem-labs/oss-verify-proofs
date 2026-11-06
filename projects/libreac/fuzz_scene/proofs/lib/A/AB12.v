(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_scene by a Theorem Labs lane's start-up collector (tools/startup, ColA of 2026-10-28) from scene's pinned image; by a Theorem Labs lane. *)
(* Modified by Theorem Labs, 2026-10: TFIB_TEXT_N re-emitted by a Theorem Labs lane's frozen atable.py (sha256 b9aa677211b7968b, a working branch 74f10defbdd): the donor's .text end relocated by the code before it; donor control byte-equal on cgif's released A/AB12.v and YB12.v. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f9000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x32b18; rw_lo := 0x9d000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x65d50; x_imemcpy := 0x65cd4; x_memset := 0x94e40; x_memcpy := 0x94a3c; x_memiszero := 0x66280;
x_istrncpy := 0x6617c; x_sealed := 0x117fe; x_popfree := 0x38f04;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8a840; x_envscan_k := 0x8a84c; x_pnscan := 0x8a904; x_pnscan_k := 0x8a910;
stops_more := [0x36b78; 0x3819c; 0x5605c; 0x5c414; 0x5c428; 0x5c43c; 0x61dcc; 0x61e9c; 0x6f3c8; 0x702d4; 0x70464; 0x7a1bc]
|}.
Definition TFIB_TEXT_LO : Z := 0x32b18.
(* TFIB_TEXT_N covers the whole own .text of this image (cited-27.md (sha256 743639650077; internal record), item 1i): (.text end 0x9a174 - TFIB_TEXT_LO 0x32b18) / 4 = 105879, .text read from the section headers of the pinned image (sha256 43654a025fd0...) and equal in its unstripped twin; atable.py's donor-relocated 105855 ended at 0x9a114. Written by text_n.py (sha256 36831235bf0b; internal record). *)
Definition TFIB_TEXT_N : nat := 105879.
