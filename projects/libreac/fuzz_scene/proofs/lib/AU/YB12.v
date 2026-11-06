(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
a_entry := 0x32b44; rw_lo := 0x9d000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x65d7c; x_imemcpy := 0x65d00; x_memset := 0x95174; x_memcpy := 0x94d70; x_memiszero := 0x662ac;
x_istrncpy := 0x661a8; x_sealed := 0x117fe; x_popfree := 0x38f30;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8ab74; x_envscan_k := 0x8ab80; x_pnscan := 0x8ac38; x_pnscan_k := 0x8ac44;
stops_more := [0x36ba4; 0x381c8; 0x56088; 0x5c440; 0x5c454; 0x5c468; 0x61df8; 0x61ec8; 0x6f3f4; 0x70300; 0x70490; 0x7a1e8]
|}.
Definition TFIB_TEXT_LO : Z := 0x32b44.
(* TFIB_TEXT_N covers the whole own .text of this image (cited-27.md (sha256 743639650077; internal record), item 1i): (.text end 0x9a4a8 - TFIB_TEXT_LO 0x32b44) / 4 = 106073, .text read from the section headers of the pinned image (sha256 e98b1ed286c1...) and equal in its unstripped twin; atable.py's donor-relocated 105929 ended at 0x9a268. Written by text_n.py (sha256 36831235bf0b; internal record). *)
Definition TFIB_TEXT_N : nat := 106073.
