(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image B's (fuzz_grant.asan-ubsan fde52226dc48) start-up table in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v; the values are image B's, from a working branch 35735e14404 lib/B/YB12.v. *)
(* Modified by Theorem Labs, 2026-10: reproduced by atable 1ce98fbad397 (startup-set-2026-10-29, no --apply) except the order of stops_more and the per-image YK09 Require. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fb000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30984; rw_lo := 0x9f000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63f14; x_imemcpy := 0x63e98; x_memset := 0x96c94; x_memcpy := 0x96890; x_memiszero := 0x64444;
x_istrncpy := 0x64340; x_sealed := 0x11806; x_popfree := 0x36d70;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c694; x_envscan_k := 0x8c6a0; x_pnscan := 0x8c758; x_pnscan_k := 0x8c764;
stops_more := [0x349e4; 0x36008; 0x54220; 0x5a5d8; 0x5a5ec; 0x5a600; 0x5ff90; 0x60060; 0x6d58c; 0x6e498; 0x6e628; 0x6e798; 0x78380]
|}.
Definition TFIB_TEXT_LO : Z := 0x30984.
Definition TFIB_TEXT_N : nat := 109969.
