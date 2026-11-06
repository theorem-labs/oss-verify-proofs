(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci's asan image by tools/startup/atable.py (commit 8cd71d3a4bb, frozen 2d236e51ad70) from fuzz_uci.asan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's A/AB12.v at origin/ossv/recipes c8557374ad2e gives the text only. *)
(* Read from: fuzz_uci.asan (reac-repacer/fuzz_uci asan) sha256 6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d; unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f4000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2fbf0; rw_lo := 0x98000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x627c0; x_imemcpy := 0x62744; x_memset := 0x90754; x_memcpy := 0x90350; x_memiszero := 0x62cf0;
x_istrncpy := 0x62bec; x_sealed := 0x117fe; x_popfree := 0x35fdc;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x86158; x_envscan_k := 0x86164; x_pnscan := 0x8621c; x_pnscan_k := 0x86228;
stops_more := [0x33c50; 0x35274; 0x52acc; 0x58e84; 0x58e98; 0x58eac; 0x5e83c; 0x5e90c; 0x6be38; 0x6cd44; 0x6ced4; 0x76c2c; 0x6d044]
|}.
Definition TFIB_TEXT_LO : Z := 0x2fbf0.
Definition TFIB_TEXT_N : nat := 104358.
