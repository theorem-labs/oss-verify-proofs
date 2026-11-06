(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci's asan-ubsan image by atable.py (frozen 42e18a7eef50, start-up tool set of commit dbb5a97ad14) from fuzz_uci.asan-ubsan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's YB12.v at commit 25e3d17bdb50 gives the text only. *)
(* Read from: fuzz_uci.asan-ubsan (reac-repacer/fuzz_uci asan-ubsan) sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc; unstripped twin sha256 8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16 *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f4000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2fbf0; rw_lo := 0x98000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x627c0; x_imemcpy := 0x62744; x_memset := 0x9085c; x_memcpy := 0x90458; x_memiszero := 0x62cf0;
x_istrncpy := 0x62bec; x_sealed := 0x117fe; x_popfree := 0x35fdc;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x86260; x_envscan_k := 0x8626c; x_pnscan := 0x86324; x_pnscan_k := 0x86330;
stops_more := [0x33c50; 0x35274; 0x52acc; 0x58e84; 0x58e98; 0x58eac; 0x5e83c; 0x5e90c; 0x6be38; 0x6cd44; 0x6ced4; 0x76c2c; 0x6d044]
|}.
Definition TFIB_TEXT_LO : Z := 0x2fbf0.
Definition TFIB_TEXT_N : nat := 104424.
