(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's asan image by tools/startup/atable.py (frozen 6a35bb77e745, the start-up tool set at commit 4453a719871) from fuzz_codec.asan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's self-loops; cgif_file_fuzzer's A/AB12.v at origin/ossv/recipes c8557374ad2e gives the text only. *)
(* Read from: fuzz_codec.asan (libdiginet/fuzz_codec asan) sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422; unstripped twin sha256 b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fb000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30b34; rw_lo := 0x9f000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63d24; x_imemcpy := 0x63ca8; x_memset := 0x96efc; x_memcpy := 0x96af8; x_memiszero := 0x64254;
x_istrncpy := 0x64150; x_sealed := 0x11825; x_popfree := 0x36f20;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c8fc; x_envscan_k := 0x8c908; x_pnscan := 0x8c9c0; x_pnscan_k := 0x8c9cc;
stops_more := [0x34b94; 0x361b8; 0x54030; 0x5a3e8; 0x5a3fc; 0x5a410; 0x5fda0; 0x5fe70; 0x6d39c; 0x6e2a8; 0x6e438; 0x78190; 0x6e5a8]
|}.
Definition TFIB_TEXT_LO : Z := 0x30b34.
Definition TFIB_TEXT_N : nat := 110015.
