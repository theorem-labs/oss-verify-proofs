(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan: every address moved from cgif_file_fuzzer.asan by the address map of the two binaries, TFIB_TEXT_N = the length in words of fuzz_manifest.asan's text segment (0x68010 bytes from 0x30404). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f7000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30404; rw_lo := 0x9b000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63df4; x_imemcpy := 0x63d78; x_memset := 0x929a8; x_memcpy := 0x925a4; x_memiszero := 0x64324;
x_istrncpy := 0x64220; x_sealed := 0x117f6; x_popfree := 0x367f0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x883a8; x_envscan_k := 0x883b4; x_pnscan := 0x8846c; x_pnscan_k := 0x88478;
stops_more := [0x34464; 0x35a88; 0x54100; 0x5a4b8; 0x5a4cc; 0x5a4e0; 0x5fe70; 0x5ff40; 0x6d46c; 0x6e378; 0x6e508; 0x78260]
|}.
Definition TFIB_TEXT_LO : Z := 0x30404.
Definition TFIB_TEXT_N : nat := 106500.
