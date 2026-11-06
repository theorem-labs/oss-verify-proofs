(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB12.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan-ubsan: every address moved from cgif_file_fuzzer.asan-ubsan by the address map of the two binaries, TFIB_TEXT_N = this image's text segment in words (0x68298 bytes from 0x30464) *)
(* Read from: fuzz_manifest.asan-ubsan (omx-clap-core/fuzz_manifest asan-ubsan) sha256 ca61e5c9eabc00501d5cebab7618d8c03e73419f52c9f0b9be51c8bedff96e5e; unstripped twin sha256 b9568e38145a50214b3744e4f26bfc2ec9f670eca737d4da9be2dca6a0cfc2de *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f7000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30464; rw_lo := 0x9b000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63e54; x_imemcpy := 0x63dd8; x_memset := 0x92c90; x_memcpy := 0x9288c; x_memiszero := 0x64384;
x_istrncpy := 0x64280; x_sealed := 0x117fd; x_popfree := 0x36850;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x88690; x_envscan_k := 0x8869c; x_pnscan := 0x88754; x_pnscan_k := 0x88760;
stops_more := [0x344c4; 0x35ae8; 0x54160; 0x5a518; 0x5a52c; 0x5a540; 0x5fed0; 0x5ffa0; 0x6d4cc; 0x6e3d8; 0x6e568; 0x782c0]
|}.
Definition TFIB_TEXT_LO : Z := 0x30464.
Definition TFIB_TEXT_N : nat := 106662.
