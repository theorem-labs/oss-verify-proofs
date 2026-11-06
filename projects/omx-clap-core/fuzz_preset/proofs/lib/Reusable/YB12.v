(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 c90d4fa54d43160b) by startb2/gen/gen_geom.py (sha256 51e8d4cb9a869e2c) from proofs/cgif/cgif_file_fuzzer/lib/YB12.v: every image number is computed from that ELF (program headers, symbols, asan_globals), module paths changed. *)
(* Modified by Theorem Labs, 2026-10-29: image B' of the harness fix #102 (oss-verify 5f067f673c44, facts 8f3e7e1a07f1). Read from the unstripped twin reports/preset-harness/bound-fix/9e1283d1/unstripped/fuzz_preset/fuzz_preset.asan-ubsan sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175; the pin of record is bound-fix/a3b65bd4/bin/fuzz_preset/fuzz_preset.asan-ubsan sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, equal to the twin in every SHF_ALLOC section (INSN-COMPARE-9e1283d1.md). CONTROL: the same generator on the OLD-pin twin 3b5e1a099b535acf reproduces lib/Reusable/YB12.v of origin/cold/h-mani-a4-preset-relocB in every definition except TFIB_TEXT_N, and except the header block the relocation route wrote there. TFIB_TEXT_N carries the item-1i DEFECT FIX: the rule is (end of the .text section - TFIB_TEXT_LO)/4, not (__lseek + 8 - e_entry)/4, so the window is .text [0x31460, 0xa123c) and TFIB_TEXT_N = 114551 (old pin: 114298, where relocB states 114274 and leaves `pipe` and `read` outside). GATE: 1478 STT_FUNC starts lie in B''s .text, 0 outside the window. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x601000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x31460; rw_lo := 0xa4000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64ba4; x_imemcpy := 0x64b28; x_memset := 0x9bf08; x_memcpy := 0x9bb04; x_memiszero := 0x650d4;
x_istrncpy := 0x64fd0; x_sealed := 0x11854; x_popfree := 0x37a58;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8f150; x_envscan_k := 0x8f15c; x_pnscan := 0x8f214; x_pnscan_k := 0x8f220;
stops_more := [0x356cc; 0x36cf0; 0x54eb0; 0x5b268; 0x5b27c; 0x5b290; 0x60c20; 0x60cf0; 0x6e21c; 0x6f128; 0x6f2b8; 0x79010]
|}.
Definition TFIB_TEXT_LO : Z := 0x31460.
Definition TFIB_TEXT_N : nat := 114551.
