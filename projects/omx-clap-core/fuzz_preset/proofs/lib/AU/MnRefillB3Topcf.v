(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillB3Topcf.v (commit 3cae605a900a, file sha256 d486901e37cd) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; cgif's image-instance names kept where preset's B' instance carries them (AGif2cgif, AImg_cgif), CfImg_cgif -> CfImg_B, cgif's image rows mapped to preset's (YGcfImgcgif.* -> CfImgB / PresetImgRefillB / PresetImgRowsB, *cgif -> *preset); its 0 image numerals moved by symbol from cgif_file_fuzzer.asan-ubsan (pin 1c29845fe605, unstripped twin of the same build) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets, derived counts and list indices by the same stage map), 0 list indices re-picked, and 0 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane W, ReallocPrimary.CfW; a Theorem Labs lane cf layer, refill half 1).  rule 24: no function proved
   (kind: composition of the B3 entry and the B3 top).

   HALF 1 of the cf refill walk at cgif's image: MnRefillSeamcf.refill_B3_entry_cf from
   - MnRefillB3Rcf.refill_B3_entry_cf_ok (the entry: the run to the join state R3_J, then the inner walk), and
   - MnRefillB3cf.refill_B3_inner_cf_of_classfull (the inner walk, every case, given the class-full arm),
   under the unit facts TS (TfibSyms B) and HIOK (the walk's [inst] is A_ALLOCATOR at cgif) and one named Prop
   (the result cells are a prior worker's refill_cells_keep_gen_cf, MnRefillB3cf.HCELLS; the image rows they read are
   ARmcf's amc_cells_owned; the budget is the layer's abudget_cf with the primary shadow, YGcfAbudget):
   - refill_B3_classfull_cf (MnRefillSeamcf.v:104): the class-full report arm (a prior worker's report walk).
   NON-VACUITY of the Section-free premises: TS holds at cgif's B (YF0m's TfibSyms instance); HIOK holds with
   IOK := fun i => i = A_ALLOCATOR. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFk5cf YFk8cf YFkbcf YFkkcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRmodel YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG AGif0n. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import MnRefillSeamcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import MnRefillB3Rcf MnRefillB3cf.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Theorem refill_B3_entry_cf_of_parts : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall inst, IOK inst -> inst = A_ALLOCATOR) ->
  refill_B3_classfull_cf ->
  @refill_B3_entry_cf fx rc ci cp AImg_cgif AGImg_cgif B IOK.
Proof.
intros B IOK TS HIOK HCF.
exact (refill_B3_entry_cf_ok B IOK TS HIOK (refill_B3_inner_cf_of_classfull HCF)).
Qed.
End t.
