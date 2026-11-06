(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillB3Topcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 d486901e37cd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane W, ReallocPrimary.CfW; a Theorem Labs lane cf layer, refill half 1).  rule 24: no function proved
   (kind: composition of the B3 entry and the B3 top).

   HALF 1 of the cf refill walk at cgif's image: MnRefillSeamcf.refill_B3_entry_cf from
   - MnRefillB3Rcf.refill_B3_entry_cf_ok (the entry: the run to the join state R3_J, then the inner walk), and
   - MnRefillB3cf.refill_B3_inner_cf_of_classfull (the inner walk, every case, given the class-full arm),
   under the unit facts TS (TfibSyms B) and HIOK (the walk's [inst] is A_ALLOCATOR at cgif) and one named Prop
   (the result cells are a Theorem Labs lane's refill_cells_keep_gen_cf, MnRefillB3cf.HCELLS; the image rows they read are
   ARmcf's amc_cells_owned; the budget is the layer's abudget_cf with the primary shadow, YGcfAbudget):
   - refill_B3_classfull_cf (MnRefillSeamcf.v:104): the class-full report arm (a Theorem Labs lane's report walk).
   NON-VACUITY of the Section-free premises: TS holds at cgif's B (YF0m's TfibSyms instance); HIOK holds with
   IOK := fun i => i = A_ALLOCATOR. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFk5cf YFk8cf YFkbcf YFkkcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill MnRefillSeamcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import MnRefillB3Rcf MnRefillB3cf.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Theorem refill_B3_entry_cf_of_parts : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall inst, IOK inst -> inst = A_ALLOCATOR) ->
  refill_B3_classfull_cf ->
  @refill_B3_entry_cf fx rc ci cp AImg_reply AGImg_reply B IOK.
Proof.
intros B IOK TS HIOK HCF.
exact (refill_B3_entry_cf_ok B IOK TS HIOK (refill_B3_inner_cf_of_classfull HCF)).
Qed.
End t.
