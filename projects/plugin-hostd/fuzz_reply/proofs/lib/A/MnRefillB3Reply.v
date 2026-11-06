(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillB3Cgif.v (commit f01d79f3fb5, cf refill round 3; file sha256 94efbdcb8a75) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane W, ReallocPrimary.CfW; a Theorem Labs lane cf layer, refill half 1 at cgif's image).
   rule 24: no function proved (kind: composition: the B3 entry with a Theorem Labs lane's class-full report arm).

   HALF 1 of the cf refill walk at cgif's image, complete: MnRefillB3Topcf.refill_B3_entry_cf_of_parts at
   ci := YGcfImgcgif.CfImg_cgif, its class-full arm from RepArmTcf.classfull_cf_of_hyps (a Theorem Labs lane,
   a working branch b811d748045), which proves the seam's refill_B3_classfull_cf at CfImg_cgif with no premise: the
   report's image facts (RepIFcf.rep_img_facts: the tool-name / callback / silent cells and VSNPrintf's read-only bytes)
   come from the seam's entry facts (ARcf's amc_pf_cells, memnorm, arodata_ok_cf; field round 3) by
   RepArmTcf.rep_img_of_seam.  So the final theorem refill_B3_entry_cf_cgif has no image premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YFk5cf YFk8cf YFkbcf YFkkcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif0n AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill MnRefillSeamcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import MnRefillB3Rcf MnRefillB3cf MnRefillB3Topcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA RepIFcf RepArmTcf.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

(* The seam's class-full case at cgif's image: the report (no premise). *)
Lemma refill_B3_classfull_cf_reply : @refill_B3_classfull_cf fx rc CfImgA.CfImg_A cp.
Proof. exact (@classfull_cf_of_hyps fx rc cp). Qed.

(* HALF 1 at cgif's image. *)
Theorem refill_B3_entry_cf_reply : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall inst, IOK inst -> inst = A_ALLOCATOR) ->
  @refill_B3_entry_cf fx rc CfImgA.CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof.
intros B IOK TS HIOK.
exact (@refill_B3_entry_cf_of_parts fx rc CfImgA.CfImg_A cp B IOK TS HIOK refill_B3_classfull_cf_reply).
Qed.
End t.
