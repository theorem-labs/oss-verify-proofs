(* The cf layer's refill contract at reply A in the form CfF1's miss twin consumes (lib/A/YGcfInstEnqMissreply.v, premise
   HIOK : IOK i -> i = as_inst B), at reply's image CfImgA.CfImg_A:
   - refill_spec_cf_reply_inst / refill_walk_cf_reply_inst: YGcfInstRefillSpecreply's refill_spec_cf_reply /
     refill_walk_cf_reply (instance row IOK i -> i = A_ALLOCATOR, and the class-full arm HCF as a premise, as at cgif)
     under HIOK; reply A's A_ALLOCATOR = TFIB_INST = 0xa2a58 (A/AFl1.v, A/AF0m.v) and TfibSyms gives
     as_inst B = TFIB_INST (ts_inst);
   - refill_walk_cf_reply_closed: the same with HCF discharged by the relocated report, RepArmTcf.classfull_cf_of_hyps
     (no premise), for the reply WalkSig closing.
   EVENT-FREE.  rule 24: no function proved (kind: restatement of the relocated refill contract). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFhy AFis AFhz YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstRefill MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFhn YFhncf YFkocf YFkxcf YFkycf YFkzcf MnRefillB2Rcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YFk5cf YFk8cf YFkkcf YFklcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormLoc MnRefillLocreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MnRefillUninitcf MnRefillB3cf MnRefillB3Topcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA YGcfInstRefillSpecreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RepArmTcf.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Lemma iok_alloc : forall (B : asyms) (IOK : Z -> Prop), TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  forall i, IOK i -> i = A_ALLOCATOR.
Proof. intros B IOK TS HIOK i Hi. rewrite (HIOK i Hi), (ts_inst B TS). reflexivity. Qed.

Theorem refill_spec_cf_reply_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_A cp ->
  @refill_spec_cf fx rc CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_spec_cf_reply B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_reply_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_A cp ->
  @refill_walk_cf fx rc CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_walk_cf_reply B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_reply_closed : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  @refill_walk_cf fx rc CfImg_A cp AImg_reply AGImg_reply B IOK.
Proof. intros B IOK TS HIOK. exact (refill_walk_cf_reply_inst B IOK TS HIOK (@RepArmTcf.classfull_cf_of_hyps fx rc cp)). Qed.
End a.
