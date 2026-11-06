(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySet), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySet.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySet.v, ported from a working branch 7c8c67da870
   (blob 72bdbdf5a63; the image-A file carries no licence lines, so none are copied).

   The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on image B, the slots 0x80ef8 ..
   0x81224 (GP_set .. GP_unset0): the composition of the pieces of a turn (LLVMFEntrySetDefs.v,
   LLVMFEntrySetHead.v, LLVMFEntrySetGa0.v, LLVMFEntrySetGa1.v, LLVMFEntrySetGa2.v, LLVMFEntrySetE2.v) into
   the phase lemma ge_set, by induction on the turns left, as cgif's walk composes its loops
   (cgif lib/A/ACfj.v:157-163).

   Image B's loop counter is s5 (x21): the init phase loads it with the count byte nset (0 < nset < 256,
   `lbu s5,0(s8)` at 0x80ecc, `beqz s5` at 0x80ed4), each turn ends with `addiw s5,s5,-1` at 0x81140 and
   `beqz s5,0x81224` at 0x81148, else `j 0x80ef8` at 0x8114c. At the head of turn i it holds nset - i; the
   induction measure is n, the turns left after the current one (GIn n: s5 = n + 1, n < 255). Image A
   counted down in s11 the same way. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntrySetHead LLVMFEntrySetGa0 LLVMFEntrySetGa1 LLVMFEntrySetGa2 LLVMFEntrySetE2.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SegSetModel.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

(* The loop from its four open pieces and the two closed ones (seg78, seg_e2). *)
Lemma ge_set_of : seg_head_stmt B MT -> seg_ga0_stmt B MT -> seg_ga1_stmt B MT -> seg_ga2_stmt B MT ->
  forall POST, ge_from B MT POST (GI_unset0 B MT) -> ge_from B MT POST (GI_set B MT).
Proof.
  intros SH S0 S1 S2 POST HU.
  assert (IND : forall n, ge_from B MT POST (GIn B MT n)).
  { intros n. induction n as [|m IH].
    - assert (H78 : forall i, ge_from B MT POST (G78 B MT 0 i))
        by (intros i; apply (seg78 B MT LAWS POST 0 i HU); intros n' Hn'; discriminate).
      assert (HE2 : forall i, ge_from B MT POST (GE2 B MT 0 i))
        by (intros i; apply (seg_e2 B MT LAWS POST 0 i), H78).
      apply SH; intros i; [apply S0 | apply S1 | apply S2]; auto.
    - assert (H78 : forall i, ge_from B MT POST (G78 B MT (S m) i))
        by (intros i; apply (seg78 B MT LAWS POST (S m) i HU); intros n' Hn'; injection Hn' as <-; exact IH).
      assert (HE2 : forall i, ge_from B MT POST (GE2 B MT (S m) i))
        by (intros i; apply (seg_e2 B MT LAWS POST (S m) i), H78).
      apply SH; intros i; [apply S0 | apply S1 | apply S2]; auto. }
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HG.
  destruct (of_set B MT cx fp k acc ly3 S3 W3 ms3 md3 HG)
    as (i & t & _ & _ & _ & _ & _ & _ & Hi & _ & _ & R21 & _).
  pose proof (SegSetModel.rd8_range (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) as Hnr.
  change (fst (GrantSlotPlan.rd8 (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx))))) with (GrantSlotPlan.nset (c_pl cx)) in Hnr.
  apply (IND (Z.to_nat (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i - 1)) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO).
  split; [exact HG|]. split; [rewrite R21; f_equal; lia | lia].
Qed.

(* The contracts the loop calls (a callee's stated contract is a Section hypothesis):
   reac_headamp_tx_set, reac_headamp_tx_effective and reac_headamp_default, each as image
   B's GrantBContracts.v states it. *)
Hypothesis SETH : tb_reac_headamp_tx_set_spec B.
Hypothesis EFFH : tb_reac_headamp_tx_effective_spec B.
Hypothesis DFLH : tb_reac_headamp_default_spec B.

(* The set loop, GP_set (0x80ef8) → GP_unset0 (0x81224). *)
Theorem ge_set : forall POST, ge_from B MT POST (GI_unset0 B MT) -> ge_from B MT POST (GI_set B MT).
Proof.
  exact (ge_set_of (ge_set_head B MT LAWS SETH)
    (ge_set_ga0 B MT LAWS (call_e2 B MT LAWS EFFH))
    (ge_set_ga1 B MT LAWS (call_e2 B MT LAWS EFFH))
    (ge_set_ga2 B MT LAWS (call_e2 B MT LAWS EFFH) EFFH DFLH)).
Qed.

End c.
End b.
End a.
