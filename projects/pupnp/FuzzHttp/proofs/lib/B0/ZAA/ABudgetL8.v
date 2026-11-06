(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 ASec AQuar AQuarM AHeap ALedger AHeap2 AHeapB AMallocP F_alloc_A F_alloc_S1.
Import ListNotations.
Open Scope Z_scope.

Definition lbZ_bytes0 (LB : list (block Z)) : Z :=
  fold_right (fun b acc => blk_size b + acc) 0 (List.filter (fun b => a0_cls (blk_size b) =? 0) LB).

Lemma lbZ_bytes0_perm : forall LB LB', Permutation LB LB' -> lbZ_bytes0 LB = lbZ_bytes0 LB'.
Proof.
  intros LB LB' PM. unfold lbZ_bytes0.
  induction PM as [|x l l' PM IH|x y l|l l' l'' P1 I1 P2 I2]; cbn [List.filter fold_right].
  - reflexivity.
  - destruct (a0_cls (blk_size x) =? 0); cbn [fold_right]; lia.
  - destruct (a0_cls (blk_size x) =? 0); destruct (a0_cls (blk_size y) =? 0); cbn [fold_right]; lia.
  - lia.
Qed.

Lemma lbZ_bytes0_cons : forall b LB, lbZ_bytes0 (b :: LB) = (if a0_cls (blk_size b) =? 0 then blk_size b else 0) + lbZ_bytes0 LB.
Proof. intros b LB. unfold lbZ_bytes0. cbn [List.filter]. destruct (a0_cls (blk_size b) =? 0); cbn [fold_right]; lia. Qed.

Section BUD.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

#[using="Type"] Lemma sec_bytes_live : forall (live : list (qchunk * Z)), Forall lr_ok live -> Forall ch_cls_ok (map fst live) -> Forall qchunk_wf (map fst live) ->
  fold_right (fun r acc => sec_rec_bytes r + acc) 0 live = lbZ_bytes0 (map (blk_ofB AL) live).
Proof.
  induction live as [|[ch cn] l IH]; intros LO CO WF; [reflexivity|].
  apply Forall_cons_iff in LO as [L1 LO]. cbn [map fst] in CO, WF. apply Forall_cons_iff in CO as [C1 CO]. apply Forall_cons_iff in WF as [(_ & _ & N1 & _) WF].
  specialize (IH LO CO WF).
  cbn [map fold_right]. rewrite lbZ_bytes0_cons, <- IH. unfold blk_ofB at 1 2, blk_size. cbn [fst snd].
  assert (EN : a0_cls cn = a0_cls (qc_n ch)) by (destruct L1 as [L1|[L1 L2]]; cbn [fst snd] in *; [rewrite L1; reflexivity| rewrite L1, L2; reflexivity]).
  rewrite EN. unfold ch_cls_ok in C1. unfold sec_rec_bytes. cbn [fst snd]. destruct (qc_kind ch) as [c' v'|sc].
  - destruct C1 as [EC NZ]. rewrite <- EC. replace (c' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). lia.
  - destruct C1 as [C1 _]. rewrite C1. cbn [Z.eqb]. lia.
Qed.

#[using="Type"] Lemma budget_sec_L8 : forall s LB (m : mem) n,
  RHEAP_B AL E s LB m ->
  lbcZ LB 0 + 1 <= A0_SEC_CNT -> lbZ_bytes0 LB + n <= A0_SEC_BYTES ->
  se_n (bs_sec s) < K_MAX_CHUNKS /\ sec_live_cnt s + 1 <= A0_SEC_CNT /\ sec_live_bytes s + n <= A0_SEC_BYTES.
Proof.
  intros s LB m n HR BC BB.
  pose proof (rheap_sec_n AL E s LB m HR) as SN.
  pose proof HR as (PLB & LOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & _ & _ & _ & _ & _ & _ & _ & _ & CCL & _).
  unfold live_chunks in *.
  split. { assert (Q : A0_QB / 64521 <= 4200) by (vm_compute; discriminate). unfold A0_SEC_CNT in BC. lia. }
  split.
  - unfold sec_live_cnt, live_chunks. rewrite (sec_cnt_live AL (bs_live s) LOK CCL), <- (lbcZ_perm _ _ 0 PLB). exact BC.
  - unfold sec_live_bytes. rewrite (sec_bytes_live (bs_live s) LOK CCL WFL), <- (lbZ_bytes0_perm _ _ PLB). exact BB.
Qed.

#[using="Type"] Lemma a0_cls_prim : forall n, a0_need n <= 65536 -> a0_cls n = class_of (a0_need n).
Proof. intros n NP. unfold a0_cls. rewrite (proj2 (Z.leb_le _ _) NP). symmetry. apply class_of_a0. Qed.
#[using="Type"] Lemma a0_cls_sec : forall n, 65536 < a0_need n -> a0_cls n = 0.
Proof. intros n NS. unfold a0_cls. rewrite (proj2 (Z.leb_gt _ _) NS). reflexivity. Qed.
#[using="Type"] Lemma a0_cls_prim_nz : forall n, 0 <= n -> a0_need n <= 65536 -> a0_cls n <> 0.
Proof.
  intros n Hn NP. rewrite (a0_cls_prim n NP), class_of_a0.
  assert (1 <= a0_need n) by (unfold a0_need; assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia);
    assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia); lia).
  pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia.
Qed.

Definition budgetZ (s : astB) (LB : list (block Z)) (n : Z) : Prop :=
  if a0_cls n =? 0 then lbcZ LB 0 + 1 <= A0_SEC_CNT /\ lbZ_bytes0 LB + n <= A0_SEC_BYTES /\ bs_nsec s + 1 <= A0_NSEC_MAX
  else (lbcZ LB (a0_cls n) + 1) * a0_csz (a0_cls n) <= A0_CAP (a0_cls n).

#[using="Type"] Lemma budgetZ_prim : forall s LB n, 0 <= n -> a0_need n <= 65536 -> budgetZ s LB n ->
  (lbcZ LB (class_of (a0_need n)) + 1) * a0_csz (class_of (a0_need n)) <= A0_CAP (class_of (a0_need n)).
Proof.
  intros s LB n Hn NP B. unfold budgetZ in B. rewrite (proj2 (Z.eqb_neq _ _) (a0_cls_prim_nz n Hn NP)) in B. rewrite (a0_cls_prim n NP) in B. exact B.
Qed.
#[using="Type"] Lemma budgetZ_sec : forall s LB (m : mem) n, RHEAP_B AL E s LB m -> 65536 < a0_need n -> budgetZ s LB n ->
  se_n (bs_sec s) < K_MAX_CHUNKS /\ sec_live_cnt s + 1 <= A0_SEC_CNT /\ sec_live_bytes s + n <= A0_SEC_BYTES /\ bs_nsec s + 1 <= A0_NSEC_MAX.
Proof.
  intros s LB m n HR NS B. unfold budgetZ in B. rewrite (a0_cls_sec n NS) in B. cbn [Z.eqb] in B. destruct B as (BC & BB & BN).
  destruct (budget_sec_L8 s LB m n HR BC BB) as (S1 & S2 & S3). tauto.
Qed.
End BUD.
