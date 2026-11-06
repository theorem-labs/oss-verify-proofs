(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import APrim APrimLem APrimPop.
Import ListNotations.
Open Scope Z_scope.

Section RF.
Variables (c : Z) (k : pclass).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis WF : pclass_wf c k.
Notation SZ := (class_size c).
Notation n := (max_count c / 2).

Hypothesis BUD1 : p_mu k + 8 * class_size c + K_MAP <= FA_OFF.
Hypothesis BUD2 : 4 * (p_nf k + (p_mu k + 8 * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.

#[using="k Hc"] Lemma half_range : 1 <= n <= 8 /\ 2 * n = max_count c.
Proof. pose proof (max_count_range c Hc) as (R & E). Z.div_mod_to_equations. lia. Qed.

#[using="Hc WF BUD1 BUD2"] Lemma gfa_req : p_nf k < n ->
  1 <= n - p_nf k <= 8
  /\ p_mu k + (n - p_nf k) * class_size c + K_MAP <= FA_OFF
  /\ 4 * (p_nf k + (p_mu k + (n - p_nf k) * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.
Proof.
  intros LT. pose proof half_range as (NR & _). pose proof (class_size_pos c Hc) as CS.
  pose proof WF as WF0. unfold pclass_wf in WF0. destruct WF0 as (Lnf & _).
  assert (R8 : (n - p_nf k) * SZ <= 8 * SZ) by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [lia|]. split; [lia|].
  assert (D : (p_mu k + (n - p_nf k) * SZ + K_MAP - p_au k) / SZ <= (p_mu k + 8 * SZ + K_MAP - p_au k) / SZ) by (apply Z.div_le_mono; lia).
  lia.
Qed.

#[using="Hc WF BUD1 BUD2"] Lemma gfa_pre_wf : pclass_wf c (gfa_pre k c n).
Proof.
  unfold gfa_pre. destruct (Z.ltb_spec (p_nf k) n) as [LT|GE]; [| exact WF].
  destruct (gfa_req LT) as (R & B1 & B2). apply populate_wf; assumption.
Qed.

#[using="Hc WF BUD1 BUD2"] Lemma gfa_pre_enough : n <= p_nf (gfa_pre k c n).
Proof.
  unfold gfa_pre. destruct (Z.ltb_spec (p_nf k) n) as [LT|GE]; [| exact GE].
  destruct (gfa_req LT) as (R & B1 & B2). pose proof (class_size_pos c Hc) as CS.
  pose proof (populate_shape c (n - p_nf k) k) as (E1 & _). rewrite E1.
  pose proof (pop_mu_facts c (n - p_nf k) k Hc R WF B1) as (_ & M2 & _).
  pose proof (pop_new_facts c (n - p_nf k) k Hc R WF B1) as (N0 & N1 & N2 & _).
  assert (X : n - p_nf k <= pop_new k c (n - p_nf k)).
  { destruct (Z.le_gt_cases (n - p_nf k) (pop_new k c (n - p_nf k))) as [LE|GT]; [exact LE| exfalso].
    assert (SZ * (pop_new k c (n - p_nf k) + 1) <= SZ * (n - p_nf k)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  lia.
Qed.

#[using="Type"] Lemma gfa_pre_cnt : p_cnt (gfa_pre k c n) = p_cnt k /\ p_chunks (gfa_pre k c n) = p_chunks k.
Proof. unfold gfa_pre. destruct (p_nf k <? n); [| split; reflexivity]. unfold populate. cbn. split; reflexivity. Qed.

#[using="Type"] Lemma refill_shape : let k1 := gfa_pre k c n in let base := p_nf k1 - n in
  refill k c = mkPCL base (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1 + n) (p_nfreed k1)
                     (firstn (Z.to_nat base) (p_fa k1)) n (skipn (Z.to_nat base) (p_fa k1)).
Proof. unfold refill, get_from_allocator. reflexivity. Qed.

#[using="Hc WF BUD1 BUD2"] Lemma refill_wf : p_cnt k = 0 -> pclass_wf c (refill k c).
Proof.
  intros C0. rewrite refill_shape. cbv zeta.
  pose proof gfa_pre_wf as WF1. pose proof gfa_pre_enough as EN. pose proof gfa_pre_cnt as (EC & ECH).
  pose proof half_range as (NR & N2). pose proof (max_count_range c Hc) as (MR & _).
  set (k1 := gfa_pre k c n) in *. unfold pclass_wf in WF1.
  destruct WF1 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
  assert (CH0 : p_chunks k1 = []). { rewrite EC, C0 in Lcnt. destruct (p_chunks k1); [reflexivity| cbn in Lcnt; lia]. }
  rewrite CH0, app_nil_r in ND, FB.
  unfold pclass_wf. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks].
  split. { rewrite length_firstn. lia. }
  split. { rewrite length_skipn. lia. }
  split; [lia|]. split; [lia|]. split; [exact MFA|]. split; [exact MFAM|]. split; [exact AU|]. split; [exact MUF|].
  split; [exact MUM|]. split; [exact AUS|]. split; [exact GAP|].
  rewrite firstn_skipn. split; [exact ND|]. split; [exact FB|]. split; lia.
Qed.
End RF.
