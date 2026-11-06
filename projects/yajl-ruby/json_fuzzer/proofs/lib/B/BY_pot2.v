(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section PHR.
Variables (acharge arefund : Z -> Z) (F : Z).
Hypothesis AC0 : forall n, 0 <= acharge n.
Hypothesis AR0 : forall n, 0 <= arefund n.
Hypothesis HF : 0 <= F <= 1.
Hypothesis BIG : forall t, 2^19 <= t -> acharge (t + 256) - arefund t <= 7.

Definition ypc (s : Z) : Z := acharge (s + 128) + F.
Definition EXC (t : Z) : Z := Z.max 0 (acharge (t + 256) + F - arefund t - 8).
Fixpoint Psum (n : nat) (s : Z) : Z := match n with O => 0 | S n' => EXC s + Psum n' (s + 128) end.
Definition NB : nat := Z.to_nat 4200.
Definition P (s : Z) : Z := Psum NB s.
Definition TT (c u s L : Z) : Z := Z.max 0 (L - c) + Z.min 0 (u - s).
Definition PHI (c u s L : Z) : Z := 8 * ((Z.max 0 (TT c u s L) + 127) / 128).
Definition RSV (c s L : Z) : Z := if c <? L then ypc s else 0.
Definition phr (c u s L : Z) : Z := 3 * F + P s + PHI c u s L + RSV c s L.

Lemma EXC_nonneg : forall t, 0 <= EXC t. Proof. intros; unfold EXC; lia. Qed.
Lemma EXC_big : forall t, 2^19 <= t -> EXC t = 0.
Proof. intros t Ht. unfold EXC. pose proof (BIG t Ht). lia. Qed.
Lemma ypc_nonneg : forall s, 0 <= ypc s. Proof. intros; unfold ypc; pose proof (AC0 (s + 128)); lia. Qed.

Lemma Psum_nonneg : forall n s, 0 <= Psum n s.
Proof. induction n; intros; cbn [Psum]; [lia|]. pose proof (EXC_nonneg s). pose proof (IHn (s + 128)). lia. Qed.
Lemma Psum_extend : forall n s, Psum (S n) s = Psum n s + EXC (s + 128 * Z.of_nat n).
Proof.
  induction n; intros.
  - cbn [Psum]. replace (s + 128 * Z.of_nat 0) with s by lia. lia.
  - change (Psum (S (S n)) s) with (EXC s + Psum (S n) (s + 128)). rewrite (IHn (s + 128)).
    change (Psum (S n) s) with (EXC s + Psum n (s + 128)).
    replace (s + 128 + 128 * Z.of_nat n) with (s + 128 * Z.of_nat (S n)) by lia. lia.
Qed.
Lemma Psum_S : forall n s, Psum (S n) s = EXC s + Psum n (s + 128). Proof. reflexivity. Qed.
Lemma NB_S : NB = S (Z.to_nat 4199). Proof. unfold NB. rewrite <- Z2Nat.inj_succ by lia. reflexivity. Qed.
Lemma P_step : forall s, 0 <= s -> P s = EXC s + P (s + 128).
Proof.
  intros s Hs. unfold P. rewrite NB_S at 1. rewrite Psum_S.
  enough (E : Psum NB (s + 128) = Psum (Z.to_nat 4199) (s + 128)) by (rewrite E; reflexivity).
  rewrite NB_S. rewrite (Psum_extend (Z.to_nat 4199) (s + 128)). rewrite Z2Nat.id by lia. rewrite EXC_big by lia.
  generalize (Psum (Z.to_nat 4199) (s + 128)). intros z. lia.
Qed.
Lemma P_nonneg : forall s, 0 <= P s. Proof. intros; unfold P; apply Psum_nonneg. Qed.
Lemma P_mono128 : forall s, 0 <= s -> P (s + 128) <= P s.
Proof. intros s Hs. rewrite (P_step s Hs). pose proof (EXC_nonneg s). lia. Qed.

Lemma PHI_nonneg : forall c u s L, 0 <= PHI c u s L.
Proof. intros. unfold PHI. Z.div_mod_to_equations. lia. Qed.
Lemma PHI_mono : forall c u s L c' u' s' L', TT c' u' s' L' <= TT c u s L -> PHI c' u' s' L' <= PHI c u s L.
Proof. intros. unfold PHI. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma PHI_drop : forall c u s L c' u' s' L', 1 <= TT c u s L -> TT c' u' s' L' <= TT c u s L - 128 -> PHI c' u' s' L' + 8 <= PHI c u s L.
Proof. intros. unfold PHI. Z.div_mod_to_equations. nia. Qed.
Lemma PHI_zero : forall c u s L, TT c u s L <= 0 -> PHI c u s L = 0.
Proof. intros. unfold PHI. rewrite Z.max_l by lia. reflexivity. Qed.
Lemma RSV_nonneg : forall c s L, 0 <= RSV c s L.
Proof. intros. unfold RSV. destruct (c <? L); [apply ypc_nonneg| lia]. Qed.

(* [comment removed for export] *)
Lemma phr_nonneg : forall c u s L, 0 <= phr c u s L.
Proof. intros. unfold phr. pose proof (P_nonneg s). pose proof (PHI_nonneg c u s L). pose proof (RSV_nonneg c s L). lia. Qed.
(* [comment removed for export] *)
Lemma phr_lex : forall c c' u s L, c <= c' -> phr c' u s L <= phr c u s L.
Proof.
  intros. unfold phr. pose proof (PHI_mono c u s L c' u s L ltac:(unfold TT; lia)).
  assert (RSV c' s L <= RSV c s L).
  { unfold RSV. destruct (Z.ltb_spec c L); destruct (Z.ltb_spec c' L); try lia. pose proof (ypc_nonneg s); lia. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma phr_pop : forall c u s L, 0 < u -> phr c (u - 1) s L <= phr c u s L.
Proof. intros. unfold phr. pose proof (PHI_mono c u s L c (u - 1) s L ltac:(unfold TT; lia)). lia. Qed.
(* [comment removed for export] *)
Lemma phr_push : forall c c' u s L, 0 <= c -> c < c' <= L -> u < s -> phr c' (u + 1) s L <= phr c u s L.
Proof.
  intros. unfold phr. pose proof (PHI_mono c u s L c' (u + 1) s L ltac:(unfold TT; lia)).
  assert (RSV c' s L <= RSV c s L).
  { unfold RSV. destruct (Z.ltb_spec c L); destruct (Z.ltb_spec c' L); try lia. pose proof (ypc_nonneg s); lia. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma phr_realloc_liq : forall c c' u s L, 0 <= c -> c < c' <= L -> u = s -> 0 <= s ->
  ypc s + phr c' u (s + 128) 0 <= phr c u s L.
Proof.
  intros c c' u s L Hc Hcc Hu Hs. unfold phr.
  rewrite (PHI_zero c' u (s + 128) 0) by (unfold TT; lia).
  replace (RSV c' (s + 128) 0) with 0 by (unfold RSV; destruct (Z.ltb_spec c' 0); [lia| reflexivity]).
  replace (RSV c s L) with (ypc s) by (unfold RSV; destruct (Z.ltb_spec c L); [reflexivity| lia]).
  pose proof (P_mono128 s Hs). pose proof (PHI_nonneg c u s L). lia.
Qed.
(* [comment removed for export] *)
Lemma phr_realloc : forall c c' u s L, 0 <= c -> c < c' <= L -> u = s -> 0 <= s ->
  phr c' (u + 1) (s + 128) L + ypc s <= phr c u s L + arefund s.
Proof.
  intros c c' u s L Hc Hcc Hu Hs. unfold phr.
  rewrite (P_step s Hs).
  pose proof (PHI_drop c u s L c' (u + 1) (s + 128) L ltac:(unfold TT; lia) ltac:(unfold TT; lia)) as D.
  replace (RSV c s L) with (ypc s) by (unfold RSV; destruct (Z.ltb_spec c L); [reflexivity| lia]).
  assert (RSV c' (s + 128) L <= EXC s + 8 + arefund s).
  { unfold RSV, EXC, ypc. destruct (Z.ltb_spec c' L); [| pose proof (AR0 s); lia].
    replace (s + 128 + 128) with (s + 256) by lia. lia. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma phr_rest : forall c c' u s L, 0 <= c' -> 0 <= L -> phr c' u s 0 <= phr c u s L.
Proof.
  intros. unfold phr.
  assert (PHI c' u s 0 <= PHI c u s L).
  { rewrite (PHI_zero c' u s 0) by (unfold TT; lia). apply PHI_nonneg. }
  replace (RSV c' s 0) with 0 by (unfold RSV; destruct (Z.ltb_spec c' 0); [lia| reflexivity]).
  pose proof (RSV_nonneg c s L). lia.
Qed.
(* [comment removed for export] *)
Lemma phr_ge_3F : forall c u s L, 3 * F <= phr c u s L.
Proof. intros. unfold phr. pose proof (P_nonneg s). pose proof (PHI_nonneg c u s L). pose proof (RSV_nonneg c s L). lia. Qed.
(* [comment removed for export] *)
Lemma phr_init_le : forall L, 0 <= L -> phr 0 0 128 L <= 3 * F + P 128 + L / 16 + 8 + ypc 128.
Proof.
  intros L HL. unfold phr. assert (PHI 0 0 128 L <= L / 16 + 8) by (unfold PHI, TT; Z.div_mod_to_equations; nia).
  assert (RSV 0 128 L <= ypc 128) by (unfold RSV; destruct (0 <? L); [lia| apply ypc_nonneg]). lia.
Qed.
End PHR.
End RC__1.
