(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtSnjd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Lemma baddr_ge : forall bs i, (length bs <= i)%nat -> baddr bs i = 0.
Proof. intros bs i H. unfold baddr. apply nth_overflow. rewrite map_length. exact H. Qed.
(* [comment removed for export] *)

Lemma baddr_cons : forall a s r i, baddr ((a, s) :: r) (S i) = baddr r i.
Proof. intros. reflexivity. Qed.
Lemma bsz_cons : forall a s r i, bsz ((a, s) :: r) (S i) = bsz r i.
Proof. intros. reflexivity. Qed.
Lemma baddr_0 : forall a s r, baddr ((a, s) :: r) 0 = a.
Proof. intros. reflexivity. Qed.
Lemma bsz_0 : forall a s r, bsz ((a, s) :: r) 0 = s.
Proof. intros. reflexivity. Qed.

Lemma lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[a s] l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma firstn_S_nth : forall (bs : list (Z * Z)) j, (j < length bs)%nat ->
  firstn (S j) bs = firstn j bs ++ [(baddr bs j, bsz bs j)].
Proof.
  induction bs as [|[a s] bs IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j as [|j]; [reflexivity|].
  cbn [firstn]. rewrite (IH j) by lia. rewrite baddr_cons, bsz_cons. reflexivity.
Qed.

Lemma lsum_firstn_S : forall bs j, (j < length bs)%nat -> lsum (firstn (S j) bs) = lsum (firstn j bs) + bsz bs j.
Proof. intros bs j Hj. rewrite firstn_S_nth by exact Hj. rewrite lsum_app. cbn. lia. Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma bwf_sz : forall bs i, bwf bs -> (i < length bs)%nat -> 0 <= bsz bs i < 2^64.
Proof. intros bs i [W _] Hi. apply (W i Hi). Qed.

Lemma lsum_firstn_nonneg : forall bs j, bwf bs -> 0 <= lsum (firstn j bs).
Proof.
  intros bs j W. induction j as [|j IH]; [rewrite firstn_O; cbn; lia|].
  destruct (Nat.lt_ge_cases j (length bs)) as [L|G].
  - rewrite lsum_firstn_S by exact L. pose proof (bwf_sz bs j W L). lia.
  - rewrite firstn_all2 by lia. rewrite firstn_all2 in IH by lia. exact IH.
Qed.

Lemma lsum_firstn_le : forall bs j, bwf bs -> lsum (firstn j bs) <= lsum bs.
Proof.
  intros bs j W. rewrite <- (firstn_skipn j bs) at 2. rewrite lsum_app.
  enough (0 <= lsum (skipn j bs)) by lia.
  revert j. induction bs as [|[a s] bs IH]; intros j; [rewrite skipn_nil; cbn; lia|].
  assert (W' : bwf bs).
  { destruct W as [W1 W2]. split.
    - intros i Hi. specialize (W1 (S i) ltac:(cbn; lia)). rewrite baddr_cons, bsz_cons in W1. exact W1.
    - intros i k Hi Hk Hik. specialize (W2 (S i) (S k) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
      rewrite !baddr_cons in W2. exact W2. }
  destruct j as [|j]; cbn [skipn].
  - cbn. pose proof (IH W' 0%nat) as H0. rewrite skipn_O in H0.
    destruct W as [W1 _]. specialize (W1 0%nat ltac:(cbn; lia)). rewrite bsz_0 in W1. lia.
  - apply IH. exact W'.
Qed.

(* [comment removed for export] *)
Lemma skipn_cons_nth : forall (bs : list (Z * Z)) j, (j < length bs)%nat ->
  skipn j bs = (baddr bs j, bsz bs j) :: skipn (S j) bs.
Proof.
  induction bs as [|[a s] bs IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn]. rewrite (IH j) by lia. rewrite baddr_cons, bsz_cons. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma npop_cons : forall qmin sz a s r,
  npop qmin sz ((a, s) :: r) = if sz <=? qmin then 0%nat else S (npop qmin (sz - s) r).
Proof. intros. reflexivity. Qed.

Lemma npop_le_length : forall qmin bs sz, (npop qmin sz bs <= length bs)%nat.
Proof. induction bs as [|[a s] bs IH]; intros sz; cbn; [lia|]. destruct (sz <=? qmin); [lia|]. specialize (IH (sz - s)). lia. Qed.

(* [comment removed for export] *)
Definition npop_from (qmin gqb : Z) (bs : list (Z * Z)) (j : nat) : nat :=
  npop qmin (gqb - lsum (firstn j bs)) (skipn j bs).

Lemma npop_from_0 : forall qmin gqb bs, npop_from qmin gqb bs 0 = npop qmin gqb bs.
Proof. intros. unfold npop_from. rewrite firstn_O, skipn_O. cbn. rewrite Z.sub_0_r. reflexivity. Qed.

Lemma npop_from_stop : forall qmin gqb bs j, gqb - lsum (firstn j bs) <= qmin -> npop_from qmin gqb bs j = 0%nat.
Proof.
  intros qmin gqb bs j H. unfold npop_from. destruct (skipn j bs) as [|[a s] r] eqn:E; [reflexivity|].
  rewrite npop_cons. rewrite (proj2 (Z.leb_le _ _) H). reflexivity.
Qed.

Lemma npop_from_step : forall qmin gqb bs j, (j < length bs)%nat -> qmin < gqb - lsum (firstn j bs) ->
  npop_from qmin gqb bs j = S (npop_from qmin gqb bs (S j)).
Proof.
  intros qmin gqb bs j Hj Hgt. unfold npop_from. rewrite (skipn_cons_nth bs j Hj), npop_cons.
  destruct (Z.leb_spec0 (gqb - lsum (firstn j bs)) qmin); [lia|].
  rewrite lsum_firstn_S by exact Hj. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma outside_bivls : forall l x, outside (bivls l) x <-> (forall i, (i < length l)%nat -> ~ (baddr l i <= x < baddr l i + 8)).
Proof.
  induction l as [|[a s] l IH]; intros x.
  - cbn. split; [intros _ i Hi; lia | intros; exact I].
  - cbn [bivls map fst snd outside length]. fold (bivls l). rewrite IH. split.
    + intros [H1 H2] i Hi. destruct i as [|i]; [rewrite baddr_0; lia | rewrite baddr_cons; apply H2; lia].
    + intros H. split; [specialize (H 0%nat ltac:(lia)); rewrite baddr_0 in H; lia|].
      intros i Hi. specialize (H (S i) ltac:(lia)). rewrite baddr_cons in H. exact H.
Qed.

Lemma baddr_firstn : forall bs k i, (i < k)%nat -> baddr (firstn k bs) i = baddr bs i.
Proof.
  intros bs k i Hik. unfold baddr. rewrite <- firstn_map, nth_firstn.
  replace (PeanoNat.Nat.ltb i k) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hik). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sub_fp_iter : forall FP bs k (j : nat) extra,
  (forall iv, In iv extra -> exists i, (i < k)%nat /\ (i < length bs)%nat /\ iv = (baddr bs i, baddr bs i + 8)) ->
  sub_fp (FP ++ extra) (FP ++ bivls (firstn k bs)).
Proof.
  intros FP bs k j extra HE x. rewrite !outside_app. intros [H1 H2]. split; [exact H1|].
  rewrite outside_bivls in H2.
  assert (G : forall iv, In iv extra -> ~ (fst iv <= x < snd iv)).
  { intros iv Hiv. destruct (HE iv Hiv) as (i & Hi & Hil & ->). cbn.
    specialize (H2 i). rewrite firstn_length in H2. rewrite baddr_firstn in H2 by exact Hi.
    apply H2. lia. }
  clear -G; try pose proof alloc_ceiling_val. induction extra as [|[lo hi] extra IH]; cbn; [exact I|].
  split; [| apply IH; intros iv Hiv; apply G; right; exact Hiv].
  specialize (G (lo, hi) (or_introl eq_refl)). cbn in G. lia.
Qed.

(* [comment removed for export] *)
Lemma bchain_cut_step : forall W m m' bs j,
  bwf bs -> (j < length bs)%nat ->
  bchain_cut m bs j -> munch W m m' -> wmono rsegs m m' ->
  (forall i, (i < length bs)%nat -> i <> j -> S i <> j -> disjoint_from W (baddr bs i) 16) ->
  rw_cells rsegs m' (baddr bs j) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bsz bs j))] ->
  (forall i, S i = j -> rw_cells rsegs m' (baddr bs i) [C8 (Z_to_bv 64 (baddr bs j)); C8 (Z_to_bv 64 (bsz bs i))]) ->
  bchain_cut m' bs (S j).
Proof.
  intros W m m' bs j WF Hj BC MU WM DJ CJ CP i Hi.
  destruct (Nat.eq_dec i j) as [->|NE].
  - rewrite Nat.eqb_refl. exact CJ.
  - destruct (Nat.eq_dec (S i) j) as [E|NE2].
    + replace (S i =? S j)%nat with false by (symmetry; apply Nat.eqb_neq; lia). rewrite E. apply CP. exact E.
    + specialize (BC i Hi). replace (S i =? j)%nat with false in BC by (symmetry; apply Nat.eqb_neq; lia).
      replace (S i =? S j)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      eapply rw_cells_transport; [exact BC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply DJ; assumption.
Qed.

End CEIL.

Lemma bchain_cut_0 : forall m bs, bchain m bs -> bchain_cut m bs 0.
Proof. intros m bs H i Hi. specialize (H i Hi). replace (S i =? 0)%nat with false by reflexivity. exact H. Qed.
