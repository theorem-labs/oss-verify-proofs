(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ASec.
Import ListNotations.
Open Scope Z_scope.

Lemma rev_cons_split {X} : forall (l : list X) x r, rev l = x :: r -> l = rev r ++ [x].
Proof. intros l x r H. rewrite <- (rev_involutive l), H. reflexivity. Qed.

Lemma remove_at_snoc : forall (l' : list schunk) (lastc : schunk) (i : nat),
  remove_at (l' ++ [lastc]) i = if (i =? length l')%nat then l' else firstn i l' ++ lastc :: skipn (Datatypes.S i) l'.
Proof. intros l' lastc i. unfold remove_at. rewrite rev_app_distr. cbn [rev app]. rewrite rev_involutive. reflexivity. Qed.

Lemma remove_at_nth : forall (l : list schunk) (i j : nat),
  (i < length l)%nat -> (j < length l - 1)%nat ->
  nth_error (remove_at l i) j = if (j =? i)%nat then nth_error l (length l - 1) else nth_error l j.
Proof.
  intros l i j Hi Hj.
  destruct (rev l) as [|lastc r] eqn:ER; [apply (f_equal (@length _)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
  pose proof (rev_cons_split l lastc r ER) as EL. set (l' := rev r) in *. rewrite EL.
  rewrite remove_at_snoc. rewrite length_app in *. cbn [length] in *. rewrite EL, length_app in Hi, Hj. cbn [length] in Hi, Hj.
  replace (length l' + 1 - 1)%nat with (length l') by lia.
  rewrite (nth_error_app2 l' [lastc] (n:=length l')) by lia. rewrite Nat.sub_diag. cbn [nth_error].
  destruct (Nat.eqb_spec i (length l')) as [E|NE].
  - destruct (Nat.eqb_spec j i); [lia|]. rewrite nth_error_app1 by lia. reflexivity.
  - destruct (Nat.eqb_spec j i) as [->|NJ].
    + rewrite nth_error_app2 by (rewrite length_firstn; apply Nat.le_min_l). rewrite length_firstn, Nat.min_l by lia. rewrite Nat.sub_diag. reflexivity.
    + rewrite (nth_error_app1 l' [lastc]) by lia.
      destruct (Nat.lt_ge_cases j i) as [LT|GE].
      * rewrite nth_error_app1 by (rewrite length_firstn; apply Nat.min_glb_lt; lia). rewrite nth_error_firstn.
        replace (j <? i)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
      * rewrite nth_error_app2 by (rewrite length_firstn; etransitivity; [apply Nat.le_min_l| lia]). rewrite length_firstn, Nat.min_l by lia.
        destruct (j - i)%nat as [|k] eqn:EK; [lia|]. cbn [nth_error]. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma remove_at_length : forall (l : list schunk) (i : nat), (i < length l)%nat -> length (remove_at l i) = (length l - 1)%nat.
Proof.
  intros l i Hi.
  destruct (rev l) as [|lastc r] eqn:ER; [apply (f_equal (@length _)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
  pose proof (rev_cons_split l lastc r ER) as EL. set (l' := rev r) in *. rewrite EL.
  rewrite remove_at_snoc. rewrite EL, length_app in Hi. cbn [length] in Hi. rewrite length_app. cbn [length].
  destruct (Nat.eqb_spec i (length l')); [lia|].
  rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. rewrite Nat.min_l by lia. lia.
Qed.

Lemma remove_at_src : forall (l : list schunk) (i j : nat) d,
  (i < length l)%nat -> nth_error (remove_at l i) j = Some d ->
  (j < length l - 1)%nat /\ nth_error l (if (j =? i)%nat then (length l - 1)%nat else j) = Some d.
Proof.
  intros l i j d Hi H. pose proof (nth_error_lt _ _ _ H) as Hj. rewrite remove_at_length in Hj by assumption.
  split; [exact Hj|]. rewrite remove_at_nth in H by assumption. destruct (j =? i)%nat; exact H.
Qed.

Lemma remove_at_In : forall (l : list schunk) (i : nat) d, (i < length l)%nat -> In d (remove_at l i) -> In d l.
Proof.
  intros l i d Hi Hd. apply In_nth_error in Hd as [j Hj]. destruct (remove_at_src l i j d Hi Hj) as [_ H]. eapply nth_error_In; exact H.
Qed.

Lemma chunks_sep_nth : forall l, chunks_sep l ->
  forall j k cj ck, j <> k -> nth_error l j = Some cj -> nth_error l k = Some ck -> apart_chunks cj ck.
Proof.
  induction 1 as [|c l Hf Hs IH]; intros j k cj ck NE Hj Hk; [destruct j; discriminate|].
  destruct j as [|j], k as [|k]; cbn in Hj, Hk; try lia.
  - inversion Hj; subst. exact (proj1 (Forall_forall _ _) Hf ck (nth_error_In _ _ Hk)).
  - inversion Hk; subst. pose proof (proj1 (Forall_forall _ _) Hf cj (nth_error_In _ _ Hj)) as A. unfold apart_chunks in *. lia.
  - apply (IH j k); [lia| assumption| assumption].
Qed.

Lemma chunks_sep_of_nth : forall l,
  (forall j k cj ck, j <> k -> nth_error l j = Some cj -> nth_error l k = Some ck -> apart_chunks cj ck) -> chunks_sep l.
Proof.
  induction l as [|c l IH]; intros H; [constructor|]. constructor.
  - apply Forall_forall. intros d Hd. apply In_nth_error in Hd as [k Hk]. apply (H 0%nat (Datatypes.S k)); [lia| reflexivity| exact Hk].
  - apply IH. intros j k cj ck NE Hj Hk. apply (H (Datatypes.S j) (Datatypes.S k)); [lia| exact Hj| exact Hk].
Qed.

Lemma chunks_sep_remove_at : forall l i, (i < length l)%nat -> chunks_sep l -> chunks_sep (remove_at l i).
Proof.
  intros l i Hi Hs. apply chunks_sep_of_nth. intros j k cj ck NE Hj Hk.
  destruct (remove_at_src l i j cj Hi Hj) as [Lj Sj]. destruct (remove_at_src l i k ck Hi Hk) as [Lk Sk].
  eapply (chunks_sep_nth l Hs); [| exact Sj| exact Sk].
  destruct (Nat.eqb_spec j i); destruct (Nat.eqb_spec k i); lia.
Qed.

Lemma remove_at_apart : forall l i c, chunks_sep l -> nth_error l i = Some c -> Forall (apart_chunks c) (remove_at l i).
Proof.
  intros l0 i0 c0 Hs Hi. pose proof (nth_error_lt _ _ _ Hi) as IL0. apply Forall_forall. intros d Hd.
  apply In_nth_error in Hd as [j Hj]. destruct (remove_at_src l0 i0 j d IL0 Hj) as [Lj Sj].
  eapply (chunks_sep_nth l0 Hs); [| exact Hi| exact Sj].
  destruct (Nat.eqb_spec j i0); lia.
Qed.

Section M.
Context {HC : HasCeiling}.
Variable AL : alayout.

#[using="Type"] Lemma sec_wf_dealloc : forall S i, sec_wf AL S -> (i < length (se_chunks S))%nat -> sec_wf AL (sec_dealloc S i).
Proof.
  intros S i (W0 & W1 & W2 & W3 & W4 & W5 & W6) Hi. unfold sec_wf, sec_dealloc, se_n in *. cbn [se_chunks se_nres].
  rewrite remove_at_length by exact Hi.
  split; [exact W0|]. split; [exact W1|]. split; [exact W2|]. split; [lia|]. split; [lia|]. split.
  - apply Forall_forall. intros d Hd. exact (proj1 (Forall_forall _ _) W5 d (remove_at_In _ _ _ Hi Hd)).
  - apply chunks_sep_remove_at; assumption.
Qed.

#[using="Type"] Lemma chunk_ok_msize : forall c, chunk_ok AL c -> 8192 <= sc_msize c /\ sc_msize c mod 4096 = 0.
Proof.
  intros c (_ & _ & SZ & MS & _). rewrite MS. unfold sec_msize, rup4k. split; [Z.div_mod_to_equations; nia|].
  rewrite <- Z.add_mod_idemp_l by lia. rewrite Z_mod_mult. reflexivity.
Qed.
End M.

Lemma parr_prefix_remove : forall (f : schunk -> word) (l : list schunk) (ws : list word) (i : nat) (lastc : schunk),
  (i < length l)%nat -> (length l <= length ws)%nat ->
  firstn (length l) ws = map f l -> nth_error l (length l - 1) = Some lastc ->
  firstn (length l - 1) (upd ws i (f lastc)) = map f (remove_at l i).
Proof.
  intros f l ws i lastc Hi Hlen FW HL.
  apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j (length l - 1)) as [LT|GE].
  - rewrite nth_error_firstn. replace (j <? length l - 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map, remove_at_nth by lia.
    destruct (Nat.eqb_spec j i) as [->|NE].
    + rewrite nth_error_upd_same by lia. rewrite HL. reflexivity.
    + rewrite nth_error_upd_other by lia.
      assert (E : nth_error (firstn (length l) ws) j = nth_error ws j)
        by (rewrite nth_error_firstn; replace (j <? length l)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity).
      rewrite <- E, FW, nth_error_map. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_firstn, upd_length; etransitivity; [apply Nat.le_min_l| lia]).
    symmetry. apply nth_error_None. rewrite length_map, remove_at_length by lia. lia.
Qed.
