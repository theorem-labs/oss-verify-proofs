(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require InitMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require ApBnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require Import BgRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma wlimbs_length : forall l, length (wlimbs l) = length l.
Proof. intros. unfold wlimbs. apply length_map. Qed.

Lemma nth_firstn_lt' : forall {A} (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n j d Hj; [destruct n; destruct j; reflexivity|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_skipn' : forall {A} (l : list A) c j d, nth j (skipn c l) d = nth (c + j) l d.
Proof.
  intros A l. induction l as [|x l IH]; intros c j d.
  - destruct c as [|c]; [reflexivity|]. cbn [skipn]. destruct j, (S c + _)%nat; reflexivity.
  - destruct c as [|c]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mont_ref_cases : forall r, mont_ref r = true <-> r = RMontRR \/ r = RMontN \/ r = RMontNi.
Proof.
  intros r. unfold mont_ref. rewrite !Bool.orb_true_iff, !Nat.eqb_eq. tauto.
Qed.

(* [comment removed for export] *)
Definition stored_ref (r : bnref) : Prop := (r < NFIX)%nat /\ r <> ROne /\ mont_ref r = false.

Lemma pl_of_stored : forall PL r, stored_ref r -> pl_of PL r = pl_bn PL r.
Proof.
  intros PL r (H1 & H2 & H3). unfold pl_of. unfold mont_ref in H3. rewrite !Bool.orb_false_iff in H3. destruct H3 as [[E1 E2] E3].
  replace (r =? ROne)%nat with false by (symmetry; apply Nat.eqb_neq; exact H2). rewrite E1, E2, E3.
  replace (r <? NFIX)%nat with true by (symmetry; apply Nat.ltb_lt; exact H1). reflexivity.
Qed.

Lemma pl_of_one : forall PL, pl_of PL ROne = Some (PStatic CONST_ONE).
Proof. reflexivity. Qed.

Lemma pl_of_pool : forall PL i, pl_of PL (RPool i) = None.
Proof. intros PL i. unfold pl_of, RPool. cbn [NFIX Nat.add]. replace (12 + i <? 12)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. Qed.

Lemma pl_of_ge : forall PL r, (NFIX <= r)%nat -> pl_of PL r = None.
Proof. intros PL r H. replace r with (RPool (r - NFIX)) by (unfold RPool; lia). apply pl_of_pool. Qed.

Lemma pl_of_mont : forall PL r, mont_ref r = true ->
  pl_of PL r = match pl_mont PL with
               | Some (am, qm) => Some (PHeap (am + 24 * Z.of_nat (r - RMontRR)) qm (24 * Z.of_nat (r - RMontRR)))
               | None => None end.
Proof.
  intros PL r H. apply mont_ref_cases in H. destruct H as [->|[->| ->]]; cbn; destruct (pl_mont PL) as [[am qm]|]; try reflexivity.
  rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pl_wf_stored : forall PL r p, pl_wf PL -> pl_bn PL r = Some p -> stored_ref r.
Proof. intros PL r p [W _] E. destruct (W r p E) as (H1 & H2 & H3 & _). split; [exact H1| split; assumption]. Qed.

(* [comment removed for export] *)
Lemma pl_of_cases : forall PL r p, pl_of PL r = Some p ->
     (r = ROne /\ p = PStatic CONST_ONE)
  \/ (exists am qm, mont_ref r = true /\ pl_mont PL = Some (am, qm) /\ p = PHeap (am + 24 * Z.of_nat (r - RMontRR)) qm (24 * Z.of_nat (r - RMontRR))
                   /\ 0 <= 24 * Z.of_nat (r - RMontRR) <= 48)
  \/ (stored_ref r /\ pl_bn PL r = Some p).
Proof.
  intros PL r p E. destruct (Nat.eq_dec r ROne) as [->|NE]; [left; rewrite pl_of_one in E; injection E as <-; auto|].
  destruct (mont_ref r) eqn:M.
  - right; left. rewrite (pl_of_mont PL r M) in E. destruct (pl_mont PL) as [[am qm]|]; [|discriminate E]. injection E as <-.
    exists am, qm. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    apply mont_ref_cases in M. destruct M as [->|[->| ->]]; cbn; lia.
  - right; right. destruct (Nat.ltb_spec r NFIX) as [Hr|Hr]; [|rewrite pl_of_ge in E by exact Hr; discriminate E].
    assert (S : stored_ref r) by (split; [exact Hr| split; [exact NE| exact M]]). split; [exact S|]. rewrite <- (pl_of_stored PL r S). exact E.
Qed.

Lemma pl_set_same : forall PL r p, pl_bn (pl_set PL r p) r = p.
Proof. intros. unfold pl_set. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma pl_set_other : forall PL r r' p, r' <> r -> pl_bn (pl_set PL r p) r' = pl_bn PL r'.
Proof. intros PL r r' p H. unfold pl_set. cbn. replace (r' =? r)%nat with false by (symmetry; apply Nat.eqb_neq; exact H). reflexivity. Qed.

Lemma pl_of_set_same : forall PL r p, stored_ref r -> pl_of (pl_set PL r p) r = p.
Proof. intros PL r p S. rewrite pl_of_stored by exact S. apply pl_set_same. Qed.

Lemma pl_of_set_other : forall PL r r' p, r' <> r -> pl_of (pl_set PL r p) r' = pl_of PL r'.
Proof.
  intros PL r r' p NE. unfold pl_of. cbn [pl_mont pl_set pl_bn].
  replace (r' =? r)%nat with false by (symmetry; apply Nat.eqb_neq; exact NE). reflexivity.
Qed.

Lemma pl_of_set_ctx : forall PL c r, pl_of (pl_set_ctx PL c) r = pl_of PL r.
Proof. reflexivity. Qed.

Lemma pl_of_set_recp : forall PL rc r, pl_of (pl_set_recp PL rc) r = pl_of PL r.
Proof. intros PL rc r. reflexivity. Qed.

Lemma pl_of_set_mont_other : forall PL mo r, mont_ref r = false -> pl_of (pl_set_mont PL mo) r = pl_of PL r.
Proof.
  intros PL mo r M. unfold pl_of. cbn [pl_mont pl_set_mont pl_bn]. unfold mont_ref in M. rewrite !Bool.orb_false_iff in M.
  destruct M as [[E1 E2] E3]. rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ref_at_fixed : forall s OW PL r a, (r < NFIX)%nat -> ref_at s OW PL r a <-> exists p, pl_of PL r = Some p /\ place_addr p = a.
Proof. intros s OW PL r a H. unfold ref_at. replace (r <? NFIX)%nat with true by (symmetry; apply Nat.ltb_lt; exact H). tauto. Qed.

Lemma ref_at_pool : forall s OW PL i a,
  ref_at s OW PL (RPool i) a <->
  exists q H, nth_error (gx_items (st_ctx s)) (i / BN_CTX_POOL_SIZE)%nat = Some q /\ In (q, H, ITEM_SZ) OW /\ a = H + 24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat.
Proof.
  intros s OW PL i a. unfold ref_at, RPool. replace (NFIX + i <? NFIX)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (NFIX + i - NFIX)%nat with i by lia. tauto.
Qed.

Lemma ref_at_one : forall s OW PL, ref_at s OW PL ROne CONST_ONE.
Proof. intros. apply ref_at_fixed; [unfold ROne, NFIX; lia|]. exists (PStatic CONST_ONE). split; [apply pl_of_one| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma ref_at_setbn : forall s OW PL r b r' a, ref_at (setbn r b s) OW PL r' a <-> ref_at s OW PL r' a.
Proof. intros. unfold ref_at. rewrite st_ctx_setbn. tauto. Qed.

Lemma ref_at_set_mont : forall s ri n0 OW PL r a, ref_at (set_mont ri n0 s) OW PL r a <-> ref_at s OW PL r a.
Proof. intros. unfold ref_at. cbn [st_ctx set_mont]. tauto. Qed.

Lemma ref_at_set_recp : forall s x y OW PL r a, ref_at (set_recp x y s) OW PL r a <-> ref_at s OW PL r a.
Proof. intros. unfold ref_at. cbn [st_ctx set_recp]. tauto. Qed.

Lemma ref_at_fixed_indep : forall s s' OW OW' PL r a, (r < NFIX)%nat -> ref_at s OW PL r a -> ref_at s' OW' PL r a.
Proof. intros s s' OW OW' PL r a Hr H. apply ref_at_fixed; [exact Hr|]. apply ref_at_fixed in H; [exact H| exact Hr]. Qed.

Lemma ref_at_pl_other : forall s OW PL r p r' a, r' <> r -> ref_at s OW (pl_set PL r p) r' a <-> ref_at s OW PL r' a.
Proof.
  intros s OW PL r p r' a H. unfold ref_at. destruct (r' <? NFIX)%nat; [|tauto].
  rewrite pl_of_set_other by exact H. tauto.
Qed.

Lemma ref_at_pl_ctx : forall s OW PL c r a, ref_at s OW (pl_set_ctx PL c) r a <-> ref_at s OW PL r a.
Proof. intros. unfold ref_at. rewrite pl_of_set_ctx. tauto. Qed.

Lemma ref_at_pl_recp : forall s OW PL rc r a, ref_at s OW (pl_set_recp PL rc) r a <-> ref_at s OW PL r a.
Proof. intros s OW PL rc r a. unfold ref_at. rewrite pl_of_set_recp. tauto. Qed.

Lemma ref_at_pl_mont_other : forall s OW PL mo r a, mont_ref r = false -> ref_at s OW (pl_set_mont PL mo) r a <-> ref_at s OW PL r a.
Proof. intros s OW PL mo r a M. unfold ref_at. destruct (r <? NFIX)%nat; [|tauto]. rewrite pl_of_set_mont_other by exact M. tauto. Qed.

Lemma ref_at_ow_mono : forall s OW OW' PL r a, (forall b, In b OW -> In b OW') -> ref_at s OW PL r a -> ref_at s OW' PL r a.
Proof.
  intros s OW OW' PL r a HI H. unfold ref_at in *. destruct (r <? NFIX)%nat; [exact H|].
  destruct H as (q & H0 & E & Hin & Ea). exists q, H0. split; [exact E|]. split; [apply HI; exact Hin| exact Ea].
Qed.

(* [comment removed for export] *)
Lemma ref_at_items_app : forall s c' OW PL r a extra,
  gx_items c' = gx_items (st_ctx s) ++ extra -> ref_at s OW PL r a -> ref_at (set_ctx c' s) OW PL r a.
Proof.
  intros s c' OW PL r a extra E H. unfold ref_at in *. destruct (r <? NFIX)%nat; [exact H|].
  destruct H as (q & H0 & Eq & Hin & Ea). exists q, H0. cbn [st_ctx set_ctx]. rewrite E. split; [|split; assumption].
  rewrite nth_error_app1; [exact Eq|]. apply nth_error_Some. congruence.
Qed.

Lemma ref_at_same_items : forall s c' OW PL r a,
  gx_items c' = gx_items (st_ctx s) -> ref_at s OW PL r a <-> ref_at (set_ctx c' s) OW PL r a.
Proof.
  intros s c' OW PL r a E. unfold ref_at. cbn [st_ctx set_ctx]. rewrite E. tauto.
Qed.

(* [comment removed for export] *)
Lemma pl_frames_n_In : forall PL n iv, In iv (pl_frames_n PL n) <-> exists k, (k < n)%nat /\ In iv (fr_ivs (pl_bn PL k)).
Proof.
  intros PL n iv. induction n as [|n IH]; cbn [pl_frames_n].
  - split; [intros []| intros (k & Hk & _); lia].
  - rewrite in_app_iff, IH. split.
    + intros [H|(k & Hk & H)]; [exists n; split; [lia| exact H]| exists k; split; [lia| exact H]].
    + intros (k & Hk & H). destruct (Nat.eq_dec k n) as [->|NE]; [left; exact H| right; exists k; split; [lia| exact H]].
Qed.

Lemma pl_frames_In : forall PL iv, In iv (pl_frames PL) <-> (exists r, (r < NFIX)%nat /\ In iv (fr_ivs (pl_bn PL r))) \/ In iv (recp_ivs (pl_recp PL)).
Proof. intros. unfold pl_frames. rewrite in_app_iff, pl_frames_n_In. tauto. Qed.

Lemma pl_frames_recp : forall PL c, pl_recp PL = Some c -> In (c, c + RECP_SC_SZ) (pl_frames PL).
Proof. intros PL c E. apply pl_frames_In. right. rewrite E. left. reflexivity. Qed.

Lemma pl_frames_empty : pl_frames pl_empty = [].
Proof. reflexivity. Qed.

Lemma pl_frames_in_mono : forall PL lo lo' hi hi', pl_frames_in PL lo hi -> lo' <= lo -> hi <= hi' -> pl_frames_in PL lo' hi'.
Proof. intros PL lo lo' hi hi' H H1 H2 iv Hiv. destruct (H iv Hiv). lia. Qed.

Lemma pl_frames_set_ctx : forall PL c, pl_frames (pl_set_ctx PL c) = pl_frames PL.
Proof. reflexivity. Qed.

Lemma pl_frames_set_mont : forall PL mo, pl_frames (pl_set_mont PL mo) = pl_frames PL.
Proof. reflexivity. Qed.

Lemma pl_frames_set_recp_In : forall PL rc iv, In iv (pl_frames (pl_set_recp PL rc)) -> In iv (recp_ivs rc) \/ In iv (pl_frames PL).
Proof.
  intros PL rc iv H. apply pl_frames_In in H. destruct H as [(k & Hk & H)|H]; [|left; exact H].
  right. apply pl_frames_In. left. exists k. exact (conj Hk H).
Qed.

(* [comment removed for export] *)
Lemma pl_frames_set_In : forall PL r p iv, In iv (pl_frames (pl_set PL r p)) -> In iv (fr_ivs p) \/ In iv (pl_frames PL).
Proof.
  intros PL r p iv H. apply pl_frames_In in H. destruct H as [(k & Hk & H)|H].
  - destruct (Nat.eq_dec k r) as [->|NE].
    + rewrite pl_set_same in H. left. exact H.
    + rewrite pl_set_other in H by exact NE. right. apply pl_frames_In. left. exists k. auto.
  - right. apply pl_frames_In. right. exact H.
Qed.

Lemma pl_frames_set_In_old : forall PL r p iv, In iv (pl_frames PL) -> pl_bn PL r = None \/ (NFIX <= r)%nat -> In iv (pl_frames (pl_set PL r p)).
Proof.
  intros PL r p iv H Hr. apply pl_frames_In in H. apply pl_frames_In. destruct H as [(k & Hk & H)|H]; [left| right; exact H]. exists k. split; [exact Hk|].
  destruct (Nat.eq_dec k r) as [->|NE]; [|rewrite pl_set_other by exact NE; exact H].
  destruct Hr as [E|Hr]; [rewrite E in H; destruct H| lia].
Qed.

(* [comment removed for export] *)
Lemma pl_frames_in_set_heap : forall PL r a q off lo hi, pl_frames_in PL lo hi -> fr_ivs (pl_bn PL r) = [] ->
  pl_frames_in (pl_set PL r (Some (PHeap a q off))) lo hi.
Proof.
  intros PL r a q off lo hi H E iv Hiv. apply pl_frames_set_In in Hiv. destruct Hiv as [[]|Hiv]. apply H. exact Hiv.
Qed.

Lemma pl_frames_in_set_none : forall PL r lo hi, pl_frames_in PL lo hi -> pl_frames_in (pl_set PL r None) lo hi.
Proof. intros PL r lo hi H iv Hiv. apply pl_frames_set_In in Hiv. destruct Hiv as [[]|Hiv]. apply H. exact Hiv. Qed.

Lemma pl_frames_in_set_recp_none : forall PL lo hi, pl_frames_in PL lo hi -> pl_frames_in (pl_set_recp PL None) lo hi.
Proof. intros PL lo hi H iv Hiv. apply pl_frames_set_recp_In in Hiv. destruct Hiv as [[]|Hiv]. apply H. exact Hiv. Qed.

Lemma pl_frames_in_set_recp : forall PL c lo hi, pl_frames_in PL lo hi -> lo <= c -> c + RECP_SC_SZ <= hi -> pl_frames_in (pl_set_recp PL (Some c)) lo hi.
Proof.
  intros PL c lo hi H H1 H2 iv Hiv. apply pl_frames_set_recp_In in Hiv. destruct Hiv as [[<-|[]]|Hiv]; [cbn [fst snd]; lia|]. apply H. exact Hiv.
Qed.

Lemma pl_frames_in_empty : forall lo hi, pl_frames_in pl_empty lo hi.
Proof. intros lo hi iv Hiv. rewrite pl_frames_empty in Hiv. destruct Hiv. Qed.

(* [comment removed for export] *)
Lemma pl_frames_outside : forall PL lo hi x, pl_frames_in PL lo hi -> x < lo \/ hi <= x -> ~ rin_ivs (pl_frames PL) x.
Proof.
  intros PL lo hi x H Hx. unfold pl_frames_in in H. revert H. generalize (pl_frames PL) as L. intros L.
  induction L as [|iv l IH]; intros H; cbn [LibKitA.rin_ivs]; [tauto|].
  intros [Hiv|Hl].
  - destruct (H iv ltac:(left; reflexivity)). lia.
  - apply IH; [|exact Hl]. intros iv' Hiv'. apply H. right. exact Hiv'.
Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. intros X Y a. induction X as [|iv X IH]; cbn [rin_ivs app]; [tauto|]. rewrite IH. tauto. Qed.

Lemma rin_ivs_In : forall X a, rin_ivs X a <-> exists iv, In iv X /\ fst iv <= a < snd iv.
Proof.
  intros X a. induction X as [|iv X IH]; cbn [rin_ivs In].
  - split; [intros []| intros (iv & [] & _)].
  - rewrite IH. split.
    + intros [H|(iv' & Hin & H)]; [exists iv; auto| exists iv'; auto].
    + intros (iv' & [<-|Hin] & H); [left; exact H| right; exists iv'; auto].
Qed.

(* [comment removed for export] *)
Lemma xw_client : forall PL LB SP SPc B x, pl_frames_in PL SPc B -> SP <= x < SPc -> SPc <= USTACK_TOP -> ~ rin_ivs LIBW_bgr x -> ax_client LB SP (XW PL) x.
Proof.
  intros PL LB SP SPc B x PF Hx HTOP HL. split; [|left; lia]. unfold XW. rewrite rin_ivs_app. intros [H|H]; [exact (HL H)|].
  eapply pl_frames_outside; [exact PF| left; exact (proj2 Hx)| exact H].
Qed.

(* [comment removed for export] *)
Lemma pl_bn_ids_In : forall PL n q, In q (pl_bn_ids PL n) <-> exists k a off, (k < n)%nat /\ pl_bn PL k = Some (PHeap a q off).
Proof.
  intros PL n q. induction n as [|n IH]; cbn [pl_bn_ids].
  - split; [intros []| intros (k & a & off & Hk & _); lia].
  - rewrite in_app_iff, IH. split.
    + intros [H|(k & a & off & Hk & E)]; [|exists k, a, off; split; [lia| exact E]].
      destruct (pl_bn PL n) as [[a q' off|a|a d|a]|] eqn:E; cbn [In] in H; try tauto. destruct H as [<-|[]]. exists n, a, off. split; [lia| exact E].
    + intros (k & a & off & Hk & E). destruct (Nat.eq_dec k n) as [->|NE]; [left; rewrite E; left; reflexivity| right]. exists k, a, off. split; [lia| exact E].
Qed.

(* [comment removed for export] *)
Lemma pl_bn_ids_nodup_neq : forall PL n r r' a a' q q' off off',
  List.NoDup (pl_bn_ids PL n) -> (r < n)%nat -> (r' < n)%nat -> r <> r' ->
  pl_bn PL r = Some (PHeap a q off) -> pl_bn PL r' = Some (PHeap a' q' off') -> q <> q'.
Proof.
  intros PL n. induction n as [|n IH]; intros r r' a a' q q' off off' ND Hr Hr' NE E E'; [lia|].
  cbn [pl_bn_ids] in ND.
  destruct (Nat.eq_dec r n) as [->|NEr]; [|destruct (Nat.eq_dec r' n) as [->|NEr']].
  - rewrite E in ND. cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hn _]. intros <-. apply Hn. apply pl_bn_ids_In.
    exists r', a', off'. split; [lia| exact E'].
  - rewrite E' in ND. cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hn _]. intros ->. apply Hn. apply pl_bn_ids_In.
    exists r, a, off. split; [lia| exact E].
  - eapply (IH r r'); try eassumption; try lia. eapply nodup_app_r. exact ND.
Qed.

Lemma pl_bn_ids_set_none : forall PL n r q, In q (pl_bn_ids (pl_set PL r None) n) -> In q (pl_bn_ids PL n).
Proof.
  intros PL n r q H. apply pl_bn_ids_In in H. apply pl_bn_ids_In. destruct H as (k & a & off & Hk & E).
  destruct (Nat.eq_dec k r) as [->|NE]; [rewrite pl_set_same in E; discriminate E|]. rewrite pl_set_other in E by exact NE. exists k, a, off. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ro_cells_recast : forall m A cs cs', ro_cells ctasegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctasegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

Definition DATA_ONE_BYTES : list byte := [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma data_one_cells : forall m, mem_inv ctasegs m -> ro_cells ctasegs m DATA_ONE [C8 (wz 1)].
Proof.
  intros m MI. pose proof (ro_cells_image ctasegs m DATA_ONE DATA_ONE_BYTES MI ltac:(vm_compute; reflexivity) ltac:(unfold DATA_ONE; lia)
                             ltac:(cbn; unfold DATA_ONE; lia)) as H.
  eapply ro_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Goal img_bytesb CONST_ONE (cells_bytes (bn_cells DATA_ONE (@bn_const_one bptr))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma const_one_cells_of_relro : forall m, relro_pristine m -> const_one_cells m.
Proof.
  intros m R. unfold const_one_cells. apply (relro_ro_cells m CONST_ONE _ R).
  - cbn. repeat split; exact I.
  - unfold CONST_ONE, RELRO_LO. lia.
  - cbn. unfold CONST_ONE, RELRO_HI. lia.
  - vm_compute. reflexivity.
Qed.
Lemma const_one_cells_of_art : forall Σ m, ART RT Σ m -> const_one_cells m.
Proof. intros Σ m HA. apply const_one_cells_of_relro. exact (af_relro RT AF Σ m HA). Qed.
Lemma const_one_cells_of_heap : forall Σ OW LB m, AHEAP Σ OW LB m -> const_one_cells m.
Proof. intros Σ OW LB m H. eapply const_one_cells_of_art. exact (AH_art _ _ _ _ H). Qed.

(* [comment removed for export] *)
Goal img_bytesb GOT_BN_ADD (cells_bytes [C8 (wz 0x235c38)]) = true /\ img_bytesb GOT_BN_SUB (cells_bytes [C8 (wz 0x23633c)]) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma got_arith_cells_of_relro : forall m, relro_pristine m -> got_arith_cells m.
Proof.
  intros m R. unfold got_arith_cells. split.
  - apply (relro_ro_cells m GOT_BN_ADD _ R).
    + cbn. repeat split; exact I.
    + unfold GOT_BN_ADD, RELRO_LO. lia.
    + cbn. unfold GOT_BN_ADD, RELRO_HI. lia.
    + vm_compute. reflexivity.
  - apply (relro_ro_cells m GOT_BN_SUB _ R).
    + cbn. repeat split; exact I.
    + unfold GOT_BN_SUB, RELRO_LO. lia.
    + cbn. unfold GOT_BN_SUB, RELRO_HI. lia.
    + vm_compute. reflexivity.
Qed.
Lemma got_arith_cells_of_art : forall Σ m, ART RT Σ m -> got_arith_cells m.
Proof. intros Σ m HA. apply got_arith_cells_of_relro. exact (af_relro RT AF Σ m HA). Qed.
Lemma got_arith_cells_of_heap : forall Σ OW LB m, AHEAP Σ OW LB m -> got_arith_cells m.
Proof. intros Σ OW LB m H. eapply got_arith_cells_of_art. exact (AH_art _ _ _ _ H). Qed.

(* [comment removed for export] *)
Definition bn_fp (OW : list block) (pl : option place) (a : Z) (b : BN) (x : Z) : Prop :=
  (a <= x < a + 24)
  \/ (exists p D, bn_d b = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ D <= x < D + 8 * Z.of_nat (bn_dmax b))
  \/ (exists y d, pl = Some (PFrameBuf y d) /\ d <= x < d + TMOD_BUF_SZ).

Lemma bn_arr_of_u64arr : forall m m' OW pl D (b : BN),
  bn_arr m OW pl D b -> u64arr ctasegs m' D (wlimbs (bn_buf b)) -> bn_arr m' OW pl D b.
Proof.
  intros m m' OW pl D b H U. unfold bn_arr in *. destruct (bn_d b); [destruct H; split; assumption|].
  destruct pl as [[x q off|x|x d|x]|]; try exact H. destruct H as (HD & _ & HL). split; [exact HD|]. split; [exact U| exact HL].
Qed.

(* [comment removed for export] *)
Lemma bn_rep_transport : forall P m m' OW OW' pl a b,
  agree_on P m m' -> (forall x, bn_fp OW pl a b x -> P x) ->
  (forall p D, bn_d b = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW') ->
  bn_rep m OW pl a b -> bn_rep m' OW' pl a b.
Proof.
  intros P m m' OW OW' pl a b AG HP HOW (D & HC & HA). exists D. split.
  - unfold struct_cells in *. destruct pl as [[x q off|x|x d|x]|];
      first [ exact HC
            | eapply rw_cells_agree; [exact AG| exact HC|]; intros y Hy; apply HP; left; cbn in Hy; lia ].
  - unfold bn_arr in *. destruct (bn_d b) as [p|] eqn:E.
    + destruct HA as [Hin Harr]. split; [apply HOW; [reflexivity| exact Hin]|].
      eapply LibKitA.u64arr_agree; [exact AG| exact Harr|]. intros x Hx. apply HP. right. left. exists p, D. rewrite wlimbs_length in Hx.
      split; [exact E|]. split; [exact Hin|]. unfold bn_dmax. lia.
    + destruct pl as [[x q off|x|x d|x]|]; try exact HA.
      destruct HA as (HD & HU & HL). split; [exact HD|]. split; [|exact HL].
      eapply LibKitA.u64arr_agree; [exact AG| exact HU|]. intros y Hy. apply HP. right. right. exists x, d. rewrite wlimbs_length, HL in Hy.
      subst D. split; [reflexivity|]. unfold TMOD_BUF_SZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bns_gen_impl : forall (R R' : bnR) l a i,
  (forall j b, nth_error l j = Some b -> R (a + 24 * Z.of_nat j) b (RPool (i + j)) -> R' (a + 24 * Z.of_nat j) b (RPool (i + j))) ->
  bns_gen R a l i -> bns_gen R' a l i.
Proof.
  intros R R' l. induction l as [|b l IH]; intros a i H HG; [exact I|].
  cbn [bns_gen] in *. destruct HG as [H1 H2]. split.
  - specialize (H 0%nat b eq_refl). rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r in H. apply H. exact H1.
  - apply IH; [|exact H2]. intros j b' Hj HR. specialize (H (S j) b' Hj).
    replace (a + 24 * Z.of_nat (S j)) with (a + 24 + 24 * Z.of_nat j) in H by lia.
    unfold RPool in *. replace (NFIX + (i + S j))%nat with (NFIX + (S i + j))%nat in H by lia. apply H. exact HR.
Qed.

Lemma bns_gen_nth : forall (R : bnR) l a i j d, bns_gen R a l i -> (j < length l)%nat ->
  R (a + 24 * Z.of_nat j) (nth j l d) (RPool (i + j)).
Proof.
  intros R l. induction l as [|b l IH]; intros a i j d HG Hj; cbn in Hj; [lia|].
  cbn [bns_gen] in HG. destruct HG as [H1 H2]. destruct j as [|j].
  - cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r. exact H1.
  - cbn [nth]. replace (a + 24 * Z.of_nat (S j)) with (a + 24 + 24 * Z.of_nat j) by lia.
    unfold RPool in *. replace (NFIX + (i + S j))%nat with (NFIX + (S i + j))%nat by lia. apply IH; [exact H2| lia].
Qed.

Lemma bns_gen_set : forall (R : bnR) l a i j b', bns_gen R a l i -> (j < length l)%nat ->
  R (a + 24 * Z.of_nat j) b' (RPool (i + j)) -> bns_gen R a (list_set l j b') i.
Proof.
  intros R l. induction l as [|b l IH]; intros a i j b' HG Hj HR; cbn in Hj; [lia|].
  cbn [bns_gen] in HG. destruct HG as [H1 H2]. destruct j as [|j]; cbn [list_set bns_gen].
  - rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r in HR. split; assumption.
  - split; [exact H1|]. apply IH; [exact H2| lia|].
    replace (a + 24 + 24 * Z.of_nat j) with (a + 24 * Z.of_nat (S j)) by lia.
    unfold RPool in *. replace (NFIX + (S i + j))%nat with (NFIX + (i + S j))%nat by lia. exact HR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma items_gen_length : forall R cxo m OW items Hs vals k prev,
  items_gen R cxo m OW items Hs vals k prev -> length Hs = length items /\ length vals = (BN_CTX_POOL_SIZE * length items)%nat.
Proof.
  intros R cxo m OW items. induction items as [|q items IH]; intros Hs vals k prev H; destruct Hs as [|H0 Hs]; cbn [items_gen] in H; try contradiction.
  - subst vals. split; reflexivity.
  - destruct H as (_ & HL16 & _ & _ & H). destruct (IH _ _ _ _ H) as [L1 L2]. cbn [length]. split; [lia|].
    pose proof (f_equal (@length _) (firstn_skipn BN_CTX_POOL_SIZE vals)) as E. rewrite length_app, L2, length_firstn in E.
    unfold BN_CTX_POOL_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma items_gen_nth : forall R cxo m OW items Hs vals k0 prev k q,
  items_gen R cxo m OW items Hs vals k0 prev -> nth_error items k = Some q ->
  exists H, nth_error Hs k = Some H /\ In (q, H, ITEM_SZ) OW
            /\ bns_gen R H (firstn BN_CTX_POOL_SIZE (skipn (BN_CTX_POOL_SIZE * k) vals)) (BN_CTX_POOL_SIZE * (k0 + k)).
Proof.
  intros R cxo m OW items. induction items as [|q0 items IH]; intros Hs vals k0 prev k q HG Hk.
  - destruct k; discriminate Hk.
  - destruct Hs as [|H0 Hs]; cbn [items_gen] in HG; [contradiction|]. destruct HG as (Hin & H16 & Hb & _ & HG).
    destruct k as [|k].
    + injection Hk as <-. exists H0. cbn [nth_error]. rewrite Nat.mul_0_r, Nat.add_0_r. cbn [skipn]. split; [reflexivity|]. split; [exact Hin| exact Hb].
    + cbn in Hk. destruct (IH _ _ _ _ _ _ HG Hk) as (H & E & Hin' & Hb'). exists H. split; [exact E|]. split; [exact Hin'|].
      rewrite skipn_skipn in Hb'. replace (BN_CTX_POOL_SIZE * k + BN_CTX_POOL_SIZE)%nat with (BN_CTX_POOL_SIZE * S k)%nat in Hb' by lia.
      replace (S k0 + k)%nat with (k0 + S k)%nat in Hb' by lia. exact Hb'.
Qed.

(* [comment removed for export] *)
Lemma items_gen_links : forall R m OW items Hs vals k0 prev k H,
  items_gen R false m OW items Hs vals k0 prev -> nth_error Hs k = Some H ->
  rw_cells ctasegs m (H + 384) [C8 (wz (match k with O => prev | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))].
Proof.
  intros R m OW items. induction items as [|q0 items IH]; intros Hs vals k0 prev k H HG Hk;
    destruct Hs as [|H0 Hs]; cbn [items_gen] in HG; try contradiction; [destruct k; discriminate Hk|].
  destruct HG as (Hin & H16 & Hb & HL & HG). destruct k as [|k].
  - injection Hk as <-. cbn [nth]. specialize (HL eq_refl). destruct Hs as [|H1 Hs]; exact HL.
  - cbn in Hk. pose proof (IH _ _ _ _ k H HG Hk) as X. cbn [nth]. destruct k as [|k]; [|exact X].
    destruct Hs as [|H1 Hs]; [discriminate Hk|]. injection Hk as <-. exact X.
Qed.

Lemma items_gen_impl : forall (R R' : bnR) cxo m OW items Hs vals k0 prev,
  (forall a b i, R a b (RPool i) -> R' a b (RPool i)) ->
  items_gen R cxo m OW items Hs vals k0 prev -> items_gen R' cxo m OW items Hs vals k0 prev.
Proof.
  intros R R' cxo m OW items. induction items as [|q items IH]; intros Hs vals k0 prev HR HG; destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & HL & HG). split; [exact Hin|]. split; [exact H16|]. split; [|split; [exact HL| apply IH; [exact HR| exact HG]]].
  eapply bns_gen_impl; [|exact Hb]. intros j b _ H. apply HR. exact H.
Qed.

(* [comment removed for export] *)
Lemma items_gen_open : forall (R : bnR) cxo m OW items Hs vals k0 prev,
  items_gen R cxo m OW items Hs vals k0 prev -> items_gen R true m OW items Hs vals k0 prev.
Proof.
  intros R cxo m OW items. induction items as [|q items IH]; intros Hs vals k0 prev HG; destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & HL & HG). repeat (split; [assumption|]). split; [intros E; discriminate E| apply IH; exact HG].
Qed.

Lemma items_gen_mem_indep : forall (R : bnR) m m' OW items Hs vals k0 prev,
  items_gen R true m OW items Hs vals k0 prev -> items_gen R true m' OW items Hs vals k0 prev.
Proof.
  intros R m m' OW items. induction items as [|q items IH]; intros Hs vals k0 prev HG; destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & HL & HG). repeat (split; [assumption|]). split; [intros E; discriminate E| apply IH; exact HG].
Qed.

Lemma items_gen_close : forall (R : bnR) m OW items Hs vals k0 prev,
  items_gen R true m OW items Hs vals k0 prev ->
  (forall k H, nth_error Hs k = Some H ->
     rw_cells ctasegs m (H + 384) [C8 (wz (match k with O => prev | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))]) ->
  items_gen R false m OW items Hs vals k0 prev.
Proof.
  intros R m OW items. induction items as [|q items IH]; intros Hs vals k0 prev HG HL; destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & _ & HG). repeat (split; [assumption|]). split.
  - intros _. specialize (HL 0%nat H0 eq_refl). cbn [nth] in HL. destruct Hs; exact HL.
  - apply IH; [exact HG|]. intros k H Hk. specialize (HL (S k) H Hk). cbn [nth] in HL. destruct k as [|k]; [|exact HL].
    destruct Hs as [|H1 Hs]; [discriminate Hk|]. injection Hk as <-. exact HL.
Qed.

(* [comment removed for export] *)
Lemma items_gen_impl_idx : forall (R R' : bnR) cxo m OW items Hs vals k0 prev,
  (forall k q H j, nth_error items k = Some q -> nth_error Hs k = Some H -> (j < BN_CTX_POOL_SIZE)%nat ->
     R (H + 24 * Z.of_nat j) (nth (BN_CTX_POOL_SIZE * k + j) vals (bn_nil 0)) (RPool (BN_CTX_POOL_SIZE * (k0 + k) + j)) ->
     R' (H + 24 * Z.of_nat j) (nth (BN_CTX_POOL_SIZE * k + j) vals (bn_nil 0)) (RPool (BN_CTX_POOL_SIZE * (k0 + k) + j))) ->
  items_gen R cxo m OW items Hs vals k0 prev -> items_gen R' cxo m OW items Hs vals k0 prev.
Proof.
  intros R R' cxo m OW items. induction items as [|q items IH]; intros Hs vals k0 prev HR HG; destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & HL & HG). split; [exact Hin|]. split; [exact H16|]. split; [|split; [exact HL|]].
  - eapply bns_gen_impl; [|exact Hb]. intros j b Hj H.
    assert (Hj16 : (j < BN_CTX_POOL_SIZE)%nat).
    { apply nth_error_Some in Hj || (assert (j < length (firstn BN_CTX_POOL_SIZE vals))%nat by (apply nth_error_Some; congruence)).
      all: rewrite length_firstn in *; lia. }
    pose proof (HR 0%nat q H0 j eq_refl eq_refl Hj16) as X. rewrite Nat.mul_0_r, Nat.add_0_l, Nat.add_0_r in X.
    assert (Eb : nth j vals (bn_nil 0) = b).
    { rewrite <- (nth_firstn_lt' vals BN_CTX_POOL_SIZE j (bn_nil 0) Hj16). apply nth_error_nth. exact Hj. }
    rewrite Eb in X. apply X. exact H.
  - apply IH; [|exact HG]. intros k q' H j Hk HH Hj HRk.
    specialize (HR (S k) q' H j Hk HH Hj). rewrite nth_skipn' in HRk |- *.
    replace (BN_CTX_POOL_SIZE + (BN_CTX_POOL_SIZE * k + j))%nat with (BN_CTX_POOL_SIZE * S k + j)%nat in * by lia.
    replace (S k0 + k)%nat with (k0 + S k)%nat in * by lia. apply HR. exact HRk.
Qed.

(* [comment removed for export] *)
Lemma items_gen_transport : forall P (R R' : bnR) cxo m m' OW OW' items Hs vals k0 prev,
  items_gen R cxo m OW items Hs vals k0 prev -> agree_on P m m' ->
  (forall q H, In q items -> In (q, H, ITEM_SZ) OW -> In (q, H, ITEM_SZ) OW' /\ (cxo = false -> forall x, H + 384 <= x < H + 400 -> P x)) ->
  items_gen R cxo m' OW' items Hs vals k0 prev.
Proof.
  intros P R R' cxo m m' OW OW' items. induction items as [|q items IH]; intros Hs vals k0 prev HG AG HOW;
    destruct Hs as [|H0 Hs]; cbn [items_gen] in *; try exact HG.
  destruct HG as (Hin & H16 & Hb & HL & HG). destruct (HOW q H0 ltac:(left; reflexivity) Hin) as [Hin' HP].
  split; [exact Hin'|]. split; [exact H16|]. split; [exact Hb|]. split.
  - intros Ec. eapply rw_cells_agree; [exact AG| exact (HL Ec)|]. intros x Hx. apply (HP Ec). cbn in Hx. lia.
  - eapply IH; [exact HG| exact AG|]. intros q' H' Hq' Hin''. apply HOW; [right; exact Hq'| exact Hin''].
Qed.

(* [comment removed for export] *)
Lemma firstn_list_set_lt : forall {A} (l : list A) n j b, (j < n)%nat -> firstn n (list_set l j b) = list_set (firstn n l) j b.
Proof.
  intros A l. induction l as [|x l IH]; intros n j b Hj; cbn [list_set]; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; cbn [firstn list_set]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

Lemma skipn_list_set_lt : forall {A} (l : list A) c i b, (i < c)%nat -> skipn c (list_set l i b) = skipn c l.
Proof.
  intros A l. induction l as [|x l IH]; intros c i b Hi; cbn [list_set]; [reflexivity|].
  destruct i as [|i]; destruct c as [|c]; cbn [skipn list_set]; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma firstn_list_set_ge : forall {A} (l : list A) n i b, (n <= i)%nat -> firstn n (list_set l i b) = firstn n l.
Proof.
  intros A l. induction l as [|x l IH]; intros n i b Hi; cbn [list_set]; [reflexivity|].
  destruct i as [|i]; destruct n as [|n]; cbn [firstn list_set]; try lia; try reflexivity. rewrite IH by lia. reflexivity.
Qed.

Lemma skipn_list_set_ge : forall {A} (l : list A) c i b, (c <= i)%nat -> skipn c (list_set l i b) = list_set (skipn c l) (i - c) b.
Proof.
  intros A l. induction l as [|x l IH]; intros c i b Hi; cbn [list_set]; [destruct c; reflexivity|].
  destruct c as [|c]; [rewrite Nat.sub_0_r; destruct i; reflexivity|]. destruct i as [|i]; [lia|]. cbn [skipn list_set]. rewrite IH by lia.
  f_equal.
Qed.

Lemma items_gen_set : forall R cxo m OW items Hs vals k0 prev k j H b',
  items_gen R cxo m OW items Hs vals k0 prev -> nth_error Hs k = Some H -> (j < BN_CTX_POOL_SIZE)%nat ->
  R (H + 24 * Z.of_nat j) b' (RPool (BN_CTX_POOL_SIZE * (k0 + k) + j)) ->
  items_gen R cxo m OW items Hs (list_set vals (BN_CTX_POOL_SIZE * k + j) b') k0 prev.
Proof.
  intros R cxo m OW items. induction items as [|q items IH]; intros Hs vals k0 prev k j H b' HG Hk Hj HR;
    destruct Hs as [|H0 Hs]; cbn [items_gen] in HG; try contradiction; [destruct k; discriminate Hk|].
  destruct HG as (Hin & H16 & Hb & HL & HG). destruct (items_gen_length _ _ _ _ _ _ _ _ _ HG) as [L1 L2].
  destruct k as [|k].
  - injection Hk as <-. cbn [items_gen]. split; [exact Hin|]. split; [rewrite list_set_length; exact H16|]. split; [|split; [exact HL|]].
    + rewrite Nat.mul_0_r, Nat.add_0_l. rewrite (firstn_list_set_lt vals BN_CTX_POOL_SIZE j b' Hj).
      apply bns_gen_set; [exact Hb| | rewrite Nat.add_0_r in HR; exact HR].
      rewrite length_firstn. unfold BN_CTX_POOL_SIZE in *. lia.
    + rewrite Nat.mul_0_r, Nat.add_0_l. rewrite skipn_list_set_lt by exact Hj. exact HG.
  - cbn in Hk. cbn [items_gen]. split; [exact Hin|]. split; [rewrite list_set_length; exact H16|]. split; [|split; [exact HL|]].
    + rewrite firstn_list_set_ge by (unfold BN_CTX_POOL_SIZE in *; lia). exact Hb.
    + rewrite skipn_list_set_ge by (unfold BN_CTX_POOL_SIZE in *; lia).
      replace (BN_CTX_POOL_SIZE * S k + j - BN_CTX_POOL_SIZE)%nat with (BN_CTX_POOL_SIZE * k + j)%nat by (unfold BN_CTX_POOL_SIZE in *; lia).
      apply (IH Hs _ (S k0) H0 k j H b' HG Hk Hj). replace (S k0 + k)%nat with (k0 + S k)%nat by lia. exact HR.
Qed.

(* [comment removed for export] *)
Lemma items_gen_Hs_unique : forall R R' cxo cxo' m m' OW items Hs Hs' vals vals' k0 k0' prev prev',
  List.NoDup (map blk_id OW) ->
  items_gen R cxo m OW items Hs vals k0 prev -> items_gen R' cxo' m' OW items Hs' vals' k0' prev' -> Hs = Hs'.
Proof.
  intros R R' cxo cxo' m m' OW items. induction items as [|q items IH]; intros Hs Hs' vals vals' k0 k0' prev prev' ND HG HG';
    destruct Hs as [|H0 Hs]; destruct Hs' as [|H0' Hs']; cbn [items_gen] in HG, HG'; try contradiction; [reflexivity|].
  destruct HG as (Hin & _ & _ & _ & HG), HG' as (Hin' & _ & _ & _ & HG').
  destruct (AH_addr_unique OW q H0 ITEM_SZ H0' ITEM_SZ ND Hin Hin') as [<- _]. f_equal. eapply IH; [exact ND| exact HG| exact HG'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma getbn_pool : forall (s : ST) i, getbn (RPool i) s = nth i (skipn NFIX (st_bns s)) (bn_nil 0).
Proof. intros s i. unfold getbn, RPool. rewrite nth_skipn'. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nth_item_slot : forall (vals : list BN) k j d, (j < BN_CTX_POOL_SIZE)%nat ->
  nth j (firstn BN_CTX_POOL_SIZE (skipn (BN_CTX_POOL_SIZE * k) vals)) d = nth (BN_CTX_POOL_SIZE * k + j) vals d.
Proof. intros vals k j d Hj. rewrite nth_firstn_lt' by exact Hj. apply nth_skipn'. Qed.

(* [comment removed for export] *)
Definition pl_blocks (OW : list block) (PL : placement) : Prop :=
     (forall r p, (r < NFIX)%nat -> pl_of PL r = Some p -> place_ok OW p)
  /\ match pl_ctx PL with Some (ac, qc) => In (qc, ac, BN_CTX_SZ) OW | None => True end
  /\ match pl_mont PL with Some (am, qm) => In (qm, am, MONT_CTX_SZ) OW | None => True end.

Lemma gen_parts : forall (R : bnR) cxo s m OW PL, bn_mem_gen R cxo s m OW PL -> pl_blocks OW PL.
Proof.
  intros R cxo s m OW PL (HF & HN & HC & HM). split; [|split].
  - intros r p Hr E. exact (proj1 (HF r p Hr E)).
  - destruct (pl_ctx PL) as [[ac qc]|]; [exact (proj1 HC)| exact I].
  - destruct (pl_mont PL) as [[am qm]|]; [exact (proj1 (proj1 HM))| exact I].
Qed.

Lemma gen_get : forall (R : bnR) cxo s m OW PL r a,
  bn_mem_gen R cxo s m OW PL -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> R a (getbn r s) r.
Proof.
  intros R cxo s m OW PL r a (HF & HN & HC & HM) ND HA. unfold ref_at in HA.
  destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - destruct HA as (p & E & Ea). destruct (HF r p Hr E) as [_ HR]. rewrite Ea in HR. exact HR.
  - destruct HA as (q & H & Eq & Hin & Ea).
    destruct (pl_ctx PL) as [[ac qc]|].
    2:{ exfalso. destruct HC as [Ec _]. rewrite Ec in Eq. cbn [gx_items gx_nil] in Eq. destruct ((r - NFIX) / BN_CTX_POOL_SIZE)%nat; cbn [nth_error] in Eq; discriminate Eq. }
    destruct HC as (Hinc & Hs & I & LHs & _ & HIT).
    destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Eq) as (H' & EH & Hin' & Hb).
    destruct (AH_addr_unique OW q H ITEM_SZ H' ITEM_SZ ND Hin Hin') as [<- _].
    pose proof (items_gen_length _ _ _ _ _ _ _ _ _ HIT) as [L1 L2].
    assert (Hk : ((r - NFIX) / BN_CTX_POOL_SIZE < length (gx_items (st_ctx s)))%nat) by (apply nth_error_Some; congruence).
    assert (Hj : ((r - NFIX) mod BN_CTX_POOL_SIZE < BN_CTX_POOL_SIZE)%nat) by (apply Nat.mod_upper_bound; unfold BN_CTX_POOL_SIZE; lia).
    pose proof (Nat.div_mod_eq (r - NFIX) BN_CTX_POOL_SIZE) as DM.
    pose proof (bns_gen_nth R _ H _ ((r - NFIX) mod BN_CTX_POOL_SIZE)%nat (bn_nil 0) Hb) as X.
    rewrite length_firstn, length_skipn, L2 in X.
    specialize (X ltac:(unfold BN_CTX_POOL_SIZE in *; nia)).
    rewrite Nat.add_0_l, nth_item_slot, <- DM in X by exact Hj. rewrite <- Ea in X.
    unfold RPool in X. replace (NFIX + (r - NFIX))%nat with r in X by lia.
    rewrite nth_skipn' in X. replace (NFIX + (r - NFIX))%nat with r in X by lia. unfold getbn. exact X.
Qed.

Lemma gen_impl : forall (R R' : bnR) cxo s m OW PL,
  (forall a b r, R a b r -> R' a b r) -> bn_mem_gen R cxo s m OW PL -> bn_mem_gen R' cxo s m OW PL.
Proof.
  intros R R' cxo s m OW PL HR (HF & HN & HC & HM).
  split; [intros r p Hr E; destruct (HF r p Hr E) as [OK H]; split; [exact OK| apply HR; exact H]|].
  split; [exact HN|]. split; [|exact HM].
  destruct (pl_ctx PL) as [[ac qc]|]; [|exact HC]. destruct HC as (Hinc & Hs & I & LHs & HCC & HIT).
  split; [exact Hinc|]. exists Hs, I. split; [exact LHs|]. split; [exact HCC|].
  eapply items_gen_impl; [|exact HIT]. intros a b i H. apply HR. exact H.
Qed.

Lemma st_bns_setbn : forall r b (s : ST), st_bns (setbn r b s) = list_set (st_bns s) r b.
Proof. reflexivity. Qed.

Lemma mont_cells_setbn : forall r b (s : ST), mont_cells (setbn r b s) = mont_cells s.
Proof. reflexivity. Qed.
Lemma recp_cells_setbn : forall r b (s : ST), recp_cells (setbn r b s) = recp_cells s.
Proof. reflexivity. Qed.

Lemma gen_set : forall (R : bnR) cxo s m OW PL r a b',
  bn_mem_gen R cxo s m OW PL -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> vref r s ->
  R a b' r -> bn_mem_gen R cxo (setbn r b' s) m OW PL.
Proof.
  intros R cxo s m OW PL r a b' (HF & HN & HC & HM) ND HA Hlen HR.
  pose proof HA as HA0. unfold ref_at in HA.
  split.
  { intros r' p Hr' E. destruct (HF r' p Hr' E) as [OK H]. split; [exact OK|].
    destruct (Nat.eq_dec r' r) as [->|NE].
    - rewrite getbn_setbn_same by exact Hlen. replace (r <? NFIX)%nat with true in HA by (symmetry; apply Nat.ltb_lt; exact Hr').
      destruct HA as (p0 & E0 & Ea). rewrite E in E0. injection E0 as <-. rewrite Ea. exact HR.
    - rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). exact H. }
  split.
  { intros r' Hr' E. destruct (Nat.eq_dec r' r) as [->|NE].
    - exfalso. replace (r <? NFIX)%nat with true in HA by (symmetry; apply Nat.ltb_lt; exact Hr'). destruct HA as (p0 & E0 & _). rewrite E in E0. discriminate E0.
    - rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). apply HN; assumption. }
  split.
  2:{ rewrite mont_cells_setbn, recp_cells_setbn. exact HM. }
  rewrite st_ctx_setbn, st_bns_setbn.
  destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - rewrite skipn_list_set_lt by exact Hr. exact HC.
  - rewrite skipn_list_set_ge by exact Hr.
    destruct HA as (q & H & Eq & Hin & Ea).
    destruct (pl_ctx PL) as [[ac qc]|].
    2:{ exfalso. destruct HC as [Ec _]. rewrite Ec in Eq. cbn [gx_items gx_nil] in Eq. destruct ((r - NFIX) / BN_CTX_POOL_SIZE)%nat; cbn [nth_error] in Eq; discriminate Eq. }
    destruct HC as (Hinc & Hs & I & LHs & HCC & HIT). split; [exact Hinc|]. exists Hs, I. split; [exact LHs|]. split; [exact HCC|].
    destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Eq) as (H' & EH & Hin' & Hb).
    destruct (AH_addr_unique OW q H ITEM_SZ H' ITEM_SZ ND Hin Hin') as [<- _].
    pose proof (Nat.div_mod_eq (r - NFIX) BN_CTX_POOL_SIZE) as DM.
    assert (Hj : ((r - NFIX) mod BN_CTX_POOL_SIZE < BN_CTX_POOL_SIZE)%nat) by (apply Nat.mod_upper_bound; unfold BN_CTX_POOL_SIZE; lia).
    rewrite DM at 1.
    eapply items_gen_set; [exact HIT| exact EH| exact Hj|].
    rewrite Nat.add_0_l, <- DM, <- Ea. unfold RPool. replace (NFIX + (r - NFIX))%nat with r by lia. exact HR.
Qed.

(* [comment removed for export] *)
Lemma gen_ref_valid : forall (R : bnR) cxo s m OW PL r a, st_wf s -> bn_mem_gen R cxo s m OW PL -> ref_at s OW PL r a -> vref r s.
Proof.
  intros R cxo s m OW PL r a (EL & _) (HF & HN & HC & HM) HA. unfold vref. rewrite EL. unfold ref_at in HA.
  destruct (Nat.ltb_spec r NFIX) as [Hr|Hr]; [lia|].
  destruct HA as (q & H & Eq & _). apply nth_error_Some_length in Eq || (assert (((r - NFIX) / BN_CTX_POOL_SIZE < length (gx_items (st_ctx s)))%nat) by (apply nth_error_Some; congruence)).
  all: pose proof (Nat.div_mod_eq (r - NFIX) BN_CTX_POOL_SIZE) as DM;
       pose proof (Nat.mod_upper_bound (r - NFIX) BN_CTX_POOL_SIZE ltac:(unfold BN_CTX_POOL_SIZE; lia)) as MB;
       unfold BN_CTX_POOL_SIZE in *; nia.
Qed.

End WithCeiling0.
