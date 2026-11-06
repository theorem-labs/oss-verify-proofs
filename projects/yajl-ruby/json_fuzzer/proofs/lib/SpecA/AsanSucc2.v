(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanFrame AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf10 AsanSucc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint gallS {R} (G : astate -> R -> Prop) (t : stree aev aans (astate * aout R)) : Prop :=
  match t with
  | SRet (s, o) => match o with ONorm r => G s r | OSpin => False | OUndef _ => True end
  | SVis e k => forall a, agrant e a -> gallS G (k a)
  end.

Definition ghoare {R} (P : astate -> Prop) (m : AM R) (G : astate -> R -> Prop) : Prop :=
  forall s, P s -> gallS G (m s).

Lemma gallS_mono : forall {R} (G G' : astate -> R -> Prop) t, gallS G t -> (forall s r, G s r -> G' s r) -> gallS G' t.
Proof.
  intros R G G' t; induction t as [[s o]|e k IH]; cbn; intros H HG; [destruct o; auto| intros a Ha; apply (IH a); auto].
Qed.

Lemma gallS_of_gall : forall {R} (G : R -> Prop) t, gall G t -> gallS (fun _ r => G r) t.
Proof. intros R G t; induction t as [[s o]|e k IH]; cbn; intros H; [destruct o; auto| intros a Ha; apply IH; auto]. Qed.

(* [comment removed for export] *)
Lemma gallS_sall_conj : forall {R} (Q : astate -> R -> Prop) (G : astate -> R -> Prop) t,
  sall (leaf_ok Q) t -> gallS G t -> gallS (fun s r => Q s r /\ G s r) t.
Proof.
  intros R Q G t; induction t as [[s o]|e k IH]; cbn; intros HQ HG.
  - destruct o as [r| |w]; cbn in HQ; auto.
  - intros a Ha. apply IH; auto.
Qed.

Lemma gallS_sbind : forall {R S} (G1 : astate -> R -> Prop) (G2 : astate -> S -> Prop)
    (t : stree aev aans (astate * aout R)) (f : astate * aout R -> stree aev aans (astate * aout S)),
  gallS G1 t ->
  (forall s r, G1 s r -> gallS G2 (f (s, ONorm r))) -> (forall s w, gallS G2 (f (s, OUndef w))) ->
  gallS G2 (sbind t f).
Proof.
  intros R S G1 G2 t; induction t as [[s o]|e k IH]; cbn; intros f Ht Hn Hu.
  - destruct o as [r| |w]; [apply Hn; exact Ht| destruct Ht| apply Hu].
  - intros a Ha. apply IH; auto.
Qed.

Lemma ghoare_of_gok : forall {R} P (m : AM R) G, gok m G -> ghoare P m (fun _ r => G r).
Proof. intros R P m G H s _. apply gallS_of_gall. apply H. Qed.

Lemma ghoare_hoare_conj : forall {R} P (m : AM R) Q G, hoare P m Q -> ghoare P m G -> ghoare P m (fun s r => Q s r /\ G s r).
Proof. intros R P m Q G HQ HG s Hs. apply gallS_sall_conj; [apply HQ, Hs| apply HG, Hs]. Qed.

Lemma ghoare_conseq : forall {R} (P P' : astate -> Prop) (m : AM R) G G',
  ghoare P m G -> (forall s, P' s -> P s) -> (forall s r, G s r -> G' s r) -> ghoare P' m G'.
Proof. intros R P P' m G G' H HP HG s Hs. eapply gallS_mono; [apply H, HP, Hs| exact HG]. Qed.

Lemma ghoare_pre : forall {R} (P : astate -> Prop) (m : AM R) G,
  (forall s, P s -> ghoare (fun s' => s' = s) m G) -> ghoare P m G.
Proof. intros R P m G H s Hs. apply (H s Hs s eq_refl). Qed.

Lemma ghoare_bind : forall {R S} (P : astate -> Prop) (m : AM R) (f : R -> AM S) G1 G2,
  ghoare P m G1 -> (forall r, ghoare (fun s => G1 s r) (f r) G2) -> ghoare P (abind m f) G2.
Proof.
  intros R S P m f G1 G2 Hm Hf s Hs. unfold abind. eapply gallS_sbind; [apply Hm, Hs| | intros; cbn; exact I].
  intros s' r Hr. cbn. apply (Hf r s' Hr).
Qed.

Lemma ghoare_ret : forall {R} (P : astate -> Prop) (r : R) G, (forall s, P s -> G s r) -> ghoare P (aret r) G.
Proof. intros R P r G H s Hs; cbn; auto. Qed.
Lemma ghoare_upd : forall (P : astate -> Prop) f G, (forall s, P s -> G (f s) tt) -> ghoare P (aupd f) G.
Proof. intros P f G H s Hs; cbn; auto. Qed.
Lemma ghoare_undef : forall {R} (P : astate -> Prop) w (G : astate -> R -> Prop), ghoare P (aundef_ w) G.
Proof. intros R P w G s Hs; cbn. exact I. Qed.

Lemma ghoare_get_bind : forall {S} (P : astate -> Prop) (f : astate -> AM S) G,
  (forall s, P s -> ghoare (fun s' => s' = s) (f s) G) -> ghoare P (abind aget f) G.
Proof. intros S P f G H s Hs. unfold abind; cbn. apply (H s Hs s eq_refl). Qed.

Lemma ghoare_upd_bind : forall {S} (P : astate -> Prop) g (f : unit -> AM S) G,
  ghoare (fun s' => exists s, P s /\ s' = g s) (f tt) G -> ghoare P (abind (aupd g) f) G.
Proof. intros S P g f G H s Hs. unfold abind; cbn. apply H. exists s; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section OPS.
Variable E : aenv.
Local Notation SB := (ae_space_beg E).
Local Notation AWF := (AWf E [] []).

(* [comment removed for export] *)
Lemma carved_pos : forall P D s c a, 1 <= c <= kLargestClassID -> AWf E P D s -> carved E s c a -> 0 < a.
Proof.
  intros P D s c a Hc WF C. destruct WF as (WE & WR & _).
  pose proof (carved_in_space E s c a Hc WR C) as [L _].
  destruct WE as (_ & HB & RS & _). clear -HB RS L. rewrite kHighMemBeg_val in HB. unfold kRegionSize in L. lia.
Qed.

Lemma gbatch_alloc : forall P s0,
  AWf E P [] s0 -> room s0 kBatchClass ->
  ghoare (fun s => s = s0) (batch_alloc E)
    (fun s' b => AWf E P [] s' /\ pframe s0 s' /\ (forall c a, carved E s0 c a -> carved E s' c a) /\ avail E [] s' kBatchClass b).
Proof.
  intros P s0 WF ROOM.
  assert (H24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  enough (G : ghoare (fun s => s = s0) (batch_alloc E) (fun _ _ => True)).
  { eapply ghoare_conseq; [apply ghoare_hoare_conj; [apply (batch_alloc_spec E P s0 WF ROOM)| exact G]| auto| intros s r [H _]; exact H]. }
  unfold batch_alloc.
  eapply ghoare_bind; [apply ghoare_hoare_conj; [apply (cache_pop_spec E P [] s0 kBatchClass H24 WF ROOM)| apply ghoare_of_gok, gok_cache_pop]|].
  intros r. apply ghoare_pre. intros s1 [(WF1 & _ & _ & _ & R1) (b & ->)].
  destruct R1 as (_ & (CV & _) & _). pose proof (carved_pos P [] s1 kBatchClass b H24 WF1 CV) as POS.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply ghoare_ret. intros; exact I.
Qed.

Lemma genqueue : forall P s0 cb n,
  AWf E (cb :: P) [] s0 -> pending s0 cb n -> room s0 kBatchClass ->
  ghoare (fun s => s = s0) (enqueue E cb n) (fun _ _ => True).
Proof.
  intros P s0 cb n WF PN ROOM. unfold enqueue. apply ghoare_get_bind. intros s ->.
  match goal with |- ghoare _ (if ?b then _ else _) _ => destruct b end.
  - eapply ghoare_bind; [apply (gbatch_alloc (cb :: P) s0 WF ROOM)|]. intros b. apply ghoare_upd. intros; exact I.
  - apply ghoare_upd. intros; exact I.
Qed.

Lemma gafree_core : forall s0 key p cm aid,
  depot_ok E s0 key -> AWF s0 ->
  as_chunks s0 !! (p - kChunkHeaderSize) = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = p ->
  room s0 kBatchClass ->
  ghoare (fun s => s = s0) (afree_core E key p) (fun _ _ => True).
Proof.
  intros s0 key p cm aid HK WF Hcm ST UB ROOM. unfold afree_core. apply ghoare_get_bind. intros s ->.
  rewrite Hcm, ST, UB, Z.eqb_refl. cbn [negb].
  set (cb := p - kChunkHeaderSize) in *.
  apply ghoare_upd_bind. apply ghoare_pre. intros s (sx & -> & ->). set (s1 := upd_ts _ s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ts| exact WF]).
  assert (HK1 : depot_ok E s1 key) by exact HK.
  eapply ghoare_bind; [apply ghoare_hoare_conj; [apply (depot_put_wf E [] [] s1 key HK1 WF1)| apply ghoare_of_gok, gok_depot_put]|].
  intros fid. apply ghoare_pre. intros s2 [(WF2 & (SR & SC & SI & SK & STQ & SG & SS & SP) & FID & NID2) _].
  assert (Hcm2 : as_chunks s2 !! cb = Some cm) by (rewrite SK; exact Hcm).
  apply ghoare_upd_bind. apply ghoare_pre. intros s (sy & -> & ->).
  destruct (AWf_flip E [] s2 cb cm aid fid WF2 Hcm2 ST FID) as [WF3 NIN].
  change (upd_chunks _ s2) with (upd_chunks (fun m => <[cb := flipped cm aid fid]> m) s2).
  set (s3 := upd_chunks _ s2) in *.
  assert (PN : pending s3 cb (cm_n cm)).
  { split; [exists (flipped cm aid fid), aid, fid; split; [cbn; apply lookup_insert_eq| split; reflexivity]|]. exact NIN. }
  assert (ROOM3 : room s3 kBatchClass) by (unfold room, get_region in *; cbn; rewrite SR; exact ROOM).
  eapply ghoare_bind; [apply (genqueue [] s3 cb (cm_n cm) WF3 PN ROOM3)|].
  intros []. apply ghoare_of_gok. apply gok_drain_if_needed.
Qed.

Theorem gafree : forall s0 key p,
  depot_ok E s0 key -> AWF s0 -> room s0 kBatchClass ->
  (p = 0 \/ exists cm aid, as_chunks s0 !! (p - kChunkHeaderSize) = Some cm /\ cm_state cm = CAllocated aid /\ cm_user_beg cm = p) ->
  ghoare (fun s => s = s0) (afree E key p) (fun _ _ => True).
Proof.
  intros s0 key p HK WF ROOM LIVE. unfold afree, ia_init.
  apply ghoare_upd_bind. apply ghoare_pre. intros s (sx & -> & ->). set (s1 := upd_ia_inited true s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ia| exact WF]).
  destruct (p =? 0) eqn:PZ; [apply ghoare_ret; intros; exact I|].
  apply Z.eqb_neq in PZ. destruct LIVE as [PZ'|(cm & aid & Hcm & ST & UB)]; [exfalso; exact (PZ PZ')|].
  exact (gafree_core s1 key p cm aid HK WF1 Hcm ST UB ROOM).
Qed.

(* [comment removed for export] *)
Theorem garealloc : forall s0 key p n,
  depot_ok2 E s0 key -> 0 <= n < 2^40 -> AWF s0 -> malloc_pre s0 n -> room2 s0 kBatchClass ->
  p <> 0 -> n <> 0 ->
  (exists cm aid, as_chunks s0 !! (p - kChunkHeaderSize) = Some cm /\ cm_state cm = CAllocated aid /\ cm_user_beg cm = p) ->
  ghoare (fun s => s = s0) (arealloc E key p n) (fun _ r => exists q, r = Some q).
Proof.
  intros s0 key p n [KL IDB] Hn WF PRE ROOM2 PZ NZ (cm & aid & Hcm & ST & UB). unfold arealloc, ia_init.
  assert (HK : depot_ok E s0 key) by (split; [exact KL| lia]).
  apply ghoare_upd_bind. apply ghoare_pre. intros s (sx & -> & ->). set (s1 := upd_ia_inited true s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ia| exact WF]).
  assert (PRE1 : malloc_pre s1 n) by exact PRE.
  assert (F01 : fsame s0 s1) by (apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl]).
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
  apply ghoare_upd_bind. apply ghoare_pre. intros s (sy & -> & ->). set (s1' := upd_ts _ s1).
  assert (WF1' : AWF s1') by (eapply AWf_same_core; [apply same_core_upd_ts| exact WF1]).
  assert (F01' : fsame s0 s1') by (apply (fsame_regions s0 s0); [reflexivity| reflexivity| apply fsame_refl]).
  pose proof (amalloc_full_spec E s1' key n HK Hn WF1' PRE1) as M. unfold amalloc in M.
  eapply ghoare_bind; [apply ghoare_hoare_conj; [exact M| apply ghoare_of_gok, gok_amalloc_core]|].
  intros r. apply ghoare_pre. intros s2 [(WF2 & NID2 & X & (extra & F2 & C2 & CN)) (q & ->)].
  assert (F02 : fcall 1 [class_id (needed1 n)] extra s0 s2) by (eapply fcall_pre_same; [exact F01'| exact F2]).
  destruct X as (M16 & NONE & ab & id & ID & Hq & HK2).
  apply ghoare_get_bind. intros s ->.
  assert (NEQ : p - kChunkHeaderSize <> q - kChunkHeaderSize) by (intros EQ; rewrite EQ in Hcm; cbn in NONE; rewrite Hcm in NONE; discriminate).
  assert (Hcm2 : as_chunks s2 !! (p - kChunkHeaderSize) = Some cm) by (rewrite HK2, lookup_insert_ne by auto; exact Hcm).
  rewrite Hcm2, ST, UB, Z.eqb_refl.
  assert (ROOMs2 : room s2 kBatchClass).
  { destruct F02 as (_ & B & _). specialize (B kBatchClass). unfold room, room2, mu, kUserMapSize in *. lia. }
  assert (DOK2 : depot_ok E s2 key) by (split; [exact KL| cbn in NID2; unfold depot_n_ids in *; cbn in *; lia]).
  eapply ghoare_bind; [apply (gafree_core s2 key p cm aid DOK2 WF2 Hcm2 ST UB ROOMs2)|].
  intros []. apply ghoare_ret. intros; eexists; reflexivity.
Qed.

End OPS.
End RC__1.
