(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0t.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/YO0t.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Reusable/YO0t.v; 800 of its 1100 lines of code are new or changed and 713 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0e YO0m YO0x.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import AllocSI AllocGS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition af_shape (a a' : ameta) : Prop :=
  am_mem a' = am_mem a /\ am_maplen a' = am_maplen a /\ am_sc a' = am_sc a /\ am_last a' = am_last a.

Definition af_frs (a a' : ameta) : Prop :=
  forall j f, ss_fr (nth_slot a' j) = Some f -> ss_fr (nth_slot a j) = Some f.

Lemma af_shape_i a a' : am_mem a' = am_mem a -> am_maplen a' = am_maplen a -> am_sc a' = am_sc a ->
  am_last a' = am_last a -> af_shape a a'.
Proof. intros H1 H2 H3 H4. split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]]. Qed.

Lemma af_shape_refl a : af_shape a a.
Proof. apply af_shape_i; reflexivity. Qed.

Lemma af_shape_trans a b c : af_shape a b -> af_shape b c -> af_shape a c.
Proof. intros (M1 & L1 & S1 & A1) (M2 & L2 & S2 & A2). apply af_shape_i; congruence. Qed.

Lemma af_shape_stride a a' : af_shape a a' -> stride_of a' = stride_of a.
Proof. intros (M & L & S & A). unfold stride_of. rewrite A, L, S. reflexivity. Qed.

Lemma af_shape_slot_start a a' j : af_shape a a' -> slot_start a' j = slot_start a j.
Proof. intros H. unfold slot_start. rewrite (af_shape_stride _ _ H), (proj1 H). reflexivity. Qed.

Lemma af_frs_slots a a' : am_slots a' = am_slots a -> af_frs a a'.
Proof. intros E j f H. unfold nth_slot in *. rewrite <- E. exact H. Qed.

Lemma frs_upd_gen am i x : ss_fr x = None \/ ss_fr x = ss_fr (nth_slot am i) -> af_frs am (upd_slot am i x).
Proof.
  intros Hx j f H. unfold nth_slot, upd_slot, am_set_slots in H. cbn [am_slots] in H. rewrite nth_lupd in H.
  destruct (Nat.eqb (Z.to_nat j) (Z.to_nat i) && Nat.ltb (Z.to_nat i) (length (am_slots am)))%bool eqn:B; [|exact H].
  destruct Hx as [Hx|Hx]; rewrite Hx in H; [discriminate|].
  apply andb_prop in B as [B _]. apply Nat.eqb_eq in B. unfold nth_slot in *. rewrite B. exact H.
Qed.

Lemma frs_upd_slot am i x : ss_fr x = None -> af_frs am (upd_slot am i x).
Proof. intros H. apply frs_upd_gen. left. exact H. Qed.

Lemma frameless_slots a a' : am_slots a' = am_slots a -> am_last a' = am_last a -> frameless a' -> frameless a.
Proof. intros Es El F i Hi. unfold nth_slot. rewrite <- Es. exact (F i ltac:(lia)). Qed.

Lemma mfree_not_used pr nx a : MFree pr nx <> MUsed a.
Proof. discriminate. Qed.

Lemma af_setm_upd p am s : setm p am s = IRet (tt, upd_meta p (MUsed am) s).
Proof. reflexivity. Qed.

Definition mcb (s s' : astate) : Prop :=
  forall q a', MT s' q = Some (MUsed a') -> exists a, MT s q = Some (MUsed a) /\
  am_maplen a' = am_maplen a /\ am_sc a' = am_sc a /\ am_last a' = am_last a /\ af_frs a a'.

Definition kr (s s' : astate) : Prop :=
  st_areas s' = st_areas s /\ st_avail_meta_count s' = st_avail_meta_count s /\ (noraw s -> noraw s') /\ mcb s s'.

Definition KR {A} (m : M A) : Prop := forall s, tall (fun r => kr s (snd r)) (m s).

Lemma kr_refl s : kr s s.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [auto|].
  intros q a H. exists a. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros j f Hf. exact Hf.
Qed.

Lemma kr_trans s1 s2 s3 : kr s1 s2 -> kr s2 s3 -> kr s1 s3.
Proof.
  intros (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2). split; [congruence|]. split; [congruence|]. split; [auto|].
  intros q a H. destruct (D2 q a H) as (a1 & H1 & L1 & S1 & T1 & F1). destruct (D1 q a1 H1) as (a0 & H0 & L0 & S0 & T0 & F0).
  exists a0. split; [exact H0|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. intros j f Hf. apply F0, F1, Hf.
Qed.

Lemma kr_same s s' : st_metas s' = st_metas s -> st_areas s' = st_areas s ->
  st_avail_meta_count s' = st_avail_meta_count s -> kr s s'.
Proof.
  intros Em Ea Ec. split; [exact Ea|]. split; [exact Ec|]. unfold noraw, mcb, MT. rewrite Em. split; [auto|].
  intros q a H. exists a. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros j f Hf. exact Hf.
Qed.

Lemma kr_upd_free s p x : (forall a, x <> MUsed a) -> x <> MRaw -> kr s (upd_meta p x s).
Proof.
  intros Hu Hr. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros N q. rewrite MT_upd. destruct (sptr_eqb q p); [intros E; injection E as E; exact (Hr E) | apply N].
  - intros q a H. rewrite MT_upd in H. destruct (sptr_eqb q p).
    + injection H as E. exfalso. exact (Hu a E).
    + exists a. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros j f Hf. exact Hf.
Qed.

Lemma kr_upd_used s p a a' : MT s p = Some (MUsed a) -> am_maplen a' = am_maplen a -> am_sc a' = am_sc a ->
  am_last a' = am_last a -> af_frs a a' -> kr s (upd_meta p (MUsed a') s).
Proof.
  intros Hp L S T F. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros N q. rewrite MT_upd. destruct (sptr_eqb q p); [discriminate | apply N].
  - intros q b H. rewrite MT_upd in H. destruct (sptr_eqb q p) eqn:E.
    + apply sptr_eqb_eq in E. subst q. injection H as <-. exists a. split; [exact Hp|]. split; [exact L|]. split; [exact S|]. split; [exact T | exact F].
    + exists b. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros j f Hf. exact Hf.
Qed.

Lemma kr_ret {A} (a : A) : KR (ret a).
Proof. intros s. exact (kr_refl s). Qed.

Lemma kr_fail {A} f : KR (@fail A f).
Proof. intros s. exact I. Qed.

Lemma kr_bind {A B} (m : M A) (k : A -> M B) : KR m -> (forall a, KR (k a)) -> KR (bind m k).
Proof.
  intros Hm Hk s. unfold bind. eapply tall_ibind; [apply Hm|]. intros [a s1] H1. cbn [snd] in *.
  eapply tall_mono; [|apply (Hk a s1)]. intros [b s2] H2. cbn [snd] in *. eapply kr_trans; eauto.
Qed.

Lemma kr_bind_get {B} (k : astate -> M B) : (forall s0, KR (k s0)) -> KR (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.

Lemma kr_bind_get' {B} (k : astate -> M B) : (forall s, tall (fun r => kr s (snd r)) (k s s)) -> KR (bind get k).
Proof. intros Hk s. exact (Hk s). Qed.

Lemma kr_modify f : (forall s, kr s (f s)) -> KR (modify f).
Proof. intros Hf s. exact (Hf s). Qed.

Lemma kr_massert b site : KR (massert b site).
Proof. unfold massert. destruct b; [apply kr_ret | apply kr_fail]. Qed.

Lemma kr_mcheck b tag : KR (mcheck b tag).
Proof. unfold mcheck. destruct b; [apply kr_ret | apply kr_fail]. Qed.

Lemma kr_getm p : KR (getm p).
Proof.
  unfold getm. apply kr_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [[pr nx| |am]|]; try apply kr_fail.
  apply kr_ret.
Qed.

Lemma kr_get_links p : KR (get_links p).
Proof. unfold get_links. apply kr_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply kr_ret | apply kr_fail]. Qed.

Lemma kr_set_links p pr nx : KR (set_links p pr nx).
Proof.
  unfold set_links. apply kr_bind_get'. intros s. destruct (mlookup (st_metas s) p) as [x|] eqn:E; [|exact I].
  destruct x as [pr0 nx0| |am].
  - exact (kr_upd_free s p (MFree pr nx) (mfree_not_used pr nx) ltac:(discriminate)).
  - exact (kr_upd_free s p (MFree pr nx) (mfree_not_used pr nx) ltac:(discriminate)).
  - exact (kr_upd_used s p am (am_set_links pr nx am) E eq_refl eq_refl eq_refl (af_frs_slots _ _ eq_refl)).
Qed.

Lemma kr_set_prev p pr : KR (set_prev p pr).
Proof. unfold set_prev. apply kr_bind; [apply kr_get_links | intros; apply kr_set_links]. Qed.

Lemma kr_set_next p nx : KR (set_next p nx).
Proof. unfold set_next. apply kr_bind; [apply kr_get_links | intros; apply kr_set_links]. Qed.

Lemma kr_get_head h : KR (get_head h).
Proof. unfold get_head. apply kr_bind_get. intros s0. destruct h; apply kr_ret. Qed.

Lemma kr_set_head h v : KR (set_head h v).
Proof. unfold set_head. destruct h; apply kr_modify; intros s; apply kr_same; reflexivity. Qed.

Lemma kr_queue h m : KR (queue h m).
Proof.
  unfold queue. apply kr_bind; [apply kr_get_links | intros l].
  apply kr_bind; [apply kr_massert | intros _].
  apply kr_bind; [apply kr_get_head | intros [head|]].
  - apply kr_bind; [apply kr_get_links | intros lh]. destruct (fst lh); [| apply kr_fail].
    apply kr_bind; [apply kr_set_links | intros _]. apply kr_bind; [apply kr_set_next | intros _]. apply kr_set_prev.
  - apply kr_bind; [apply kr_set_links | intros _]. apply kr_set_head.
Qed.

Lemma kr_dequeue h m : KR (dequeue h m).
Proof.
  unfold dequeue. apply kr_bind; [apply kr_get_links | intros l].
  apply kr_bind; [| intros _; apply kr_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply kr_set_head|].
  destruct (fst l); [| apply kr_fail]. destruct (snd l); [| apply kr_fail].
  apply kr_bind; [apply kr_set_next | intros _]. apply kr_bind; [apply kr_set_prev | intros _].
  apply kr_bind; [apply kr_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply kr_set_head | apply kr_ret].
Qed.

Lemma kr_free_meta m : KR (free_meta m).
Proof.
  unfold free_meta. apply kr_bind; [|intros; apply kr_queue].
  intros s. exact (kr_upd_free s m (MFree None None) (mfree_not_used None None) ltac:(discriminate)).
Qed.

Lemma kr_activate_group m : KR (activate_group m).
Proof.
  intros s. unfold activate_group, getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) m) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  unfold massert, ret, fail. destruct (am_avail am =? 0); cbn [ibind]; [| exact I].
  cbv zeta. rewrite af_setm_upd. cbn [ibind tall snd].
  eapply kr_upd_used; [exact E | reflexivity | reflexivity | reflexivity | apply af_frs_slots; reflexivity].
Qed.

Lemma kr_set_usage_of sc v : KR (set_usage_of sc v).
Proof. unfold set_usage_of. apply kr_modify. intros s. apply kr_same; reflexivity. Qed.

Lemma kr_step_seq : KR step_seq.
Proof. unfold step_seq. apply kr_modify. intros s. destruct (st_seq s =? 255); apply kr_same; reflexivity. Qed.

Lemma kr_record_seq sc : KR (record_seq sc).
Proof.
  unfold record_seq. destruct (bounce_idx sc); [apply kr_modify; intros s; apply kr_same; reflexivity | apply kr_ret].
Qed.

Lemma kr_find_frame p : KR (find_frame p).
Proof.
  unfold find_frame. apply kr_bind_get. intros s0. destruct (find_frame_in (st_metas s0) p); [apply kr_ret | apply kr_fail].
Qed.

Lemma kr_getm_setm p (F : ameta -> ameta) :
  (forall am, am_maplen (F am) = am_maplen am /\ am_sc (F am) = am_sc am /\ am_last (F am) = am_last am /\ af_frs am (F am)) ->
  KR (bind (getm p) (fun am => setm p (F am))).
Proof.
  intros HF s. unfold getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  destruct (HF am) as (L & S & T & F'). exact (kr_upd_used s p am (F am) E L S T F').
Qed.

Lemma kr_getm_setm_k {B} p (F : ameta -> ameta) (k : ameta -> unit -> M B) :
  (forall am, am_maplen (F am) = am_maplen am /\ am_sc (F am) = am_sc am /\ am_last (F am) = am_last am /\ af_frs am (F am)) ->
  (forall am u, KR (k am u)) ->
  KR (bind (getm p) (fun am => bind (setm p (F am)) (k am))).
Proof.
  intros HF Hk s. unfold getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  rewrite af_setm_upd. cbn [ibind].
  eapply tall_mono; [|apply (Hk am tt)]. intros [b s2] H2. cbn [snd] in *. eapply kr_trans; [|exact H2].
  destruct (HF am) as (L & S & T & F'). exact (kr_upd_used s p am (F am) E L S T F').
Qed.

Lemma kr_forget_frame g i : KR (forget_frame g i).
Proof.
  unfold forget_frame. cbv zeta. apply kr_getm_setm. intros am.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply frs_upd_slot. reflexivity.
Qed.

Lemma kr_release_slot g i : KR (release_slot g i).
Proof.
  unfold release_slot. cbv zeta. apply kr_getm_setm. intros am.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply frs_upd_gen.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:E; [destruct (fr_off fr =? 0); left; reflexivity|].
  left. first [reflexivity | exact E].
Qed.

Lemma kr_upd_region r f : KR (upd_region r f).
Proof. unfold upd_region. apply kr_modify. intros s. apply kr_same; reflexivity. Qed.

Lemma kr_ask q : KR (ask q).
Proof. intros s z. exact (kr_refl s). Qed.

Theorem kr_nontrivial_free fuel : forall g i, KR (nontrivial_free fuel g i).
Proof.
  induction fuel as [|fuel IH]; intros g i; [intros s; exact I|].
  cbn fix beta iota delta [nontrivial_free].
  apply kr_bind; [apply kr_getm | intros am].
  apply kr_bind_get. intros s0. cbn zeta.
  destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s0 g am).
  - apply kr_bind.
    + destruct (am_next am); [| apply kr_ret].
      apply kr_bind; [apply kr_massert | intros _]. apply kr_bind; [apply kr_get_head | intros hd].
      apply kr_bind; [apply kr_dequeue | intros _]. apply kr_bind; [apply kr_get_head | intros hd'].
      destruct (osptr_eqb hd (Some g)); [| apply kr_ret]. destruct hd'; [| apply kr_ret].
      apply kr_bind; [apply kr_activate_group | intros _; apply kr_ret].
    + intros _. apply kr_bind; [apply kr_getm | intros am'].
      apply kr_bind; [destruct (am_sc am <? 48); [apply kr_set_usage_of | apply kr_ret] | intros _].
      apply kr_bind; [| intros mi; apply kr_bind; [apply kr_free_meta | intros _; apply kr_ret]].
      destruct (negb (am_maplen am' =? 0)).
      * apply kr_bind; [apply kr_step_seq | intros _]. apply kr_bind; [apply kr_record_seq | intros _]. apply kr_ret.
      * apply kr_bind; [apply kr_find_frame | intros pf]. apply kr_bind; [apply kr_getm | intros amp].
        apply kr_bind; [apply kr_mcheck | intros _]. apply kr_bind; [apply kr_forget_frame | intros _]. apply IH.
  - apply kr_bind.
    + destruct (Z.lor (am_freed am) (am_avail am) =? 0); [| apply kr_ret].
      apply kr_bind; [apply kr_massert | intros _]. apply kr_bind; [apply kr_get_head | intros hd].
      destruct (osptr_eqb hd (Some g)); [apply kr_ret | apply kr_queue].
    + intros _. apply (kr_getm_setm_k g (fun am' => am_set_freed (Z.lor (am_freed am') (bit i)) am') (fun _ _ => ret None)).
      * intros am'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply af_frs_slots. reflexivity.
      * intros _ _. apply kr_ret.
Qed.

Theorem kr_free p : KR (free p).
Proof.
  unfold free. destruct p as [p|]; [|apply kr_ret].
  apply kr_bind; [apply kr_find_frame | intros gi]. cbv zeta.
  apply kr_bind; [apply kr_getm | intros am].
  apply kr_bind; [apply kr_release_slot | intros _].
  apply kr_bind; [apply kr_massert | intros _].
  match goal with |- KR (if ?b then _ else _) => destruct b end.
  - apply kr_getm_setm. intros am'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply af_frs_slots. reflexivity.
  - apply kr_bind; [apply kr_nontrivial_free | intros mi]. destruct mi as [[r len]|]; [|apply kr_ret].
    apply kr_bind; [apply kr_ask | intros _]. apply kr_upd_region.
Qed.

Theorem free_hand : forall s p n tr s', WF s -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (tt, s') -> hand s' = hand s.
Proof.
  intros s p n tr s' _ _ Y. pose proof (tall_yields _ _ tr (tt, s') (kr_free (Some p) s) Y) as (A & B & _).
  cbn [snd] in A, B. unfold hand, nareas. rewrite A, B. reflexivity.
Qed.

Theorem free_noraw : forall s p n tr s', WF s -> In (p, n) (user_blocks s) -> noraw s ->
  yields (free (Some p) s) tr (tt, s') -> noraw s'.
Proof.
  intros s p n tr s' _ _ N Y. pose proof (tall_yields _ _ tr (tt, s') (kr_free (Some p) s) Y) as (_ & _ & K & _).
  exact (K N).
Qed.

Theorem free_GS : forall s p n tr s', WF s -> GS s -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (tt, s') -> GS s'.
Proof.
  intros s p n tr s' _ HG _ Y. pose proof (tall_yields _ _ tr (tt, s') (kr_free (Some p) s) Y) as (_ & _ & _ & Mc).
  cbn [snd] in Mc. intros g a' Hu Hml. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  destruct (Mc g a' Mg) as (a & Ma & L & S & _ & F).
  destruct (HG g a (usedX_intro [] s g a eq_refl Ma) ltac:(lia)) as [H1 H2]. rewrite L, S. split.
  - exact H1.
  - intros H63 fr Hfr. exact (H2 H63 fr (F 0 fr Hfr)).
Qed.

Theorem free_NL : forall s p n tr s', WF s -> NL s -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (tt, s') -> NL s'.
Proof.
  intros s p n tr s' _ HN _ Y. pose proof (tall_yields _ _ tr (tt, s') (kr_free (Some p) s) Y) as (_ & _ & _ & Mc).
  cbn [snd] in Mc. intros g a' Hu Hml. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  destruct (Mc g a' Mg) as (a & Ma & L & _ & T & _). rewrite T.
  apply (HN g a (usedX_intro [] s g a eq_refl Ma)). rewrite <- L. exact Hml.
Qed.

Definition fwdM (s s' : astate) : Prop :=
  forall q a, MT s q = Some (MUsed a) -> exists a', MT s' q = Some (MUsed a') /\ strip a' = strip a.

Definition PF {A} (m : M A) : Prop := forall s, tall (fun r => fwdM s (snd r)) (m s).

Lemma fwdM_refl s : fwdM s s.
Proof. intros q a H. exists a. split; [exact H | reflexivity]. Qed.

Lemma fwdM_trans s1 s2 s3 : fwdM s1 s2 -> fwdM s2 s3 -> fwdM s1 s3.
Proof.
  intros A B q a H. destruct (A q a H) as (a1 & H1 & E1). destruct (B q a1 H1) as (a2 & H2 & E2).
  exists a2. split; [exact H2 | congruence].
Qed.

Lemma fwdM_same s s' : st_metas s' = st_metas s -> fwdM s s'.
Proof. intros E q a H. exists a. unfold MT in *. rewrite E. split; [exact H | reflexivity]. Qed.

Lemma pf_ret {A} (a : A) : PF (ret a).
Proof. intros s. exact (fwdM_refl s). Qed.

Lemma pf_fail {A} f : PF (@fail A f).
Proof. intros s. exact I. Qed.

Lemma pf_bind {A B} (m : M A) (k : A -> M B) : PF m -> (forall a, PF (k a)) -> PF (bind m k).
Proof.
  intros Hm Hk s. unfold bind. eapply tall_ibind; [apply Hm|]. intros [a s1] H1. cbn [snd] in *.
  eapply tall_mono; [|apply (Hk a s1)]. intros [b s2] H2. cbn [snd] in *. eapply fwdM_trans; eauto.
Qed.

Lemma pf_bind_get {B} (k : astate -> M B) : (forall s0, PF (k s0)) -> PF (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.

Lemma pf_bind_get' {B} (k : astate -> M B) : (forall s, tall (fun r => fwdM s (snd r)) (k s s)) -> PF (bind get k).
Proof. intros Hk s. exact (Hk s). Qed.

Lemma pf_modify f : (forall s, fwdM s (f s)) -> PF (modify f).
Proof. intros Hf s. exact (Hf s). Qed.

Lemma pf_massert b site : PF (massert b site).
Proof. unfold massert. destruct b; [apply pf_ret | apply pf_fail]. Qed.

Lemma pf_get_links p : PF (get_links p).
Proof. unfold get_links. apply pf_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply pf_ret | apply pf_fail]. Qed.

Lemma pf_set_links p pr nx : PF (set_links p pr nx).
Proof.
  unfold set_links. apply pf_bind_get'. intros s. destruct (mlookup (st_metas s) p) as [x|] eqn:E; [|exact I].
  assert (H : fwdM s (upd_meta p (with_links x pr nx) s)).
  { intros q a Hq. rewrite MT_upd. destruct (sptr_eqb q p) eqn:Eq.
    - apply sptr_eqb_eq in Eq. subst q. unfold MT in Hq. rewrite E in Hq. injection Hq as ->.
      exists (am_set_links pr nx a). split; [reflexivity | destruct a; reflexivity].
    - exists a. split; [exact Hq | reflexivity]. }
  exact H.
Qed.

Lemma pf_set_prev p pr : PF (set_prev p pr).
Proof. unfold set_prev. apply pf_bind; [apply pf_get_links | intros; apply pf_set_links]. Qed.

Lemma pf_set_next p nx : PF (set_next p nx).
Proof. unfold set_next. apply pf_bind; [apply pf_get_links | intros; apply pf_set_links]. Qed.

Lemma pf_get_head h : PF (get_head h).
Proof. unfold get_head. apply pf_bind_get. intros s0. destruct h; apply pf_ret. Qed.

Lemma pf_set_head h v : PF (set_head h v).
Proof. unfold set_head. destruct h; apply pf_modify; intros s; apply fwdM_same; reflexivity. Qed.

Lemma pf_queue h m : PF (queue h m).
Proof.
  unfold queue. apply pf_bind; [apply pf_get_links | intros l].
  apply pf_bind; [apply pf_massert | intros _].
  apply pf_bind; [apply pf_get_head | intros [head|]].
  - apply pf_bind; [apply pf_get_links | intros lh]. destruct (fst lh); [| apply pf_fail].
    apply pf_bind; [apply pf_set_links | intros _]. apply pf_bind; [apply pf_set_next | intros _]. apply pf_set_prev.
  - apply pf_bind; [apply pf_set_links | intros _]. apply pf_set_head.
Qed.

Lemma pf_dequeue h m : PF (dequeue h m).
Proof.
  unfold dequeue. apply pf_bind; [apply pf_get_links | intros l].
  apply pf_bind; [| intros _; apply pf_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply pf_set_head|].
  destruct (fst l); [| apply pf_fail]. destruct (snd l); [| apply pf_fail].
  apply pf_bind; [apply pf_set_next | intros _]. apply pf_bind; [apply pf_set_prev | intros _].
  apply pf_bind; [apply pf_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply pf_set_head | apply pf_ret].
Qed.

Lemma itok_tall_imp {A} (t : itree astate A) (P Q : A -> Prop) :
  itok t (fun a => P a -> Q a) -> tall P t -> itok t Q.
Proof.
  induction t as [a | q snap k IH | f]; cbn; intros H1 H2.
  - exact (H1 H2).
  - destruct H1 as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [apply Hk, Hz | apply H2].
  - exact H1.
Qed.

Lemma dequeue_f X R U s sc g am (Q : unit * astate -> Prop) :
  Inv X R U s -> 0 <= sc < 48 -> usedX X s g am -> am_sc am = sc ->
  (am_prev am, am_next am) <> (None, None) ->
  (forall j, ss_fr (nth_slot am j) = None) ->
  (forall p i, R = Some (p, i) -> p = g) ->
  (forall s', fwdM s s' ->
    Inv (g :: X) None (fun c => U c + contrib X s c g) s' ->
    same_but_metas_heads s s' ->
    MT s' g = Some (MUsed (am_set_links None None am)) ->
    (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
    (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s' q = MT s q) ->
    (forall q a', usedX (g :: X) s' q a' -> q <> g /\ exists a, usedX X s q a /\ strip a' = strip a) ->
    (active_hd s sc <> Some g -> active_hd s' sc = active_hd s sc) ->
    (active_hd s sc = Some g ->
      active_hd s' sc = None \/
      exists h ah, active_hd s' sc = Some h /\ h <> g /\ usedX (g :: X) s' h ah /\ am_sc ah = sc /\ am_avail ah = 0) ->
    ub_same s s' ->
    Q (tt, s')) ->
  itok (dequeue (HActive sc) g s) Q.
Proof.
  intros HI Hsc Hu Hs Hl Hf HR HQ. apply (itok_tall_imp _ (fun r => fwdM s (snd r))); [|apply pf_dequeue].
  eapply dequeue_exempt_spec; [exact HI | exact Hsc | exact Hu | exact Hs | exact Hl | exact Hf | exact HR |].
  intros s' A1 A2 A3 A4 A5 A6 A7 A8 A9 F. exact (HQ s' F A1 A2 A3 A4 A5 A6 A7 A8 A9).
Qed.

Lemma requeue_f X U s sc g i am (Q : unit * astate -> Prop) :
  Inv X (Some (g, i)) U s -> 0 <= sc < 48 -> usedX X s g am -> am_sc am = sc ->
  am_prev am = None -> am_next am = None -> active_hd s sc <> Some g ->
  (forall s' pr nx, fwdM s s' ->
    Inv X (Some (g, i)) U s' -> same_but_metas_heads s s' ->
    MT s' g = Some (MUsed (am_set_links (Some pr) (Some nx) am)) ->
    (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
    (forall q a', usedX X s' q a' -> exists a, usedX X s q a /\ strip a' = strip a) ->
    ub_same s s' ->
    Q (tt, s')) ->
  itok (queue (HActive sc) g s) Q.
Proof.
  intros HI Hsc Hu Hs Hp Hn Hnh HQ. apply (itok_tall_imp _ (fun r => fwdM s (snd r))); [|apply pf_queue].
  eapply requeue_spec; [exact HI | exact Hsc | exact Hu | exact Hs | exact Hp | exact Hn | exact Hnh |].
  intros s' pr nx A1 A2 A3 A4 A5 A6 F. exact (HQ s' pr nx F A1 A2 A3 A4 A5 A6).
Qed.

Lemma step_seq_spec_h X R U s (Q : unit * astate -> Prop) :
  Inv X R U s ->
  (forall s', Inv X R U s' -> ctx_frame s s' -> st_avail_meta_count s' = st_avail_meta_count s -> Q (tt, s')) ->
  itok (step_seq s) Q.
Proof.
  intros HI HQ. apply (itok_tall_imp _ (fun r => kr s (snd r))); [|apply kr_step_seq].
  eapply step_seq_spec; [exact HI|]. intros s' H1 H2 K. destruct K as (_ & K & _). exact (HQ s' H1 H2 K).
Qed.

Lemma record_seq_spec_h X R U s sc (Q : unit * astate -> Prop) :
  Inv X R U s ->
  (forall s', Inv X R U s' -> ctx_frame s s' -> st_avail_meta_count s' = st_avail_meta_count s -> Q (tt, s')) ->
  itok (record_seq sc s) Q.
Proof.
  intros HI HQ. apply (itok_tall_imp _ (fun r => kr s (snd r))); [|apply kr_record_seq].
  eapply record_seq_spec; [exact HI|]. intros s' H1 H2 K. destruct K as (_ & K & _). exact (HQ s' H1 H2 K).
Qed.

Definition afrel (X : list sptr) (s : astate) (X' : list sptr) (R' : option (sptr * Z)) (s' : astate) : Prop :=
  (forall q a', usedX X' s' q a' -> exists a, usedX X s q a /\ af_shape a a' /\ af_frs a a' /\
     (unreserved R' q -> frameless a' -> frameless a)) /\
  (forall q a, usedX X s q a -> memb q X' = false -> exists a', usedX X' s' q a' /\ af_shape a a').

Definition owned_ex (X : list sptr) (E : nat -> Prop) (s : astate) : Prop :=
  forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> ~ E k ->
  exists g am, usedX X s g am /\ 0 < am_maplen am /\ prid (am_mem am) = k.

Definition mi_ex (mi : option (nat * Z)) (k : nat) : Prop :=
  match mi with Some (k0, _) => k = k0 | None => False end.

Definition SIXo (X : list sptr) (mi : option (nat * Z)) (s : astate) : Prop :=
  owned_ex X (mi_ex mi) s /\ empty_ok X None s /\ empty_unique X None s /\ children_ok X s /\ hand_keys s.

Definition afhk (s s' : astate) : Prop :=
  keys s' = keys s /\ st_areas s' = st_areas s /\ st_avail_meta_count s' = st_avail_meta_count s.

Lemma afhk_hand s s' : afhk s s' -> hand_keys s -> hand_keys s'.
Proof.
  intros (K & A & C) H. unfold hand_keys, hand, nareas in *. rewrite A, C, H. f_equal.
  unfold keys in K. rewrite <- (length_map fst (st_metas s')), <- (length_map fst (st_metas s)), K. reflexivity.
Qed.

Lemma owned_of_ex X s : owned_ex X (fun _ => False) s -> owned_maps X s.
Proof. intros O k rg H1 H2 H3. exact (O k rg H1 H2 H3 (fun x => x)). Qed.

Lemma ex_of_owned X s : owned_maps X s -> owned_ex X (fun _ => False) s.
Proof. intros O k rg H1 H2 H3 _. exact (O k rg H1 H2 H3). Qed.

Lemma unres_None q : unreserved None q.
Proof. intros j E. discriminate. Qed.

Lemma unres_cons X s g i q a : usedX (g :: X) s q a -> unreserved (Some (g, i)) q.
Proof. intros H j E. injection E as E _. exact (proj1 (usedX_cons_inv _ _ _ _ _ H) (eq_sym E)). Qed.

Lemma not_unres_eq g i q : ~ unreserved (Some (g, i)) q -> q = g.
Proof.
  intros Hn. destruct (sptr_eq_dec q g) as [E|E]; [exact E|]. exfalso. apply Hn.
  intros j E'. injection E' as E'' _. exact (E (eq_sym E'')).
Qed.

Lemma unreserved_dec R q : unreserved R q \/ ~ unreserved R q.
Proof.
  destruct R as [[g0 i0]|]; [|left; apply unres_None].
  destruct (sptr_eq_dec q g0) as [->|Hne].
  - right. intros H. exact (H i0 eq_refl).
  - left. intros j E. injection E as E _. exact (Hne (eq_sym E)).
Qed.

Lemma usedX_metas X s s' q a : st_metas s' = st_metas s -> (usedX X s' q a <-> usedX X s q a).
Proof. intros E. unfold usedX, MTX, MT. rewrite E. tauto. Qed.

Lemma afrel_metas X s X' R' s1 s2 : afrel X s X' R' s1 -> st_metas s2 = st_metas s1 -> afrel X s X' R' s2.
Proof.
  intros [B F] E. split.
  - intros q a' H. apply B. exact (proj1 (usedX_metas X' s1 s2 q a' E) H).
  - intros q a H Hm. destruct (F q a H Hm) as (a' & H' & Sh). exists a'.
    split; [exact (proj2 (usedX_metas X' s1 s2 q a' E) H') | exact Sh].
Qed.

Lemma afrel_trans X s X1 R1 s1 X2 R2 s2 : afrel X s X1 R1 s1 -> afrel X1 s1 X2 R2 s2 ->
  (forall q, memb q X1 = true -> memb q X2 = true) ->
  (forall q a2, usedX X2 s2 q a2 -> unreserved R2 q -> unreserved R1 q) ->
  afrel X s X2 R2 s2.
Proof.
  intros [B1 F1] [B2 F2] HX HR. split.
  - intros q a2 H2. destruct (B2 q a2 H2) as (a1 & H1 & Sh2 & Fs2 & Fl2). destruct (B1 q a1 H1) as (a & H & Sh1 & Fs1 & Fl1).
    exists a. split; [exact H|]. split; [eapply af_shape_trans; eauto|]. split; [intros j f Hf; apply Fs1, Fs2, Hf|].
    intros U Fr. apply Fl1; [exact (HR q a2 H2 U) | apply Fl2; assumption].
  - intros q a H Hm. assert (Hm1 : memb q X1 = false).
    { destruct (memb q X1) eqn:E; [rewrite (HX q E) in Hm; discriminate | reflexivity]. }
    destruct (F1 q a H Hm1) as (a1 & H1 & Sh1). destruct (F2 q a1 H1 Hm) as (a2 & H2 & Sh2).
    exists a2. split; [exact H2 | eapply af_shape_trans; eauto].
Qed.

Lemma owned_tr X E s X' R' E' s' : owned_ex X E s -> afrel X s X' R' s' -> st_regions s' = st_regions s ->
  (forall k, E k -> E' k) ->
  (forall q a, usedX X s q a -> 0 < am_maplen a -> ~ E' (prid (am_mem a)) -> memb q X' = false) ->
  owned_ex X' E' s'.
Proof.
  intros O [_ F] Rg HE Hm k rg Hk Hkd Hl HnE. unfold region_of in Hk. rewrite Rg in Hk.
  destruct (O k rg Hk Hkd Hl (fun H => HnE (HE k H))) as (q & a & Hq & Hml & Hp).
  assert (Hn : ~ E' (prid (am_mem a))) by (rewrite Hp; exact HnE).
  destruct (F q a Hq (Hm q a Hq Hml Hn)) as (a' & Hq' & (M & L & _)).
  exists q, a'. split; [exact Hq'|]. split; [lia|]. rewrite M. exact Hp.
Qed.

Lemma empty_ok_tr X R s X' R' s' : empty_ok X R s -> afrel X s X' R' s' ->
  (forall q a', usedX X' s' q a' -> unreserved R' q -> frameless a' -> ~ unreserved R q ->
     0 < am_maplen a' /\ 0 <= am_sc a' < 48) ->
  empty_ok X' R' s'.
Proof.
  intros E [B _] Hx q a' Hq Hf Hu. destruct (unreserved_dec R q) as [Hr|Hr]; [|exact (Hx q a' Hq Hu Hf Hr)].
  destruct (B q a' Hq) as (a & Ha & (M & L & S & La) & _ & Hfl). destruct (E q a Ha (Hfl Hu Hf) Hr) as [A1 A2].
  rewrite L, S. split; assumption.
Qed.

Lemma empty_unique_tr X R s X' R' s' : empty_unique X R s -> afrel X s X' R' s' ->
  (forall q1 a1 q2 a2, usedX X' s' q1 a1 -> usedX X' s' q2 a2 -> frameless a1 -> frameless a2 ->
     unreserved R' q1 -> unreserved R' q2 -> am_sc a1 = am_sc a2 -> ~ unreserved R q1 -> q1 = q2) ->
  empty_unique X' R' s'.
Proof.
  intros E [B _] Hx q1 a1 q2 a2 H1 H2 F1 F2 U1 U2 Es.
  destruct (unreserved_dec R q1) as [R1|R1]; [|exact (Hx _ _ _ _ H1 H2 F1 F2 U1 U2 Es R1)].
  destruct (unreserved_dec R q2) as [R2|R2]; [|symmetry; exact (Hx _ _ _ _ H2 H1 F2 F1 U2 U1 (eq_sym Es) R2)].
  destruct (B q1 a1 H1) as (b1 & Hb1 & (_ & _ & S1 & _) & _ & Fl1). destruct (B q2 a2 H2) as (b2 & Hb2 & (_ & _ & S2 & _) & _ & Fl2).
  exact (E q1 b1 q2 b2 Hb1 Hb2 (Fl1 U1 F1) (Fl2 U2 F2) R1 R2 ltac:(congruence)).
Qed.

Lemma children_tr X s X' R' s' : children_ok X s -> afrel X s X' R' s' ->
  (forall q a' j fr c ac, usedX X' s' q a' -> 0 <= j <= am_last a' -> ss_fr (nth_slot a' j) = Some fr ->
     fr_kind fr = FGroup -> usedX X s c ac -> am_maplen ac = 0 -> am_mem ac = slot_start a' j -> memb c X' = false) ->
  children_ok X' s'.
Proof.
  intros C [B F] Hx q a' j fr Hq Hj Hfr Hk.
  destruct (B q a' Hq) as (a & Ha & Sh & Fs & _). pose proof Sh as (M & L & S & La).
  destruct (C q a j fr Ha ltac:(lia) (Fs j fr Hfr) Hk) as (c & ac & Hc & Hml & Hmem & Hsc).
  rewrite <- (af_shape_slot_start a a' j Sh) in Hmem.
  destruct (F c ac Hc (Hx q a' j fr c ac Hq Hj Hfr Hk Hc Hml Hmem)) as (ac' & Hc' & (M' & L' & S' & _)).
  exists c, ac'. split; [exact Hc'|]. split; [lia|]. split; [rewrite M'; exact Hmem | lia].
Qed.

Lemma SIXo_equiv X X' mi s s' : (forall q a, usedX X s' q a <-> usedX X' s q a) ->
  st_regions s' = st_regions s -> afhk s s' -> SIXo X' mi s -> SIXo X mi s'.
Proof.
  intros EQ Rg Hk (O & E & EU & C & H). split; [|split; [|split; [|split]]].
  - intros k rg Hr Hkd Hl HE. unfold region_of in Hr. rewrite Rg in Hr.
    destruct (O k rg Hr Hkd Hl HE) as (q & a & Hq & Hm). exists q, a. split; [exact (proj2 (EQ q a) Hq) | exact Hm].
  - intros q a Hq Hf Hu. exact (E q a (proj1 (EQ q a) Hq) Hf Hu).
  - intros q1 a1 q2 a2 H1 H2. exact (EU q1 a1 q2 a2 (proj1 (EQ _ _) H1) (proj1 (EQ _ _) H2)).
  - intros q a j fr Hq Hj Hf Hk'. destruct (C q a j fr (proj1 (EQ _ _) Hq) Hj Hf Hk') as (c & ac & Hc & R).
    exists c, ac. split; [exact (proj2 (EQ _ _) Hc) | exact R].
  - exact (afhk_hand _ _ Hk H).
Qed.

Lemma SIXo_kill X r len v s : SIXo X (Some (r, len)) s -> (r < length (st_regions s))%nat -> rg_live v = false ->
  SIXo X None (set_regions (lupd (st_regions s) r v) s).
Proof.
  intros (O & E & EU & C & H) Hr Hv. split; [|split; [exact E|split; [exact EU|split; [exact C | exact H]]]].
  intros k rg Hk Hkd Hl _. unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_lupd in Hk.
  destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:B.
  - injection Hk as <-. rewrite Hv in Hl. discriminate.
  - assert (Hkr : k <> r).
    { intros ->. rewrite Nat.eqb_refl in B. cbn in B. apply Nat.ltb_ge in B. lia. }
    exact (O k rg Hk Hkd Hl Hkr).
Qed.

Lemma SI_of_SIXo s : SIXo [] None s -> SI s.
Proof.
  intros (O & E & EU & C & H). split; [apply owned_of_ex; exact O|]. split; [exact E|]. split; [exact EU|]. split; [exact C | exact H].
Qed.

Lemma mask_add_full fr av i L : 0 <= i -> Z.testbit (Z.lor fr av) i = false ->
  Z.lor (Z.lor fr (bit i)) av = ones L -> Z.lor fr av + bit i = ones L.
Proof.
  intros Hi Hb H. rewrite (add_bit_lor _ _ Hi Hb). rewrite <- H. apply bits_inj_nonneg. intros j Hj.
  rewrite !Z.lor_spec. destruct (Z.testbit fr j), (Z.testbit av j), (Z.testbit (bit i) j); reflexivity.
Qed.

Lemma mask_of_frameless X U s g a : Inv X None U s -> usedX X s g a -> frameless a ->
  Z.lor (am_freed a) (am_avail a) = ones (am_last a).
Proof.
  intros HI Hu Hf. pose proof (inv_groups HI g a Hu) as ((Glast & _ & _ & _ & _ & _ & Gabove & _ & _) & _ & Gsl & _).
  apply bits_inj_nonneg. intros j Hj. rewrite testbit_ones by lia. rewrite Z.lor_spec.
  destruct (Z_le_dec j (am_last a)) as [Hle|Hgt].
  - pose proof (Gsl j ltac:(lia)) as (_ & _ & S3). rewrite (Hf j ltac:(lia)) in S3.
    destruct S3 as [Hal|E]; [|discriminate].
    unfold allocated in Hal. rewrite Z.lor_spec in Hal.
    replace ((0 <=? j) && (j <=? am_last a)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct (Z.testbit (am_avail a) j), (Z.testbit (am_freed a) j); cbn in Hal |- *; congruence.
  - destruct (Gabove j ltac:(lia)) as [A B]. rewrite A, B.
    replace (j <=? am_last a) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. reflexivity.
Qed.

Lemma okay_false s g am : okay_to_free s g am = false -> am_maplen am <> 0 /\ am_next am = Some g.
Proof.
  unfold okay_to_free. cbv zeta.
  destruct ((48 <=? am_sc am) || (stride_of am <? class_size (am_sc am))); [intros H; discriminate H|].
  destruct (am_maplen am =? 0) eqn:E; [intros H; discriminate H|].
  destruct (osptr_eqb (am_next am) (Some g)) eqn:E2; [|intros H; discriminate H].
  intros _. split; [apply Z.eqb_neq; exact E | apply osptr_eqb_eq; exact E2].
Qed.

Lemma ring_singleton lk hd ms g p : ring_ok lk hd ms -> In g ms -> lk g = Some (p, Some g) ->
  forall q, In q ms -> q = g.
Proof.
  intros [[Hnd Hc] _] Hin Hl q Hq. destruct ms as [|m0 rest]; [destruct Hin|].
  change (chain lk (last (m0 :: rest) m0) (m0 :: rest) m0) in Hc.
  destruct (chain_next _ _ _ _ _ _ _ Hc Hin Hl) as (l1 & l2 & E & En & _).
  injection En as En. rewrite E in Hnd, Hq.
  destruct l2 as [|y l2'].
  - cbn in En. destruct l1 as [|z l1'].
    + cbn in Hq. destruct Hq as [<-|[]]. reflexivity.
    + cbn in E. injection E as Ez _. subst. exfalso. cbn in Hnd. inversion Hnd as [|x l Hn Hnd'].
      apply Hn. apply in_or_app. right. left. reflexivity.
  - cbn in En. subst y. exfalso. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. left. reflexivity.
Qed.

Theorem nf_SI fuel : forall X U s g i am (Q : option (nat * Z) * astate -> Prop),
Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c) ->
((am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) <> Some g -> am_freed am <> 0) ->
(fneed (am_sc am) <= fuel)%nat -> SIX X (Some (g, i)) s ->
(forall r, nf_post X U s r -> SIXo X (fst r) (snd r) -> Q r) ->
itok (nontrivial_free fuel g i s) Q.
Proof.
induction fuel as [|f IH]; intros X U s g i am Q HI Hu HU HR2g Hf HS HQ.
{ exfalso. unfold fneed in Hf. destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. }
destruct HS as (SXo & SXe & SXu & SXc & SXh).
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
cbn fix beta iota delta [nontrivial_free].
mbinds. eapply itok_getm; [exact Mg|]. msimp. mbinds. apply itok_get. msimp. cbn zeta.
set (sc := am_sc am) in *. set (mask := Z.lor (am_freed am) (am_avail am)).
destruct ((mask + bit i =? ones (am_last am)) && okay_to_free s g am) eqn:Hcond.
-
apply andb_prop in Hcond as [Hmask Hok]. apply Z.eqb_eq in Hmask.
pose proof (frameless_of_mask X U s g i am HI Hu Hmask) as Hnofr.
set (U1 := fun c => U c + contrib X s c g).
mbinds.
match goal with |- itok (?mm s) _ =>
assert (STEP1 : itok (mm s) (fun r => let s1 := snd r in
Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
(forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
(forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1 /\
(forall q a, usedX X s q a -> q <> g -> exists a', usedX (g :: X) s1 q a' /\ af_shape a a') /\
(forall q a', usedX (g :: X) s1 q a' -> exists a, usedX X s q a /\ af_shape a a' /\ am_slots a' = am_slots a) /\
afhk s s1)) end.
{ destruct (am_next am) as [nx|] eqn:Enx.
- assert (Hsc : 0 <= sc < 48).
{ destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
mbinds. eapply (dequeue_f X (Some (g, i)) U s sc g am); [exact HI | exact Hsc | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr | intros p j E; injection E; auto |].
intros s1 FWd1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
pose proof Sb1 as (_&_&_&Eamc1&_&_&_&_&_&Eus1&_&_&_&_&Erg1&Ear1&EK1).
assert (C1 : forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
{ intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). pose proof (strip_fields _ _ E) as (Em&_&_&_&_&Eml&_).
exists a0. auto. }
assert (Cr1 : corr X s s1).
{ intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
- pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
split; [exact Hu|]. destruct am; split; reflexivity.
- apply C1. apply usedX_cons; assumption. }
assert (FWs : forall q a, usedX X s q a -> q <> g -> exists a', usedX (g :: X) s1 q a' /\ strip a' = strip a).
{ intros q a Hq Hne. pose proof (usedX_MT _ _ _ _ Hq) as [Mq Nq]. destruct (FWd1 q a Mq) as (a' & M' & E').
exists a'. split; [|exact E']. apply usedX_intro; [|exact M']. rewrite memb_cons, Nq, orb_false_r. apply sptr_eqb_neq. exact Hne. }
assert (BWs : forall q a', usedX (g :: X) s1 q a' -> exists a, usedX X s q a /\ af_shape a a' /\ am_slots a' = am_slots a).
{ intros q a' Hq. destruct (Bwd1 q a' Hq) as (_ & a & Ha & E). pose proof (strip_fields _ _ E) as (M0&_&_&L0&S0&P0&_&Q0).
exists a. split; [exact Ha|]. split; [apply af_shape_i; assumption | exact Q0]. }
assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
(exists h x, s1' = upd_meta h x s1 /\ h <> g /\
(exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ am_mem ah' = am_mem ah /\ am_maplen ah' = am_maplen ah /\
blocks_of h ah' = blocks_of h ah /\ am_sc ah' = am_sc ah /\ am_last ah' = am_last ah /\ am_slots ah' = am_slots ah)) \/ s1' = s1 ->
let s1 := s1' in
Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
(forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
(forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1 /\
(forall q a, usedX X s q a -> q <> g -> exists a', usedX (g :: X) s1 q a' /\ af_shape a a') /\
(forall q a', usedX (g :: X) s1 q a' -> exists a, usedX X s q a /\ af_shape a a' /\ am_slots a' = am_slots a) /\
afhk s s1).
{ intros s1' HI1' Hcase. cbn zeta. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Emh & Emlh & Ebl & Esch & Elah & Eslh) | ->].
- split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
split; [exact Eus1|]. split; [exact Erg1|].
assert (C2 : forall q a, usedX (g :: X) (upd_meta h (MUsed ah') s1) q a ->
exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
{ intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
- injection E as <-. destruct (C1 h ah Uh) as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence.
- apply C1. exact Hq. }
split.
{ intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
- pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite MT_upd_other in M by (intros E; exact (Hhg (eq_sym E))).
rewrite Mg1 in M. injection M as <-. exists am. split; [exact Hu|]. destruct am; split; reflexivity.
- apply C2. apply usedX_cons; assumption. }
split; [exact C2|]. split.
{ intros q Hq Hqg. destruct (sptr_eq_dec q h) as [->|Hqh].
+ exfalso. destruct (Bwd1 h ah Uh) as (_ & a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (_&_&_&_&Es&_).
apply (Hq a0 H0). congruence.
+ rewrite MT_upd_other by exact Hqh. apply Mo1; assumption. }
split.
{ eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))|].
rewrite (proj1 (usedX_MT _ _ _ _ Uh)). cbn. exact Ebl. }
split.
{ intros q a Hq Hne. destruct (FWs q a Hq Hne) as (a1 & H1 & E1). pose proof (strip_fields _ _ E1) as (M1&_&_&L1&S1&P1&_).
destruct (sptr_eq_dec q h) as [->|Hqh].
+ pose proof (usedX_fun _ _ _ _ _ H1 Uh) as ->. exists ah'. split.
* apply usedX_upd. left. split; [reflexivity|]. split; [exact (proj2 (usedX_MT _ _ _ _ Uh)) | reflexivity].
* apply af_shape_i; congruence.
+ exists a1. split; [apply usedX_upd; right; split; [exact Hqh | exact H1] | apply af_shape_i; assumption]. }
split.
{ intros q a' Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
+ injection E as <-. destruct (BWs h ah Uh) as (a & Ha & Sh0 & Esl0). exists a. split; [exact Ha|].
destruct Sh0 as (M0 & P0 & S0 & L0). split; [apply af_shape_i; congruence | congruence].
+ exact (BWs q a' Hq). }
split; [|split; [exact Ear1 | exact Eamc1]].
rewrite keys_upd_In; [exact EK1 | eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))].
- split; [exact HI1'|]. split; [exact Mg1|]. split; [exact Eus1|]. split; [exact Erg1|]. split; [exact Cr1|]. split; [exact C1|].
split; [exact Mo1|]. split; [exact UB1|].
split; [intros q a Hq Hne; destruct (FWs q a Hq Hne) as (a1 & H1 & E1); pose proof (strip_fields _ _ E1) as (M1&_&_&L1&S1&P1&_); exists a1; split; [exact H1 | apply af_shape_i; assumption]|].
split; [exact BWs|]. split; [exact EK1 | split; [exact Ear1 | exact Eamc1]]. }
destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
+ apply osptr_eqb_eq in Ehd. destruct (Hnew1 Ehd) as [Hnone | (h & ah & Hh & Hhg & Uh & Sh & Avh)].
* rewrite Hnone. apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
* rewrite Hh. mbinds. eapply activate_group_spec; [exact HI1 | exact Hsc | exact Uh | exact Sh | exact Hh | exact Avh |].
intros mk s2 HI2 Es2. msimp. apply itok_ret. cbn [snd]. apply (POST1 s2 HI2). left.
eexists h, _. split; [exact Es2|]. split; [exact Hhg|]. eexists ah, _. split; [reflexivity|]. split; [exact Uh|]. split; [exact Sh|].
split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity|]. split; [apply blocks_of_ext; destruct ah; reflexivity|].
split; [destruct ah; reflexivity|]. split; [destruct ah; reflexivity | destruct ah; reflexivity].
+ apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
- apply itok_ret. cbn [snd].
assert (Hp : am_prev am = None).
{ destruct Hscr as [H63|Hsc]; [destruct (inv_rings HI) as (_ & _ & D); exact (proj1 (D g am Hu H63))|].
eapply unlinked_of_next_None; eauto. }
split; [apply (Inv_exempt X (Some (g, i)) U s g am HI Hu Hnofr Hp Enx); intros p j E; injection E; auto|].
split; [rewrite Mg; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
+ intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. auto.
+ split; [intros; reflexivity|]. split; [apply ub_same_refl|].
split; [intros q a Hq Hne; exists a; split; [apply usedX_cons; assumption | apply af_shape_refl]|].
split; [intros q a' Hq; apply usedX_cons_inv in Hq as [_ Hq]; exists a'; split; [exact Hq | split; [apply af_shape_refl | reflexivity]]|].
split; [reflexivity | split; reflexivity]. }
revert STEP1. apply itok_mono. intros [u1 s1] (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1 & FW1 & BW1 & HK1). cbn [fst snd] in *. msimp.
mbinds. eapply itok_getm; [exact Mg1|]. msimp.
replace (am_last (am_set_links None None am)) with (am_last am) by (destruct am; reflexivity).
replace (am_maplen (am_set_links None None am)) with (am_maplen am) by (destruct am; reflexivity).
replace (am_mem (am_set_links None None am)) with (am_mem am) by (destruct am; reflexivity).
assert (HU1 : forall c, 0 <= c < 48 -> U1 c = U c + (if sc =? c then am_last am + 1 else 0)).
{ intros c Hc. unfold U1. rewrite (contrib_used X s c g am Hu). reflexivity. }
mbinds.
match goal with |- itok (?mm s1) _ =>
assert (STEP2 : itok (mm s1) (fun r => let s2 := snd r in
Inv (g :: X) None U s2 /\ st_metas s2 = st_metas s1 /\ st_regions s2 = st_regions s /\ st_active s2 = st_active s1 /\
st_areas s2 = st_areas s1 /\ st_avail_meta_count s2 = st_avail_meta_count s1)) end.
{ destruct (sc <? 48) eqn:E48.
- apply Z.ltb_lt in E48. apply itok_set_usage_of. cbn zeta.
assert (Hv : am_last am + 1 <= usage_of s sc).
{ rewrite (inv_usage HI sc ltac:(lia)). pose proof (class_sum_ge_contrib X _ U s sc g HI Kg) as Hge.
rewrite (contrib_used X s sc g am Hu) in Hge. fold sc in Hge. rewrite Z.eqb_refl in Hge. pose proof (HU sc). lia. }
pose proof (Inv_set_usage (g :: X) None U1 s1 sc (usage_of s sc - (am_last am + 1)) HI1 ltac:(lia) ltac:(lia)) as HI2.
split; [|split; [reflexivity|split; [exact Erg1|split; [reflexivity|split; reflexivity]]]].
eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. rewrite (HU1 c Hc).
replace (usage_of s1 sc) with (usage_of s sc) by (unfold usage_of; rewrite Eus1; reflexivity).
destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
- apply Z.ltb_ge in E48. apply itok_ret. cbn zeta. split; [|split; [reflexivity|split; [exact Erg1|split; [reflexivity|split; reflexivity]]]].
eapply Inv_U_ext; [|exact HI1]. intros c Hc. rewrite (HU1 c Hc).
destruct (sc =? c) eqn:E2; [apply Z.eqb_eq in E2; lia | lia]. }
revert STEP2. apply itok_mono. intros [u2 s2] (HI2 & Em2 & Erg2 & Ea2 & Ear2 & Eamc2). cbn [fst snd] in *. msimp.
assert (MT2 : forall q, MT s2 q = MT s1 q) by (intros; unfold MT; rewrite Em2; reflexivity).
assert (EU2 : forall Y q a, usedX Y s2 q a <-> usedX Y s1 q a) by (intros; unfold usedX, MTX; rewrite MT2; tauto).
assert (C2 : forall q a, usedX (g :: X) s2 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
{ intros q a Hq. apply EU2 in Hq. apply C1. exact Hq. }
assert (REL2 : afrel X s (g :: X) None s2).
{ split.
- intros q a' Hq. apply EU2 in Hq. destruct (BW1 q a' Hq) as (a & Ha & Sh' & Esl). exists a. split; [exact Ha|].
split; [exact Sh'|]. split; [apply af_frs_slots; exact Esl|]. intros _. apply frameless_slots; [exact Esl | exact (proj2 (proj2 (proj2 Sh')))].
- intros q a Hq Hm. rewrite memb_cons in Hm. apply orb_false_elim in Hm as [Hm _]. apply sptr_eqb_neq in Hm.
destruct (FW1 q a Hq Hm) as (a' & Ha' & Sh'). exists a'. split; [apply EU2; exact Ha' | exact Sh']. }
assert (HK2 : afhk s s2).
{ destruct HK1 as (K1 & A1 & C1'). split; [unfold keys; rewrite Em2; exact K1 | split; [rewrite Ear2; exact A1 | rewrite Eamc2; exact C1']]. }
mbinds.
match goal with |- itok (?mm s2) _ =>
assert (STEP3 : itok (mm s2) (fun r => let s4 := snd r in
Inv (g :: X) None U s4 /\ ub_same s s4 /\
(forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0) /\
match fst r with
| None => True
| Some (k, len) => exists rg, region_of s4 k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
rg_len rg = page_round len /\ 0 <= len /\ (forall q a, usedX (g :: X) s4 q a -> 0 < am_maplen a -> prid (am_mem a) <> k)
end /\ SIXo (g :: X) (fst r) s4)) end.
{ destruct (negb (am_maplen am =? 0)) eqn:Eml.
-
assert (Hml : 0 < am_maplen am) by (destruct (am_maplen am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; lia]).
mbinds. eapply step_seq_spec_h; [exact HI2|]. intros s3 HI3 (Em3 & _ & Er3 & _ & _ & Ear3) Eamc3. msimp.
mbinds. eapply record_seq_spec_h; [exact HI3|]. intros s4 HI4 (Em4 & _ & Er4 & _ & _ & Ear4) Eamc4. msimp.
apply itok_ret. cbn zeta. cbn [fst snd].
assert (EU4 : forall q a, usedX (g :: X) s4 q a <-> usedX (g :: X) s2 q a) by (intros; unfold usedX, MTX, MT; rewrite Em4, Em3; tauto).
split; [exact HI4|]. split.
{ eapply ub_same_trans; [exact UBs1|]. apply ub_same_metas. rewrite Em4, Em3, Em2. reflexivity. }
split; [intros q a Hq; apply C2; apply EU4; exact Hq|].
split.
{ destruct (Gmp Hml) as (r & rg & Emem & Hr & Hk & Hl & Hlen & _). exists rg. rewrite Emem. cbn [prid].
split; [unfold region_of in *; rewrite Er4, Er3, Erg2; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split.
{ rewrite Hlen. unfold PGSZ. rewrite page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult. }
split; [lia|].
intros q a Hq Hqm. apply EU4 in Hq. pose proof (usedX_cons_inv _ _ _ _ _ Hq) as [Hqg _].
destruct (C2 q a Hq) as (a0 & H0 & E0 & F0). rewrite E0. rewrite F0 in Hqm. intros Ep. apply Hqg.
eapply (inv_maps HI q a0 g am H0 Hu Hqm Hml). rewrite Emem. cbn. exact Ep. }
assert (REL4 : afrel X s (g :: X) None s4) by (eapply afrel_metas; [exact REL2 | rewrite Em4, Em3; reflexivity]).
split; [|split; [|split; [|split]]].
+ eapply owned_tr; [apply ex_of_owned; exact SXo | exact REL4 | rewrite Er4, Er3; exact Erg2 | intros k [] |].
intros q a Hq _ Hne. rewrite memb_cons, (proj2 (usedX_MT _ _ _ _ Hq)), orb_false_r. apply sptr_eqb_neq. intros ->.
apply Hne. rewrite (usedX_fun _ _ _ _ _ Hq Hu). exact eq_refl.
+ eapply empty_ok_tr; [exact SXe | exact REL4 |]. intros q a' Hq _ _ Hn. exfalso. exact (Hn (unres_cons _ _ _ i _ _ Hq)).
+ eapply empty_unique_tr; [exact SXu | exact REL4 |]. intros q1 a1 q2 a2 H1 _ _ _ _ _ _ Hn. exfalso. exact (Hn (unres_cons _ _ _ i _ _ H1)).
+ eapply children_tr; [exact SXc | exact REL4 |]. intros q a' j fr c ac _ _ _ _ Hc Hmlc _.
rewrite memb_cons, (proj2 (usedX_MT _ _ _ _ Hc)), orb_false_r. apply sptr_eqb_neq. intros ->.
rewrite (usedX_fun _ _ _ _ _ Hc Hu) in Hmlc. lia.
+ eapply afhk_hand; [|exact SXh]. destruct HK2 as (K & A & C).
split; [unfold keys; rewrite Em4, Em3; exact K | split; [rewrite Ear4, Ear3; exact A | rewrite Eamc4, Eamc3; exact C]].
-
assert (Hml : am_maplen am = 0) by (destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; exact E | discriminate]).
destruct (Gns Hml) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & Fit).
assert (Hsc : 0 <= sc < 48) by (destruct Hscr as [H|H]; [exfalso; exact (N63 H) | exact H]).
pose proof (inv_groups HI g' am' U') as G'. pose proof G' as ((_ & _ & Glen' & _) & _ & Gsl' & Gcl' & _).
pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'. destruct S3' as (Hal' & _ & (_ & _ & _ & _ & FG') & _).
destruct (FG' K') as [Hoff' _].
assert (Hsc'48 : 0 <= am_sc am' < 48) by (destruct Gcl' as [(C & _) | (C & _)]; [exfalso; exact (N63' C) | exact C]).
assert (Hg'g : g' <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ U' Hu) as E; rewrite E in Hsc'; lia).
pose proof (usedX_MT _ _ _ _ U') as [Mg' NXg'].
assert (U'2 : usedX (g :: X) s2 g' am').
{ apply EU2. apply usedX_intro.
- rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity.
- rewrite (Mo1 g'); [exact Mg' | | exact Hg'g]. intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha U') as ->. lia. }
assert (Eptr : am_mem am = frame_ptr am' i' fr').
{ unfold frame_ptr. rewrite Hoff', Z.mul_0_r, padd_0. exact Emem. }
mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
rewrite Eptr, (find_frame_in_spec (g :: X) None U s2 HI2 g' am' i' fr' U'2 Hi' F'). msimp. apply itok_ret. cbn [fst snd].
mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U'2))|]. msimp.
mbinds. apply itok_mcheck; [unfold slot_is_group; rewrite F', K'; reflexivity|]. msimp.
mbinds. eapply (forget_frame_spec (g :: X) U s2 g' i' am' fr'); [exact HI2 | exact U'2 | exact Hi' | exact F' | |].
{ intros c ac Hc Hmlc Emc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
destruct (C2 c ac Hc) as (ac0 & H0 & E0 & _).
eapply (same_mem_contra X _ U s c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Emem. }
intros s3 Es3 HI3. msimp.
set (am'' := upd_slot am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) in Es3.
assert (U'3 : usedX (g :: X) s3 g' am'').
{ rewrite Es3. apply usedX_upd. left. split; [reflexivity|]. split; [|reflexivity].
rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity. }
pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am'' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (REL23 : afrel (g :: X) s2 (g :: X) (Some (g', i')) s3).
{ split.
- intros q a' Hq. rewrite Es3 in Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
+ injection E as <-. exists am'. split; [exact U'2|]. split; [apply af_shape_i; assumption|].
split; [apply frs_upd_slot; reflexivity|]. intros Hr. exfalso. exact (Hr i' eq_refl).
+ exists a'. split; [exact Hq|]. split; [apply af_shape_refl|]. split; [intros j f0 Hf'; exact Hf' | auto].
- intros q a Hq _. destruct (sptr_eq_dec q g') as [->|Hne].
+ pose proof (usedX_fun _ _ _ _ _ Hq U'2) as ->. exists am''. split; [exact U'3 | apply af_shape_i; assumption].
+ exists a. split; [rewrite Es3; apply usedX_upd; right; split; assumption | apply af_shape_refl]. }
assert (REL3 : afrel X s (g :: X) (Some (g', i')) s3).
{ eapply afrel_trans; [exact REL2 | exact REL23 | auto |]. intros q a2 _ _ j E. discriminate. }
assert (HK3 : afhk s s3).
{ destruct HK2 as (K & A & C). rewrite Es3. split; [|split; [exact A | exact C]].
rewrite keys_upd_In; [exact K | eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U'2))]. }
eapply (IH (g :: X) U s3 g' i' am''); [exact HI3 | exact U'3 | exact HU | | | |].
+
intros Hl Hnh. replace (am_freed am'') with (am_freed am') by (subst am''; destruct am'; reflexivity).
replace (am_prev am'', am_next am'') with (am_prev am', am_next am') in Hl by (subst am''; destruct am'; reflexivity).
rewrite Fsc in Hnh. replace (active_hd s3 (am_sc am')) with (active_hd s2 (am_sc am')) in Hnh by (rewrite Es3; reflexivity).
apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 U'2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate].
+ rewrite Fsc. unfold fneed in Hf |- *. fold sc in Hf.
replace (sc <? 48) with true in Hf by (symmetry; apply Z.ltb_lt; lia).
replace (am_sc am' <? 48) with true by (symmetry; apply Z.ltb_lt; lia). lia.
+ split; [|split; [|split; [|split]]].
* apply owned_of_ex. eapply owned_tr; [apply ex_of_owned; exact SXo | exact REL3 | rewrite Es3; exact Erg2 | intros k [] |].
intros q a Hq Hqm _. rewrite memb_cons, (proj2 (usedX_MT _ _ _ _ Hq)), orb_false_r. apply sptr_eqb_neq. intros ->.
rewrite (usedX_fun _ _ _ _ _ Hq Hu) in Hqm. lia.
* eapply empty_ok_tr; [exact SXe | exact REL3 |]. intros q a' Hq _ _ Hn. exfalso. exact (Hn (unres_cons _ _ _ i _ _ Hq)).
* eapply empty_unique_tr; [exact SXu | exact REL3 |]. intros q1 a1 q2 a2 H1 _ _ _ _ _ _ Hn. exfalso. exact (Hn (unres_cons _ _ _ i _ _ H1)).
* eapply children_tr; [exact SXc | exact REL3 |].
intros q a3 j fr c ac Hq Hj Hfj Hkj Hc Hmlc Hmemc.
rewrite memb_cons, (proj2 (usedX_MT _ _ _ _ Hc)), orb_false_r. apply sptr_eqb_neq. intros ->.
pose proof (usedX_fun _ _ _ _ _ Hc Hu) as ->.
destruct (proj1 REL3 q a3 Hq) as (a & Ha & Sha & _).
rewrite (af_shape_slot_start _ _ j Sha) in Hmemc.
assert (Hja : 0 <= j <= am_last a) by (destruct Sha as (_ & _ & _ & La); lia).
destruct (slot_starts_distinct X (Some (g, i)) U s HI q a j g' am' i' Ha U' Hja Hi' ltac:(rewrite <- Hmemc; exact Emem)) as [-> ->].
rewrite Es3 in Hq. apply usedX_upd in Hq. destruct Hq as [(_ & _ & E) | (Hne & _)]; [|exact (Hne eq_refl)].
injection E as <-. unfold am'' in Hfj. rewrite nth_slot_upd_slot in Hfj; [| lia | lia | rewrite Glen'; lia].
rewrite Z.eqb_refl in Hfj. cbn in Hfj. discriminate Hfj.
* eapply afhk_hand; [exact HK3 | exact SXh].
+ intros [mi s4] (HI4 & Cr4 & UB34 & Hmi) S4. cbn [fst snd] in *. cbn zeta.
assert (C4 : forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0).
{ intros q a Hq. destruct (Cr4 q a Hq) as (a3 & H3 & E3 & F3).
rewrite Es3 in H3. apply usedX_upd in H3. destruct H3 as [(-> & _ & E) | (Hne & H2')].
- injection E as <-. destruct (C2 g' am' U'2) as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence.
- destruct (C2 q a3 H2') as (a0 & H0 & E0 & F0). exists a0. split; [exact H0|]. split; congruence. }
split; [exact HI4|]. split; [|split; [exact C4 | split; [exact Hmi | exact S4]]].
eapply ub_same_trans; [exact UBs1|]. eapply ub_same_trans; [apply ub_same_metas; exact Em2|]. eapply ub_same_trans; [|exact UB34].
rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U'2))|].
rewrite (proj1 (usedX_MT _ _ _ _ U'2)). cbn. pose proof (inv_groups HI2 g' am' U'2) as ((_ & _ & Glen2 & _) & _).
apply blocks_of_upd_slot_same; [exact Hi' | exact Glen2 |]. unfold slotst_block, slot_block. cbn. rewrite F', K'. reflexivity. }
revert STEP3. apply itok_mono. intros [mi s4] (HI4 & UB4 & C4 & Hmi & S4). cbn [fst snd] in *. msimp.
mbinds. eapply free_meta_spec; [exact HI4 | left; reflexivity |]. intros s5 HI5 Sb5 Ea5 EU5 UB5. msimp.
rewrite (remove_head_notin g X NXg) in HI5, EU5.
apply itok_ret. apply HQ.
+ unfold nf_post. cbn [fst snd].
split; [exact HI5|]. split.
{ intros q a Hq. apply EU5 in Hq. apply C4. exact Hq. }
split; [eapply ub_same_trans; [exact UB4 | exact UB5]|].
destruct mi as [[k len]|]; [|exact I].
destruct Hmi as (rg & Hr & Hk & Hl & Hlen & Hlen0 & Hno). exists rg.
pose proof Sb5 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg5&_).
split; [unfold region_of in *; rewrite Erg5; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
intros q a Hq. apply EU5 in Hq. exact (Hno q a Hq).
+ cbn [fst snd]. pose proof Sb5 as (_&_&_&Eamc5&_&_&_&_&_&_&_&_&_&_&Erg5&Ear5&EK5).
exact (SIXo_equiv X (g :: X) mi s4 s5 EU5 Erg5 (conj EK5 (conj Ear5 Eamc5)) S4).
-
destruct (else_branch_facts X U s g i am HI Hu Hcond) as [Hsc Hstr]. fold sc in Hsc, Hstr.
pose proof (ring_facts X (Some (g, i)) U s g am HI Hu ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3). fold sc in RF1, RF2, RF3.
mbinds.
match goal with |- itok (?mm s) _ =>
assert (STEPE : itok (mm s) (fun r => let s1 := snd r in
Inv X (Some (g, i)) U s1 /\
exists am2, MT s1 g = Some (MUsed am2) /\ (am_prev am2, am_next am2) <> (None, None) /\ strip am2 = strip am /\
(forall q a', usedX X s1 q a' -> exists a, usedX X s q a /\ strip a' = strip a) /\ ub_same s s1 /\
(forall q a, usedX X s q a -> exists a', usedX X s1 q a' /\ strip a' = strip a) /\
st_regions s1 = st_regions s /\ afhk s s1)) end.
{ destruct (mask =? 0) eqn:Em0.
- apply Z.eqb_eq in Em0.
assert (Hfr0 : am_freed am = 0).
{ subst mask. apply Z.lor_eq_0_iff in Em0. exact (proj1 Em0). }
mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
+ apply osptr_eqb_eq in Ehd. apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
split; [exact Mg|].
split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | split; [apply ub_same_refl | split; [intros q a Hq; exists a; auto | split; [reflexivity | split; [reflexivity | split; reflexivity]]]]]]].
destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & _).
apply (Mem g am Hu eq_refl). rewrite Ehd in Rg. exact (proj1 (ring_head_In _ _ _ Rg)).
+ assert (Hnh : active_hd s sc <> Some g) by (intros E; rewrite E in Ehd; cbn in Ehd; rewrite sptr_eqb_refl in Ehd; discriminate).
assert (Hunl : am_prev am = None /\ am_next am = None).
{ destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; try (exfalso; apply (HR2g ltac:(discriminate) Hnh); exact Hfr0). auto. }
destruct Hunl as [Hp Hn].
eapply (requeue_f X U s sc g i am); [exact HI | exact Hsc | exact Hu | reflexivity | exact Hp | exact Hn | exact Hnh |].
intros s1 pr nx F1 HI1 Sb1 Mg1 EH1 Bwd1 UB1. cbn zeta. cbn [snd]. split; [exact HI1|]. exists (am_set_links (Some pr) (Some nx) am).
pose proof Sb1 as (_&_&_&Eamc1&_&_&_&_&_&_&_&_&_&_&Erg1&Ear1&EK1).
split; [exact Mg1|]. split; [destruct am; cbn; discriminate|]. split; [destruct am; reflexivity|]. split; [exact Bwd1|]. split; [exact UB1|].
split; [|split; [exact Erg1 | split; [exact EK1 | split; [exact Ear1 | exact Eamc1]]]].
intros q a Hq. pose proof (usedX_MT _ _ _ _ Hq) as [Mq Nq]. destruct (F1 q a Mq) as (a' & M' & E'). exists a'. split; [apply usedX_intro; assumption | exact E'].
- apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
split; [exact Mg|].
split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | split; [apply ub_same_refl | split; [intros q a Hq; exists a; auto | split; [reflexivity | split; [reflexivity | split; reflexivity]]]]]]].
intros HL. destruct (RF1 HL) as [Hav0 Hfr0]. apply Z.eqb_neq in Em0. apply Em0. subst mask. rewrite Hav0, Hfr0. reflexivity. }
revert STEPE. apply itok_mono. intros [u1 s1] (HI1 & am2 & Mg2 & Hl2 & Hst2 & Bwd1 & UB1 & FWE & ErgE & HKE). cbn [fst snd] in *. msimp.
pose proof (strip_fields _ _ Hst2) as (Emem2 & _ & _ & _ & Esc2 & Eml2 & _).
assert (U2 : usedX X s1 g am2) by (apply usedX_intro; [exact NXg | exact Mg2]).
mbinds. eapply itok_getm; [exact Mg2|]. msimp. mbinds. apply itok_setm'. msimp. apply itok_ret.
apply HQ.
+ unfold nf_post. cbn [fst snd]. split; [|split; [|split; [|exact I]]].
* apply (set_freed_Inv X U s1 g i am2 HI1 U2); [rewrite Esc2; exact Hsc | exact Hl2 |].
rewrite Esc2, (strip_stride _ _ Hst2). exact Hstr.
* intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
-- injection E as <-. exists am. split; [exact Hu|]. destruct am2, am; cbn in Emem2, Eml2 |- *; subst; auto.
-- destruct (Bwd1 q a Hq) as (a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (Em&_&_&_&_&Eml&_). exists a0. auto.
* eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg2|]. rewrite Mg2. cbn. apply blocks_of_freed.
+ cbn [fst snd]. set (a' := am_set_freed (Z.lor (am_freed am2) (bit i)) am2).
pose proof (strip_fields _ _ Hst2) as (_ & Eav2 & Efr2 & Ela2 & _ & _ & _ & Esl2).
assert (Ua' : usedX X (upd_meta g (MUsed a') s1) g a') by (apply usedX_upd; left; split; [reflexivity | split; [exact NXg | reflexivity]]).
assert (Esla : am_slots a' = am_slots am) by exact Esl2.
assert (Sha : af_shape am a') by (apply af_shape_i; [exact Emem2 | exact Eml2 | exact Esc2 | exact Ela2]).
assert (HI' : Inv X None U (upd_meta g (MUsed a') s1)).
{ apply (set_freed_Inv X U s1 g i am2 HI1 U2); [rewrite Esc2; exact Hsc | exact Hl2 |]. rewrite Esc2, (strip_stride _ _ Hst2). exact Hstr. }
assert (RELB : afrel X s X None (upd_meta g (MUsed a') s1)).
{ split.
- intros q b Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
* injection E as <-. exists am. split; [exact Hu|]. split; [exact Sha|]. split; [apply af_frs_slots; exact Esla|].
intros _. apply frameless_slots; [exact Esla | exact Ela2].
* destruct (Bwd1 q b Hq) as (a & Ha & E). pose proof (strip_fields _ _ E) as (M1&_&_&L1&S1&P1&_&Q1).
exists a. split; [exact Ha|]. split; [apply af_shape_i; assumption|]. split; [apply af_frs_slots; exact Q1|].
intros _. apply frameless_slots; [exact Q1 | exact L1].
- intros q a Hq _. destruct (sptr_eq_dec q g) as [->|Hne].
* pose proof (usedX_fun _ _ _ _ _ Hq Hu) as ->. exists a'. split; [exact Ua' | exact Sha].
* destruct (FWE q a Hq) as (b & Hb & E). pose proof (strip_fields _ _ E) as (M1&_&_&L1&S1&P1&_).
exists b. split; [apply usedX_upd; right; split; [exact Hne | exact Hb] | apply af_shape_i; assumption]. }
assert (Hfull : frameless a' -> 0 < am_maplen am /\ am_next am = Some g).
{ intros Hfa. pose proof (mask_of_frameless X U _ g a' HI' Ua' Hfa) as E.
assert (Hm : mask + bit i = ones (am_last am)).
{ unfold mask. apply mask_add_full; [lia | |].
- rewrite Z.lor_comm. revert Hal. unfold allocated.
destruct (Z.testbit (Z.lor (am_avail am) (am_freed am)) i); intros H; [cbn in H; discriminate H | reflexivity].
- unfold a' in E. cbn [am_freed am_avail am_last am_set_freed] in E. rewrite Efr2, Eav2, Ela2 in E. exact E. }
rewrite Hm, Z.eqb_refl, andb_true_l in Hcond. destruct (okay_false s g am Hcond) as [A B]. split; [lia | exact B]. }
split; [|split; [|split; [|split]]].
* eapply owned_tr; [apply ex_of_owned; exact SXo | exact RELB | exact ErgE | intros k [] |].
intros q a Hq _ _. exact (proj2 (usedX_MT _ _ _ _ Hq)).
* eapply empty_ok_tr; [exact SXe | exact RELB |]. intros q b Hq _ Hfb Hn.
pose proof (not_unres_eq _ _ _ Hn) as ->. pose proof (usedX_fun _ _ _ _ _ Hq Ua') as ->.
destruct (Hfull Hfb) as [Hp _]. destruct Sha as (_ & P & S & _). rewrite P, S. split; [exact Hp | exact Hsc].
* eapply empty_unique_tr; [exact SXu | exact RELB |]. intros q1 b1 q2 b2 H1 H2 F1 F2 _ _ Es Hn.
pose proof (not_unres_eq _ _ _ Hn) as ->. pose proof (usedX_fun _ _ _ _ _ H1 Ua') as ->.
destruct (Hfull F1) as [_ Hnx].
destruct (sptr_eq_dec q2 g) as [E|Hne]; [exact (eq_sym E)|]. exfalso.
destruct (proj1 RELB q2 b2 H2) as (c2 & Hc2 & Sh2 & _ & Fl2). pose proof (Fl2 (unres_None q2) F2) as Fc2.
assert (Esc2q : am_sc c2 = sc).
{ destruct Sh2 as (_ & _ & S2 & _). destruct Sha as (_ & _ & S1 & _). unfold sc. congruence. }
destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & Full & _).
assert (Hgin : In g ms) by (apply (proj2 (Mem g am Hu eq_refl)); rewrite Hnx; intros E; discriminate).
assert (Hlk : alinks X s sc g = Some (am_prev am, Some g)).
{ unfold alinks. pose proof Hu as Hu0. unfold usedX in Hu0. rewrite Hu0. cbv beta iota.
replace (am_sc am =? sc) with true by (symmetry; apply Z.eqb_eq; reflexivity). rewrite Hnx. reflexivity. }
destruct (in_dec sptr_eq_dec q2 ms) as [Hin|Hnin].
-- exact (Hne (ring_singleton _ _ _ _ _ Rg Hgin Hlk q2 Hin)).
-- destruct (Full q2 c2 Hc2 Esc2q Hnin) as [Hav0 Hfr0].
pose proof (inv_groups HI q2 c2 Hc2) as ((Gl2 & _) & _ & Gsl2 & _).
pose proof (Gsl2 0 ltac:(lia)) as (_ & _ & S03). rewrite (Fc2 0 ltac:(lia)) in S03.
destruct S03 as [Hal0|Er]; [|injection Er as Er _; exact (Hne (eq_sym Er))].
unfold allocated in Hal0. rewrite Hav0, Hfr0 in Hal0. cbn in Hal0. discriminate Hal0.
* eapply children_tr; [exact SXc | exact RELB |]. intros q b j fr c ac _ _ _ _ Hc _ _. exact (proj2 (usedX_MT _ _ _ _ Hc)).
* eapply afhk_hand; [|exact SXh]. destruct HKE as (K & A & C). split; [|split; [exact A | exact C]].
rewrite keys_upd_In; [exact K | eapply MT_Some_In_keys; exact Mg2].
Qed.

Theorem free_SIspec s g am idx fr (Q : unit * astate -> Prop) :
WF s -> SI s -> usedX [] s g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
(forall s', SI s' -> Q (tt, s')) ->
itok (free (Some (frame_ptr am idx fr)) s) Q.
Proof.
intros HI HS Hu Hidx Hfr Hk HQ.
pose proof HS as (SXo & SXe & SXu & SXc & SXh).
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & _ & _).
assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
unfold free. mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
rewrite (find_frame_in_spec [] None U0 s HI g am idx fr Hu Hidx Hfr). apply itok_ret. msimp.
mbinds. eapply itok_getm; [exact Mg|]. msimp. cbn zeta.
mbinds. eapply release_slot_spec; [exact HI | exact Hu | exact Hidx | exact Hfr | exact Hk |].
intros s1 x Es1 Hx HI1. msimp.
set (am1 := upd_slot am idx x) in Es1.
assert (U1 : usedX [] s1 g am1) by (rewrite Es1; apply usedX_upd; left; auto).
pose proof (upd_slot_fields am idx x) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am1 in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (Flk : (am_prev am1, am_next am1) = (am_prev am, am_next am) /\ am_freed am1 = am_freed am /\ am_avail am1 = am_avail am).
{ subst am1. destruct am; repeat split; reflexivity. }
destruct Flk as (Flk & Ffr & Fav).
assert (Hbits : Z.testbit (am_freed am) idx = false /\ Z.testbit (am_avail am) idx = false).
{ unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) idx), (Z.testbit (am_freed am) idx); cbn in Hal; try discriminate; auto. }
destruct Hbits as [Hfb Hab].
mbinds. apply itok_massert.
{ apply Z.eqb_eq. apply bits_inj_nonneg. intros j Hj. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.bits_0 by lia.
destruct (Z.eq_dec idx j) as [<-|Hne]; [rewrite Hfb, Hab, Z.eqb_refl; reflexivity|].
replace (idx =? j) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply andb_false_r. }
msimp.
assert (REL1 : afrel [] s [] (Some (g, idx)) s1).
{ split.
- intros q b Hq. rewrite Es1 in Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
+ injection E as <-. exists am. split; [exact Hu|]. split; [apply af_shape_i; assumption|].
split; [apply frs_upd_slot; exact Hx|]. intros Hr. exfalso. exact (Hr idx eq_refl).
+ exists b. split; [exact Hq|]. split; [apply af_shape_refl|]. split; [intros j f0 Hf0; exact Hf0 | auto].
- intros q a Hq _. destruct (sptr_eq_dec q g) as [->|Hne].
+ pose proof (usedX_fun _ _ _ _ _ Hq Hu) as ->. exists am1. split; [exact U1 | apply af_shape_i; assumption].
+ exists a. split; [rewrite Es1; apply usedX_upd; right; split; assumption | apply af_shape_refl]. }
assert (HK1 : afhk s s1).
{ rewrite Es1. split; [|split; reflexivity]. apply keys_upd_In. eapply MT_Some_In_keys. exact Mg. }
assert (S1 : SIX [] (Some (g, idx)) s1).
{ split; [|split; [|split; [|split]]].
- apply owned_of_ex. eapply owned_tr; [apply ex_of_owned; exact SXo | exact REL1 | rewrite Es1; reflexivity | intros k [] | intros; reflexivity].
- eapply empty_ok_tr; [exact SXe | exact REL1 |]. intros q b _ _ _ Hn. exfalso. exact (Hn (unres_None q)).
- eapply empty_unique_tr; [exact SXu | exact REL1 |]. intros q1 b1 q2 b2 _ _ _ _ _ _ _ Hn. exfalso. exact (Hn (unres_None q1)).
- eapply children_tr; [exact SXc | exact REL1 | intros; reflexivity].
- eapply afhk_hand; [exact HK1 | exact SXh]. }
pose proof (ring_facts [] None U0 s g am HI Hu) as RF.
destruct (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit idx =? ones (am_last am))) eqn:Ebr.
-
apply andb_prop in Ebr as [Efr0 Efull]. assert (Hfr0 : am_freed am <> 0) by (destruct (am_freed am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; exact E]).
assert (Hsc : 0 <= am_sc am < 48).
{ destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct Gcl as [(_ & _ & _ & _ & C5 & _) | (C & _)]; [exact (Hfr0 C5) | lia]. }
destruct (RF ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3).
assert (Hlinked : (am_prev am, am_next am) <> (None, None)) by (intros HL; destruct (RF1 HL) as [_ E]; exact (Hfr0 E)).
assert (Hstr : class_size (am_sc am) <= stride_of am).
{ destruct Gcl as [(C & _) | (_ & CN1 & _)]; [lia|]. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia].
exfalso. destruct (CN1 Hlt) as [Hl0 _]. apply Hfr0. apply mask_zero_of_bits; [exact Gfrn|]. intros j Hj.
destruct (Z.eq_dec j idx) as [->|Hne]; [exact Hfb|]. destruct (Gabove j ltac:(lia)) as [_ B]. exact B. }
mbinds. eapply itok_getm; [rewrite Es1; apply MT_upd_same|]. msimp. apply itok_setm'.
rewrite (add_bit_lor (am_freed am) idx ltac:(lia) Hfb). rewrite <- Ffr.
apply HQ.
set (a' := am_set_freed (Z.lor (am_freed am1) (bit idx)) am1).
assert (HI' : Inv [] None U0 (upd_meta g (MUsed a') s1)).
{ apply (set_freed_Inv [] U0 s1 g idx am1 HI1 U1); [rewrite Fsc; exact Hsc | rewrite Flk; exact Hlinked | rewrite Fsc, Fst; exact Hstr]. }
assert (Ua' : usedX [] (upd_meta g (MUsed a') s1) g a') by (apply usedX_upd; left; auto).
assert (Esla : am_slots a' = am_slots am1) by reflexivity.
assert (Sha : af_shape am1 a') by (apply af_shape_i; reflexivity).
assert (RELF : afrel [] s1 [] None (upd_meta g (MUsed a') s1)).
{ split.
- intros q b Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
+ injection E as <-. exists am1. split; [exact U1|]. split; [exact Sha|]. split; [apply af_frs_slots; exact Esla|].
intros _. apply frameless_slots; [exact Esla | reflexivity].
+ exists b. split; [exact Hq|]. split; [apply af_shape_refl|]. split; [intros j f0 Hf0; exact Hf0 | auto].
- intros q a Hq _. destruct (sptr_eq_dec q g) as [->|Hne].
+ pose proof (usedX_fun _ _ _ _ _ Hq U1) as ->. exists a'. split; [exact Ua' | exact Sha].
+ exists a. split; [apply usedX_upd; right; split; assumption | apply af_shape_refl]. }
assert (Hnf : ~ frameless a').
{ intros Hfa. pose proof (mask_of_frameless [] U0 _ g a' HI' Ua' Hfa) as E.
unfold a' in E. cbn [am_freed am_avail am_last am_set_freed] in E. rewrite Ffr, Fav, Fl in E.
assert (Hm : Z.lor (am_freed am) (am_avail am) + bit idx = ones (am_last am)).
{ apply mask_add_full; [lia | rewrite Z.lor_spec, Hfb, Hab; reflexivity | exact E]. }
rewrite Hm, Z.eqb_refl in Efull. cbn in Efull. discriminate Efull. }
destruct S1 as (S1o & S1e & S1u & S1c & S1h).
split; [|split; [|split; [|split]]].
+ apply owned_of_ex. eapply owned_tr; [apply ex_of_owned; exact S1o | exact RELF | reflexivity | intros k [] | intros; reflexivity].
+ eapply empty_ok_tr; [exact S1e | exact RELF |]. intros q b Hq _ Hfb' Hn. exfalso.
pose proof (not_unres_eq _ _ _ Hn) as ->. pose proof (usedX_fun _ _ _ _ _ Hq Ua') as ->. exact (Hnf Hfb').
+ eapply empty_unique_tr; [exact S1u | exact RELF |]. intros q1 b1 q2 b2 H1 _ F1 _ _ _ _ Hn. exfalso.
pose proof (not_unres_eq _ _ _ Hn) as ->. pose proof (usedX_fun _ _ _ _ _ H1 Ua') as ->. exact (Hnf F1).
+ eapply children_tr; [exact S1c | exact RELF | intros; reflexivity].
+ eapply afhk_hand; [|exact S1h]. split; [|split; reflexivity]. apply keys_upd_In. eapply MT_Some_In_keys. exact (proj1 (usedX_MT _ _ _ _ U1)).
-
mbinds. eapply (nf_SI NEST_FUEL [] U0 s1 g idx am1); [exact HI1 | exact U1 | exact U0_nonneg | | | exact S1 |].
+ rewrite Flk, Ffr, Fsc. replace (active_hd s1 (am_sc am)) with (active_hd s (am_sc am)) by (rewrite Es1; reflexivity).
intros HL Hnh. destruct Hscr as [H63|Hsc].
{ exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [P N]. apply HL. rewrite P, N. reflexivity. }
destruct (RF ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
+ rewrite Fsc. apply fneed_le. destruct Hscr as [H|H]; lia.
+ intros [mi s2] (HI2 & Cr2 & UB2 & Hmi) S2. cbn [fst snd] in *. msimp.
destruct mi as [[r len]|].
* destruct Hmi as (rg & Hr & Hkd & Hl & Hlen & Hlen0 & Hno).
mbinds. apply itok_ask.
{ cbn [req_ok]. exists rg. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
apply (used_metas_iff s2 q a (proj1 (inv_keys HI2))) in Hin.
exact (Hno q a (usedX_intro [] s2 q a eq_refl Hin) Hml). }
intros z _. msimp. unfold upd_region. apply itok_modify. apply HQ. apply SI_of_SIXo.
eapply SIXo_kill; [exact S2 | | reflexivity].
unfold region_of in Hr. apply nth_error_Some. rewrite Hr. discriminate.
* apply itok_ret. apply HQ. apply SI_of_SIXo. exact S2.
Qed.

Theorem free_SI : forall s p n tr s', WF s -> SI s -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (tt, s') -> SI s'.
Proof.
  intros s p n tr s' HW HS Hin Hy. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  exact (itok_yields _ (fun r => SI (snd r)) tr (tt, s') (free_SIspec s g am idx fr _ HW HS Hu Hi Hfr Hk (fun s1 H => H)) Hy).
Qed.
