(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv
  MI_Inv MI_Kit MI_Contracts.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition exhausted_head (r : meta) (m : aptr) : Prop :=
  m_avail r = 0 /\ m_freed r = 0 /\ m_next r = Some m /\ m_prev r = Some m.

Definition buf_group (cs : mstate) (m : aptr) : Prop :=
  let r := get_meta_rec cs m in
  m_last_idx r = 0 /\ m_maplen r <> 0 /\ m_freeable r = 1 /\ m_avail r = 0 /\ m_freed r = 0
  /\ ( (m_next r = Some m /\ m_prev r = Some m /\ active cs (m_sizeclass r) = Some m
        /\ 0 <= m_sizeclass r < 48 /\ get_stride r < UNIT * size_class (m_sizeclass r))
     \/ (m_next r = None /\ m_prev r = None /\ 48 <= m_sizeclass r) ).

Definition PHI (cs : mstate) : Prop :=
  c_init_done (s_ctx cs) = 1
  /\ 49 <= c_avail_meta_count (s_ctx cs)
  /\ (forall sc m, active cs sc = Some m -> exhausted_head (get_meta_rec cs m) m)
  /\ ((c_free_meta_head (s_ctx cs) = None /\ 50 <= c_avail_meta_count (s_ctx cs))
      \/ exists m, c_free_meta_head (s_ctx cs) = Some m
           /\ s_metas cs !! m = Some (mkMeta (Some m) (Some m) None 0 0 0 0 0 0))
  /\ (forall b h, s_groups cs !! b = Some h -> exists m, g_meta h = Some m /\ buf_group cs m).

Definition PHIB (cs : mstate) : Prop :=
  c_init_done (s_ctx cs) = 1
  /\ 49 <= c_avail_meta_count (s_ctx cs)
  /\ (forall sc m, active cs sc = Some m -> exhausted_head (get_meta_rec cs m) m)
  /\ c_free_meta_head (s_ctx cs) = None
  /\ (forall b h, s_groups cs !! b = Some h -> exists m, g_meta h = Some m /\ buf_group cs m).

Lemma PHIB_PHI_shape cs : PHIB cs -> 50 <= c_avail_meta_count (s_ctx cs) -> PHI cs.
Proof. intros (A & B & C & D & E) H. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [left; auto| exact E]. Qed.

Definition phiC (k : nat) (cs : mstate) : Prop := PHI cs.
Definition phiB (k : nat) (cnew : cptr) (cs : mstate) : Prop := PHIB cs.

Lemma T2_Bs : forall k cs, phiC k cs ->
  c_free_meta_head (s_ctx cs) <> None \/ 0 < c_avail_meta_count (s_ctx cs).
Proof. intros k cs (_ & H & _). right. lia. Qed.

Record CF (cs : mstate) : Prop := mkCF {
  cf_count : 0 <= c_avail_meta_count (s_ctx cs) <= NSLOTS;
  cf_avail : 0 < c_avail_meta_count (s_ctx cs) ->
     exists a, c_avail_meta (s_ctx cs) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx cs)))
       /\ snd a mod PGSZ = 0
       /\ forall k, NSLOTS - c_avail_meta_count (s_ctx cs) <= k < NSLOTS -> s_metas cs !! (mslot a k) = None;
  cf_groups : forall b m ai, s_groups cs !! b = Some (mkGhdr (Some m) ai) ->
     s_metas cs !! m <> None /\ m_mem (get_meta_rec cs m) = Some b;
  cf_nometa : forall b ai, s_groups cs !! b = Some (mkGhdr None ai) -> False;
  cf_active : forall sc m, active cs sc = Some m -> s_metas cs !! m <> None /\ 0 <= sc < 48
     /\ exists b ai, s_groups cs !! b = Some (mkGhdr (Some m) ai) /\ m_sizeclass (get_meta_rec cs m) = sc;
  cf_free : forall m, c_free_meta_head (s_ctx cs) = Some m -> s_metas cs !! m <> None
     /\ forall b h, s_groups cs !! b = Some h -> g_meta h <> Some m;
  cf_actives_keys : forall sc m, active cs sc = Some m -> 0 <= sc < 48
}.

Lemma strip_fields st :
  s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_metas (strip st) = s_metas st
  /\ s_areas (strip st) = s_areas st /\ s_groups (strip st) = s_groups st /\ s_slots (strip st) = s_slots st
  /\ s_next_rid (strip st) = s_next_rid st /\ s_reserved (strip st) = s_reserved st /\ s_secret (strip st) = s_secret st.
Proof. repeat split; reflexivity. Qed.

Lemma get_meta_rec_strip st m : get_meta_rec (strip st) m = get_meta_rec st m.
Proof. reflexivity. Qed.
Lemma active_strip st sc : active (strip st) sc = active st sc.
Proof. reflexivity. Qed.

Lemma CF_strip st : CF st -> CF (strip st).
Proof. intros H; destruct H; constructor; assumption. Qed.

Lemma INVL_CF X st L BL LS : INVL X st L BL LS -> CF st.
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  constructor.
  - exact (proj1 (ia_avail _ IA)).
  - intros HC. destruct (ia_avail _ IA) as [_ A2]. destruct (A2 HC) as (a & Ht & Eam & FREE).
    exists a. split; [exact Eam|]. split; [| exact FREE].
    pose proof (ia_tail _ IA a Ht) as Ha'. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| exfalso; apply Ha'; reflexivity].
    destruct (proj1 (ia_areas _ IA a ar Ea)) as (r & _ & _ & AL & _). exact AL.
  - intros b m ai Hb. pose proof (ig_ok _ _ _ IG m b ai Hb) as GO. split; [exact (g_present _ _ _ _ _ _ GO)|].
    destruct (im_hdr _ _ _ IM b _ Hb) as (m' & Em & Mm & _). cbn in Em. injection Em as <-. exact Mm.
  - intros b ai Hb. exact (ig_nometa _ _ _ IG b ai Hb).
  - intros sc m HA. pose proof (il_head _ _ IL (LActive sc)) as HH. cbn [get_head] in HH. rewrite HA in HH.
    destruct (LS (LActive sc)) as [|m' rest] eqn:EL; [discriminate|]. cbn in HH. injection HH as <-.
    destruct (il_active _ _ IL sc m ltac:(rewrite EL; left; reflexivity)) as (Hsc & (b & ai & Hb) & SC).
    pose proof (ig_ok _ _ _ IG m b ai Hb) as GO. split; [exact (g_present _ _ _ _ _ _ GO)|]. split; [exact Hsc|].
    exists b, ai. split; [exact Hb| exact SC].
  - intros m Hm. pose proof (il_head _ _ IL LFree) as HH. cbn [get_head] in HH. unfold ctx in HH. rewrite Hm in HH.
    destruct (LS LFree) as [|m' rest] eqn:EL; [discriminate|]. cbn in HH. injection HH as <-.
    assert (INm : In m (LS LFree)) by (rewrite EL; left; reflexivity).
    pose proof (il_free _ _ IL m INm) as FR.
    split.
    + intros ABS. pose proof (proj1 (proj1 (il_link _ _ IL m)) (ex_intro _ LFree INm)) as NX.
      unfold MR, get_meta_rec in FR. rewrite ABS in FR. cbn in FR.
      apply NX. unfold MR, get_meta_rec. rewrite ABS. reflexivity.
    + intros b h Hb Eg. destruct h as [gm ai]. cbn in Eg. subst gm.
      destruct (im_hdr _ _ _ IM b _ Hb) as (m' & Em & Mm & _). cbn in Em. injection Em as <-.
      unfold MR in FR. change (get_meta_rec st m) with (MR st m) in Mm. unfold MR in Mm. rewrite FR in Mm. cbn in Mm. discriminate.
  - intros sc m HA. exact (ia_active_keys _ IA sc m HA).
Qed.

Theorem sim_CF cs L : SIMREL cs L -> CF cs.
Proof.
  intros CR. destruct CR as (st & BL & LS & <- & INV & _). apply CF_strip. eapply INVL_CF. exact INV.
Qed.
Theorem creach_CF cs L : creach cs L -> CF cs.
Proof. intros CR. exact (sim_CF cs L (creach_sim cs L CR)). Qed.

End CEIL.
