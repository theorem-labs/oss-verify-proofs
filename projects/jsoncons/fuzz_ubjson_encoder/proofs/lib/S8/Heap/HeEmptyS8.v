(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMEMPTY.
Context {RUNp : RunP}.

Definition GEOM (r : meta) : optr * Z * Z * Z * Z := (m_mem r, m_last_idx r, m_freeable r, m_sizeclass r, m_maplen r).

Lemma GEOM_eq r r' : GEOM r' = GEOM r ->
  m_mem r' = m_mem r /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.
Proof. unfold GEOM. intros H. inversion H. repeat split; reflexivity. Qed.

Lemma GEOM_data r r' : data_of r' = data_of r -> GEOM r' = GEOM r.
Proof. intros H. apply data_of_eq in H as (E1 & _ & _ & E4 & E5 & E6 & E7). unfold GEOM. rewrite E1, E4, E5, E6, E7. reflexivity. Qed.

Lemma fmask_data r r' : data_of r' = data_of r -> fmask r' = fmask r.
Proof. intros H. apply data_of_eq in H as (_ & E2 & E3 & _). unfold fmask. rewrite E2, E3. reflexivity. Qed.

Lemma gempty_data st st' m : data_of (MR st' m) = data_of (MR st m) -> gempty st' m <-> gempty st m.
Proof.
  intros H. unfold gempty. rewrite (fmask_data _ _ H). apply data_of_eq in H as (_ & _ & _ & E4 & _). rewrite E4. tauto.
Qed.

Lemma otf_false st g : m_freeable (MR st g) = 1 -> okay_to_free st g = false ->
  m_sizeclass (MR st g) < 48 /\ m_maplen (MR st g) <> 0 /\ m_next (MR st g) = Some g /\ 7 <= m_sizeclass (MR st g) <= 38.
Proof.
  intros Hf H. unfold okay_to_free in H. fold (MR st g) in H. rewrite Hf in H. cbn [Z.eqb Pos.eqb] in H.
  destruct ((48 <=? m_sizeclass (MR st g)) || (get_stride (MR st g) <? UNIT * size_class (m_sizeclass (MR st g)))) eqn:C1; [discriminate|].
  apply Bool.orb_false_iff in C1 as [C1 _]. apply Z.leb_gt in C1.
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [C2|C2]; [discriminate|].
  destruct (optr_eqb_spec (m_next (MR st g)) (Some g)) as [C3|C3]; cbn [negb] in H; [|discriminate].
  destruct (is_bouncing (m_sizeclass (MR st g)) st) eqn:C4; cbn [negb] in H; [|discriminate].
  unfold is_bouncing, sc_in_seq_range in C4. apply Bool.andb_true_iff in C4 as [C4 _]. apply Bool.andb_true_iff in C4 as [C4a C4b].
  apply Z.leb_le in C4a. apply Z.ltb_lt in C4b. repeat split; auto; lia.
Qed.

Lemma lists_sole st LS h s : lists_ok st LS -> In s (LS h) -> m_next (MR st s) = Some s -> LS h = [s].
Proof.
  intros LO Hin Hn. apply in_split in Hin as (l1 & l2 & E).
  pose proof (lo_dll _ _ LO h) as D. rewrite E in D. apply dll_rot in D. cbn [app] in D.
  pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
  destruct (l2 ++ l1) as [|y r] eqn:Er.
  - apply app_eq_nil in Er as [-> ->]. exact E.
  - exfalso. cbn [dll app linked] in D. destruct D as (D1 & _). rewrite Hn in D1. injection D1 as <-.
    apply NoDup_app in ND as (_ & DISJ & ND2). apply NoDup_cons in ND2 as [N _].
    assert (Hy : In s (l2 ++ l1)) by (rewrite Er; left; reflexivity).
    apply in_app_iff in Hy as [Hy|Hy].
    + apply N. apply list_elem_of_In. exact Hy.
    + apply (DISJ s); apply list_elem_of_In; [exact Hy| left; reflexivity].
Qed.

Lemma fmask_set_freed_or r i : fmask (m_set_freed (Z.lor (m_freed r) (bit i)) r) = Z.lor (fmask r) (bit i).
Proof. unfold fmask, m_set_freed. cbn. rewrite Z.lor_assoc. reflexivity. Qed.

Lemma fmask_activate r act : m_avail r = 0 ->
  fmask (m_set_avail (Z.land (m_freed r) act) (m_set_freed (Z.ldiff (m_freed r) act) r)) = fmask r.
Proof.
  intros H. unfold fmask, m_set_avail, m_set_freed. cbn. rewrite H, Z.lor_0_l.
  apply Z.bits_inj'. intros j Hj. rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec.
  destruct (Z.testbit (m_freed r) j), (Z.testbit act j); reflexivity.
Qed.

Lemma GEOM_set_freed r v : GEOM (m_set_freed v r) = GEOM r. Proof. reflexivity. Qed.
Lemma GEOM_set_avail r v : GEOM (m_set_avail v r) = GEOM r. Proof. reflexivity. Qed.

Lemma EINV_after st0 st' L BL LS (K : aptr -> Prop) :
  INVC x0 st0 L BL LS -> EINV st0 ->
  (forall b m, hosts st' b m -> gempty st' m ->
      (hosts st0 b m /\ GEOM (MR st' m) = GEOM (MR st0 m))
      /\ (gempty st0 m \/ (K m /\ m_next (MR st0 m) = Some m /\ m_maplen (MR st0 m) <> 0 /\ 7 <= m_sizeclass (MR st0 m) <= 38))) ->
  (forall m1 m2, K m1 -> K m2 -> m1 = m2) ->
  EINV st'.
Proof.
  intros (IR & IA & IM & IL & IG & IS) E0 HST KU.
  assert (LO : lists_ok st0 LS).
  { destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. }

  assert (LISTED : forall b m, hosts st0 b m -> gempty st0 m -> In m (LS (LActive (m_sizeclass (MR st0 m))))).
  { intros b m Hb He. destruct (e_top _ E0 b m Hb He) as [_ Hsc].
    destruct Hb as [ai Hg]. pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO.
    destruct (m_next (MR st0 m)) as [nx|] eqn:Hnx.
    - assert (IN : in_list LS m) by (apply (proj2 (proj1 (il_link _ _ IL m))); rewrite Hnx; discriminate).
      destruct IN as [h Hh]. destruct h as [sc|].
      + pose proof (il_active _ _ IL sc m Hh) as (_ & _ & Esc). rewrite Esc. exact Hh.
      + exfalso. pose proof (il_free _ _ IL m Hh) as F. pose proof (im_hdr _ _ _ IM _ _ Hg) as (m' & Hm' & Hmem & _).
        cbn in Hm'. injection Hm' as <-. rewrite F in Hmem. discriminate.
    - assert (NL : ~ in_list LS m) by (intros IN; apply (proj1 (proj1 (il_link _ _ IL m)) IN); exact Hnx).
      exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) ltac:(lia) NL) as [Ha Hf].
      unfold gempty, fmask in He. rewrite Ha, Hf in He. cbn in He. pose proof (g_li _ _ _ _ _ _ GO) as LI.
      pose proof (testbit_mask_upto (m_last_idx (MR st0 m)) 0 ltac:(lia) ltac:(lia)) as T. rewrite <- He in T. rewrite Z.bits_0 in T.
      symmetry in T. apply Z.leb_gt in T. lia. }

  assert (SOLE : forall b m, hosts st0 b m -> m_next (MR st0 m) = Some m -> LS (LActive (m_sizeclass (MR st0 m))) = [m]).
  { intros b m Hb Hn. assert (IN : in_list LS m) by (apply (proj2 (proj1 (il_link _ _ IL m))); rewrite Hn; discriminate).
    destruct IN as [h Hh]. destruct h as [sc|].
    - pose proof (il_active _ _ IL sc m Hh) as (_ & _ & Esc). rewrite Esc. exact (lists_sole st0 LS _ m LO Hh Hn).
    - exfalso. pose proof (il_free _ _ IL m Hh) as F. destruct Hb as [ai Hg]. pose proof (im_hdr _ _ _ IM _ _ Hg) as (m' & Hm' & Hmem & _).
      cbn in Hm'. injection Hm' as <-. rewrite F in Hmem. discriminate. }
  constructor.
  - intros b1 m1 b2 m2 H1 H2 He1 He2 Esc.
    destruct (HST b1 m1 H1 He1) as ((H01 & G1) & C1). destruct (HST b2 m2 H2 He2) as ((H02 & G2) & C2).
    apply GEOM_eq in G1 as (_ & _ & _ & S1 & _). apply GEOM_eq in G2 as (_ & _ & _ & S2 & _).
    assert (Esc0 : m_sizeclass (MR st0 m1) = m_sizeclass (MR st0 m2)) by congruence.
    assert (SAME : m1 = m2 -> b1 = b2) by (intros <-; eapply hosts_inj; [exact IM| exact H01| exact H02]).
    destruct C1 as [C1|(K1 & N1 & _)]; destruct C2 as [C2|(K2 & N2 & _)].
    + exact (e_uniq _ E0 b1 m1 b2 m2 H01 H02 C1 C2 Esc0).
    + apply SAME. pose proof (LISTED b1 m1 H01 C1) as L1. rewrite Esc0, (SOLE b2 m2 H02 N2) in L1. destruct L1 as [->|[]]. reflexivity.
    + apply SAME. pose proof (LISTED b2 m2 H02 C2) as L2. rewrite <- Esc0, (SOLE b1 m1 H01 N1) in L2. destruct L2 as [->|[]]. reflexivity.
    + apply SAME. exact (KU m1 m2 K1 K2).
  - intros b m H He. destruct (HST b m H He) as ((H0 & G) & C). apply GEOM_eq in G as (_ & _ & _ & S & ML). rewrite S, ML.
    destruct C as [C|(_ & _ & Hml & Hsc)]; [exact (e_top _ E0 b m H0 C)| split; assumption].
Qed.

End HMEMPTY.
