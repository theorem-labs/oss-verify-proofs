(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_Pres2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Definition inT (rid : N) (lo hi : Z) (q : aptr) : Prop := fst q = rid /\ lo <= snd q < hi.

Section WRITE_T.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo hi q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Local Notation R := (MR st).

#[using="RD"] Lemma known_out q v : ~ inT (fst bm) lo hi q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
#[using="RD"] Lemma unknown_out q : ~ inT (fst bm) lo hi q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.

#[using="st' TK"] Lemma not_inT_lo q : snd q < lo -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [H1 _]]. lia. Qed.
#[using="st' TK"] Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. lia. Qed.
#[using="Type"] Lemma not_inT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo hi q.
Proof. intros H [H1 _]. exact (H H1). Qed.

#[using="X st LS IM IG IS ISH m bm i Hm Hi NH NB lo hi CE TK RD DOM TKS"] Theorem inv_SH_write_T : inv_SH st' BL.
Proof.
  pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
  - intros rid sh H. rewrite HR. eapply DOM. exact H.
  - intros rid sh H. rewrite TK. eapply TKS. exact H.
  - (* [comment removed for export] *)
    intros b2 m2 i2 Hb2 Hi2. apply HE in Hb2. rewrite ME in Hi2 |- *.
    apply known_out; [| exact (D3 b2 m2 i2 Hb2 Hi2)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    unfold cnt_of in Hi2.
    destruct (aptr_eq_dec m2 m) as [Em|NEm]; [destruct (Z.eq_dec i2 i) as [Ei|NEi]|].
    + subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_intror NEi)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_introl NEm)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 o Hb2 Ho. apply HE in Hb2. apply unknown_out; [| exact (D4 b2 m2 o Hb2 Ho)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 Hb2 Ef) as [A|A];
      [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 p2 i2 Hb2 Hml Hs. apply HE in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp2 Hp2] & Hi2 & Eb2).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp2) in Eb2.
    assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo hi (fst b2, snd b2 - d)).
    { intros d Hd. subst b2. cbn [fst snd].
      destruct (N.eq_dec (fst bp2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      assert (NE : p2 <> m \/ i2 <> i).
      { destruct (aptr_eq_dec p2 m) as [->|]; [right| left; assumption]. intros ->.
        pose proof (hosts_inj _ _ _ IM _ _ _ Hp2 Hm). subst bp2. destruct Hb2 as [ai2 Hb2]. rewrite Hb2 in NH. discriminate. }
      destruct (sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH p2 bp2 i2 Hp2 Ef Hi2 NE) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    split; [exists v3; split; [apply known_out; [apply (OUT 3); lia| exact K3]| auto]|].
    split; [apply known_out; [apply (OUT 2); lia| exact K2]|].
    split; [apply known_out; [apply (OUT 1); lia| exact K1]| exact Q].
  - (* [comment removed for export] *)
    intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
    destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
    pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
    assert (NH2 : s_groups st !! (fst b2, sstart (R m2) i2) = None).
    { destruct Hb2 as [ai2 Hb2']. pose proof (is_part _ _ _ IS _ _ _ _ Hb2' Hi2) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai2 Hb2')) in P.
      unfold one5 in P. destruct (s_groups st !! (fst b2, sstart (R m2) i2)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst b2, sstart (R m2) i2) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst b2, sstart (R m2) i2) <> None) by congruence. tauto. }
    assert (NE : m2 <> m \/ i2 <> i).
    { destruct (aptr_eq_dec m2 m) as [->|]; [right| left; assumption]. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2. exact (NB k Hk Ek). }
    assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo hi (fst (bslot k), o)).
    { intros o Ho. rewrite Ek. cbn [fst].
      destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 NE NH2) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
    rewrite sstart_succ in OUT. unfold UNIT, IB in *.
    split; [apply known_out; [apply OUT; lia| exact A1]|].
    split; [apply known_out; [apply OUT; lia| exact A2]|].
    split; [apply known_out; [apply OUT; lia| exact A3]|].
    split; [apply known_out; [apply OUT; lia| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
      repeat split; try (apply known_out; [apply OUT; lia| assumption]). exact B6.
    + split; [intros Hr; apply known_out; [apply OUT; lia| apply A7; exact Hr]|].
      intros a Ha. apply unknown_out; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
#[using="Type"] Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
#[using="Type"] Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
#[using="Type"] Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
  intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
  intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
  exists l1 l2, BL = l1 ++ k :: l2 /\ bl_remove (bslot k) BL = l1 ++ l2 /\ ~ In (bslot k) (map bslot l1) /\ ~ In (bslot k) (map bslot l2).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn in ND. apply NoDup_cons in ND as [N1 N2].
  destruct Hin as [<-|Hin].
  - exists [], BL. cbn. rewrite aptr_eqb_refl. repeat split; auto. intros H. apply N1. apply list_elem_of_In. exact H.
  - destruct (IH N2 Hin) as (l1 & l2 & E1 & E2 & M1 & M2).
    assert (NE : bslot b <> bslot k).
    { intros E. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin. }
    exists (b :: l1), l2. cbn. rewrite (aptr_eqb_neq (bslot b) (bslot k)) by exact NE. rewrite E1, E2 at 1. rewrite <- E1.
    repeat split; auto. cbn. intros [H|H]; [exact (NE H)| exact (M1 H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMOVE_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Let X' := mkX (x_idle X) (x_zomb X) (Some (bslot k)) (x_orph X) (x_fresh X).
Let BL' := bl_remove (bslot k) BL.
(* [comment removed for export] *)
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! (bslot k) = Some (m, i) ->
  forall q, ~ inT (fst (bslot k)) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

#[using="st INV Hk NP CE TK RD DOM TKS"] Theorem INVL_remove_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  assert (SUB : forall k', In k' BL' -> In k' BL /\ bslot k' <> bslot k).
  { intros k' H. subst BL'. rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
    - apply in_app_iff. cbn. tauto.
    - intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H. }
  (* [comment removed for export] *)
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite NP in P.
      assert (MEMk : In (slot_start' (MR st m2) i2) (map bslot BL) <->
                     In (slot_start' (MR st m2) i2) (map bslot BL') \/ slot_start' (MR st m2) i2 = bslot k).
      { subst BL'. rewrite EBL' , EBL. rewrite !map_app. cbn. rewrite !in_app_iff. cbn. intuition congruence. }
      assert (NOTk : In (slot_start' (MR st m2) i2) (map bslot BL') -> slot_start' (MR st m2) i2 <> bslot k).
      { intros H E. subst BL'. rewrite EBL' in H. rewrite map_app, in_app_iff in H. rewrite E in H. tauto. }
      unfold one5 in P |- *.
      assert (D : @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2)) <-> slot_start' (MR st m2) i2 = bslot k) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (U' := In (slot_start' (MR st m2) i2) (map bslot BL')) in *.
      set (E := slot_start' (MR st m2) i2 = bslot k) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := None = Some (slot_start' (MR st m2) i2)) in *.
      fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. first [ solve [ clear - P D N5 NOTk; tauto ] | tauto ].   (* [comment removed for export] *)
    - intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
    - subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
      apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
      apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
    - intros k' Hk'. apply S6. apply SUB. exact Hk'. }
  assert (ISH' : inv_SH st' BL').
  { eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try eassumption.
    - apply (inv_SH_incl st BL). { intros k' H. apply SUB. exact H. } exact ISH.
    - (* [comment removed for export] *)
      destruct Hm as [ai Hm']. pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')) in P. unfold one5 in P.
      destruct (s_groups st !! (fst bm, sstart (MR st m) i)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst bm, sstart (MR st m) i) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst bm, sstart (MR st m) i) <> None) by congruence. tauto.
    - intros k' Hk' E. destruct (SUB k' Hk') as [_ NE]. apply NE. rewrite E, Ek. reflexivity.
    - intros q Hq. apply (RD m i Hs). rewrite Ek. exact Hq. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.

#[using="CEc X st L LS INV Hk"] Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  subst BL'. rewrite EBL', EBL. rewrite !in_app_iff. cbn. split.
  - intros H. split; [tauto|]. intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
  - intros [[H|[<-|H]] NE]; [tauto| congruence| tauto].
Qed.
End REMOVE_BLOCK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk_shadow_ok (st : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
  let rid := fst (bslot k) in
  let p := snd (bslot k) + UNIT * boff k in
  let e := snd (bslot k) + get_stride (MR st m) - IB in
  let res := e - p - bsize k in
  let q := (p - snd (gbase (MR st m)) - UNIT) / UNIT in
  known st (rid, p - 4) 0
  /\ known st (rid, p - 3) (i + 32 * Z.min res 5)
  /\ known st (rid, p - 2) (byte_of q 0) /\ known st (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
  /\ (5 <= res -> known st (rid, e - 4) (byte_of res 0) /\ known st (rid, e - 3) (byte_of res 1)
                /\ known st (rid, e - 2) (byte_of res 2) /\ known st (rid, e - 1) (byte_of res 3)
                /\ known st (rid, e - 5) 0 /\ res < 2^32)
  /\ (0 < res -> known st (rid, e - res) 0)
  /\ (forall a, p <= a < p + bsize k -> unknown st (rid, a)).

#[using="Type"] Lemma inv_SH_cons st BL k m i :
  inv_SH st BL -> s_slots st !! (bslot k) = Some (m, i) -> blk_shadow_ok st k m i -> inv_SH st (k :: BL).
Proof.
  intros I Hs Hk. destruct I; constructor; try assumption.
  intros k' m' i' [<-|Hk'] Hs'.
  - rewrite Hs in Hs'. inversion Hs'. subst. exact Hk.
  - apply ish_blk; assumption.
Qed.

Section ADD_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
  forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
  0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

#[using="st INV HP CE TK RD DOM TKS BLK"] Theorem INVL_add_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).
  (* [comment removed for export] *)
  destruct Hm as [ai Hm'].
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
  assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
  assert (NH : s_groups st !! c = None).
  { destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite HP in P. subst BL'.
      assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
      unfold one5 in P |- *. rewrite EQm.
      assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      assert (NU' : c = slot_start' (MR st m2) i2 -> ~ In (slot_start' (MR st m2) i2) (map bslot BL)) by (intros <-; exact NU).
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (E := c = slot_start' (MR st m2) i2) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := @eq (option aptr) None (Some (slot_start' (MR st m2) i2))) in *.
      clearbody U E A F Hh P5 Q5. first [ solve [ clear - P D N5 NU'; tauto ] | tauto ].   (* [comment removed for export] *)
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_T X st st' BL LS IM IG IS); try eassumption.
      + exists ai. exact Hm'.
      + rewrite <- Ek. exact NH.
      + intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
      + intros q Hq. apply (RD m i eq_refl). rewrite Ek. exact Hq.
    - rewrite (ce_slots _ _ CE). exact Hs.
    - exact SHK. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.
End ADD_BLOCK.

End WithCeil.
End MI_Pres2.

(* [comment removed for export] *)
Module MI_Pres2T.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Section WRITE_TT.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
(* [comment removed for export] *)
Hypothesis TOP : m_maplen (MR st m) <> 0.
Hypothesis LAST : i = m_last_idx (MR st m).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo (hi + 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
(* [comment removed for export] *)
Hypothesis HE : cell_read (get_shadow st' (fst bm)) hi = cell_read (get_shadow st (fst bm)) hi.
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Local Notation R := (MR st).

#[using="RD"] Lemma known_outT q v : ~ inT (fst bm) lo (hi + 4) q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
#[using="RD"] Lemma unknown_outT q : ~ inT (fst bm) lo (hi + 4) q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.
#[using="HE"] Lemma known_hiT v : known st (fst bm, hi) v -> known st' (fst bm, hi) v.
Proof. intros K. unfold known, SHd in *. cbn [fst snd] in *. rewrite HE. exact K. Qed.

#[using="st' TK"] Lemma notT_lo q : snd q < lo -> ~ inT (fst bm) lo (hi + 4) q.
Proof. intros H [_ [H1 _]]. lia. Qed.
#[using="Type"] Lemma notT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo (hi + 4) q.
Proof. intros H [H1 _]. exact (H H1). Qed.

(* [comment removed for export] *)
#[using="X st' BL LS IM IG IS Hm NH TOP LAST lo hi TK"] Lemma sep_top m2 b2 : hosts st b2 m2 -> fst b2 = fst bm -> m2 <> m -> gend (R m2) <= sstart (R m) i.
Proof.
  intros H2 Hf NE.
  destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
  - destruct (top_chain _ _ _ _ IM IG IS m2 b2 H2 M2) as (t & j & c & bt & Ha & Ht & Mt & Hft).
    assert (Et : t = m) by (apply (top_unique _ _ _ IG t m bt bm Ht Hm Mt TOP); congruence). subst t.
    pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hm). subst bt.
    destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (bm2 & bp & Hm2 & Hp & _ & Hj & _).
    destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ _ _ IM IG IS m bm i Hm NH m2 c Ha)|].
    destruct (anc_box _ _ _ _ IM IG IS m2 m j c b2 Ha H2) as (_ & GE & _).
    pose proof (sstart_mono _ _ _ IG bm m (j + 1) i Hm ltac:(lia)). lia.
  - exfalso. apply NE. apply (top_unique _ _ _ IG m2 m b2 bm H2 Hm M2 TOP). exact Hf.
Qed.

#[using="X st LS IM IG IS ISH m bm i Hm Hi NH NB TOP LAST lo hi CE TK RD HE DOM TKS"] Theorem inv_SH_write_TT : inv_SH st' BL.
Proof.
  pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HEx.
  pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (last_idx_nonneg _ _ _ IG _ _ Hm) as L0.
  pose proof (top_at0 _ _ _ IG _ _ Hm TOP) as B0.
  destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
  - intros rid sh H. rewrite HR. eapply DOM. exact H.
  - intros rid sh H. rewrite TK. eapply TKS. exact H.
  - (* [comment removed for export] *)
    intros b2 m2 i2 Hb2 Hi2. apply HEx in Hb2. rewrite ME in Hi2 |- *.
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply known_outT; [apply notT_rid; exact Nf| exact (D3 b2 m2 i2 Hb2 Hi2)]].
    unfold cnt_of in Hi2.
    destruct (aptr_eq_dec m2 m) as [Em|NEm].
    + subst m2. pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2.
      destruct (Z.eq_dec i2 (i + 1)) as [->|Ni].
      * (* [comment removed for export] *) pose proof (D3 bm m (i + 1) Hm Hi2) as K. unfold IB in K |- *. fold hi in K |- *.
        apply known_hiT. exact K.
      * apply known_outT; [| exact (D3 bm m i2 Hm Hi2)]. apply notT_lo. cbn [snd]. unfold lo.
        pose proof (sstart_mono _ _ _ IG bm m i2 i Hm ltac:(lia)). unfold IB. lia.
    + apply known_outT; [| exact (D3 b2 m2 i2 Hb2 Hi2)]. apply notT_lo. cbn [snd]. unfold lo.
      pose proof (sep_top m2 b2 Hb2 Ef NEm) as GE. rewrite gend_eq in GE.
      pose proof (sstart_mono _ _ _ IG b2 m2 i2 (m_last_idx (R m2) + 1) Hb2 ltac:(lia)). unfold IB. lia.
  - (* [comment removed for export] *)
    intros b2 m2 o Hb2 Ho. apply HEx in Hb2. apply unknown_outT; [| exact (D4 b2 m2 o Hb2 Ho)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply notT_rid; exact Nf].
    apply notT_lo. cbn [snd]. unfold lo.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    + pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2.
      pose proof (sstart_mono _ _ _ IG bm m 0 i Hm ltac:(lia)). unfold UNIT in S0. lia.
    + pose proof (sep_top m2 b2 Hb2 Ef NEm) as GE. pose proof (gend_ge _ _ _ IM IG b2 m2 Hb2). lia.
  - (* [comment removed for export] *)
    intros b2 m2 p2 i2 Hb2 Hml Hs. apply HEx in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo (hi + 4) (fst b2, snd b2 - d)).
    { intros d Hd. destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply notT_rid; exact Nf].
      apply notT_lo. cbn [snd]. unfold lo.
      assert (NEm : m2 <> m) by (intros ->; rewrite Hml in TOP; exact (TOP eq_refl)).
      pose proof (sep_top m2 b2 Hb2 Ef NEm) as GE. pose proof (gend_ge _ _ _ IM IG b2 m2 Hb2). lia. }
    split; [exists v3; split; [apply known_outT; [apply (OUT 3); lia| exact K3]| auto]|].
    split; [apply known_outT; [apply (OUT 2); lia| exact K2]|].
    split; [apply known_outT; [apply (OUT 1); lia| exact K1]| exact Q].
  - (* [comment removed for export] *)
    intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
    pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
    destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
    assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo (hi + 4) (fst (bslot k), o)).
    { intros o Ho. rewrite Ek. cbn [fst].
      destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply notT_rid; exact Nf].
      apply notT_lo. cbn [snd]. unfold lo.
      destruct (aptr_eq_dec m2 m) as [->|NEm].
      - pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2.
        assert (Ni : i2 <> i) by (intros ->; exact (NB k Hk Ek)).
        pose proof (sstart_mono _ _ _ IG bm m (i2 + 1) i Hm ltac:(lia)). lia.
      - pose proof (sep_top m2 b2 Hb2 Ef NEm) as GE. rewrite gend_eq in GE.
        pose proof (sstart_mono _ _ _ IG b2 m2 (i2 + 1) (m_last_idx (R m2) + 1) Hb2 ltac:(lia)). lia. }
    assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
    rewrite sstart_succ in OUT. unfold UNIT, IB in *.
    split; [apply known_outT; [apply OUT; lia| exact A1]|].
    split; [apply known_outT; [apply OUT; lia| exact A2]|].
    split; [apply known_outT; [apply OUT; lia| exact A3]|].
    split; [apply known_outT; [apply OUT; lia| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
      repeat split; try (apply known_outT; [apply OUT; lia| assumption]). exact B6.
    + split; [intros Hr; apply known_outT; [apply OUT; lia| apply A7; exact Hr]|].
      intros a Ha. apply unknown_outT; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_TT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ADD_BLOCK_T.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis TOPc : forall m i, s_slots st !! c = Some (m, i) -> m_maplen (MR st m) <> 0 /\ i = m_last_idx (MR st m).
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
  forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1)) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis HE : forall m i, s_slots st !! c = Some (m, i) ->
  cell_read (get_shadow st' (fst c)) (sstart (MR st m) (i + 1) - 4) = cell_read (get_shadow st (fst c)) (sstart (MR st m) (i + 1) - 4).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
  0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

#[using="st INV HP CE TK TOPc RD HE DOM TKS BLK"] Theorem INVL_add_block_tail : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).
  destruct (TOPc m i eq_refl) as [TOP LAST].
  destruct Hm as [ai Hm'].
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
  assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
  assert (NH : s_groups st !! c = None).
  { destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite HP in P. subst BL'.
      assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
      unfold one5 in P |- *. rewrite EQm.
      assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      set (E := c = slot_start' (MR st m2) i2) in *. set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := @None aptr = Some (slot_start' (MR st m2) i2)) in *.
      fold P5 in P. fold Q5. clearbody E U A F Hh P5 Q5. first [ solve [ clear - P D N5; tauto ] | tauto ].   (* [comment removed for export] *)
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros Hin. apply NU. apply list_elem_of_In. exact Hin.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_TT X st st' BL LS IM IG IS); try eassumption.
      + exists ai. exact Hm'.
      + rewrite <- Ek. exact NH.
      + intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
      + intros q Hq. apply (RD m i eq_refl). rewrite Ek. cbn [fst]. intros [H1 H2]. apply Hq. split; [exact H1| lia].
      + pose proof (HE m i eq_refl) as HE'. rewrite Ek in HE'. cbn [fst] in HE'. exact HE'.
    - rewrite (ce_slots _ _ CE). exact Hs.
    - exact SHK. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.
End ADD_BLOCK_T.

End WithCeil.
End MI_Pres2T.

(* [comment removed for export] *)
Module MI_Pres3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
  cs_secret : c_secret c' = c_secret c;
  cs_init : c_init_done c' = c_init_done c;
  cs_fmh : c_free_meta_head c' = c_free_meta_head c;
  cs_am : c_avail_meta c' = c_avail_meta c;
  cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cs_mah : c_meta_area_head c' = c_meta_area_head c;
  cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cs_active : c_active c' = c_active c;
  cs_usage : c_usage c' = c_usage c;
  cs_brk : c_brk c' = c_brk c;
  (* [comment removed for export] *)
  cs_mc : 0 <= c_mmap_counter c' < 2^32;
  cs_seq : 0 <= c_seq c' < 256;
  cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
  cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.

#[using="INV CS"] Theorem INVL_ctx_scalars : INVL X st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
  assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
  assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
    + intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
  - destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
    + split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
    + intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.

#[using="Type"] Lemma ctx_scalars_refl c :
  0 <= c_mmap_counter c < 2^32 -> 0 <= c_seq c < 256 ->
  (forall i v, c_bounces c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  (forall i v, c_unmap_seq c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  ctx_scalars_eq c c.
Proof. intros; constructor; auto. Qed.

#[using="Type"] Lemma ia_ctx_facts st : inv_A st ->
  0 <= c_mmap_counter (s_ctx st) < 2^32 /\ 0 <= c_seq (s_ctx st) < 256
  /\ (forall i v, c_bounces (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
  /\ (forall i v, c_unmap_seq (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256).
Proof. intros IA. exact (ia_ctx _ IA). Qed.

#[using="Type"] Lemma INVL_step_seq X st L BL LS : INVL X st L BL LS -> INVL X (step_seq st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
  - intros i v H. rewrite lookup_empty in H. discriminate.
  - unfold ctx in NE. lia.
Qed.

#[using="Type"] Lemma INVL_record_seq X st L BL LS sc : INVL X st L BL LS -> INVL X (record_seq sc st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C4.
Qed.

#[using="Type"] Lemma INVL_set_bounce X st L BL LS i v : INVL X st L BL LS -> 0 <= i < 32 -> 0 <= v < 256 -> INVL X (set_bounce i v st) L BL LS.
Proof.
  intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  intros j w. destruct (Z.eq_dec j i) as [->|NE].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C3.
Qed.

#[using="Type"] Lemma bounces_range st i : inv_A st -> 0 <= bounces st i < 256.
Proof.
  intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
  destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.

#[using="Type"] Lemma INVL_account_bounce X st L BL LS sc : INVL X st L BL LS -> INVL X (account_bounce sc st) L BL LS.
Proof.
  intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (negb _ && _); [| exact INV].
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.

#[using="Type"] Lemma INVL_decay_bounces X st L BL LS sc : INVL X st L BL LS -> INVL X (decay_bounces sc st) L BL LS.
Proof.
  intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
  apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  apply INVL_set_bounce; auto; lia.
Qed.

#[using="Type"] Lemma INVL_mmap_counter X st L BL LS : INVL X st L BL LS ->
  INVL X (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).

#[using="Type"] Lemma in_rem x g l : In x (rem g l) <-> In x l /\ x <> g.
Proof. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma present_of_mem st m b : m_mem (MR st m) = Some b -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
#[using="Type"] Lemma present_of_next st m x : m_next (MR st m) = Some x -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.

#[using="Type"] Lemma gcnt_ext_groups st st' :
  s_groups st' = s_groups st ->
  (forall b h m, s_groups st !! b = Some h -> g_meta h = Some m ->
     m_sizeclass (MR st' m) = m_sizeclass (MR st m) /\ cnt_of (MR st' m) = cnt_of (MR st m)) ->
  forall sc, gcnt st' sc = gcnt st sc.
Proof.
  intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
  destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.

#[using="Type"] Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
#[using="Type"] Lemma uz_R_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.

#[using="INV Hz"] Theorem INVL_unzombie : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_zomb _ _ _ IM g Hz) as (NIg & Ng & Pg & bg & Mg & NGg).
  assert (NLg : forall b, ~ hosts st b g).
  { intros b [ai Hb]. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hm & _). cbn in Em. inversion Em. subst m. rewrite Mg in Hm. inversion Hm. subst. rewrite Hb in NGg. discriminate. }
  assert (RG : forall b m, hosts st b m -> MR st' m = MR st m).
  { intros b m Hm. apply uz_R_other. intros ->. exact (NLg b Hm). }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
  { intros x. unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
    split; [intros _; exact (present_of_mem st g bg Mg)| intros _; discriminate]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_X X); [reflexivity|]. destruct IR; constructor; try assumption.
  - destruct IA; constructor; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
      intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
      rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
    + intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
      destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
    + intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
      assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
      rewrite (uz_R_other m NE). auto.
    + intros m Hm. cbn in Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
    + intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
      rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite uz_R_other; try reflexivity; intros ->; apply NIg; exists h; rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros m. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite uz_R, aptr_eqb_refl. cbn. split; [| reflexivity]. split; [intros H; exfalso; exact (NIg H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (uz_R_other m NE). apply L5.
    + intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists LFree; exact Hm|]. rewrite (uz_R_other m NE). apply L6. exact Hm.
    + intros sc m Hm. destruct (L7 sc m Hm) as (A1 & A2 & A3).
      destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists (LActive sc); exact Hm|]. rewrite (uz_R_other m NE). auto.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    + intros m b ai Hb. pose proof (G1 m b ai Hb) as GO.
      assert (NE : m <> g) by (intros ->; exact (NLg b (ex_intro _ ai Hb))).
      destruct GO; constructor; rewrite ?(uz_R_other m NE); try assumption.
      * apply KEYS. exact g_present.
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hst).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _).
        assert (NEp : p <> g) by (intros ->; exact (NLg bp Hp)).
        exists p, i. rewrite (uz_R_other p NEp). auto 10.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2.
      rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
      rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (RG _ _ Hm). auto.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
    + intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
    + intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
      destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
    + intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
    + intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.

End WithCeil.
End MI_Pres3.

(* [comment removed for export] *)
Module MI_WFree.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma guard_true {R} tag (c : bool) (k bail : M R) : c = true -> guard tag c k bail = k.
Proof. intros ->. reflexivity. Qed.

#[using="Type"] Lemma size_class_28 sc : 28 <= sc < 48 -> 292 <= size_class sc.
Proof.
  intros H. unfold size_class.
  assert (E : exists n, Z.to_nat sc = (28 + n)%nat /\ (n < 20)%nat) by (exists (Z.to_nat sc - 28)%nat; lia).
  destruct E as (n & -> & Hn).
  do 20 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma guard16_arith S stride i off n q last :
  1 <= S -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off <= 255 -> 0 <= i <= last ->
  (stride = 16 * S \/ last = 0) -> (stride <= 16 * S \/ 292 <= S) ->
  S * i <= q < S * (i + 1).
Proof.
  intros HS Hq Hfit Hn Hoff Hi A B.
  destruct A as [E|L0].
  - subst stride. assert (q = S * i + off) by lia. subst q. nia.
  - assert (i = 0) by lia. subst i. assert (q = off) by lia. subst q. lia.
Qed.

#[using="Type"] Lemma guard17_arith stride i off n q last maplen :
  16 <= stride -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off -> 0 <= i <= last ->
  16 + stride * (last + 1) <= maplen * 4096 ->
  q <= maplen * 4096 / 16 - 1.
Proof.
  intros. replace (maplen * 4096 / 16) with (maplen * 256) by (rewrite <- (Z.div_mul (maplen * 256) 16) by lia; f_equal; lia).
  assert (stride * i + stride <= stride * (last + 1)) by nia. lia.
Qed.

(* [comment removed for export] *)
Section BLOCK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (c : cptr) (off n : Z).
Hypothesis Hk : In ((c, off), n) BL.

Local Notation R := (MR st).

Record blk_facts (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) : Prop := mkBF {
  bf_slot : s_slots st !! c = Some (m, i);
  bf_hosts : s_groups st !! bm = Some (mkGhdr (Some m) ai);
  bf_mem : m_mem (R m) = Some bm;
  bf_c : c = (fst bm, sstart (R m) i);
  bf_i : 0 <= i <= m_last_idx (R m);
  bf_li : m_last_idx (R m) <= 31;
  bf_ai : 0 <= ai <= m_last_idx (R m);
  bf_off : 0 <= off <= 255;
  bf_n : 0 <= n;
  bf_fit : UNIT * off + n <= get_stride (R m) - IB;
  bf_stride : UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0;
  bf_b16 : 0 <= snd bm /\ snd bm mod UNIT = 0;
  bf_notA : tbit (m_avail (R m)) i = false;
  bf_notF : tbit (m_freed (R m)) i = false;
  bf_notH : s_groups st !! c = None;
  bf_sc : (0 <= m_sizeclass (R m) < 48 /\ (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
            /\ (get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) \/ (m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0)))
          \/ m_sizeclass (R m) = 63;
  bf_top : m_maplen (R m) <> 0 -> snd bm = 0 /\ gend (R m) <= m_maplen (R m) * 4096;
  bf_maplen : 0 <= m_maplen (R m);
  bf_area : s_areas st !! a = Some ar /\ a_check ar = c_secret (s_ctx st) /\ snd a mod PGSZ = 0 /\ 0 <= ka < NSLOTS /\ m = mslot a ka;
  bf_shadow : blk_shadow_ok st ((c, off), n) m i;
  bf_hdr0 : known st (fst bm, sstart (R m) (i + 1) - IB) 0;
  bf_bytes : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256
}.

#[using="CE X L BL LS INV Hk"] Lemma block_facts : exists m bm i ai a ar ka, blk_facts m bm i ai a ar ka.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Hoff & Hn & Hfit). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec).
  pose proof Hm as [ai Hm'].
  pose proof (ig_ok _ _ _ IG _ _ _ Hm') as GO.
  pose proof (hosts_mem _ _ _ IM _ _ Hm) as Hmem.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
  pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! m) as [mr|] eqn:Em; [| congruence].
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
  exists m, bm, i, ai, a, ar, ka.
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec in P.
  assert (U : In c (map bslot BL)) by (change c with (bslot ((c, off), n)); apply in_map; exact Hk).
  unfold one5 in P.
  constructor; auto.
  - pose proof (g_li _ _ _ _ _ _ GO). lia.
  - exact (g_ai _ _ _ _ _ _ GO).
  - exact (stride_ge _ _ _ IG _ _ Hm).
  - exact (g_align _ _ _ _ _ _ GO).
  - destruct (tbit (m_avail (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (tbit (m_freed (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. tauto.
  - destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc Hml]|(Hsc & Hli & Hml & _)]; [left| right; exact Hsc].
    destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
    split; [exact Hsc|]. split; [exact S1|].
    unfold get_stride. destruct (m_last_idx (R m) =? 0) eqn:E0; destruct (m_maplen (R m) =? 0) eqn:EM; cbn [andb negb];
      first [left; reflexivity | right; split; [apply Z.eqb_eq; exact E0| apply Z.eqb_neq; exact EM]].
  - intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r' & _ & _ & _ & Hge). auto.
  - exact (g_maplen _ _ _ _ _ _ GO).
  - exact (ish_blk _ _ ISH _ m i Hk Hs).
  - apply (ish_hdr0 _ _ ISH _ _ _ Hm). unfold cnt_of. lia.
  - intros q v Hq. eapply known_byte; [| exact Hq]. intros sh o' v' t Hsh Hc. exact (proj1 (proj1 (ish_ticks _ _ ISH _ _ Hsh) o' v' t Hc)).
Qed.
End BLOCK.

Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let e : Z := snd c + stride - IB.
Let res : Z := e - snd p - n.
Let q : Z := (snd p - snd bm - UNIT) / UNIT.

#[using="n bm ai a ar ka BF"] Lemma p_snd : snd p = sstart (R m) i + UNIT * off.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="st n m i ai a ar ka BF"] Lemma p_fst : fst p = fst bm.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="c off n i ai a ar ka BF"] Lemma gbase_bm : gbase (R m) = bm.
Proof. unfold gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
#[using="off n bm ai a ar ka BF"] Lemma c_snd : snd c = sstart (R m) i.
Proof. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.

#[using="n ai a ar ka BF e res"] Lemma q16 : UNIT * q = stride * i + UNIT * off /\ 0 <= q < 2^16.
Proof.
  destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (_ & _ & _ & _ & Q & _). cbn [bslot boff fst snd] in Q.
  rewrite gbase_bm in Q. subst q p. cbn [snd aadd] in *. rewrite c_snd in *. unfold sstart in *. rewrite gbase_bm in *.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. subst stride.
  replace (snd bm + UNIT + get_stride (R m) * i + UNIT * off - snd bm - UNIT) with (get_stride (R m) * i + UNIT * off) in Q |- * by lia.
  split; [| exact Q].
  unfold UNIT in *. pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). rewrite S2 in H.
  replace (get_stride (R m) * i + 16 * off) with ((get_stride (R m) / 16 * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

Let SH := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.

#[using="st n m bm i ai a ar ka BF stride e res q"] Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  rewrite p_snd. unfold sstart. rewrite gbase_bm.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. destruct (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2]. unfold UNIT in *.
  pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + get_stride (R m) * i + 16 * off) with ((snd bm / 16 + 1 + get_stride (R m) / 16 * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed.

#[using="bm i ai a ar ka BF q"] Lemma res_nonneg : 0 <= res.
Proof.
  subst res e p stride. cbn [snd aadd]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. lia.
Qed.

#[using="n ai a ar ka BF stride e res SH"] Lemma get_meta_eq {T} (k : aptr -> Z -> Z -> M T) bail : get_meta st p k bail = k m q i.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  unfold get_meta.
  rewrite (guard_true 10) by (apply Z.eqb_eq; exact p_mod16).
  unfold rd16.
  rewrite (rd8_known st (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-4)) 0) by (eapply known_at; [exact K4| cbn; lia| reflexivity]).
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bm).
  { pose proof q16 as [Q1 _]. pose proof p_snd as PS. pose proof p_fst as PF. unfold sstart in PS. rewrite gbase_bm in PS.
    subst stride. unfold aadd. destruct bm as [br bo]. cbn [fst snd] in *. f_equal; [exact PF| lia]. }
  rewrite Ebase. unfold get_group. rewrite (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). cbn [g_meta].
  rewrite (land31_idx i (Z.min res 5)) by lia. fold (MR st m).
  rewrite (guard_true 11) by (rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  rewrite (guard_true 13) by (unfold testbit; rewrite (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  rewrite (guard_true 14) by (unfold testbit; rewrite (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  rewrite (guard_true 15) by (rewrite Em, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; exact Hck).
  pose proof q16 as [Q1 _]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. fold stride in FIT.
  unfold UNIT, IB in Q1, FIT. fold stride in FIT.
  rewrite (guard_true 16).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
      - fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
        pose proof (size_class_bound _ Hsc) as SB.
        assert (A : stride = 16 * size_class (m_sizeclass (R m)) \/ m_last_idx (R m) = 0) by tauto.
        assert (B : stride <= 16 * size_class (m_sizeclass (R m)) \/ 292 <= size_class (m_sizeclass (R m))).
        { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
        clearbody p stride e res q. clear SH Hle Hst.
        pose proof (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B) as [G1 G2].
        destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [|lia].
        apply Bool.andb_true_iff. split; [apply Z.leb_le; exact G1| apply Z.ltb_lt; exact G2].
      - clearbody p stride e res q. clear SH. destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [lia|]. apply Z.eqb_eq. exact E63. }
  rewrite (guard_true 17).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (Z.eqb_spec (m_maplen (R m)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE]. apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite gbase_bm, B0 in GE. fold stride in GE. unfold UNIT in GE.
      pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _]. fold stride in S1. unfold UNIT in S1.
      clearbody p stride e res q. clear SH.
      eapply (guard17_arith stride i off n q); try eassumption; lia. }
  reflexivity.
Qed.


(* [comment removed for export] *)
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).

#[using="Type"] Lemma ea_fst : fst ea = fst bm. Proof. reflexivity. Qed.
#[using="off n ai a ar ka BF p res q"] Lemma ea_snd : snd ea = e.
Proof. subst ea e stride. cbn [snd aadd]. rewrite c_snd. unfold sstart. rewrite gbase_bm. lia. Qed.

#[using="off n ai a ar ka BF p res q"] Lemma ea_off d : snd (aadd ea d) = e + d.
Proof. pose proof ea_snd as EA. unfold aadd at 1. cbn [snd]. rewrite <- EA. reflexivity. Qed.

#[using="ai a ar ka BF e res q SH"] Lemma get_nominal_size_eq {T} (k : Z -> M T) bail : get_nominal_size st p ea k bail = k n.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof ea_snd as EA. pose proof p_fst as PF. pose proof c_snd as CS.
  assert (CF : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (Hres : res = e - snd p - n) by reflexivity.
  assert (He : e = snd c + stride - IB) by reflexivity.
  assert (Hst : stride = get_stride (R m)) by reflexivity.
  assert (Hp2 : snd p = snd c + UNIT * off) by reflexivity.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ, <- CS, <- Hst in H0.
  (* [comment removed for export] *)
  assert (OFF : forall d, snd (aadd ea d) = snd c + get_stride (R m) - IB + d) by (intros d; rewrite ea_off, He, Hst; reflexivity).
  clearbody q. clear SH.
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
  cbv beta. rewrite (shiftr5_res i (Z.min res 5)) by lia. cbv zeta.
  destruct (Z.leb_spec 5 (Z.min res 5)) as [R5|R5].
  - (* [comment removed for export] *)
    destruct (K5 ltac:(lia)) as (B0 & B1 & B2 & B3 & B5 & R32).
    rewrite (guard_true 20) by (apply Z.eqb_eq; lia).
    unfold rd32.
    rewrite (rd8_known st (aadd ea (-4)) (byte_of res 0)) by (eapply known_at; [exact B0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 1) (byte_of res 1)) by (eapply known_at; [exact B1| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 2) (byte_of res 2)) by (eapply known_at; [exact B2| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 3) (byte_of res 3)) by (eapply known_at; [exact B3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (u32_bytes res) by lia.
    rewrite (guard_true 21) by (apply Z.leb_le; lia).
    rewrite (rd8_known st (aadd ea (-5)) 0) by (eapply known_at; [exact B5| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 25) by reflexivity.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [apply Kr; lia| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
  - (* [comment removed for export] *)
    replace (Z.min res 5) with res by lia.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    assert (Kr0 : known st (fst c, snd c + get_stride (R m) - IB - res) 0).
    { destruct (Z.eq_dec res 0) as [E0|NE]; [| apply Kr; lia]. rewrite E0, Z.sub_0_r, CF, <- Hst. exact H0. }
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [exact Kr0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
Qed.

#[using="n bm ai a ar ka BF stride e res q SH ea"] Lemma free_hdr_eq : free_hdr st p = SRet (Some (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st), m, i)).
Proof.
  unfold free_hdr. rewrite get_meta_eq. cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  match goal with |- get_nominal_size st p ?e ?k ?b = _ => change (get_nominal_size st p e k b) with (get_nominal_size st p ea k b) end.
  rewrite get_nominal_size_eq. reflexivity.
Qed.
End HDR.

End WithCeil.
End MI_WFree.

(* [comment removed for export] *)
Module MI_WFree2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma add_bit_lor f i : 0 <= f -> 0 <= i -> Z.testbit f i = false -> f + 2 ^ i = Z.lor f (2 ^ i).
Proof.
  intros Hf Hi Hb. rewrite <- Z.lxor_lor.
  - apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros j Hj.
    rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
    + rewrite Hb. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
  - apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
    + rewrite Hb. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.

#[using="Type"] Lemma testbit_add_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = false ->
  Z.testbit (f + 2 ^ i) j = Z.testbit f j || (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (add_bit_lor f i Hf Hi Hb). rewrite Z.lor_spec. f_equal.
  destruct (Z.eqb_spec i j) as [<-|NE]; [apply Z.pow2_bits_true; lia| apply Z.pow2_bits_false; lia].
Qed.

#[using="Type"] Lemma bit_eq i : bit i = 2 ^ i. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WR.
Variables (st : mstate) (q : aptr) (v : Z).
Let st' := wr8 q v st.

#[using="Type"] Lemma wr8_shadow_lookup rid :
  s_shadow st' !! rid = if (rid =? fst q)%N then Some (mkShadow (<[snd q := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst q)))) (r_hav (get_shadow st (fst q))) (r_havp (get_shadow st (fst q)))) else s_shadow st !! rid.
Proof.
  unfold st', wr8, upd_shadow. cbn. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

#[using="Type"] Lemma wr8_dom (P : N -> Prop) :
  (forall rid sh, s_shadow st !! rid = Some sh -> P rid) -> P (fst q) ->
  forall rid sh, s_shadow st' !! rid = Some sh -> P rid.
Proof.
  intros H Hq rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [auto|]. apply H.
Qed.

#[using="Type"] Lemma wr8_tks (T : N) :
  (s_tick st <= T)%N ->
  (forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N)) ->
  forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Proof.
  intros HT H rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
  intros E. inversion E. subst sh. cbn.
  assert (G : forall o w t, r_cells (get_shadow st (fst q)) !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N).
  { intros o w t Ho. unfold get_shadow in Ho. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Ho.
    - exact (proj1 (H _ _ E0) o w t Ho).
    - rewrite lookup_empty in Ho. discriminate. }
  assert (G2 : forall u hl ch, r_hav (get_shadow st (fst q)) !! u = Some hl -> In ch hl -> (snd ch <= T)%N).
  { intros u hl ch Hu Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hu.
    - exact (proj1 (proj2 (H _ _ E0)) u hl ch Hu Hin).
    - rewrite lookup_empty in Hu. discriminate. }
  assert (G3 : forall pg t, r_havp (get_shadow st (fst q)) !! pg = Some t -> (t <= T)%N).
  { intros pg t Hp. unfold get_shadow in Hp. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hp.
    - exact (proj2 (proj2 (H _ _ E0)) pg t Hp).
    - rewrite lookup_empty in Hp. discriminate. }
  split; [| split; [exact G2| exact G3]].
  intros o w t. destruct (Z.eq_dec o (snd q)) as [->|NEo].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. split; [| exact HT].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - rewrite lookup_insert_ne by congruence. apply G.
Qed.
End WR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xpend (X : extras) (p : option aptr) : extras := mkX (x_idle X) (x_zomb X) p (x_orph X) (x_fresh X).
Definition xorph (X : extras) (o : option N) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) o (x_fresh X).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NTF_SPEC : Prop :=
  forall (T : Type) (f : nat) X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec_hdr f st g i k bail = k st' mi /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma g_remove_perm lG : forall rest b l,
  Permutation lG ((b, l) :: rest) -> (forall y, In y rest -> fst y <> b) -> Permutation (g_remove b lG) rest.
Proof.
  induction lG as [|y lG IH]; intros rest b l P Hr.
  - apply Permutation_nil_cons in P. destruct P.
  - cbn. assert (Hy : In y ((b, l) :: rest)) by (eapply Permutation_in; [exact P| left; reflexivity]).
    destruct (Z.eqb_spec (fst y) b) as [E|NE].
    + destruct Hy as [<-|Hy]; [| exfalso; exact (Hr _ Hy E)].
      apply Permutation_cons_inv with (a := (b, l)). exact P.
    + destruct Hy as [<-|Hy]; [cbn in NE; congruence|].
      destruct (in_split _ _ Hy) as (r1 & r2 & ->).
      assert (P' : Permutation lG ((b, l) :: r1 ++ r2)).
      { apply Permutation_cons_inv with (a := y). eapply Permutation_trans; [exact P|].
        change ((b, l) :: r1 ++ y :: r2) with (((b, l) :: r1) ++ y :: r2). change (y :: (b, l) :: r1 ++ r2) with (y :: ((b, l) :: r1) ++ r2).
        apply Permutation_sym. apply Permutation_middle. }
      eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. apply (IH _ _ l P').
      intros z Hz. apply Hr. apply in_app_iff in Hz. apply in_app_iff. cbn. tauto.
Qed.

#[using="Type"] Lemma round_up_ge x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

#[using="Type"] Lemma perm_filter {A} (f : A -> bool) l l' : Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  induction 1; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

#[using="Type"] Lemma regions_delete_perm (st : mstate) rid r (F : N * region -> bool) :
  s_regions st !! rid = Some r ->
  Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F ((rid, r) :: map_to_list (delete rid (s_regions st)))).
Proof. intros H. apply perm_filter. apply Permutation_sym. apply map_to_list_delete. exact H. Qed.

#[using="Type"] Lemma inv_S_X X X' st BL : x_pend X' = x_pend X -> inv_S X st BL -> inv_S X' st BL.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.

Section DROP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (r : region).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = Some rid.
Hypothesis Hr : s_regions st !! rid = Some r.
Let st' := drop_region rid st.
Let L' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups (g_remove (r_base r) (ld_groups L)) L.
Let X' := xorph X None.

#[using="Type"] Lemma drop_lookup q : s_regions st' !! q = if (q =? rid)%N then None else s_regions st !! q.
Proof. apply lookup_drop_region. Qed.
#[using="Type"] Lemma drop_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st' !! q = Some rq.
Proof. intros H NE. rewrite drop_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
#[using="Type"] Lemma drop_some q rq : s_regions st' !! q = Some rq -> s_regions st !! q = Some rq /\ q <> rid.
Proof. rewrite drop_lookup. destruct (N.eqb_spec q rid); [discriminate| auto]. Qed.

#[using="INV HO Hr"] Theorem INVL_drop_orph : INVL X' st' L' BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ir_orph _ _ _ IR rid HO) as (r0 & Hr0 & Hk & NOG). rewrite Hr in Hr0. symmetry in Hr0. inversion Hr0. subst r0. clear Hr0.
  assert (KEEP : forall q rq, s_regions st !! q = Some rq -> r_kind rq <> RKGroup \/ q <> rid -> s_regions st' !! q = Some rq).
  { intros q rq Hq [K|NE]; apply drop_keep; auto. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
  assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by (intros; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[drop_region g_remove frontier region_live_range round_up_pg Z.mul Z.pow Z.add].
    + intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_ids q rq Hq).
    + intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_shape q rq Hq).
    + intros q1 q2 r1 r2 H1 H2 NE. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_disj q1 q2 r1 r2 H1 H2 NE).
    + exact ir_resv.
    + (* [comment removed for export] *)
      apply g_remove_perm with (l := r_len r).
      * eapply Permutation_trans; [exact ir_groups|].
        eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
        cbn. rewrite Hk. cbn. apply perm_skip. unfold st', drop_region. cbn. apply Permutation_refl.
      * intros y Hy. apply in_map_iff in Hy as ([q rq] & <- & Hq). apply filter_In in Hq as [Hq Hkq]. cbn in Hkq |- *.
        apply elem_of_list_In in Hq || apply list_elem_of_In in Hq. apply elem_of_map_to_list in Hq.
        unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
        destruct (r_kind rq) eqn:Ek; try discriminate.
        intros E. pose proof (ir_disj q rid rq r Hq Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ek, Hk in D.
        pose proof (ir_shape _ _ Hq) as (S1 & _ & S3 & _). pose proof (ir_shape _ _ Hr) as (T1 & _ & T3 & _).
        pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). lia.
    + eapply Permutation_trans; [exact ir_metas|].
      eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
      cbn. rewrite Hk. cbn. unfold st', drop_region. cbn. apply Permutation_refl.
    + intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_metalen q rq Hq K).
    + intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_brkfront q rq Hq K).
    + destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
      right. exists q, rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
    + intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
      * split; [apply KEEP; [exact Hq| left; congruence]| auto].
      * apply drop_some in Hq as [Hq _]. auto.
    + intros q1 q2 r1 r2 H1 H2. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_brk1 q1 q2 r1 r2 H1 H2).
    + revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (NB q rq Hq).
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
    + destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
      intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
    + intros q Hq. cbn in Hq. discriminate.
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite FR. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply KEEP; [exact Hrq| left; destruct K; congruence]| exact K].
  - apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
      * intros q rq Hq K E. apply KEEP; [exact Hq|]. right. intros ->. specialize (NOG b E). rewrite NOG in Hb. discriminate.
      * apply (group_ok_X X); [reflexivity|]. eapply G1. exact Hb.
    + exact G2.
    + exact G3.
    + intros q rq Hq K _. apply drop_some in Hq as [Hq NE]. apply (G4 q rq Hq K). rewrite HO. congruence.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [| exact K]. apply KEEP; [exact Hq|]. right. intros E. specialize (NOG b E). rewrite NOG in Hb. discriminate.
  - apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
  - assert (GS : forall q, q <> rid -> get_shadow st' q = get_shadow st q).
    { intros q NE. unfold get_shadow, st', drop_region. cbn. rewrite lookup_delete_ne by congruence. reflexivity. }
    assert (KN : forall q o v, q <> rid -> known st (q, o) v -> known st' (q, o) v).
    { intros q o v NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
    assert (UN : forall q o, q <> rid -> unknown st (q, o) -> unknown st' (q, o)).
    { intros q o NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
    assert (HNE : forall b m, hosts st b m -> fst b <> rid).
    { intros b m [ai Hb] E. specialize (NOG b E). rewrite NOG in Hb. discriminate. }
    destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
    + intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
      destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply drop_keep; auto| exact K].
    + intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq]. eapply D2. exact Hq.
    + intros b m i Hb Hi. apply KN; [exact (HNE b m Hb)|]. apply (D3 b m i Hb Hi).
    + intros b m o Hb Ho. apply UN; [exact (HNE b m Hb)|]. apply (D4 b m o Hb Ho).
    + intros b m p i Hb Hml Hs. destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
      pose proof (HNE b m Hb) as NE.
      split; [exists v3; split; [apply KN; [exact NE| exact K3]| auto]|]. split; [apply KN; [exact NE| exact K2]|]. split; [apply KN; [exact NE| exact K1]| exact Q].
    + intros k m i Hkk Hs. destruct (D6 k m i Hkk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      assert (NE : fst (bslot k) <> rid).
      { destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Ek). rewrite Ek. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). exact (HNE b m Hb). }
      split; [apply KN; [exact NE| exact A1]|]. split; [apply KN; [exact NE| exact A2]|]. split; [apply KN; [exact NE| exact A3]|]. split; [apply KN; [exact NE| exact A4]|].
      split; [exact A5|]. split.
      * intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try (apply KN; [exact NE| assumption]). exact B6.
      * split; [intros Hres; apply KN; [exact NE| apply A7; exact Hres]|]. intros a Ha. apply UN; [exact NE| apply A8; exact Ha].
Qed.
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma In_perm_map {A B} (f : A -> B) l l' x : Permutation l (map f l') -> In x l' -> In (f x) l.
Proof. intros P Hx. eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_map. exact Hx. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma group_region_in_ledger X st L rid r :
  inv_R X st L -> s_regions st !! rid = Some r -> r_kind r = RKGroup -> In (r_base r, r_len r) (ld_groups L).
Proof.
  intros IR Hr Hk. pose proof (ir_groups _ _ _ IR) as P.
  apply (In_perm_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ (rid, r) P).
  apply filter_In. split; [| rewrite Hk; reflexivity]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hr.
Qed.

#[using="Type"] Lemma brk_quiet_of X st L : inv_R X st L -> brk_quiet L.
Proof.
  intros IR. pose proof (ir_brk _ _ _ IR) as B. unfold brk_quiet.
  destruct (c_brk (s_ctx st)); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I.
Qed.

Section FREE.
Hypothesis NTF : NTF_SPEC.

#[using="NTF"] Theorem free_INVL st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  ftree L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof.
  intros INV Hk.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold free. rewrite (free_hdr_eq st c off n m bm i ai a ar ka BF). cbn [sbind].
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  (* [comment removed for export] *)
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _].
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ; unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Hkr); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  (* [comment removed for export] *)
  unfold free_tail.
  assert (MR1' : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; reflexivity).
  assert (MR1 : forall x, get_meta_rec st1 x = get_meta_rec st x) by exact MR1'.
  rewrite !MR1.
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st m); rewrite NA, NF; reflexivity).
  fold (MR st m).
  destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
  - (* [comment removed for export] *)
    cbn [ftree ret]. exists LS.
    pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
    pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
    assert (Efun : upd_meta m (m_set_freed (m_freed (MR st m) + bit i)) st1
                  = upd_meta m (fun r => m_set_avail (m_avail (MR st m)) (m_set_freed (m_freed (MR st m) + bit i) r)) st1).
    { unfold upd_meta. f_equal. all: rewrite <- (MR1 m); fold (MR st1 m); destruct (MR st1 m); reflexivity. }
    rewrite Efun.
    assert (Hfr : m_freed (MR st m) <> 0).
    { intros E. rewrite E in BR. cbn in BR. discriminate. }
    apply (INVL_mask_change (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm ai (m_avail (MR st m)) (m_freed (MR st m) + bit i) None INV1).
    + exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
    + rewrite !MR1'. rewrite bit_eq. unfold tbit.
      split; [exact M1|]. split; [pose proof (Z.pow_nonneg 2 i); lia|]. split; [exact M3|]. split; [| split].
      * intros j Hj. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [apply M4; auto| apply Z.eqb_eq in H; lia].
      * intros j Hj Ha. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
      * pose proof (bf_ai _ _ _ _ _ _ _ _ _ _ _ BF) as AI. intros j Hj. rewrite testbit_add_bit by (auto; lia). unfold tbit in M6. rewrite (M6 j Hj). reflexivity.
    + (* [comment removed for export] *)
      intros j Hj. rewrite !MR1'. cbn zeta.
      destruct INV1 as (_ & _ & _ & _ & _ & IS1 & _).
      pose proof (is_part _ _ _ IS1 bm m ai j (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(rewrite MR1'; exact Hj)) as P1.
      rewrite !MR1' in P1. cbn zeta in P1. cbn [x_pend xpend] in P1.
      unfold tbit in *. rewrite bit_eq. rewrite testbit_add_bit by (auto; lia).
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) in P1 |- *.
      assert (N5 : ~ (@None aptr = Some (fst bm, sstart (MR st m) j))) by discriminate.
      destruct (Z.eqb_spec i j) as [<-|NE].
      * rewrite <- Ec in P1 |- *. rewrite NF, Bool.orb_false_l || rewrite Bool.orb_true_r.
        unfold one5 in P1 |- *. rewrite NF in P1.
        clear - P1. revert P1.
        generalize (Z.testbit (m_avail (MR st m)) i = true) as A.
        generalize (In c (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! c <> None) as Hh.
        generalize (@eq (option aptr) (Some c) (Some c)) as P5 || idtac.
        intros. assert (FF : ~ (false = true)) by discriminate. assert (N5 : forall x : aptr, ~ (@None aptr = Some x)) by discriminate.
        pose proof (N5 c). pose proof (@eq_refl (option aptr) (Some c)). tauto.
      * rewrite Bool.orb_false_r.
        assert (NS : ~ (Some c = Some (fst bm, sstart (MR st m) j))).
        { intros E. apply NE. assert (E2 : slot_start' (MR st m) i = slot_start' (MR st m) j).
          { rewrite !(slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). rewrite <- Ec. congruence. }
          exact (proj2 (slot_key_inj _ _ _ IS _ _ _ _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) Hi Hj E2)). }
        unfold one5 in P1 |- *.
        clear - P1 NS N5. revert P1 NS N5.
        generalize (Z.testbit (m_avail (MR st m)) j = true) as A. generalize (Z.testbit (m_freed (MR st m)) j = true) as F.
        generalize (In (fst bm, sstart (MR st m) j) (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! (fst bm, sstart (MR st m) j) <> None) as Hh.
        intros. tauto.
    + right. split.
      * intros s Hs'. cbn in Hs'. inversion Hs'. subst s. exists i. rewrite !MR1'. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). exact Ec.
      * intros s Hs'. discriminate.
    + intros _ sc Hin Hnh. split; [| pose proof (Z.pow_nonneg 2 i); rewrite bit_eq; lia]. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
    + intros _ Hsc NI. exfalso. apply Hfr. rewrite MR1' in Hsc. exact (proj2 (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NI)).
    + intros _ Hsc Hst. exfalso. apply Hfr. rewrite MR1' in Hsc, Hst. exact (proj2 (g_under _ _ _ _ _ _ GO ltac:(discriminate) Hsc Hst)).
  - (* [comment removed for export] *)
    pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
    assert (Hsc0 : 0 <= m_sizeclass (MR st m)).
    { pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as [[? _]|(E63 & _)]; lia. }
    destruct (NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1)
      as (st' & mi & LS' & EQ & POST).
    + apply (hosts_ext st st1); [reflexivity|]. exists ai. exact Hb.
    + rewrite MR1'. exact Hi.
    + cbn [x_pend xpend]. rewrite MR1', Ec. reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold FUEL. lia.
    + rewrite MR1'. unfold FUEL. lia.
    + rewrite EQ. destruct mi as [[base len]|].
      * destruct POST as (r & Hb0 & Hr & Hkr & Hlen & Hpos & INV').
        destruct (Z.eqb_spec len 0) as [|NZ]; [lia|]. cbn [negb].
        pose proof INV' as (IR' & _).
        cbn [ftree]. split.
        -- split; [exact (brk_quiet_of _ _ _ IR')|]. exists (r_len r). split; [| right; exact Hlen].
           rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r. exact (group_region_in_ledger _ _ _ _ _ IR' Hr Hkr).
        -- intros z. cbn [answer_ok]. destruct (munmap_answer_ok z); [| exact I].
           cbn [ftree ret]. exists LS'. rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r.
           apply (INVL_drop_orph (xorph (xpend (xpend x0 (Some c)) None) (Some (fst base))) st' L (bl_remove c BL) LS' (fst base) r INV' eq_refl Hr).
      * cbn [ftree ret]. exists LS'. exact POST.
Qed.
End FREE.

End WithCeil.
End MI_WFree2.
