(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Shadow MI_Pres1.
Import ListNotations.
Local Open Scope Z_scope.

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
Proof. intros H [_ [H1 _]]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59308579152.26000009S2TK1H2H1".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="st' TK"] Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59308579281.26000009S2TK1H2H2".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
    + subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. Local Ltac2 Set LiaHints.tbl := fun () => "00I0>11466512665.6711470697803.6012622611033.6712626701835.6013661702990.6016235939683.541687815369.61 18299437249.4118299437249.4223681655864.402402433910.37 24267310137.6727090621896.5427549090083.542975750329.67 2980033771.60 3408989475.54 39040944597.5442633240268.6242746344060.4142746344060.4246097234189.6067463663417.6767476136811.6067930885629.4000000<00S00_01601B01F01[01d01m02902@02L02X02\02h03?03C03O03e03n04704C04O04f052S2TK2SG4EsndS2TK4Hoff3Hsz4Hfit4EsndS2TK2SG4EsndS2TK4Hoff3Hsz4Hfit4EsndS2TK2Ho2Ef1AS2TKS2TK4Hoff3Hsz4Esnd2HrS2TK2Ef1AS2TK2Ef1AS2TK2Ho2Ef1AS2TK2EfS2TK2SG4EsndS2TK2Hd2Ef1AS2TKS2TK2SG4EsndS2TK4Hoff3Hsz4Hfit4EsndS2TKS2TK2Hd2Ef1AS2TK4Hoff4Hfit4Esnd2HaS2TK2Ef1AS2TK2Ef1AS2TK2Ho2Ef1AS2TK2SG4EsndS2TK4Hoff3Hsz4Hfit4EsndS2TK2Ho2Ef1A".
lia.
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WRITE_T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
  intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
  intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
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
      fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. tauto.
    - intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
    - subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
      apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
      apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
    - intros k' Hk'. apply S6. apply SUB. exact Hk'. }
  assert (ISH' : inv_SH st' BL').
  { eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
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

#[using="X st L LS INV Hk"] Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
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

Lemma inv_SH_cons st BL k m i :
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
      clearbody U E A F Hh P5 Q5. tauto.
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_T X st st' BL LS IM IG IS); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
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
