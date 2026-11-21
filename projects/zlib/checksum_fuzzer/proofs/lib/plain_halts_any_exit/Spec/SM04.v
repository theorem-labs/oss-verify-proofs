(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require KInv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_Inv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_Ext.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_WFree2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM02.
From Stdlib Require Permutation.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_Pres3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_Pres4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_WAMeta.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require MI_WFree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM07.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MI_TF2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Inv. Import SM08. Import SM08.MI_Kit. Import SM01. Import SM01.MI_Arith. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Ext. Import SM01.MI_Shadow. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WFree2. Import SM02. Import SM02.MI_WGroup.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

Definition PS (st : mstate) (q : aptr) : Prop :=
  exists b m, hosts st b m /\ fst b = fst q /\
    ((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
     \/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 st : TF0 st -> TF2 st. Proof. apply TF0_TW. Qed.
Lemma TF0_TF st : TF0 st -> TF st.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.

Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

Definition geom_kept (st st' : mstate) : Prop :=
  forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
                              /\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

Lemma geom_kept_refl st : geom_kept st st.
Proof. intros b m H. auto. Qed.
Lemma geom_kept_trans a b c : geom_kept a b -> geom_kept b c -> geom_kept a c.
Proof.
  intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
  split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.

Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
  intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
  exists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

Lemma geom_kept_of st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall b m, hosts st b m -> MR st' m = MR st m) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
  r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other l : forall st rid o, ~ In (rid, o) (map fst l) ->
  r_cells (get_shadow (wrs l st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.


Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma PS_not_interior q :
  PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
  intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    +
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  -
    destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
    destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

Lemma TF2_interior_old :
  TF2 st -> forall o v t, r_cells (get_shadow st (fst bg)) !! o = Some (v, t) ->
  sstart (MR st g) idx <= o < sstart (MR st g) (idx + 1) - IB -> (t < s_tick st)%N.
Proof.
  intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

Lemma TF2_ghdr_old (p : aptr) :
  TF2 st -> snd p mod 16 = 0 ->
  forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
  intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

Lemma TF2_TF : TF2 st -> TF st.
Proof.
  intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.
End MI_TF2.

Module MI_WAMeta2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_List. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Ext. Import SM01.MI_Ext2. Import SM01.MI_Shadow. Import SM01.MI_Read. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres4. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WFree2. Import SM02. Import SM02.MI_Ledger. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WAMeta.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

Lemma INVL_am_init X st L BL LS : INVL X st L BL LS ->
  INVL X (am_init st) L BL LS /\ c_init_done (s_ctx (am_init st)) = 1 /\ AM_frame st (am_init st).
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.


Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 (Some m)) Post.

Lemma am_take_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
  intros INV AF LF HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

Lemma am_carve_ft s p L LS : INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

Lemma am_finish_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
  ftree L (am_finish st true k bail) Post.
Proof.
  intros INV AF LF HC HI.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
  intros INV AF LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

Lemma lbrk_pages_ok_ext L1 L2 lo len :
  ld_resv L1 = ld_resv L2 -> ld_groups L1 = ld_groups L2 -> ld_metas L1 = ld_metas L2 -> ld_brkreg L1 = ld_brkreg L2 ->
  ld_atop L1 = ld_atop L2 ->
  lbrk_pages_ok L1 lo len = lbrk_pages_ok L2 lo len.
Proof. intros E1 E2 E3 E4 E5. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.

Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 LF.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
    eapply KS; [exact INV1| | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  -
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
  -
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.
End MI_WAMeta2.

Module MI_WNtf2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_List. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Ext. Import SM01.MI_Ext2. Import SM01.MI_Shadow. Import SM01.MI_Read. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres4. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WFree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WFree2. Import SM07. Import SM07.MI_WKill. Import SM07.MI_WNtf.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition decodes (T : Type) (st : mstate) (p pm : aptr) (ip : Z) : Prop :=
  s_slots st !! p = Some (pm, ip) /\ forall (k : aptr -> Z -> M T) (bail : M T), dec_hdr st p k bail = k pm ip.
Definition DEC_OK (T : Type) (dec : decoder T) : Prop :=
  forall st p pm ip (k : aptr -> Z -> M T) (bail : M T), decodes T st p pm ip -> dec st p k bail = k pm ip.
Lemma dec_hdr_ok T : DEC_OK T dec_hdr.
Proof. intros st p pm ip k bail [_ H]. apply H. Qed.
Lemma dec_slots_ok T : DEC_OK T dec_slots.
Proof. intros st p pm ip k bail [H _]. unfold dec_slots. rewrite H. reflexivity. Qed.

Definition NTF_AT (T : Type) (f : nat) : Prop :=
  forall (dec1 dec2 : decoder T), DEC_OK T dec1 -> DEC_OK T dec2 ->
  forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec1 f st g i k bail = k st' mi /\ nontrivial_free dec2 f st g i k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

Lemma rem_notin g l : ~ In g l -> rem g l = l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|]. intros H.
  unfold rem. cbn. destruct (aptr_eq_dec g x) as [->|NE]; [exfalso; apply H; left; reflexivity|].
  cbn. f_equal. apply IH. tauto.
Qed.

Lemma regions_fm_st st g : s_regions (fm_st st g) = s_regions st.
Proof. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 st)) as (E & _). rewrite E. reflexivity. Qed.

Lemma INVL_free_zombie idle zomb pend orph st L BL LS g :
  INVL (mkX idle (g :: zomb) pend orph None) st L BL LS ->
  ~ In g zomb -> ~ In g idle ->
  exists LS', INVL (mkX idle zomb pend orph None) (fm_st st g) L BL LS'.
Proof.
  intros INV NZ NI.
  pose proof (INVL_unzombie _ st L BL LS g INV ltac:(left; reflexivity)) as INV1. cbn in INV1.
  unfold xzomb in INV1. cbn in INV1.
  unfold rem in INV1. cbn in INV1. destruct (aptr_eq_dec g g) as [_|NE]; [| congruence]. cbn in INV1.
  fold (rem g zomb) in INV1. rewrite (rem_notin g zomb NZ) in INV1.
  eexists. unfold fm_st.
  apply (INVL_queue _ (put_meta g meta0 st) L BL LS g LFree INV1).
  - unfold MR. rewrite get_meta_rec_put_same. reflexivity.
  - rewrite lookup_metas_put, aptr_eqb_refl. discriminate.
  - cbn. split; [unfold MR; rewrite get_meta_rec_put_same; reflexivity|]. split; [exact NI| exact NZ].
Qed.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_AT T f.
Variables (dec1 dec2 : decoder T).
Hypothesis D1 : DEC_OK T dec1.
Hypothesis D2 : DEC_OK T dec2.
Variables (idle zomb : list aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Variables (k : mstate -> mapinfo -> M T) (bail : M T).
Let X := mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis NL : m_next (MR st g) = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Hypothesis FUEL : 49 - m_sizeclass (MR st g) <= Z.of_nat (S f).

Theorem free_group_ok :
  exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st g k bail = k st' mi /\
    free_group T dec2 (nontrivial_free dec2 f) st g k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (mkX idle zomb None None None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
    end.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
            (del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
  assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
  { intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
  unfold free_group. fold (MR st g).
  set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
  rewrite (hosts_mem _ _ _ IM _ _ Hgh).
  set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
  pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
  cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
  pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
  -
    destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
                (fun m idx => nontrivial_free dec1 f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
      as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
    fold stk in EQ, Hs', Hpm'.
    assert (DQ : decodes T stk bg pm ip).
    { split; [exact Hs'|]. intros k' bail'.
      destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
      fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
    rewrite (D1 stk bg pm ip _ bail DQ), (D2 stk bg pm ip _ bail DQ).
    destruct (IHf dec1 dec2 D1 D2 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
                  (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
      as (st3 & mi & LS3 & EQ3 & EQ3b & REG3 & POST3).
    + rewrite KMR. exact Hip.
    + cbn. rewrite KMR, Ep. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + rewrite KMR. lia.
    + rewrite EQ3, EQ3b. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
      destruct mi as [[base len]|].
      * destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
        destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. exists r.
        split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
      * cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]| exact INV4].
  -
    rewrite !free_meta_eq.
    destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
    fold stk in Hr.
    assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
    { apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
    destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
    assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    eexists _, _, LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, RS, FMSEC, RSS.
    split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. cbn. exists r. cbn.
    split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.


Lemma ntf_unfold {T} dec f st g i (k : mstate -> mapinfo -> M T) bail :
  nontrivial_free dec (S f) st g i k bail =
    (if (Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g then
      match m_next (MR st g) with
      | Some _ =>
        guard 50 (m_sizeclass (MR st g) <? 48) (
          match optr_eqb (active st (m_sizeclass (MR st g))) (Some g), active (dequeue (LActive (m_sizeclass (MR st g))) g st) (m_sizeclass (MR st g)) with
          | true, Some a => activate_group a (dequeue (LActive (m_sizeclass (MR st g))) g st)
                              (fun st2 _ => free_group T dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group T dec (nontrivial_free dec f) (dequeue (LActive (m_sizeclass (MR st g))) g st) g k bail
          end) bail
      | None => free_group T dec (nontrivial_free dec f) st g k bail
      end
    else if Z.lor (m_freed (MR st g)) (m_avail (MR st g)) =? 0 then
      guard 51 (m_sizeclass (MR st g) <? 48) (
        if negb (optr_eqb (active st (m_sizeclass (MR st g))) (Some g))
        then queue (LActive (m_sizeclass (MR st g))) g st (fun st' => k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st') None) bail
        else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None) bail
    else
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None).
Proof. reflexivity. Qed.

Lemma data_same r r' i : data_of r' = data_of r ->
  sstart r' i = sstart r i /\ m_last_idx r' = m_last_idx r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r /\ m_mem r' = m_mem r.
Proof.
  intros D. pose proof (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold sstart, gbase. rewrite (get_stride_data _ _ D), E1. repeat split; auto.
Qed.

Lemma head_of_eq_app (l1 l2 : list aptr) g : NoDup (l1 ++ g :: l2) -> head_of (l1 ++ g :: l2) = Some g -> l1 = [].
Proof.
  intros ND H. destruct l1 as [|a l1']; [reflexivity|]. cbn in H. inversion H. subst a. exfalso.
  cbn in ND. apply NoDup_cons in ND as [N _]. apply N. apply elem_of_list_In || apply list_elem_of_In. apply in_app_iff. right. left. reflexivity.
Qed.

Theorem ntf_all T : forall f, NTF_AT T f.
Proof.
  induction f as [|f IH]; intros dec1 dec2 D1 D2 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
  destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof Hgh as [ai Hg].
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi. cbn [x_pend] in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false) by (destruct (tbit (m_avail (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  assert (NB : tbit (m_freed (MR st g)) i = false) by (destruct (tbit (m_freed (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  clear Pi.
  rewrite !ntf_unfold.
  set (mask := Z.lor (m_freed (MR st g)) (m_avail (MR st g))).
  assert (MN : 0 <= mask) by (apply Z.lor_nonneg; auto).
  assert (MI : Z.testbit mask i = false) by (unfold mask; rewrite Z.lor_spec; unfold tbit in NA, NB; rewrite NA, NB; reflexivity).
  assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; auto; lia).
  assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
  { intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
    destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
    rewrite Bool.orb_true_r in OK. discriminate. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
  -
    apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
    assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
    { intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
      rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
      unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
    pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
    assert (FGT : forall st2 LS2,
      INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
      s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
      exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st2 g k bail = k st' mi /\
        free_group T dec2 (nontrivial_free dec2 f) st2 g k bail = k st' mi /\
        (s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2) /\
        match mi with
        | None => INVL (mkX idle zomb None None None) st' L BL LS'
        | Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
            /\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
        end).
    { intros st2 LS2 INV2 HG2 DD2 NL2. destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
      rewrite <- Es in INV2.
      apply (free_group_ok T f IH dec1 dec2 D1 D2 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
      - rewrite HG2. exact Hg.
      - exact NL2.
      - rewrite El. exact Hi.
      - rewrite El, Ea, Ef. exact ALL.
      - rewrite Esc. exact F2. }
    destruct (m_next (MR st g)) as [nx|] eqn:NX.
    +
      assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
      destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
      destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
      rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
      destruct (in_split _ _ Hin) as (l1 & l2 & HL).
      pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
      assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
      { apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
      set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
      destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _). fold st1 in G1, RG1, SE1.
      pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
      assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
      assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
      { pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
      destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
      *
        destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
        assert (El1 : l1 = []).
        { apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
        subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
        assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
        assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
        destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
        pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
        pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
        destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
        assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
        assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
        assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
        { rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
        rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
        pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
        set (st2 := upd_meta a _ st1) in INV2 |- *.
        destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & EQb & REG & POST).
        -- unfold st2. cbn. exact G1.
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
        -- exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|].
           split; [destruct REG as [RA RB]; rewrite RA, RB; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| etransitivity; [| exact SE1]; reflexivity]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
    +
      destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & POST). exists st', mi, LS'. split; [exact EQ| exact POST].
  -
    assert (OKF : m_last_idx (MR st g) = 0 -> okay_to_free st g = false).
    { intros L0. rewrite L0 in C1. assert (i = 0) by lia. subst i.
      assert (mask = 0).
      { apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0. unfold mask. rewrite Z.lor_spec.
        destruct (Z.eq_dec j 0) as [->|NE]; [unfold tbit in NA, NB; rewrite NA, NB; reflexivity|].
        destruct (Z.testbit (m_freed (MR st g)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|].
        destruct (Z.testbit (m_avail (MR st g)) j) eqn:EA; [pose proof (M3 j Hj EA); lia|]. reflexivity. }
      rewrite H in C1. cbn in C1. exact C1. }
    assert (C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
    { intros Hsc. destruct (Z.eq_dec (m_last_idx (MR st g)) 0) as [L0|L0]; [exact (NU (OKF L0) Hsc)|].
      unfold get_stride. destruct (Z.eqb_spec (m_last_idx (MR st g)) 0); [lia|]. cbn. lia. }
    destruct (Z.eqb_spec mask 0) as [MZ|MNZ].
    +
      assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
      { destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
        rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
        cbn in OKF. discriminate (OKF L0). }
      rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
      destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
      *
        eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
        apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
        -- intros _ sc _ _. exact AZ.
        -- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
        -- exact C3.
      *
        assert (NL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
          assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
          destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
          destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
          apply NHD. rewrite <- Esc at 1 || idtac.
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
          rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
        assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
        rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
        pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
        pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
        cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(repeat split; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
        set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
        set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
        destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _). fold stq in Gq, RGq, SEq.
        pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
        destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
        assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
        { apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
          - rewrite Gq. exact Hg.
          - rewrite El. exact Hi.
          - cbn. rewrite Es. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
        eexists _, None, LSq. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; rewrite RGq, SEq; split; reflexivity|]. cbn.
        apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
        intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
        assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
        split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
        split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
        intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
        replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
        rewrite (get_stride_data _ _ Dq) in LT. lia.
    +
      eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
      apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
      * intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
      * intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
        -- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
        -- exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc (fun H => lists_notin st LS (old_lists _ _ _ _ _ INV) g NX _ (proj2 (In_nth _ _ g H) ))) || idtac.
           assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
           destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
      * exact C3.
Qed.

Theorem ntf_spec : NTF_SPEC.
Proof.
  intros T f X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_hdr (dec_hdr_ok T) (dec_hdr_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ & _ & _ & POST).
  exists st', mi, LS'. split; [exact EQ| exact POST].
Qed.

Theorem ntf_slots_agree T f X st L BL LS g bg i (k : mstate -> mapinfo -> M T) bail :
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  nontrivial_free dec_slots f st g i k bail = nontrivial_free dec_hdr f st g i k bail.
Proof.
  intros INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_slots (dec_hdr_ok T) (dec_slots_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ1 & EQ2 & _).
  rewrite EQ1, EQ2. reflexivity.
Qed.

Theorem ntf_spec2 T f : NTF_AT T f.
Proof. apply ntf_all. Qed.

Theorem free_INVL_closed st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  ftree L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof. exact (free_INVL ntf_spec st L BL LS c off n). Qed.
End MI_WNtf2.

Module MI_WTry.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. Import SM02. Import SM02.MI_Bits. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_List. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Ext. Import SM01.MI_Ext2. Import SM01.MI_Shadow. Import SM01.MI_Read. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_Pres4. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import MI_WFree2. Import SM07. Import SM07.MI_WKill. Import SM07.MI_WNtf.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma one5_A_to_E (A B C D E A' E' : Prop) : A -> ~ A' -> E' -> one5 A B C D E -> one5 A' B C D E'.
Proof. unfold one5. tauto. Qed.

Section TAFIN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m bm : aptr) (ai : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hm : s_groups st !! bm = Some (mkGhdr (Some m) ai).
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st m)))) = Some m.
Let mask := m_avail (MR st m).
Hypothesis MNZ : mask <> 0.
Let first := lowbit mask.
Let idx := ctz32 first.
Let st' := upd_meta m (m_set_avail (mask - first)) st.

Lemma tafin_listed : In m (LS (LActive (m_sizeclass (MR st m)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st m)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem ta_fin_ok :
  INVL (xpend X (Some (fst bm, sstart (MR st m) idx))) st' L BL LS
  /\ 0 <= idx <= m_last_idx (MR st m) /\ first <> 0 /\ 0 <= first
  /\ UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m).
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hmh : hosts st bm m) by (exists ai; exact Hm).
  assert (MPOS : 0 < mask) by (unfold mask in *; lia).
  destruct (lowbit_idiom mask MPOS) as (k0 & K0 & EL & EC & TB & A0 & TA).
  assert (Eidx : idx = k0) by (unfold idx, first; exact EC).
  assert (Hk0 : k0 <= ai) by (apply M3; [exact K0| exact TB]).
  assert (NU : UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m)).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(E63 & _)].
    - destruct (Z.lt_ge_cases (get_stride (MR st m)) (UNIT * size_class (m_sizeclass (MR st m)))) as [LT|GE]; [| exact GE].
      exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite HF; discriminate) ltac:(lia) LT) as [A _]. unfold mask in MNZ. exact (MNZ A).
    - rewrite E63. change (size_class 63) with 0. pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _]. unfold UNIT in *. lia. }
  assert (Ef : st' = upd_meta m (fun r => m_set_avail (mask - first) (m_set_freed (m_freed (MR st m)) r)) st).
  { unfold st', upd_meta, MR. destruct (get_meta_rec st m); reflexivity. }
  rewrite Ef.
  assert (FNZ : first <> 0 /\ 0 <= first) by (unfold first; rewrite EL; clear -K0; pose proof (Z.pow_pos_nonneg 2 k0); split; [lia| apply Z.pow_nonneg; lia]).
  rewrite Eidx.
  pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _].
  split; [| split; [clear -K0 Hk0 AI; lia| split; [exact (proj1 FNZ)| split; [exact (proj2 FNZ)| exact NU]]]]. replace X with (mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) at 1 by (destruct X; reflexivity).
  apply (INVL_mask_change X st L BL LS m bm ai (mask - first) (m_freed (MR st m)) (Some (fst bm, sstart (MR st m) k0)) INV Hm).
  - unfold first. split; [exact A0|]. split; [exact M2|]. split; [| split; [exact M4| split; [| exact M6]]].
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M3 i Hi H).
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M5 i Hi H).
  - intros j Hj. cbn zeta. unfold first, tbit. rewrite TA by (clear -Hj; lia).
    pose proof (is_part _ _ _ IS _ _ _ j Hm Hj) as P. cbn zeta in P. rewrite HP in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh) in P |- *.
    unfold tbit in P. destruct (Z.eqb_spec k0 j) as [<-|NE].
    + eapply one5_A_to_E; [exact TB| rewrite TB; cbn; discriminate| reflexivity| exact P].
    + rewrite Bool.andb_true_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      split; [discriminate|]. intros E. exfalso. inversion E.
      destruct (Z.lt_total k0 j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ k0 j Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j k0 Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
  - right. split; [rewrite HP; discriminate|]. intros s Hs. inversion Hs. subst s. exists k0. split; [clear -K0 Hk0 AI; lia|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh). reflexivity.
  - intros _ sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc m Hin) as (_ & _ & Esc). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros _ _ NI. exfalso. apply NI. eexists. exact tafin_listed.
  - intros _ Hsc LT. exfalso. clear -LT NU. lia.
Qed.
End TAFIN.


Section SETAI.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m b : aptr) (ai ai' : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hm : s_groups st !! b = Some (mkGhdr (Some m) ai).
Hypothesis Hai' : ai <= ai' <= m_last_idx (MR st m).
Hypothesis AV : forall i, 0 <= i -> tbit (m_avail (MR st m)) i = true -> i <= ai'.
Hypothesis LISTED : ai' < m_last_idx (MR st m) -> In m (LS (LActive (m_sizeclass (MR st m)))).
Let st' := Malloc.set_groups (<[b := mkGhdr (Some m) ai']> (s_groups st)) st.

Lemma sa_lookup bb : s_groups st' !! bb = if aptr_eqb bb b then Some (mkGhdr (Some m) ai') else s_groups st !! bb.
Proof.
  unfold st'. cbn. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma sa_hosts bb x : hosts st' bb x <-> hosts st bb x.
Proof.
  unfold hosts. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| tauto].
  split; intros [a H]; [rewrite Hm; inversion H; subst; eexists; reflexivity| rewrite Hm in H; inversion H; subst; eexists; reflexivity].
Qed.
Lemma sa_live x : live_group st' x <-> live_group st x.
Proof. unfold live_group. split; intros [bb H]; exists bb; apply sa_hosts; exact H. Qed.

Theorem INVL_set_ai : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (GNE : forall bb h, s_groups st' !! bb = Some h -> (bb = b /\ h = mkGhdr (Some m) ai') \/ (bb <> b /\ s_groups st !! bb = Some h)).
  { intros bb h. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [intros H; inversion H; auto| auto]. }
  assert (GN : forall bb, s_groups st' !! bb <> None <-> s_groups st !! bb <> None).
  { intros bb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite Hm; split; discriminate| tauto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; try assumption.
    intros rid Ho. destruct (ir_orph rid Ho) as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
    intros bb Hbb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| exact (NG bb Hbb)]. specialize (NG b Hbb). rewrite Hm in NG. discriminate.
  - destruct IA; constructor; try assumption.
    intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). unfold gcnt.
    change (s_groups st') with (<[b:=mkGhdr (Some m) ai']> (s_groups st)).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (s_groups st) b _ Hm))).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (<[b:=mkGhdr (Some m) ai']> (s_groups st)) b (mkGhdr (Some m) ai') ltac:(apply lookup_insert_eq)))).
    cbn [map zsum fold_right snd g_meta]. rewrite delete_insert_eq. reflexivity.
  - destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; try assumption.
    + intros x bb Hx. destruct (Q2 x bb Hx) as [H|H]; [left; apply sa_hosts; exact H| right; exact H].
    + intros bb h Hbb. apply GNE in Hbb as [[-> ->]|[NE Hbb]]; [| exact (Q3 bb h Hbb)].
      exists m. cbn [g_meta g_active_idx]. split; [reflexivity|]. split; [exact (hosts_mem _ _ _ (mkIM _ _ _ Q1 Q2 Q3 Q4 Q5) _ _ (ex_intro _ ai Hm))| change (MR st' m) with (MR st m); lia].
    + intros z Hz. destruct (Q5 z Hz) as (A1 & A2 & A3 & bz & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      exists bz. split; [exact A4|]. rewrite sa_lookup. destruct (aptr_eqb_spec bz b) as [->|NE]; [rewrite Hm in A5; discriminate| exact A5].
  - destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. apply (dll_ext_metas st st' eq_refl). apply L2.
    + intros sc x Hx. destruct (L7 sc x Hx) as (B1 & B2 & B3). split; [exact B1|]. split; [apply sa_live; exact B2| exact B3].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros x bb aix Hbb. apply GNE in Hbb as [[-> E]|[NE Hbb]].
      * inversion E. subst x aix. destruct GO; constructor; change (MR st') with (MR st); try assumption.
        -- lia.
        -- destruct g_masks as (W1 & W2 & W3 & W4 & W5 & W6). split; [exact W1|]. split; [exact W2|]. split; [exact AV|]. split; [exact W4|]. split; [exact W5|].
           intros i Hi. apply W6. lia.
        -- intros NF Hlt. apply LISTED. exact Hlt.
        -- intros Hsc0. pose proof (g_full0 Hsc0). lia.
      * apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 x bb aix Hbb)].
    + intros bb aix Hbb. apply GNE in Hbb as [[_ E]|[NE Hbb]]; [discriminate| exact (G2 bb aix Hbb)].
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2 P1 P2 Esc. change (MR st') with (MR st) in P1, P2, Esc.
      apply GNE in H1 as [[-> E1]|[N1 H1]]; apply GNE in H2 as [[-> E2]|[N2 H2]].
      * inversion E1. inversion E2. subst. reflexivity.
      * inversion E1. subst m1 ai1. eapply G3; [exact Hm| exact H2| lia| exact P2| exact Esc].
      * inversion E2. subst m2 ai2. eapply G3; [exact H1| exact Hm| exact P1| lia| exact Esc].
      * eapply G3; eassumption.
    + intros rid r Hr K Ho. destruct (G4 rid r Hr K Ho) as (x & Hx & Hml). exists x. split; [apply sa_hosts; exact Hx| exact Hml].
    + intros bb h Hbb. apply GNE in Hbb as [[-> _]|[NE Hbb]]; [exact (G5 _ _ Hm)| exact (G5 bb h Hbb)].
  - destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s x i Hs. destruct (S1 s x i Hs) as (B1 & B2 & B3). split; [apply sa_live; exact B1| auto].
    + intros bb x i Hbb Hi. apply (S2 bb); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x aix i Hbb Hi. cbn zeta. change (MR st') with (MR st) in Hi |- *.
      eapply one5_iff; [reflexivity| reflexivity| reflexivity| apply iff_sym; apply GN| reflexivity|].
      apply GNE in Hbb as [[-> E]|[NE Hbb]]; [inversion E; subst x aix; exact (S3 b m ai i Hm Hi)| exact (S3 bb x aix i Hbb Hi)].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros bb x i Hbb Hi. apply (D3 bb x i); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x o Hbb Ho. apply (D4 bb x o); [apply sa_hosts; exact Hbb| exact Ho].
    + intros bb x p i Hbb Hml Hs. apply (D5 bb x p i); [apply sa_hosts; exact Hbb| exact Hml| exact Hs].
Qed.
End SETAI.

Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.
End MI_WTry.
