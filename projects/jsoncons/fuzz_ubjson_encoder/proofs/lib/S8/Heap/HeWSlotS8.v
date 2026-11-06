(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 KStepS8 MI_WAMetaS8 MI_Pres4S8 MI_WFree2S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Bits.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMWSLOT.
Context {RUNp : RunP}.

Definition fsub (a b : Z) : Prop := forall i, 0 <= i -> Z.testbit a i = true -> Z.testbit b i = true.

Lemma fsub_refl a : fsub a a. Proof. intros i _ H. exact H. Qed.
Lemma fsub_trans a b c : fsub a b -> fsub b c -> fsub a c. Proof. intros H1 H2 i Hi H. apply H2; [exact Hi| apply H1; assumption]. Qed.

Section MW.
Variables (st0 : mstate) (L0 : mled) (BL0 : list blk) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVC x0 st0 L0 BL0 LS0.

Definition NEWG (st : mstate) (m : aptr) : Prop :=
  ~ gempty st m /\ (m_sizeclass (MR st m) < 48 \/ m_sizeclass (MR st m) = 63) /\ m_mem (MR st m) <> None
  /\ fsub (fmask (MR st m)) (mask_upto (m_last_idx (MR st m))).

Definition PEND (st : mstate) (LS : lhead -> list aptr) (m : aptr) : Prop :=
  data_of (MR st m) = data_of meta0 /\ ~ live_group st m /\ (forall h, ~ In m (LS h)).

Record MWA (st : mstate) (LS : lhead -> list aptr) (N : list aptr) : Prop := mkMWA {
  ma_lists : lists_ok st LS;
  ma_curi : CURI st;
  ma_marith : MARITH st;
  ma_free : exists k, LS LFree = skipn k (LS0 LFree) /\ (forall m, In m (firstn k (LS0 LFree)) -> In m N)
            /\ (forall m, In m N -> In m (firstn k (LS0 LFree)) \/ s_metas st0 !! m = None)
            /\ Z.of_nat (length N) = Z.of_nat k + (nmeta st - nmeta st0);
  ma_old : forall b m, hosts st0 b m -> ~ In m N /\ GEOM (MR st m) = GEOM (MR st0 m) /\ fsub (fmask (MR st m)) (fmask (MR st0 m));
  ma_hosts : forall b m, hosts st b m -> hosts st0 b m \/ In m N;
  ma_new : forall m, In m N -> ~ (exists b, hosts st0 b m) /\ s_metas st !! m <> None /\ (NEWG st m \/ PEND st LS m);
  ma_nd : NoDup N;
  ma_pres : forall x, s_metas st !! x <> None -> s_metas st0 !! x <> None \/ In x N;
  ma_keep : forall x, s_metas st0 !! x <> None -> s_metas st !! x <> None;
  ma_carve : nmeta st = nmeta st0 \/ LS LFree = [];
  ma_regions : forall rid r, s_regions st0 !! rid = Some r -> r_kind r <> RKBrk -> s_regions st !! rid = Some r;
  ma_rid : (s_next_rid st0 <= s_next_rid st)%N;
  ma_slots : forall s v, s_slots st !! s = Some v -> s_slots st0 !! s = Some v \/ In (fst v) N
}.

Record MW (st : mstate) (LS : lhead -> list aptr) (N : list aptr) (sc : Z) : Prop := mkMW {
  mw_a : MWA st LS N;
  mw_fdata : forall m, In m (LS LFree) -> data_of (MR st m) = data_of meta0;
  mw_above : forall b m, hosts st0 b m -> sc <= m_sizeclass (MR st0 m) -> data_of (MR st m) = data_of (MR st0 m) /\ hosts st b m;
  mw_act : forall sc', sc <= sc' -> active st sc' = active st0 sc' /\ LS (LActive sc') = LS0 (LActive sc');
  mw_actok : forall sc' m, In m (LS (LActive sc')) -> live_group st m /\ m_sizeclass (MR st m) = sc';
  mw_fnl : forall m, In m (LS LFree) -> ~ live_group st m
}.

Lemma MW_init sc : CURI st0 -> MARITH st0 -> MW st0 LS0 [] sc.
Proof.
  intros C M. pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  assert (LO : lists_ok st0 LS0) by (destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; auto).
  constructor; [constructor| | | | |].
  - exact LO.
  - exact C.
  - exact M.
  - exists 0%nat. split; [reflexivity|]. split; [intros m []|]. split; [intros m []| cbn; lia].
  - intros b m H. split; [intros []|]. split; [reflexivity| apply fsub_refl].
  - intros b m H. left. exact H.
  - intros m [].
  - constructor.
  - intros x H. left. exact H.
  - intros x H. exact H.
  - left. reflexivity.
  - intros rid r H _. exact H.
  - apply N.le_refl.
  - intros s v H. left. exact H.
  - intros m Hm. pose proof (il_free _ _ IL m Hm) as F. rewrite F. reflexivity.
  - intros b m H _. split; [reflexivity| exact H].
  - intros sc' _. split; reflexivity.
  - intros sc' m H. exact (proj2 (il_active _ _ IL sc' m H)).
  - intros m Hm [b [ai Hb]]. pose proof (il_free _ _ IL m Hm) as F. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Hm' & Hmem & _).
    cbn in Hm'. injection Hm' as <-. rewrite F in Hmem. discriminate.
Qed.

Lemma gempty_fsub_mono r r' : GEOM r' = GEOM r -> fsub (fmask r') (fmask r) -> fsub (fmask r) (mask_upto (m_last_idx r)) ->
  fmask r' = mask_upto (m_last_idx r') -> fmask r = mask_upto (m_last_idx r).
Proof.
  intros G S B E. apply GEOM_eq in G as (_ & Li & _). rewrite Li in E. apply Z.bits_inj'. intros i Hi.
  destruct (Z.testbit (fmask r) i) eqn:T1; destruct (Z.testbit (mask_upto (m_last_idx r)) i) eqn:T2; auto.
  - rewrite (B i Hi T1) in T2. discriminate.
  - rewrite <- E in T2. rewrite (S i Hi T2) in T1. discriminate.
Qed.

Lemma MW_step st LS N sc st' LS' : MW st LS N sc ->
  lists_ok st' LS' -> (forall h, h <> LActive sc -> LS' h = LS h) -> (forall x, In x (LS' (LActive sc)) -> In x (LS (LActive sc))) ->
  (forall x, MR st' x = MR st x \/ (In x (LS (LActive sc)) /\ GEOM (MR st' x) = GEOM (MR st x) /\ fsub (fmask (MR st' x)) (fmask (MR st x)))) ->
  (forall b m, hosts st' b m <-> hosts st b m) ->
  MFR st st' -> (forall sc', sc' <> sc -> active st' sc' = active st sc') -> s_slots st' = s_slots st ->
  MW st' LS' N (sc + 1).
Proof.
  intros [[W1 W2 W3 W4 W6 W7 W8 W9 W10 W10k W11 W16 W17 W18] W5 W12 W13 W14 W15] LO' ELS SUB MRC HO MF ACT SL.
  assert (FR : LS' LFree = LS LFree) by (apply ELS; discriminate).
  assert (CLS : forall x, In x (LS (LActive sc)) -> m_sizeclass (MR st x) = sc) by (intros x Hx; exact (proj2 (W14 sc x Hx))).
  assert (NL : forall m, (forall h, ~ In m (LS h)) -> MR st' m = MR st m).
  { intros m Hm. destruct (MRC m) as [E|(Hm' & _)]; [exact E| exfalso; exact (Hm _ Hm')]. }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
  { intros x. split; intros H E; apply H; apply (mf_keys _ _ MF); exact E. }
  constructor; [constructor| | | | |].
  - exact LO'.
  - exact (CURI_frame _ _ W2 MF).
  - exact (MARITH_frame _ _ W3 MF).
  - rewrite FR, (nmeta_keys _ _ (mf_keys _ _ MF)). exact W4.
  - intros b m H. destruct (W6 b m H) as (N1 & G1 & F1). split; [exact N1|].
    destruct (MRC m) as [E|(_ & G2 & F2)]; [rewrite E; split; assumption|]. split; [congruence| exact (fsub_trans _ _ _ F2 F1)].
  - intros b m H. apply HO in H. exact (W7 b m H).
  - intros m Hm. destruct (W8 m Hm) as (N1 & P1 & C1). split; [exact N1|]. split; [apply KEYS; exact P1|].
    destruct C1 as [(NE1 & C1 & M1 & F1)|(D1 & U1 & L1)].
    + left. destruct (MRC m) as [E|(_ & G2 & F2)].
      * unfold NEWG, gempty. rewrite E. auto.
      * split.
        -- intros He. apply NE1. unfold gempty in *. exact (gempty_fsub_mono _ _ G2 F2 F1 He).
        -- apply GEOM_eq in G2 as (Mm & Li & _ & Sc & _). rewrite Sc, Li, Mm. split; [exact C1|]. split; [exact M1|].
           exact (fsub_trans _ _ _ F2 F1).
    + right. unfold PEND. rewrite (NL m L1). split; [exact D1|]. split.
      * intros [b Hb]. apply U1. exists b. apply HO. exact Hb.
      * intros h Hh. destruct (decide (h = LActive sc)) as [->|NEh]; [apply (L1 (LActive sc)); apply SUB; exact Hh|].
        rewrite ELS in Hh by exact NEh. exact (L1 h Hh).
  - exact W9.
  - intros x Hx. apply W10. apply KEYS. exact Hx.
  - intros x Hx. apply KEYS. exact (W10k x Hx).
  - rewrite FR. rewrite (nmeta_keys _ _ (mf_keys _ _ MF)). exact W11.
  - intros rid r H K. rewrite (mf_regions _ _ MF). exact (W16 rid r H K).
  - rewrite (mf_rid _ _ MF). exact W17.
  - intros s v H. rewrite SL in H. exact (W18 s v H).
  - intros m Hm. rewrite FR in Hm. destruct (MRC m) as [E|(Hm' & _)]; [rewrite E; exact (W5 m Hm)|].
    exfalso. pose proof (lo_disj _ _ W1 _ _ m Hm Hm') as E. discriminate.
  - intros b m H Hc. destruct (W12 b m H ltac:(lia)) as [E Hb]. split; [| apply HO; exact Hb].
    destruct (MRC m) as [E2|(Hm & _)]; [rewrite E2; exact E|]. exfalso. pose proof (CLS m Hm) as Cm.
    apply data_of_eq in E as (_ & _ & _ & _ & _ & Esc & _). rewrite Esc in Cm. lia.
  - intros sc' Hc. destruct (W13 sc' ltac:(lia)) as [E1 E2]. split; [rewrite ACT by lia; exact E1| rewrite ELS by (intros E; injection E; lia); exact E2].
  - intros sc' m Hm. destruct (decide (LActive sc' = LActive sc)) as [Eq|NEq].
    + injection Eq as ->. apply SUB in Hm. destruct (W14 sc m Hm) as ([b Hb] & Ec). split; [exists b; apply HO; exact Hb|].
      destruct (MRC m) as [E2|(_ & G2 & _)]; [rewrite E2; exact Ec| apply GEOM_eq in G2 as (_ & _ & _ & Sc & _); rewrite Sc; exact Ec].
    + rewrite ELS in Hm by exact NEq. destruct (W14 sc' m Hm) as ([b Hb] & Ec). split; [exists b; apply HO; exact Hb|].
      destruct (MRC m) as [E2|(Hm2 & _)]; [rewrite E2; exact Ec|]. exfalso. pose proof (lo_disj _ _ W1 _ _ m Hm Hm2). congruence.
  - intros m Hm [b Hb]. rewrite FR in Hm. apply (W15 m Hm). exists b. apply HO. exact Hb.
Qed.

Definition RELm (st : mstate) (mem : aptr -> Prop) (a : mstate) : Prop :=
  forall x, MR a x = MR st x \/ (mem x /\ GEOM (MR a x) = GEOM (MR st x) /\ fsub (fmask (MR a x)) (fmask (MR st x))).

Lemma RELm_refl st mem : RELm st mem st. Proof. intros x. left. reflexivity. Qed.
Lemma RELm_trans st mem a b : RELm st mem a -> RELm a mem b -> RELm st mem b.
Proof.
  intros H1 H2 x. destruct (H2 x) as [E2|(M2 & G2 & F2)]; destruct (H1 x) as [E1|(M1 & G1 & F1)].
  - left. congruence.
  - right. rewrite E2. auto.
  - right. rewrite <- E1. auto.
  - right. split; [exact M2|]. split; [congruence| exact (fsub_trans _ _ _ F2 F1)].
Qed.
Lemma RELm_metas st mem a : s_metas a = s_metas st -> RELm st mem a.
Proof. intros E x. left. unfold MR, get_meta_rec. rewrite E. reflexivity. Qed.
Lemma RELm_upd st mem a x f : RELm st mem a -> mem x -> GEOM (f (MR a x)) = GEOM (MR a x) -> fsub (fmask (f (MR a x))) (fmask (MR a x)) ->
  RELm st mem (upd_meta x f a).
Proof.
  intros H Mx G F. apply (RELm_trans st mem a); [exact H|]. intros y.
  destruct (aptr_eqb_spec y x) as [->|NE].
  - right. assert (E : MR (upd_meta x f a) x = f (MR a x)) by (unfold MR; apply get_meta_rec_upd_same). rewrite E. auto.
  - left. unfold MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity.
Qed.
Lemma RELm_dequeue st mem LS h m : lists_ok st LS -> In m (LS h) -> (forall y, In y (LS h) -> mem y) -> RELm st mem (dequeue h m st).
Proof.
  intros LO Hm MEM x. destruct (aptr_eqb_spec x m) as [->|NE].
  - right. split; [apply MEM; exact Hm|]. pose proof (dequeue_data h m st m) as D. split; [exact (GEOM_data _ _ D)| rewrite (fmask_data _ _ D); apply fsub_refl].
  - destruct (optr_eqb_spec (m_prev (MR st m)) (Some x)) as [Ep|Np].
    + right. destruct (lists_prev_in _ _ LO h m Hm) as (y & Hy & Ey & _). rewrite Ep in Ey. injection Ey as <-. split; [apply MEM; exact Hy|].
      pose proof (dequeue_data h m st x) as D. split; [exact (GEOM_data _ _ D)| rewrite (fmask_data _ _ D); apply fsub_refl].
    + destruct (optr_eqb_spec (m_next (MR st m)) (Some x)) as [En|Nn].
      * right. destruct (lists_next_in _ _ LO h m Hm) as (y & Hy & Ey & _). rewrite En in Ey. injection Ey as <-. split; [apply MEM; exact Hy|].
        pose proof (dequeue_data h m st x) as D. split; [exact (GEOM_data _ _ D)| rewrite (fmask_data _ _ D); apply fsub_refl].
      * left. unfold MR, get_meta_rec. rewrite (dequeue_metas_other h m st x NE Np Nn). reflexivity.
Qed.

Lemma MFR_refl s : MFR s s. Proof. constructor; reflexivity. Qed.
Lemma MFR_trans a b c : MFR a b -> MFR b c -> MFR a c.
Proof. intros [] []. constructor; try congruence. intros x. etransitivity; eauto. Qed.

Definition TAFR (st : mstate) (LS : lhead -> list aptr) (st1 : mstate) (LS1 : lhead -> list aptr) : Prop :=
  (forall m, (forall h, ~ In m (LS h)) -> MR st1 m = MR st m /\ (forall h, ~ In m (LS1 h))) /\ (forall b m, hosts st1 b m <-> hosts st b m).

Definition TAP (st1 : mstate) (sc first : Z) : Prop :=
  first <> 0 -> exists g bg, active st1 sc = Some g /\ hosts st1 bg g /\ hosts st0 bg g /\ m_sizeclass (MR st1 g) = sc
    /\ 0 <= ctz32 first <= m_last_idx (MR st1 g) /\ Z.testbit (fmask (MR st1 g)) (ctz32 first) = false.

Definition TAO (st : mstate) (LS : lhead -> list aptr) (st1 : mstate) (LS1 : lhead -> list aptr) (sc first : Z) : Prop :=
  (forall sc', sc' <> sc -> active st1 sc' = active st sc' /\ LS1 (LActive sc') = LS (LActive sc')) /\ (first = 0 -> active st1 sc = None).

Section TA.
Variables (T : Type) (sc : Z) (st : mstate) (LS : lhead -> list aptr) (N : list aptr).
Variables (k : mstate -> Z -> M T) (bail : M T) (c : Z) (n : nat) (Q : Z -> nat -> T -> Prop).
Hypothesis W : MW st LS N sc.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis CONT : forall st1 LS1 first, MW st1 LS1 N (sc + 1) -> TAP st1 sc first -> Phi st1 = Phi st -> Psi st1 = Psi st -> TAFR st LS st1 LS1 ->
  TAO st LS st1 LS1 sc first -> apw ecost (k st1 first) c n Q.

Let mem := fun x => In x (LS (LActive sc)).

Lemma mem_facts x : In x (LS (LActive sc)) ->
  exists b ai, s_groups st0 !! b = Some (mkGhdr (Some x) ai) /\ group_ok x0 st0 LS0 x b ai /\ data_of (MR st x) = data_of (MR st0 x) /\ hosts st b x
             /\ m_sizeclass (MR st0 x) = sc.
Proof.
  intros Hx. pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  destruct (mw_act _ _ _ _ W sc ltac:(lia)) as [_ EL]. rewrite EL in Hx.
  destruct (il_active _ _ IL sc x Hx) as (_ & [b [ai Hb]] & Ec).
  destruct (mw_above _ _ _ _ W b x (ex_intro _ ai Hb) ltac:(lia)) as [E Hs].
  exists b, ai. split; [exact Hb|]. split; [exact (ig_ok _ _ _ IG _ _ _ Hb)|]. auto.
Qed.

Definition LINKw (a : mstate) (LSa : lhead -> list aptr) : Prop :=
  lists_ok a LSa /\ (forall h, h <> LActive sc -> LSa h = LS h) /\ (forall x, In x (LSa (LActive sc)) -> In x (LS (LActive sc)))
  /\ RELm st mem a /\ (forall b m, hosts a b m <-> hosts st b m)
  /\ MFR st a /\ (forall sc', sc' <> sc -> active a sc' = active st sc') /\ s_slots a = s_slots st.
Definition LINK (a : mstate) (LSa : lhead -> list aptr) : Prop := LINKw a LSa /\ (forall x, data_of (MR a x) = data_of (MR st x)).

Lemma LINK_refl : LINK st LS.
Proof.
  split; [| intros; reflexivity].
  split; [exact (ma_lists _ _ _ (mw_a _ _ _ _ W))|]. split; [intros; reflexivity|]. split; [auto|]. split; [apply RELm_refl|].
  split; [tauto|]. split; [apply MFR_refl| split; [intros; reflexivity| reflexivity]].
Qed.

Lemma LEAF a LSa first : LINKw a LSa -> TAP a sc first -> (first = 0 -> active a sc = None) -> apw ecost (k a first) c n Q.
Proof.
  intros (L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9) TP TZ. apply (CONT a LSa first); [| exact TP| | | |].
  5:{ split; [| exact TZ]. intros sc' NE. split; [exact (L8 sc' NE)| apply L2; intros E; injection E; lia]. }
  - exact (MW_step st LS N sc a LSa W L1 L2 L3 L4 L6 L7 L8 L9).
  - rewrite !Phi_regsum, (regsum_ext _ _ _ (mf_regions _ _ L7)). unfold brk_dead_w. rewrite (mf_brk _ _ L7). reflexivity.
  - unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ (mf_regions _ _ L7)), (mf_areas _ _ L7). reflexivity.
  - split; [| exact L6]. intros m Hm. split.
    + destruct (L4 m) as [E|(Mm & _)]; [exact E| exfalso; exact (Hm _ Mm)].
    + intros h Hh. destruct (decide (h = LActive sc)) as [->|NE]; [exact (Hm _ (L3 m Hh))| rewrite (L2 h NE) in Hh; exact (Hm h Hh)].
Qed.

Lemma fin_leaf a LSa m mask : LINKw a LSa -> m_sizeclass (MR a m) = sc -> active a sc = Some m -> In m (LSa (LActive sc)) ->
  m_avail (MR a m) = mask -> mask <> 0 -> 0 <= mask ->
  (forall i, 0 <= i -> Z.testbit mask i = true -> Z.testbit (m_freed (MR a m)) i = false /\ i <= m_last_idx (MR a m)) ->
  apw ecost (ta_fin a m mask k) c n Q.
Proof.
  intros LK Ecl HA Hm AM MNZ MNN BITS. unfold ta_fin.
  destruct LK as (L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9).
  destruct (lowbit_idiom mask ltac:(lia)) as (kk & Hk & Elb & Ectz & Tk & Pos & Tsub).
  set (a' := upd_meta m (m_set_avail (mask - lowbit mask)) a).
  assert (MRm : MR a' m = m_set_avail (mask - lowbit mask) (MR a m)) by (unfold a', MR; apply get_meta_rec_upd_same).
  assert (MRo : forall x, x <> m -> MR a' x = MR a x) by (intros x NE; unfold a', MR; apply get_meta_rec_upd_other; exact NE).
  assert (Pm : s_metas a !! m <> None) by (apply present_of_next; exact (lists_in_next_some _ _ L1 _ m Hm)).
  assert (FS : fsub (fmask (MR a' m)) (fmask (MR a m))).
  { rewrite MRm. unfold fmask, m_set_avail. cbn. intros i Hi. rewrite !Z.lor_spec, Tsub by exact Hi. rewrite <- AM.
    destruct (Z.testbit (m_avail (MR a m)) i); cbn; [reflexivity| tauto]. }
  apply (LEAF a' LSa (lowbit mask)).
  - split; [apply (lists_ok_links a a' LSa L1); [intros h; unfold a'; apply get_head_upd_meta|]; intros x; destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite MRm; split; reflexivity| rewrite (MRo x NE); split; reflexivity]|].
    split; [exact L2|]. split; [exact L3|].
    split; [apply (RELm_trans st mem a); [exact L4|]; intros x; destruct (aptr_eqb_spec x m) as [->|NE]; [right; split; [exact (L3 m Hm)| split; [rewrite MRm; apply GEOM_set_avail| exact FS]]| left; exact (MRo x NE)]|].
    split; [intros b mm; unfold hosts, a'; cbn; exact (L6 b mm)|].
    split; [apply (MFR_trans st a); [exact L7|]; constructor; try reflexivity; intros x; unfold a'; rewrite s_metas_upd_meta, lookup_insert_None; split; [intros [H _]; exact H| intros H; split; [exact H| intros <-; exact (Pm H)]]|].
    split; [intros sc' NE; rewrite active_upd_meta; exact (L8 sc' NE)| exact L9].
  - intros _. exists m. destruct (mem_facts m (L3 m Hm)) as (b & ai & Hb & _ & _ & Hs & Ec).
    exists b. split; [rewrite active_upd_meta; exact HA|]. split; [unfold hosts, a'; cbn; apply L6; exact Hs|]. split; [exists ai; exact Hb|].
    rewrite MRm. cbn [m_sizeclass m_last_idx m_set_avail]. rewrite Ectz.
    destruct (BITS kk Hk Tk) as [Fk Lk].
    split; [exact Ecl|].
    split; [lia|]. unfold fmask, m_set_avail. cbn [m_avail m_freed]. rewrite Z.lor_spec, Tsub by exact Hk. rewrite Z.eqb_refl, Fk. cbn. rewrite Bool.andb_false_r. reflexivity.
  - intros E0. exfalso. rewrite Elb in E0. pose proof (Z.pow_pos_nonneg 2 kk ltac:(lia) Hk). lia.
Qed.

Lemma MFR_dequeue_l a LSa h m : lists_ok a LSa -> In m (LSa h) -> MFR a (dequeue h m a).
Proof.
  intros LO Hm. destruct (dequeue_frame h m a) as (D1 & _ & D3 & D4 & _ & _ & _ & _ & _ & D10).
  assert (Pm : s_metas a !! m <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h m Hm)).
  constructor; try (apply D10); auto.
  intros x. split.
  - intros Hx. destruct (s_metas a !! x) eqn:E; [| reflexivity]. exfalso. apply (dequeue_keys_mono h m a x) in Hx; [exact Hx| rewrite E; discriminate].
  - intros Hx. destruct (s_metas (dequeue h m a) !! x) eqn:E; [| reflexivity]. exfalso.
    destruct (dequeue_keys h m a x ltac:(rewrite E; discriminate)) as [H|[->|[H|H]]]; [exact (H Hx)| exact (Pm Hx)| |].
    + destruct (lists_prev_in _ _ LO h m Hm) as (y & Hy & Ey & _). fold (MR a m) in H. rewrite H in Ey. injection Ey as <-.
      exact (present_of_next _ _ (lists_in_next_some _ _ LO h x Hy) Hx).
    + destruct (lists_next_in _ _ LO h m Hm) as (y & Hy & Ey & _). fold (MR a m) in H. rewrite H in Ey. injection Ey as <-.
      exact (present_of_next _ _ (lists_in_next_some _ _ LO h x Hy) Hx).
Qed.

Lemma MFR_same_metas a b : s_metas b = s_metas a -> s_regions b = s_regions a -> s_areas b = s_areas a -> s_next_rid b = s_next_rid a ->
  c_avail_meta_count (s_ctx b) = c_avail_meta_count (s_ctx a) -> c_avail_meta_area_count (s_ctx b) = c_avail_meta_area_count (s_ctx a) ->
  c_avail_meta (s_ctx b) = c_avail_meta (s_ctx a) -> c_avail_meta_areas (s_ctx b) = c_avail_meta_areas (s_ctx a) ->
  c_meta_area_tail (s_ctx b) = c_meta_area_tail (s_ctx a) -> c_meta_alloc_shift (s_ctx b) = c_meta_alloc_shift (s_ctx a) ->
  c_brk (s_ctx b) = c_brk (s_ctx a) -> c_init_done (s_ctx b) = c_init_done (s_ctx a) -> MFR a b.
Proof. intros. constructor; auto. intros x. rewrite H. tauto. Qed.

Lemma ta_final a LSa m3 : LINK a LSa -> active a sc = Some m3 -> In m3 (LSa (LActive sc)) ->
  apw ecost (activate_group m3 a (fun st4 mask => guard 40 (negb (mask =? 0))
                (ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail) c n Q.
Proof.
  intros ((L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9) & L5) HA Hm. unfold activate_group. fold (MR a m3).
  apply apw_guard. intros A0. apply Z.eqb_eq in A0.
  set (act := match m_mem (MR a m3) with Some _ => mask_upto (group_active_idx a (default (0%N, -1) (m_mem (MR a m3)))) | None => 0 end).
  set (fm := m_freed (MR a m3)).
  set (a4 := upd_meta m3 (fun r => m_set_avail (Z.land fm act) (m_set_freed (Z.ldiff fm act) r)) a).
  apply apw_guard. intros G40. apply Bool.negb_true_iff, Z.eqb_neq in G40.
  assert (MR4 : MR a4 m3 = m_set_avail (Z.land fm act) (m_set_freed (Z.ldiff fm act) (MR a m3))) by (unfold a4, MR; apply get_meta_rec_upd_same).
  assert (MR4o : forall x, x <> m3 -> MR a4 x = MR a x) by (intros x NE; unfold a4, MR; apply get_meta_rec_upd_other; exact NE).
  set (a5 := decay_bounces (m_sizeclass (get_meta_rec a4 m3)) a4).
  assert (MR5 : forall x, MR a5 x = MR a4 x) by (intros x; unfold a5, MR, get_meta_rec; rewrite s_metas_decay_bounces; reflexivity).
  assert (Pm : s_metas a !! m3 <> None) by (apply present_of_next; exact (lists_in_next_some _ _ L1 _ m3 Hm)).
  destruct (mem_facts m3 (L3 m3 Hm)) as (b3 & ai3 & Hb3 & GO3 & E30 & Hs3 & Ec3).
  pose proof (g_masks _ _ _ _ _ _ GO3) as (Wa & Wf & Wab & Wfb & Wd & Wi).
  assert (Dm : data_of (MR a m3) = data_of (MR st0 m3)) by (rewrite L5; exact E30).
  apply data_of_eq in Dm as (Em & Eav & Efr & Eli & Efa & Esc & Eml).
  apply (fin_leaf a5 LSa m3 (Z.land fm act)).
  - split; [apply (lists_ok_links a a5 LSa L1); [intros h; unfold a5, a4; destruct h; cbn; unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity|];
            intros x; rewrite MR5; destruct (aptr_eqb_spec x m3) as [->|NE]; [rewrite MR4; split; reflexivity| rewrite (MR4o x NE); split; reflexivity]|].
    split; [exact L2|]. split; [exact L3|].
    split; [apply (RELm_trans st mem a); [exact L4|]; intros x; rewrite MR5; destruct (aptr_eqb_spec x m3) as [->|NE];
            [right; split; [exact (L3 m3 Hm)| rewrite MR4; split; [reflexivity| rewrite fmask_activate by exact A0; apply fsub_refl]]| left; exact (MR4o x NE)]|].
    split; [intros b m; unfold hosts, a5, a4; rewrite s_groups_decay_bounces; cbn; exact (L6 b m)|].
    split; [apply (MFR_trans st a); [exact L7|]; constructor; unfold a5; rewrite ?s_regions_decay_bounces, ?s_areas_decay_bounces, ?s_metas_decay_bounces, ?s_next_rid_decay_bounces,
              ?c_avail_meta_count_decay_bounces, ?c_avail_meta_area_count_decay_bounces, ?c_avail_meta_decay_bounces, ?c_avail_meta_areas_decay_bounces,
              ?c_meta_area_tail_decay_bounces, ?c_meta_alloc_shift_decay_bounces, ?c_brk_decay_bounces, ?c_init_done_decay_bounces; try reflexivity;
            intros x; unfold a4; rewrite s_metas_upd_meta, lookup_insert_None; split; [intros [H _]; exact H| intros H; split; [exact H| intros <-; exact (Pm H)]]|].
    split; [| unfold a5; rewrite s_slots_decay_bounces; exact L9].
    intros sc' NE. unfold a5, active, ctx. rewrite c_active_decay_bounces. change (c_active (s_ctx a4) !! sc') with (active a sc'). exact (L8 sc' NE).
  - rewrite MR5, MR4. cbn. rewrite Esc. exact Ec3.
  - unfold a5, active, ctx. rewrite c_active_decay_bounces. change (c_active (s_ctx a4) !! sc) with (active a sc). exact HA.
  - exact Hm.
  - rewrite MR5, MR4. reflexivity.
  - exact G40.
  - apply Z.land_nonneg. left. unfold fm. rewrite Efr. exact Wf.
  - intros i Hi Tb. rewrite MR5, MR4. cbn. rewrite Z.land_spec in Tb. apply Bool.andb_true_iff in Tb as [T1 T2].
    rewrite Z.ldiff_spec, T1, T2. split; [reflexivity|]. unfold fm in T1. rewrite Efr in T1. rewrite Eli. exact (Wfb i Hi T1).
Qed.

Lemma LINK_head a LSa x : LINK a LSa -> active a sc = Some x -> exists tl, LSa (LActive sc) = x :: tl.
Proof.
  intros ((L1 & _) & _) HA. pose proof (lo_head _ _ L1 (LActive sc)) as E. change (get_head a (LActive sc)) with (active a sc) in E.
  rewrite HA in E. destruct (LSa (LActive sc)) as [|y tl]; [discriminate| injection E as ->; exists tl; reflexivity].
Qed.

Lemma LINK_rotate a LSa x tl y : LINK a LSa -> LSa (LActive sc) = x :: tl -> m_next (MR a x) = Some y ->
  LINK (set_active sc (Some y) a) (fupd LSa (LActive sc) (tl ++ [x])) /\ active (set_active sc (Some y) a) sc = Some y
  /\ In y (fupd LSa (LActive sc) (tl ++ [x]) (LActive sc)).
Proof.
  intros ((L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9) & L5) E Hn.
  pose proof (lists_rotate a LSa L1 (LActive sc) x tl y E Hn) as LO'. change (set_head (LActive sc) (Some y) a) with (set_active sc (Some y) a) in LO'.
  assert (HA' : active (set_active sc (Some y) a) sc = Some y) by (rewrite active_set_active, Z.eqb_refl; reflexivity).
  split; [| split; [exact HA'|]].
  - split; [| intros x'; rewrite <- (L5 x'); reflexivity].
    split; [exact LO'|]. split; [intros h NE; rewrite fupd_ne by exact NE; exact (L2 h NE)|].
    split; [intros x' Hx'; rewrite fupd_eq in Hx'; apply L3; rewrite E; apply in_app_iff in Hx' as [H|[<-|[]]]; [right; exact H| left; reflexivity]|].
    split; [apply (RELm_trans st mem a); [exact L4| apply RELm_metas; reflexivity]|].
    split; [intros b m; unfold hosts; cbn; exact (L6 b m)|].
    split; [apply (MFR_trans st a); [exact L7|]; apply MFR_same_metas; reflexivity|].
    split; [| exact L9].
    intros sc' NE. rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| exact (L8 sc' NE)].
  - pose proof (lo_head _ _ LO' (LActive sc)) as Eh. change (get_head (set_active sc (Some y) a) (LActive sc)) with (active (set_active sc (Some y) a) sc) in Eh.
    rewrite HA' in Eh. destruct (fupd LSa (LActive sc) (tl ++ [x]) (LActive sc)) as [|z r]; [discriminate| injection Eh as ->; left; reflexivity].
Qed.

Lemma LINK_dequeue a LSa x tl : LINK a LSa -> LSa (LActive sc) = x :: tl ->
  LINK (dequeue (LActive sc) x a) (fupd LSa (LActive sc) tl) /\ active (dequeue (LActive sc) x a) sc = head_of tl.
Proof.
  intros ((L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9) & L5) E.
  assert (Hx : In x (LSa (LActive sc))) by (rewrite E; left; reflexivity).
  pose proof (lists_dequeue a LSa L1 (LActive sc) x [] tl ltac:(rewrite E; reflexivity)) as LO'. cbn [app] in LO'.
  destruct (dequeue_frame (LActive sc) x a) as (D1 & _ & D3 & D4 & D5 & D6 & _ & _ & _ & D10).
  split.
  - split; [| intros x'; rewrite dequeue_data; exact (L5 x')].
    split; [exact LO'|]. split; [intros h NE; rewrite fupd_ne by exact NE; exact (L2 h NE)|].
    split; [intros x' Hx'; rewrite fupd_eq in Hx'; apply L3; rewrite E; right; exact Hx'|].
    split; [apply (RELm_trans st mem a); [exact L4| apply (RELm_dequeue a mem LSa (LActive sc) x L1 Hx); intros y Hy; exact (L3 y Hy)]|].
    split; [intros b m; unfold hosts; rewrite D5; exact (L6 b m)|].
    split; [apply (MFR_trans st a); [exact L7| exact (MFR_dequeue_l a LSa (LActive sc) x L1 Hx)]|].
    split; [| rewrite D6; exact L9].
    intros sc' NE. change (active (dequeue (LActive sc) x a) sc') with (get_head (dequeue (LActive sc) x a) (LActive sc')). rewrite dequeue_head.
    destruct (decide (LActive sc' = LActive sc)) as [Eq|_]; [injection Eq; congruence| exact (L8 sc' NE)].
  - pose proof (lo_head _ _ LO' (LActive sc)) as Eh. rewrite fupd_eq in Eh. exact Eh.
Qed.

Lemma LINK_setai a LSa g v : LINK a LSa -> LINK (set_group_active_idx g v a) LSa.
Proof.
  intros ((L1 & L2 & L3 & L4 & L6 & L7 & L8 & L9) & L5).
  assert (EM : s_metas (set_group_active_idx g v a) = s_metas a) by (apply s_metas_set_group_active_idx).
  assert (HO : forall b m, hosts (set_group_active_idx g v a) b m <-> hosts a b m).
  { intros b m. unfold hosts. rewrite lookup_set_group_active_idx. destruct (aptr_eqb_spec b g) as [->|NE]; [|tauto].
    destruct (s_groups a !! g) as [[mo ai]|]; cbn; split; intros [ai' H]; try discriminate; injection H as ->; eauto. }
  assert (CX : s_ctx (set_group_active_idx g v a) = s_ctx a) by (unfold set_group_active_idx; destruct (get_group a g); reflexivity).
  assert (RG : s_regions (set_group_active_idx g v a) = s_regions a) by (unfold set_group_active_idx; destruct (get_group a g); reflexivity).
  assert (AR : s_areas (set_group_active_idx g v a) = s_areas a) by (unfold set_group_active_idx; destruct (get_group a g); reflexivity).
  assert (NR : s_next_rid (set_group_active_idx g v a) = s_next_rid a) by (unfold set_group_active_idx; destruct (get_group a g); reflexivity).
  split; [| intros x; unfold MR, get_meta_rec; rewrite EM; exact (L5 x)].
  split; [apply (lists_ok_same_metas a _ LSa L1 EM); intros h; destruct h; unfold get_head, active, ctx; rewrite CX; reflexivity|].
  split; [exact L2|]. split; [exact L3|].
  split; [apply (RELm_trans st mem a); [exact L4| apply RELm_metas; exact EM]|].
  split; [intros b m; rewrite HO; exact (L6 b m)|].
  split; [apply (MFR_trans st a); [exact L7| apply MFR_same_metas; rewrite ?CX; auto]|].
  split; [| unfold set_group_active_idx; destruct (get_group a g); exact L9].
  intros sc' NE. unfold active, ctx. rewrite CX. exact (L8 sc' NE).
Qed.

Theorem ta_walk : apw ecost (try_avail sc st k bail) c n Q.
Proof.
  unfold try_avail. destruct (active st sc) as [m|] eqn:HA.
  2:{ apply (LEAF st LS 0 (proj1 LINK_refl)); [intros E; exfalso; exact (E eq_refl)| intros _; exact HA]. }
  fold (MR st m).
  destruct (LINK_head st LS m LINK_refl HA) as (rest & EL).
  assert (Hm : In m (LS (LActive sc))) by (rewrite EL; left; reflexivity).
  destruct (mem_facts m Hm) as (bm & aim & Hbm & GOm & E0m & Hsm & Ecm).
  apply data_of_eq in E0m as (_ & Eav0 & Efr0 & Eli0 & _ & Esc0 & _).
  pose proof (g_masks _ _ _ _ _ _ GOm) as (Wa & Wf & Wab & Wfb & Wd & Wi). pose proof (g_ai _ _ _ _ _ _ GOm) as AIm.
  destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ apply (fin_leaf st LS m _ (proj1 LINK_refl)); [rewrite Esc0; exact Ecm| exact HA| exact Hm| reflexivity| exact ANZ| rewrite Eav0; exact Wa|].
      intros i Hi Tb. rewrite Eav0 in Tb. rewrite Efr0, Eli0. split.
      - destruct (Z.testbit (m_freed (MR st0 m)) i) eqn:F; [exfalso; exact (Wd i Hi Tb F)| reflexivity].
      - pose proof (Wab i Hi Tb). lia. }

  assert (STEP1 : (exists st1 m1 LS1,
      (if m_freed (MR st m) =? 0
       then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
       else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
      /\ LINK st1 LS1 /\ active st1 sc = Some m1 /\ In m1 (LS1 (LActive sc)))
    \/ ((if m_freed (MR st m) =? 0
         then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
         else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = None
        /\ m_freed (MR st m) = 0 /\ LINK (dequeue (LActive sc) m st) (fupd LS (LActive sc) rest) /\ active (dequeue (LActive sc) m st) sc = None)).
  { destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (LINK_dequeue st LS m rest LINK_refl EL) as [LKd HAd]. rewrite HAd.
      destruct rest as [|m1 rest'].
      + right. split; [reflexivity|]. split; [exact FZ| split; [exact LKd| reflexivity]].
      + left. exists (dequeue (LActive sc) m st), m1, (fupd LS (LActive sc) (m1 :: rest')). split; [reflexivity|]. split; [exact LKd|].
        split; [exact HAd| rewrite fupd_eq; left; reflexivity].
    - destruct (lists_next_in _ _ (ma_lists _ _ _ (mw_a _ _ _ _ W)) _ m Hm) as (mn & _ & Hn & _). rewrite Hn.
      destruct (LINK_rotate st LS m rest mn LINK_refl EL Hn) as (LK1 & HA1 & Hin1).
      left. eexists _, mn, _. split; [reflexivity|]. split; [exact LK1|]. split; [exact HA1| exact Hin1]. }
  destruct STEP1 as [(st1 & m1 & LS1 & E1 & LK1 & HA1 & Hm1)|(E1n & FZ & LKd & HAn)].
  2:{ rewrite E1n. cbn iota. rewrite (proj2 (Z.eqb_eq _ _) FZ). apply (LEAF _ _ 0 (proj1 LKd)); [intros E; exfalso; exact (E eq_refl)| intros _; exact HAn]. }
  rewrite E1. cbn iota. clear E1.

  assert (STEP3 : forall st2 LS2 m2 mask, LINK st2 LS2 -> active st2 sc = Some m2 -> In m2 (LS2 (LActive sc)) ->
    apw ecost (let mr2 := get_meta_rec st2 m2 in
      let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
      let '(st3, m3) :=
        if Z.land mask (mask_upto gai) =? 0 then
          if negb (optr_eqb (m_next mr2) (Some m2)) then
            match m_next mr2 with
            | Some mn => (set_active sc (Some mn) st2, mn)
            | None => (st2, m2)
            end
          else
            let cnt := gai + 2 in
            let size := size_class (m_sizeclass mr2) * UNIT in
            let span := UNIT + size * cnt in
            let cnt := span_loop 300%nat cnt span size in
            let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
            match m_mem mr2 with
            | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
            | None => (st2, m2)
            end
        else (st2, m2) in
      activate_group m3 st3 (fun st4 mask => guard 40 (negb (mask =? 0))
          (ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail) c n Q).
  { intros st2 LS2 m2 mask LK2 HA2 Hm2. cbv zeta.
    destruct (Z.land mask _ =? 0).
    - destruct (negb (optr_eqb (m_next (get_meta_rec st2 m2)) (Some m2))).
      + destruct (m_next (get_meta_rec st2 m2)) as [mn|] eqn:N3; cbn iota.
        * destruct (LINK_head st2 LS2 m2 LK2 HA2) as (r2 & E2). destruct (LINK_rotate st2 LS2 m2 r2 mn LK2 E2 N3) as (LK3 & HA3 & Hm3).
          exact (ta_final _ _ mn LK3 HA3 Hm3).
        * exact (ta_final _ _ m2 LK2 HA2 Hm2).
      + destruct (m_mem (get_meta_rec st2 m2)) as [g|]; cbn iota.
        * apply (ta_final _ LS2 m2 (LINK_setai st2 LS2 g _ LK2)); [| exact Hm2].
          unfold active, ctx. unfold set_group_active_idx. destruct (get_group st2 g); exact HA2.
        * exact (ta_final _ _ m2 LK2 HA2 Hm2).
    - cbn iota. exact (ta_final _ _ m2 LK2 HA2 Hm2). }

  cbv zeta.
  destruct ((m_freed (get_meta_rec st1 m1) =? mask_upto (m_last_idx (get_meta_rec st1 m1))) && negb (m_freeable (get_meta_rec st1 m1) =? 0)).
  - destruct (m_next (get_meta_rec st1 m1)) as [mn|] eqn:N2; cbn iota.
    + destruct (LINK_head st1 LS1 m1 LK1 HA1) as (r1 & E1'). destruct (LINK_rotate st1 LS1 m1 r1 mn LK1 E1' N2) as (LK2 & HA2 & Hm2).
      exact (STEP3 _ _ mn _ LK2 HA2 Hm2).
    + exact (STEP3 _ _ m1 _ LK1 HA1 Hm1).
  - cbn iota. exact (STEP3 _ _ m1 _ LK1 HA1 Hm1).
Qed.

End TA.

End MW.
End HMWSLOT.
