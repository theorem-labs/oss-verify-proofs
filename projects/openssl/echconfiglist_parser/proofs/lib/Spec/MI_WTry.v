(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_WKill MI_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  - intros E63. exfalso. apply MNZ. exact (proj1 (g_big0 _ _ _ _ _ _ GO E63)).
  - (* [comment removed for export] *)
    intros AF. exfalso. pose proof (f_equal (fun z => Z.testbit z k0) AF) as T. cbn beta in T.
    unfold first in T. rewrite Z.lor_spec, TA, TB, Z.eqb_refl, testbit_mask_upto in T by (clear -K0 Hk0 AI; lia).
    destruct (Z.testbit (m_freed (MR st m)) k0) eqn:EF; [exact (M5 k0 K0 TB EF)|].
    cbn in T. symmetry in T. apply Z.leb_nle in T. clear -T K0 Hk0 AI. lia.
Qed.
End TAFIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  - destruct IM as [Q1 Q2 Q3 Q4 Q5 QAL]; constructor; try assumption.
    + intros x bb Hx. destruct (Q2 x bb Hx) as [H|H]; [left; apply sa_hosts; exact H| right; exact H].
    + intros bb h Hbb. apply GNE in Hbb as [[-> ->]|[NE Hbb]]; [| exact (Q3 bb h Hbb)].
      exists m. cbn [g_meta g_active_idx]. split; [reflexivity|]. split; [exact (hosts_mem _ _ _ (mkIM _ _ _ Q1 Q2 Q3 Q4 Q5 QAL) _ _ (ex_intro _ ai Hm))| change (MR st' m) with (MR st m); lia].
    + intros z Hz. destruct (Q5 z Hz) as (A1 & A2 & A3 & bz & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      exists bz. split; [exact A4|]. rewrite sa_lookup. destruct (aptr_eqb_spec bz b) as [->|NE]; [rewrite Hm in A5; discriminate| exact A5].
    + intros x Hx. destruct (QAL x Hx) as [A|A]; [left; apply sa_live; exact A| right; exact A].
  - destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. apply (dll_ext_metas st st' eq_refl). apply L2.
    + intros sc x Hx. destruct (L7 sc x Hx) as (B1 & B2 & B3). split; [exact B1|]. split; [apply sa_live; exact B2| exact B3].
  - destruct IG as [G1 G2 G3 G4 G5 GOE]; constructor.
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
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. change (MR st') with (MR st).
      apply GNE in H1 as [[-> E1]|[N1 H1]]; apply GNE in H2 as [[-> E2]|[N2 H2]].
      * inversion E1. inversion E2. subst. intros; reflexivity.
      * inversion E1. subst m1 ai1. eapply GOE; [exact Hm| exact H2].
      * inversion E2. subst m2 ai2. eapply GOE; [exact H1| exact Hm].
      * eapply GOE; eassumption.
  - destruct IS as [S1 S2 S3 S4 S5 S6 SBG SSM]; constructor; try assumption.
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

(* [comment removed for export] *)
Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.
