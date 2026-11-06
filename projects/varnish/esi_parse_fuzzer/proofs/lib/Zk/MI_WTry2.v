(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf MI_WNtf2.

Module MI_WTry.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Bits OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma one5_A_to_E (A B C D E A' E' : Prop) : A -> ~ A' -> E' -> one5 A B C D E -> one5 A' B C D E'.
Proof. unfold one5. tauto. Qed.

Section TAFIN.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SETAI.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.
End MI_WTry.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Bits OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Record TA_frame (st st1 : mstate) (sc : Z) : Prop := mkTAF {
  taf_regions : s_regions st1 = s_regions st;
  taf_shadow : s_shadow st1 = s_shadow st;
  taf_tick : s_tick st1 = s_tick st;
  taf_slots : s_slots st1 = s_slots st;
  taf_areas : s_areas st1 = s_areas st;
  taf_next_rid : s_next_rid st1 = s_next_rid st;
  taf_heads : forall h, h <> LActive sc -> get_head st1 h = get_head st h;
  taf_usage : forall sc', usage st1 sc' = usage st sc';
  taf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  taf_ssec : s_secret st1 = s_secret st;
  taf_secret : c_secret (s_ctx st1) = c_secret (s_ctx st) /\ c_init_done (s_ctx st1) = c_init_done (s_ctx st)
}.
Lemma taf_refl st sc : TA_frame st st sc. Proof. constructor; auto. Qed.
Lemma taf_trans a b c sc : TA_frame a b sc -> TA_frame b c sc -> TA_frame a c sc.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
  all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
  all: try (intros sc'; rewrite (B8 sc'); apply A8).
  all: split; congruence.
Qed.
Lemma taf_upd_meta st m f sc : TA_frame st (upd_meta m f st) sc.
Proof. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active st sc v : TA_frame st (set_active sc v st) sc.
Proof.
  constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay st sc sc0 : TA_frame st (decay_bounces sc0 st) sc.
Proof. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue st sc m : TA_frame st (dequeue (LActive sc) m st) sc.
Proof.
  (first [ pose proof ((dequeue_frame (LActive sc) m st)) as dR_1; dand10 dR_1 as F1 F2 F3 F4 F5 F6 F7 F8 F9 FC | destruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC) ]). destruct FC.
  constructor; auto.
  all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
  all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (split; assumption).
Qed.

(* [comment removed for export] *)
Section HEADFACTS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HA : active st sc = Some m.
Lemma hd_list : exists rest, LS (LActive sc) = m :: rest.
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
  destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
Lemma hd_in : In m (LS (LActive sc)).
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
Lemma hd_facts : 0 <= sc < 48 /\ m_sizeclass (MR st m) = sc /\ exists b ai, s_groups st !! b = Some (mkGhdr (Some m) ai).
Proof.
  (first [ pose proof ((il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in)) as dR_2; dand3 dR_2 as A [b [ai Hb]] C | destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C) ]). split; [exact A|]. split; [exact C|]. exists b, ai. exact Hb.
Qed.
Lemma hd_head : head_of (LS (LActive sc)) = Some m.
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
Lemma hd_next : exists mn, m_next (MR st m) = Some mn /\ In mn (LS (LActive sc)).
Proof.
  (first [ pose proof ((lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in)) as dR_3; dex1 dR_3 as y; dand3 dR_3 as Hy E _ | pose proof ((lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in)) as dR_3; dand4 dR_3 as y Hy E _ | destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _) ]). exists y. auto.
Qed.
End HEADFACTS.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition GOODH (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr) : Prop :=
  INVL X st L BL LS /\ active st sc = Some m /\ m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0.

End CEIL.

Section STEPS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma rotate_ok st LS m mn :
  GOODH X st L BL LS sc m -> m_next (MR st m) = Some mn ->
  exists LS', GOODH X (set_active sc (Some mn) st) L BL LS' sc mn.
Proof.
  ((first [ intro dR_32; dand4 dR_32 as INV HA AV FR | intros (INV & HA & AV & FR) ]); intros Hn).
  destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  assert (INV' : INVL X (set_head (LActive sc) (Some mn) st) L BL (fupd LS (LActive sc) (rest ++ [m]))).
  { apply (INVL_rotate X st L BL LS sc m mn rest INV HL Hn). intros _ _. auto. }
  exists (fupd LS (LActive sc) (rest ++ [m])). split; [exact INV'|].
  split; [unfold active, set_active, ctx; cbn; rewrite lookup_insert_eq; reflexivity|].
  change (MR (set_active sc (Some mn) st) mn) with (MR st mn).
  pose proof (next_listed X st L BL LS INV (LActive sc) m mn (hd_in X st L BL LS sc m INV HA) Hn) as Hin.
  destruct (aptr_eq_dec mn m) as [->|NE]; [auto|].
  (first [ pose proof ((il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin)) as dR_4; dand3 dR_4 as _ [bb [aa Hbb]] _ | destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin) as (_ & [bb [aa Hbb]] & _) ]).
  apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
  rewrite (hd_head X st L BL LS sc m INV HA). congruence.
Qed.

(* [comment removed for export] *)
Lemma dequeue_exhausted_ok st LS m :
  INVL X st L BL LS -> active st sc = Some m -> m_avail (MR st m) = 0 -> m_freed (MR st m) = 0 ->
  exists LS' rest, INVL X (dequeue (LActive sc) m st) L BL LS' /\ LS (LActive sc) = m :: rest
    /\ active (dequeue (LActive sc) m st) sc = head_of rest
    /\ (forall m1, head_of rest = Some m1 -> m_avail (MR st m1) = 0 /\ m_freed (MR st m1) <> 0).
Proof.
  intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  (first [ pose proof ((hd_facts X st L BL LS sc m INV HA)) as dR_5; dand5 dR_5 as _ Esc b ai Hb | destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb) ]).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
  assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
  { apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl). intros bb aix Hbb.
    (first [ pose proof ((dequeue_frame (LActive sc) m st)) as dR_6; dand6 dR_6 as _ _ _ _ G5 _ | destruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _) ]). rewrite G5 in Hbb.
    pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ (ex_intro _ aix Hbb) (ex_intro _ ai Hb)) as ->. rewrite Hb in Hbb. inversion Hbb. subst aix.
    pose proof (dequeue_data (LActive sc) m st m) as D. (first [ pose proof ((data_same _ _ 0 D)) as dR_7; dand6 dR_7 as _ El Ea Ef Es _ | destruct (data_same _ _ 0 D) as (_ & El & Ea & Ef & Es & _) ]).
    rewrite El, Ea, Ef, Es. split; [| split; [intros; auto| split; [| intros; auto]]].
    - intros Hlt. exfalso. (first [ pose proof ((g_masks _ _ _ _ _ _ GO)) as dR_8; dand6 dR_8 as _ _ _ _ _ M6 | pose proof (g_masks _ _ _ _ _ _ GO) as (_ & _ & _ & _ & _ & M6) ]). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
      specialize (M6 (m_last_idx (MR st m)) ltac:(lia)). unfold tbit in M6. rewrite FR, Z.bits_0 in M6. discriminate.
    - intros sc0 Hin. exfalso. cbn in Hin.
      apply (m_out X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)). exists (LActive sc0). exact Hin. }
  replace (xfresh (xfresh X (Some m)) None) with X in INV2 by (destruct X; cbn in HF |- *; subst; reflexivity).
  exists (fupd LS (LActive sc) ([] ++ rest)), rest. split; [exact INV2|]. split; [exact HL|]. split.
  - change (active (dequeue (LActive sc) m st) sc) with (get_head (dequeue (LActive sc) m st) (LActive sc)). rewrite dequeue_head.
    rewrite decide_True by reflexivity. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. rewrite HL in HH. cbn in HH.
    (first [ pose proof ((hd_next X st L BL LS sc m INV HA)) as dR_9; dex1 dR_9 as mn; destruct dR_9 as [Hn Hin] | pose proof ((hd_next X st L BL LS sc m INV HA)) as dR_9; dand3 dR_9 as mn Hn Hin | destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin) ]). rewrite Hn.
    destruct (optr_eqb_spec (Some mn) (Some m)) as [E|NE].
    + inversion E. subst mn. pose proof (proj1 (lists_singleton st LS (old_lists _ _ _ _ _ INV) (LActive sc) m rest HL) Hn) as ER. rewrite ER. reflexivity.
    + change (get_head st (LActive sc)) with (active st sc). rewrite HA, optr_eqb_refl. rewrite HL in Hin. destruct Hin as [->|Hin]; [congruence|].
      destruct rest as [|a rest']; [destruct Hin|]. cbn.
      pose proof (il_dll _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as D. rewrite HL in D. cbn [dll app] in D. destruct D as (D1 & _). rewrite Hn in D1. exact D1.
  - intros m1 Hm1. destruct rest as [|a rest']; cbn in Hm1; [discriminate|]. inversion Hm1. subst a.
    assert (Hin : In m1 (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
    (first [ pose proof ((il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin)) as dR_10; dand3 dR_10 as _ [bb [aa Hbb]] _ | destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin) as (_ & [bb [aa Hbb]] & _) ]).
    apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
    rewrite HL. cbn. intros E. inversion E. subst m1.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left.
Qed.
End STEPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_upto_all f n : 0 <= f -> 0 <= n -> (forall i, 0 <= i -> Z.testbit f i = true -> i <= n) -> Z.land f (mask_upto n) = f.
Proof.
  intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
  destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.

Lemma land_mask_upto_zero_above f n : 0 <= f -> 0 <= n -> Z.land f (mask_upto n) = 0 ->
  forall i, 0 <= i -> Z.testbit f i = true -> n < i.
Proof.
  intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
  assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
  rewrite H, Z.bits_0 in T. discriminate.
Qed.

Section TRY.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

Definition TA_POST (st st1 : mstate) (first : Z) (LS1 : lhead -> list aptr) : Prop :=
  TA_frame st st1 sc /\
  ((first = 0 /\ active st1 sc = None /\ INVL X st1 L BL LS1)
   \/ (exists g bg ai idx, first <> 0 /\ 0 <= first /\ ctz32 first = idx /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ 0 <= idx <= m_last_idx (MR st1 g)
         /\ m_sizeclass (MR st1 g) = sc /\ UNIT * size_class sc <= get_stride (MR st1 g)
         /\ INVL (xpend X (Some (fst bg, sstart (MR st1 g) idx))) st1 L BL LS1)).

Lemma set_avail_views v r : m_last_idx (m_set_avail v r) = m_last_idx r /\ m_sizeclass (m_set_avail v r) = m_sizeclass r
  /\ get_stride (m_set_avail v r) = get_stride r /\ (forall i, sstart (m_set_avail v r) i = sstart r i).
Proof. destruct r; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fin_ok st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST st0 st1 first LS1.
Proof.
  intros INV TF HA AM MNZ. (first [ pose proof ((hd_facts X st L BL LS sc m INV HA)) as dR_11; dand5 dR_11 as _ Esc bm ai Hbm | destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm) ]).
  (first [ pose proof ((ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ))) as dR_12; dand5 dR_12 as INV1 R1 R2 R3 R4 | pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4) ]).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. (first [ pose proof ((set_avail_views (mask - lowbit mask) (MR st m))) as dR_13; dand4 dR_13 as V1 V2 V3 V4 | destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4) ]). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_ok st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST st st1 first LS1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ TA_frame st st1 sc
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - (first [ pose proof ((dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ)) as dR_14; dand6 dR_14 as LS1 rest INV1 HL HA1 NXT | destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT) ]).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| apply taf_dequeue].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. (first [ pose proof ((data_same _ _ 0 D)) as dR_15; dand5 dR_15 as _ _ Ea Ef _ | destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _) ]).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - (first [ pose proof ((hd_next X st L BL LS sc m INV HA)) as dR_16; dex1 dR_16 as mn; destruct dR_16 as [Hn Hin] | pose proof ((hd_next X st L BL LS sc m INV HA)) as dR_16; dand3 dR_16 as mn Hn Hin | destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin) ]). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| apply taf_set_active]. }
  (first [ dex2 STEP1 as st1 m1; destruct STEP1 as [LS1 [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]] | dand4 STEP1 as st1 m1 LS1 [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)] | destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]) ]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [apply taf_dequeue| left; auto]. }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ TA_frame st st2 sc).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - (first [ pose proof (G1) as dR_18; dand3 dR_18 as INV1 HA1 _ | pose proof G1 as (INV1 & HA1 & _) ]). (first [ pose proof ((hd_next X st1 L BL LS1 sc m1 INV1 HA1)) as dR_19; dex1 dR_19 as mn; destruct dR_19 as [Hn _] | pose proof ((hd_next X st1 L BL LS1 sc m1 INV1 HA1)) as dR_19; dand3 dR_19 as mn Hn _ | destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _) ]). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| eapply taf_trans; [exact TF1| apply taf_set_active]].
    - exists st1, m1, LS1. auto. }
  (first [ dex2 STEP2 as st2 m2; dand4 STEP2 as LS2 E2 G2 TF2 | dand6 STEP2 as st2 m2 LS2 E2 G2 TF2 | destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & TF2) ]). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  (first [ dand4 G2 as INV2 HA2 AZ2 FNZ2 | destruct G2 as (INV2 & HA2 & AZ2 & FNZ2) ]).
  (first [ pose proof ((hd_facts X st2 L BL LS2 sc m2 INV2 HA2)) as dR_22; dand5 dR_22 as _ Esc2 b2 ai2 Hb2 | destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2) ]).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  (first [ pose proof ((g_masks _ _ _ _ _ _ GO2)) as dR_23; dand6 dR_23 as W1 W2 W3 W4 W5 W6 | pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6) ]). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ TA_frame st st3 sc
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      (first [ pose proof ((hd_next X st2 L BL LS2 sc m2 INV2 HA2)) as dR_24; dex1 dR_24 as mn; destruct dR_24 as [Hn Hin] | pose proof ((hd_next X st2 L BL LS2 sc m2 INV2 HA2)) as dR_24; dand3 dR_24 as mn Hn Hin | destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin) ]). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        (first [ pose proof ((il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin)) as dR_25; dand3 dR_25 as _ [b3 [ai3 Hb3]] Esc3 | destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3) ]).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [eapply taf_trans; [exact TF2| apply taf_set_active]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        (first [ pose proof ((g_masks _ _ _ _ _ _ GO3)) as dR_26; dand6 dR_26 as V1 V2 V3 V4 V5 V6 | pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6) ]).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        (first [ dand4 G3 as _ _ _ F3 | destruct G3 as (_ & _ & _ & F3) ]). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  (first [ dex2 STEP3 as st3 m3; dand8 STEP3 as LS3 b3 ai3 E3 G3 TF3 Hb3 ACT | dand10 STEP3 as st3 m3 LS3 b3 ai3 E3 G3 TF3 Hb3 ACT | destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & TF3 & Hb3 & ACT) ]).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  (first [ dand4 G3 as INV3 HA3 AZ3 FNZ3 | destruct G3 as (INV3 & HA3 & AZ3 & FNZ3) ]).
  (first [ pose proof ((hd_facts X st3 L BL LS3 sc m3 INV3 HA3)) as dR_30; dand3 dR_30 as _ Esc3 _ | destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _) ]).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  (first [ pose proof ((fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5)) as dR_31; dex2 dR_31 as st6 first; dand3 dR_31 as LS6 E6 POST | pose proof ((fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5)) as dR_31; dand5 dR_31 as st6 first LS6 E6 POST | destruct (fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST) ]).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRY.
