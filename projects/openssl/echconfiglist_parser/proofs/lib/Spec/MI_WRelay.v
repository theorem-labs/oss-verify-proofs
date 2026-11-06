(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe MI_WEnframe2 MI_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition relay (st : mstate) (W : list (aptr * Z)) (c : cptr) (off n : Z) : mstate :=
  havoc (aadd c (UNIT * off)) n (wrs W (set_tick (N.succ (s_tick st)) st)).

Definition relay_ok (st : mstate) (c : cptr) (W : list (aptr * Z)) (off n : Z) : Prop :=
  exists m i, s_slots st !! c = Some (m, i)
    /\ m_sizeclass (MR st m) < 48
    /\ (27 <= m_sizeclass (MR st m) -> 2028 < n)   (* [comment removed for export] *)
    /\ 0 <= off <= 258 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB
    /\ (forall a, In a (map fst W) ->
          fst a = fst c /\ snd c - 3 <= snd a < snd c + get_stride (MR st m) - 4
          /\ ~ (snd c + UNIT * off <= snd a < snd c + UNIT * off + n))
    /\ blk_shadow_ok (relay st W c off n) ((c, off), n) m i.

Lemma strip_wrs l st : strip (wrs l st) = strip st.
Proof. revert st. induction l as [|[q v] l IH]; intros st; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma strip_relay st W c off n : strip (relay st W c off n) = strip st.
Proof. unfold relay. rewrite strip_havoc, strip_wrs, strip_set_tick. reflexivity. Qed.

Lemma relay_ctrl st W c off n : ctrl_eq st (relay st W c off n) /\ s_tick (relay st W c off n) = N.succ (s_tick st).
Proof.
  unfold relay. destruct (havoc_ctrl (aadd c (UNIT * off)) n (wrs W (set_tick (N.succ (s_tick st)) st))) as [C1 T1].
  destruct (wrs_ctrl W (set_tick (N.succ (s_tick st)) st)) as [C2 T2].
  split; [| rewrite T1, T2; reflexivity].
  eapply ctrl_eq_trans; [apply ctrl_eq_set_tick|]. eapply ctrl_eq_trans; [exact C2| exact C1].
Qed.

Lemma conc_relay st W c off n q : conc (relay st W c off n) q = conc st q.
Proof. unfold conc, get_region. rewrite (ce_regions _ _ (proj1 (relay_ctrl st W c off n))). reflexivity. Qed.

Lemma s_secret_relay st W c off n : s_secret (relay st W c off n) = s_secret st.
Proof. exact (ce_secret _ _ (proj1 (relay_ctrl st W c off n))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section READ.
Variables (st : mstate) (W : list (aptr * Z)) (c : cptr) (off n : Z).
Hypothesis TK : TKS st (s_tick st).
Hypothesis C16 : snd c mod 16 = 0.
Hypothesis WNU : forall a, In a (map fst W) -> ~ (fst a = fst c /\ snd c + UNIT * off <= snd a < snd c + UNIT * off + n).
Let st0 := set_tick (N.succ (s_tick st)) st.
Let st1 := wrs W st0.
Let pp := aadd c (UNIT * off).

Lemma st0_TKS : TKS st0 (s_tick st0).
Proof.
  intros rid sh H. cbn in H |- *. destruct (TK rid sh H) as (A & B & C).
  split; [| split].
  - intros o w t Ho. destruct (A o w t Ho) as [R LE]. split; [exact R| lia].
  - intros u hl ch Hu Hch. pose proof (B u hl ch Hu Hch). lia.
  - intros pg t Hp. pose proof (C pg t Hp). lia.
Qed.

Lemma st1_TKS : TKS st1 (s_tick st0).
Proof. unfold st1. apply wrs_TKS; [lia| apply st0_TKS]. Qed.

Lemma st1_tick : s_tick st1 = s_tick st0. Proof. exact (proj2 (wrs_ctrl W st0)). Qed.

Lemma pp16 : snd pp mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, C16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.

Lemma st1_hav u hl : r_hav (get_shadow st1 (fst pp)) !! u = Some hl -> hl_ticks hl (s_tick st1).
Proof. intros Hu ch Hch. pose proof st1_TKS as T. rewrite <- st1_tick in T. exact (proj1 (sh_ticks_of _ _ T) u hl ch Hu Hch). Qed.

Lemma relay_read_out r : ~ (fst r = fst c /\ snd pp <= snd r < snd pp + n) ->
  cell_read (get_shadow (relay st W c off n) (fst r)) (snd r) = cell_read (get_shadow st1 (fst r)) (snd r).
Proof.
  intros Hr. unfold relay. fold st0 st1 pp. destruct (Z.le_gt_cases n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out pp n st1 pp16 ltac:(lia) st1_hav). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma relay_known_w x w :
  ~ (snd pp <= x < snd pp + n) ->
  lastw W (fst c, x) None = Some w -> known (relay st W c off n) (fst c, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (relay_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold st1. rewrite (wrs_lastw W st0 (fst c, x) st0_TKS). rewrite HL. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma relay_known_old q v :
  ~ (fst q = fst c /\ snd pp <= snd q < snd pp + n) ->
  lastw W q None = None -> known st q v -> known (relay st W c off n) q v.
Proof.
  intros Hq HL K. unfold known, SHd in *.
  rewrite (relay_read_out q) by exact Hq.
  unfold st1. rewrite (wrs_lastw W st0 q st0_TKS). rewrite HL. cbn. exact K.
Qed.

(* [comment removed for export] *)
Lemma relay_unknown_old q :
  ~ (fst q = fst c /\ snd pp <= snd q < snd pp + n) ->
  lastw W q None = None -> unknown st q -> unknown (relay st W c off n) q.
Proof.
  intros Hq HL K. unfold unknown, SHd in *.
  rewrite (relay_read_out q) by exact Hq.
  unfold st1. rewrite (wrs_lastw W st0 q st0_TKS). rewrite HL. cbn. exact K.
Qed.

(* [comment removed for export] *)
Lemma relay_unknown a : snd pp <= a < snd pp + n -> unknown (relay st W c off n) (fst c, a).
Proof.
  intros Ha. unfold unknown, SHd, relay. fold st0 st1 pp. cbn [fst snd].
  destruct (cell_read_havoc_in pp n st1 pp16 ltac:(lia) st1_hav (fst c, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold st1 in Hc. rewrite wrs_cells_other in Hc.
  2:{ intros Hin. apply (WNU _ Hin). cbn [fst snd]. split; [reflexivity|]. unfold pp, aadd in Ha. cbn [snd] in Ha. exact Ha. }
  rewrite st1_tick. change (fst pp) with (fst c) in Hc. cbn in Hc |- *.
  destruct (s_shadow st !! fst c) as [sh|] eqn:Esh.
  - unfold get_shadow in Hc. rewrite Esh in Hc. cbn in Hc. destruct (TK _ _ Esh) as (A & _ & _). destruct (A _ _ _ Hc) as [_ LE]. lia.
  - unfold get_shadow in Hc. rewrite Esh in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
Qed.
End READ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RELAY.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (k : blk) (W : list (aptr * Z)) (off n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In k BL.
Let c := bslot k.
Hypothesis ROK : relay_ok st c W off n.
Let st0 := set_tick (N.succ (s_tick st)) st.
Let st' := relay st W c off n.
Let X1 := xpend x0 (Some c).

Theorem relay_INVL : INVL x0 st' L (((c, off), n) :: bl_remove c BL) LS.
Proof.
  destruct ROK as (m & i & Hs & SC & SCL & Hoff & Hn & Hfit & HW & SHOK).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [S16 SM].
  assert (C16 : snd c mod 16 = 0).
  { rewrite Ec. cbn [snd]. pose proof (sstart_res x0 st L BL LS INV bm m i Hm) as R16. unfold IB in R16.
    pose proof (Z.div_mod (sstart (MR st m) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st m) i) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st m) i) 16 ltac:(lia)). lia. }
  assert (REG : exists rg, s_regions st !! (fst c) = Some rg /\ r_kind rg = RKGroup).
  { destruct Hm as [ai Hbm]. rewrite Ec. cbn [fst]. exact (ig_region _ _ _ IG _ _ Hbm). }
  destruct REG as (rg & Hrg & Krg).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TK0 : TKS st0 (s_tick st0)) by (exact (TKS_of _ _ _ _ _ INV0)).
  assert (INV1 : INVL X1 st0 L (bl_remove c BL) LS).
  { apply (INVL_remove_block x0 st0 st0 L BL LS k INV0 Hk eq_refl (ctrl_eq_refl _) eq_refl).
    - intros; reflexivity.
    - exact (DOMS_of _ _ _ _ _ INV0).
    - exact (TKS_of _ _ _ _ _ INV0). }
  destruct (wrs_ctrl W st0) as [CW TW].
  destruct (havoc_ctrl (aadd c (UNIT * off)) n (wrs W st0)) as [CH TH].
  assert (CE : ctrl_eq st0 st') by (eapply ctrl_eq_trans; [exact CW| exact CH]).
  assert (TK' : s_tick st' = s_tick st0) by (unfold st', relay; fold st0; rewrite TH, TW; reflexivity).
  change (INVL (xpend X1 None) st' L (((c, off), n) :: bl_remove c BL) LS).
  apply (INVL_add_block X1 st0 st' L (bl_remove c BL) LS c off n INV1 eq_refl CE TK').
  - (* [comment removed for export] *)
    intros m' i' Hs' q Hq. cbn in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
    change (MR st0 m) with (MR st m) in Hq.
    assert (SC2 : snd c = sstart (MR st m) i) by (rewrite Ec; reflexivity).
    assert (NQ : ~ (fst q = fst c /\ snd (aadd c (UNIT * off)) <= snd q < snd (aadd c (UNIT * off)) + n)).
    { intros [F R]. apply Hq. unfold inT. split; [exact F|]. unfold aadd in R. cbn [snd] in R. rewrite SC2 in R.
      rewrite sstart_succ. unfold IB, UNIT in *. lia. }
    unfold st'. rewrite (relay_read_out st W c off n (TKS_of _ _ _ _ _ INV) C16 q NQ). fold st0.
    apply wrs_read_other. intros Hin. destruct (HW q Hin) as (F & R & _). apply Hq. unfold inT. split; [exact F|].
    rewrite SC2 in R. rewrite sstart_succ. unfold IB in *. lia.
  - (* [comment removed for export] *)
    change (DOMS st0 st'). unfold st', relay. fold st0.
    assert (D1 : DOMS st0 (wrs W st0)).
    { apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV0)|]. intros q Hin. destruct (HW q Hin) as (F & _). rewrite F. exists rg. cbn. auto. }
    destruct (Z.le_gt_cases n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; exact D1|].
    apply DOMS_havoc; [lia| exact D1|]. exists rg. cbn. auto.
  - (* [comment removed for export] *)
    change (TKS st' (s_tick st0)). unfold st', relay. fold st0.
    destruct (Z.le_gt_cases n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; apply wrs_TKS; [lia| exact TK0]|].
    rewrite <- TW. apply TKS_havoc; [| lia| rewrite TW; apply wrs_TKS; [lia| exact TK0]].
    unfold aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, C16, Z.mul_comm, Z_mod_mult by lia. reflexivity.
  - (* [comment removed for export] *)
    intros m' i' Hs'. cbn in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-. change (MR st0 m) with (MR st m). auto.
  - intros m' i' Hs' H63. cbn in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-. change (MR st0 m) with (MR st m) in H63. exfalso. lia.
  - intros m' i' Hs' H63. cbn in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-. change (MR st0 m) with (MR st m) in H63. exfalso. lia.
  - intros m' i' Hs' H27. cbn in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-. change (MR st0 m) with (MR st m) in H27. exact (SCL H27).
Qed.

Lemma relay_members k' : In k' (bl_remove c BL) <-> In k' BL /\ bslot k' <> c.
Proof.
  apply (remove_block_members x0 st L BL LS k INV Hk).
Qed.
End RELAY.
