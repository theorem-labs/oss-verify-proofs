(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe MI_WEnframe2 MI_WMalloc.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ss_list (p e : aptr) (n b3 : Z) : list (aptr * Z) :=
  let res := snd e - snd p - n in
  (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p (-3), Z.land b3 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma set_size_eq p e n b3 st : fst e = fst p -> set_size p e n b3 st = wrs (ss_list p e n b3) st.
Proof.
  intros E. unfold set_size, ss_list.
  destruct (snd e - snd p - n =? 0); cbn beta iota delta [wr32 wrs app negb];
    destruct (5 <=? snd e - snd p - n); cbn beta iota delta [wrs app negb]; reflexivity.
Qed.

Section RESIZE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n n' : Z) (m : aptr) (i : Z).
Let k : blk := ((c, off), n).
Let k' : blk := ((c, off), n').
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Hypothesis Hs : s_slots st !! c = Some (m, i).
Hypothesis Hn' : 0 <= n'.
Let stride := get_stride (MR st m).
Hypothesis Hfit' : UNIT * off + n' <= stride - IB.
Hypothesis Hres' : stride - IB - UNIT * off - n' < 2 ^ 32.

Hypothesis Hcls : (m_sizeclass (MR st m) < 48 -> m_sizeclass (MR st m) <= size_to_class n' + 1)
  /\ (m_sizeclass (MR st m) = 63 -> stride <= n' + UNIT * off + IB + 4095).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Let p : aptr := aadd c (UNIT * off).
Let e : aptr := aadd c (stride - IB).
Let res : Z := snd e - snd p - n.
Let res' : Z := snd e - snd p - n'.
Let b3 : Z := i + 32 * Z.min res 5.
Let t1 : N := N.succ (s_tick st).
Definition rs_st1 : mstate := set_tick t1 st.
Definition rs_st2 : mstate := wrs (ss_list p e n' b3) rs_st1.
Definition rs_st3 : mstate := havoc p n' rs_st2.

#[using="X L BL LS c n' i k INV Hk Hs Hfit' Hres' Hcls IS p"] Lemma rs_blocks : 0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= stride - IB.
Proof. destruct (is_blocks _ _ _ IS k Hk) as (m2 & i2 & Hs2 & A & B & C). rewrite Hs in Hs2. inversion Hs2; subst. auto. Qed.

#[using="X L BL LS INV Hs IS"] Lemma rs_valid : live_group st m /\ 0 <= i <= m_last_idx (MR st m) /\ c = slot_start' (MR st m) i.
Proof. exact (is_valid _ _ _ IS _ _ _ Hs). Qed.

#[using="X L BL LS INV Hs IM IS"] Lemma rs_hosts : exists bg, hosts st bg m /\ fst bg = fst c /\ snd c = sstart (MR st m) i.
Proof.
  destruct rs_valid as ([bg Hbg] & Hi & Ec). exists bg. split; [exact Hbg|].
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbg) in Ec. rewrite Ec. cbn. split; reflexivity.
Qed.

#[using="X L BL LS c INV Hs IS"] Lemma rs_idx : 0 <= i <= m_last_idx (MR st m).
Proof. exact (proj1 (proj2 rs_valid)). Qed.

#[using="X L BL LS c i INV Hs IM IG IS"] Lemma rs_stride : 16 <= stride /\ stride mod 16 = 0.
Proof.
  destruct rs_hosts as (bg & Hbg & _ & _). pose proof (stride_ge _ _ _ IG _ _ Hbg) as [A B]. unfold UNIT in *. split; assumption.
Qed.

#[using="X st L BL LS off n n' m i INV Hs stride IM IS p e res res' b3 t1"] Lemma rs_c16 : snd c mod 16 = 0.
Proof.
  destruct rs_hosts as (bg & Hbg & _ & Ec). rewrite Ec.
  pose proof (sstart_res X st L BL LS INV bg m i Hbg) as R. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st m) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st m) i) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st m) i) 16 ltac:(lia)). lia.
Qed.

#[using="X st L BL LS n n' m i INV Hs stride IM IS e res res' b3 t1"] Lemma p16 : snd p mod 16 = 0.
Proof. unfold p, aadd. cbn [snd]. pose proof rs_c16. unfold UNIT. Z.div_mod_to_equations. nia. Qed.

#[using="X L BL LS INV Hk Hs ISH"] Lemma rs_old : blk_shadow_ok st k m i.
Proof. exact (ish_blk _ _ ISH k m i Hk Hs). Qed.

#[using="Type"] Lemma st1_ctrl : ctrl_eq st rs_st1 /\ s_tick rs_st1 = t1.
Proof. split; [constructor; reflexivity| reflexivity]. Qed.
#[using="Type"] Lemma st2_ctrl : ctrl_eq st rs_st2 /\ s_tick rs_st2 = t1.
Proof.
  destruct (wrs_ctrl (ss_list p e n' b3) rs_st1) as [C T]. split; [eapply ctrl_eq_trans; [apply (proj1 st1_ctrl)| exact C]| rewrite T; reflexivity].
Qed.
#[using="Type"] Lemma st3_ctrl : ctrl_eq st rs_st3 /\ s_tick rs_st3 = t1.
Proof.
  destruct (havoc_ctrl p n' rs_st2) as [C T]. destruct st2_ctrl as [C2 T2].
  split; [eapply ctrl_eq_trans; [exact C2| exact C]| rewrite T; exact T2].
Qed.

#[using="c off n n' m i INV stride p e res res' b3"] Lemma INV1 : INVL X rs_st1 L BL LS.
Proof. apply INVL_set_tick; [unfold t1; lia| exact INV]. Qed.

#[using="X L BL LS c off n n' m i INV stride p e res res' b3"] Lemma TKS1 : TKS rs_st1 t1.
Proof. pose proof (TKS_of _ _ _ _ _ INV1) as T. exact T. Qed.
#[using="X L BL LS INV res'"] Lemma TKS2 : TKS rs_st2 t1.
Proof. unfold rs_st2. apply wrs_TKS; [cbn; lia| exact TKS1]. Qed.
#[using="X L BL LS INV res'"] Lemma st2_hav u hl : r_hav (get_shadow rs_st2 (fst p)) !! u = Some hl -> hl_ticks hl (s_tick rs_st2).
Proof.
  intros Hu ch Hch. pose proof TKS2 as TK. rewrite <- (proj2 st2_ctrl) in TK.
  exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch).
Qed.
#[using="X L BL LS INV Hs Hn' IM IS res'"] Lemma TKS3 : TKS rs_st3 t1.
Proof.
  unfold rs_st3. destruct (Z.eq_dec n' 0) as [Z0|NZ]; [rewrite havoc_le0 by lia; exact TKS2|].
  rewrite <- (proj2 st2_ctrl). apply TKS_havoc; [apply p16| lia| rewrite (proj2 st2_ctrl); exact TKS2].
Qed.

#[using="X L BL LS k INV Hk Hs Hn' Hfit' Hres' Hcls IM IG IS res' t1"] Lemma ss_addrs a : In a (map fst (ss_list p e n' b3)) ->
  fst a = fst c /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd p <= snd a < snd p + n') \/
  (fst a = fst c /\ snd a = snd p - 3).
Proof.
  intros Hin. pose proof rs_stride as [S16 SM]. pose proof rs_blocks as (Ho & _ & _). pose proof rs_c16 as C16.
  assert (R : 0 <= res') by (unfold res', e, p, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
  unfold ss_list in Hin.
  destruct (Z.eqb_spec (snd e - snd p - n') 0) as [R0|R0]; destruct (Z.leb_spec 5 (snd e - snd p - n')) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold res', e, p, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd];
    first [ right; split; [reflexivity| lia]
          | left; split; [reflexivity|]; split; lia ].
Qed.

#[using="X L BL LS INV Hs Hn' IM IS res'"] Lemma st3_read_out r : ~ (fst r = fst p /\ snd p <= snd r < snd p + n') ->
  cell_read (get_shadow rs_st3 (fst r)) (snd r) = cell_read (get_shadow rs_st2 (fst r)) (snd r).
Proof.
  intros Hr. unfold rs_st3. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out p n' rs_st2 p16 ltac:(lia) st2_hav). exact Hr.
Qed.

#[using="X L BL LS INV Hs Hn' Hcls IM IS res'"] Lemma st3_known_w x w : ~ (snd p <= x < snd p + n') ->
  lastw (ss_list p e n' b3) (fst c, x) None = Some w -> known rs_st3 (fst c, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (st3_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold rs_st2. rewrite (wrs_lastw (ss_list p e n' b3) rs_st1 (fst c, x) TKS1). rewrite HL. reflexivity.
Qed.

#[using="X L BL LS INV Hs Hn' Hcls IM IS res'"] Lemma st3_known_old x v : ~ (snd p <= x < snd p + n') ->
  lastw (ss_list p e n' b3) (fst c, x) None = None -> known st (fst c, x) v -> known rs_st3 (fst c, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (st3_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold rs_st2. rewrite (wrs_lastw (ss_list p e n' b3) rs_st1 (fst c, x) TKS1). rewrite HL.
  unfold rs_st1. exact K.
Qed.

#[using="X L BL LS k INV Hk Hs Hn' Hfit' Hres' Hcls IM IG IS res' t1"] Lemma ss_not_in a : snd p <= a < snd p + n' -> ~ In (fst c, a) (map fst (ss_list p e n' b3)).
Proof.
  intros Ha Hin. destruct (ss_addrs _ Hin) as [(_ & _ & NR)|(_ & E)]; cbn [fst snd] in *; [apply NR; exact Ha| unfold p, aadd in Ha, E; cbn in Ha, E; lia].
Qed.

#[using="X L BL LS k INV Hk Hs Hn' Hfit' Hres' Hcls IM IG IS res'"] Lemma st3_unknown a : snd p <= a < snd p + n' -> unknown rs_st3 (fst c, a).
Proof.
  intros Ha. unfold unknown, SHd, rs_st3. cbn [fst snd].
  destruct (cell_read_havoc_in p n' rs_st2 p16 ltac:(lia) st2_hav (fst c, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold rs_st2 in Hc. rewrite wrs_cells_other in Hc by (apply ss_not_in; exact Ha).
  rewrite (proj2 st2_ctrl). unfold rs_st1 in Hc. change (get_shadow (set_tick t1 st) (fst c)) with (get_shadow st (fst c)) in Hc.

  destruct (get_shadow_cells_some st (fst c) a (v, tk) Hc) as (sh & Hsh & Hc').
  pose proof (proj1 (TKS_of _ _ _ _ _ INV _ _ Hsh) a v tk Hc') as [_ LE]. unfold t1. lia.
Qed.

Ltac raeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold e, p, aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold e, p, aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

#[using="n i res b3 t1"] Lemma res'_eq : res' = stride - IB - UNIT * off - n'.
Proof. unfold res', e, p, aadd. cbn [snd]. lia. Qed.

#[using="X L BL LS k INV Hk Hs Hn' Hfit' Hres' Hcls IM IG IS ISH res'"] Lemma rs_blk_ok : blk_shadow_ok rs_st3 k' m i.
Proof.
  pose proof rs_stride as [S16 SM]. pose proof rs_blocks as (Ho & Hn & Hfit). pose proof rs_idx as IDX.
  destruct st3_ctrl as [CE TK].
  assert (MRE : MR rs_st3 m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  destruct rs_hosts as (bg & Hbg & Fbg & Ec). destruct Hbg as [ai Hb] eqn:EH.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  pose proof rs_old as OLD. unfold blk_shadow_ok in OLD |- *. unfold k, k' in OLD |- *. cbn [bslot boff bsize fst snd] in OLD |- *.
  rewrite MRE. fold stride in OLD |- *.
  rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hb)) in OLD |- *.
  destruct OLD as (O4 & O3 & O2 & O1 & OQ & O5 & OC & OU).
  assert (PP : snd p = snd c + UNIT * off) by reflexivity.
  assert (EE : snd e = snd c + stride - IB) by (unfold e, aadd; cbn [snd]; lia).
  replace (snd c + stride - IB - (snd c + UNIT * off) - n') with res' by (rewrite res'_eq; lia).
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with res in O3, O5, OC by (unfold res; rewrite EE, PP; lia).
  assert (R0 : 0 <= res') by (rewrite res'_eq; unfold IB, UNIT in *; lia).
  assert (R0o : 0 <= res) by (unfold res; rewrite EE, PP; unfold IB, UNIT in *; lia).
  assert (NPn : forall x, x < snd p \/ snd p + n' <= x -> ~ (snd p <= x < snd p + n')) by (intros; lia).
  replace (fst c) with (fst c) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact OQ| split; [| split]]]]]].
  -   apply st3_known_old; [apply NPn; unfold IB, UNIT in *; lia| | exact O4].
    unfold ss_list. fold res'. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [lastw app]; repeat raeq; reflexivity.
  -
    replace (i + 32 * Z.min res' 5) with (Z.land (Z.land b3 31 + Z.shiftl (if 5 <=? res' then 5 else res') 5) 255).
    2:{ unfold b3. replace (Z.land (i + 32 * Z.min res 5) 31) with i.
        2:{ symmetry. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof rs_idx.
            pose proof (Z.le_min_l res 5). pose proof (Z.le_min_r res 5). Z.div_mod_to_equations. nia. }
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 res').
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply st3_known_w; [apply NPn; unfold IB, UNIT in *; lia|].
    unfold ss_list. fold res'. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [negb lastw app]; repeat raeq; reflexivity.
  -   apply st3_known_old; [apply NPn; unfold IB, UNIT in *; lia| | exact O2].
    unfold ss_list. fold res'. destruct (Z.eqb_spec res' 0); destruct (Z.leb_spec 5 res'); cbn [negb lastw app]; try (exfalso; lia); repeat raeq; reflexivity.
  -   apply st3_known_old; [apply NPn; unfold IB, UNIT in *; lia| | exact O1].
    unfold ss_list. fold res'. destruct (Z.eqb_spec res' 0); destruct (Z.leb_spec 5 res'); cbn [negb lastw app]; try (exfalso; lia); repeat raeq; reflexivity.
  -   intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : res' < 2 ^ 32) by (rewrite res'_eq; exact Hres').
    assert (E5 : (5 <=? res') = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply st3_known_w; [apply NPn; rewrite ?res'_eq; unfold IB, UNIT in *; lia|];
         unfold ss_list; fold res'; rewrite E5, EZ; cbn [negb lastw app]; repeat raeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (st3_known_w _ 0); [apply NPn; rewrite ?res'_eq; unfold IB, UNIT in *; lia|].
    unfold ss_list; fold res'; rewrite E5, EZ; cbn [negb lastw app]; repeat raeq; reflexivity.
  -   intros RP.
    replace (snd c + stride - IB - res') with (snd p + n') by (rewrite res'_eq, PP; lia).
    apply (st3_known_w _ 0); [apply NPn; unfold IB, UNIT in *; lia|].
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold ss_list; fold res'; rewrite EZ. destruct (Z.leb_spec 5 res'); cbn [negb lastw app];
      try (destruct (Z.eq_dec res' 5)); try (exfalso; lia); repeat raeq; reflexivity.
  -   intros a Ha. apply st3_unknown. rewrite PP. exact Ha.
Qed.

#[using="k INV Hk NP Hs Hn' Hfit' Hres' Hcls IM IG IS ISH res'"] Theorem INVL_resize : INVL X rs_st3 L (k' :: bl_remove c BL) LS.
Proof.
  pose proof rs_stride as [S16 _]. pose proof rs_blocks as (Ho & Hn & Hfit).
  destruct rs_hosts as (bg & Hbg & Fbg & Ec).
  destruct st3_ctrl as [CE3 TK3]. destruct st1_ctrl as [CE1 TK1'].
  assert (CE13 : ctrl_eq rs_st1 rs_st3).
  { destruct (wrs_ctrl (ss_list p e n' b3) rs_st1) as [C2 _]. destruct (havoc_ctrl p n' rs_st2) as [C3 _].
    eapply ctrl_eq_trans; [exact C2| exact C3]. }

  set (X' := mkX (x_idle X) (x_zomb X) (Some c) (x_orph X) (x_fresh X)).
  assert (INVp : INVL X' rs_st1 L (bl_remove c BL) LS).
  { change c with (bslot k). apply (INVL_remove_block X rs_st1 rs_st1 L BL LS k INV1 Hk NP).
    - apply ctrl_eq_refl.
    - reflexivity.
    - intros; reflexivity.
    - exact (DOMS_of _ _ _ _ _ INV1).
    - exact (TKS_of _ _ _ _ _ INV1). }

  assert (EX : X = mkX (x_idle X') (x_zomb X') None (x_orph X') (x_fresh X')) by (destruct X; cbn; cbn in NP; rewrite NP; reflexivity).
  rewrite EX. apply (INVL_add_block X' rs_st1 rs_st3 L (bl_remove c BL) LS c off n' INVp eq_refl CE13).
  - rewrite TK3. symmetry. exact TK1'.
  - intros m2 i2 Hs2 q Hq. cbn [s_slots rs_st1 set_tick] in Hs2. rewrite Hs in Hs2. inversion Hs2. subst m2 i2.
    assert (MR1 : MR rs_st1 m = MR st m) by reflexivity. rewrite MR1 in Hq.
    assert (NQ : ~ (fst q = fst p /\ snd p <= snd q < snd p + n')).
    { intros [F R]. apply Hq. unfold inT. split; [exact F|]. rewrite <- Ec, sstart_succ. fold stride. unfold p, aadd in R. cbn [snd] in R. unfold IB, UNIT in *. lia. }
    rewrite (st3_read_out q NQ). unfold rs_st2. apply wrs_read_other.
    intros Hin. destruct (ss_addrs q Hin) as [(F & R & _)|(F & R)]; apply Hq; unfold inT; (split; [exact F|]);
      rewrite <- Ec, sstart_succ; fold stride; unfold p, aadd in R; cbn [snd] in R; unfold IB, UNIT in *; lia.
  - intros rid sh Hsh. assert (REG' : exists r, s_regions st !! fst c = Some r /\ r_kind r = RKGroup).
    { destruct Hbg as [ai Hb]. rewrite <- Fbg. exact (ig_region _ _ _ IG _ _ Hb). }
    change (s_regions rs_st1) with (s_regions st).
    revert rid sh Hsh. change (DOMS st rs_st3). unfold rs_st3. destruct (Z.eq_dec n' 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. unfold rs_st2. apply wrs_DOMS; [| intros q Hin; destruct (ss_addrs q Hin) as [(F & _)|(F & _)]; rewrite F; exact REG'].
      intros rid sh H. exact (DOMS_of _ _ _ _ _ INV rid sh H).
    + apply DOMS_havoc; [lia| | exact REG']. unfold rs_st2. apply wrs_DOMS; [| intros q Hin; destruct (ss_addrs q Hin) as [(F & _)|(F & _)]; rewrite F; exact REG'].
      intros rid sh H. exact (DOMS_of _ _ _ _ _ INV rid sh H).
  - change (s_tick rs_st1) with t1. exact TKS3.
  - intros m2 i2 Hs2. cbn [s_slots rs_st1 set_tick] in Hs2. rewrite Hs in Hs2. inversion Hs2. subst m2 i2.
    split; [exact Ho|]. split; [exact Hn'|]. split; [exact Hfit'|]. exact rs_blk_ok.
  - intros m2 i2 Hs2. cbn [s_slots rs_st1 set_tick] in Hs2. rewrite Hs in Hs2. inversion Hs2. subst m2 i2.
    change (MR rs_st1 m) with (MR st m). exact Hcls.
Qed.

#[using="Type"] Lemma strip_wrs l : forall s0, strip (wrs l s0) = strip s0.
Proof. induction l as [|[q v] l IH]; intros s0; cbn; [reflexivity|]. rewrite IH. apply strip_wr8. Qed.

#[using="Type"] Lemma rs_st3_strip : strip rs_st3 = strip st.
Proof. unfold rs_st3, rs_st2, rs_st1. rewrite strip_havoc, strip_wrs, strip_set_tick. reflexivity. Qed.

End RESIZE.
