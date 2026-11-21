(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot MI_WSlot2
  LB_AG LB_WSlot MF_Defs MF_WTry MF_WAMeta.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma halve_even_32 u : 0 <= u <= 7 -> halve_even 8 32 u = 1.
Proof.
  intros Hu. cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 16) with true by (symmetry; apply Z.ltb_lt; lia). cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 4) with true by (symmetry; apply Z.ltb_lt; lia). cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma halve_even_28 u : 0 <= u <= 55 -> halve_even 8 28 u = 7.
Proof.
  intros Hu. cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 28) with true by (symmetry; apply Z.ltb_lt; lia). cbn -[Z.ltb Z.mul].
  replace (u <? 4 * 14) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ag_cnt1_K sc u : KCLS sc -> KPRE sc 0 u -> 0 <= u ->
  (sc = 31 -> ag_cnt1 sc u = 1) /\ (sc <> 31 -> ag_cnt1 sc u = 7) /\ PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u + UNIT.
Proof.
  intros K (P1 & P2 & P3) Hu. unfold ag_cnt1, cnt0_of.
  destruct K as [->|[->| ->]].
  - specialize (P1 eq_refl). change (31 <? 9) with false. change (Z.land 31 3) with 3. change (med_cnt 3) with 32.
    rewrite halve_even_32 by lia. cbn. repeat split; intros; try reflexivity; lia.
  - destruct (P2 eq_refl) as [U _]. change (40 <? 9) with false. change (Z.land 40 3) with 0. change (med_cnt 0) with 28.
    rewrite halve_even_28 by lia. cbn. repeat split; intros; try reflexivity; lia.
  - destruct (P3 eq_refl) as [U _]. change (44 <? 9) with false. change (Z.land 44 3) with 0. change (med_cnt 0) with 28.
    rewrite halve_even_28 by lia. cbn. repeat split; intros; try reflexivity; lia.
Qed.

Lemma KPRE_req0 sc req u : KPRE sc req u -> KPRE sc 0 u.
Proof. intros (P1 & P2 & P3). split; [exact P1|]. split; [intros E; split; [exact (proj1 (P2 E))| intros; lia]| intros E; split; [exact (proj1 (P3 E))| intros; lia]]. Qed.

Lemma ag_cn3_K sc req u c3 n3 : KCLS sc -> KPRE sc req u -> 0 <= u -> 0 <= req ->
  ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u) u false) u false = (c3, n3) -> c3 = 1.
Proof.
  intros K P Hu Hreq E.
  destruct (ag_cnt1_K sc u K (KPRE_req0 _ _ _ P) Hu) as (C31 & C40 & _).
  pose proof (round_up_pg_spec (req + IB + UNIT)) as [R1 R2]. set (req' := round_up_pg (req + IB + UNIT)) in *.
  assert (Hq : exists q, req' = 4096 * q) by (exists (req' / 4096); pose proof (Z.div_mod req' 4096 ltac:(lia)); lia).
  destruct Hq as [q Hq].
  unfold ag_cn3, ag_cnt2, adj in E. destruct P as (P1 & P2 & P3).
  destruct K as [->|[->| ->]].
  - rewrite (C31 eq_refl) in E. change (Z.land 31 3) with 3 in E. cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul] in E.
    fold req' in E.
    destruct (u <? 4 * 1); cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul] in E;
      destruct ((req' <? _) || _); inversion E; reflexivity.
  - rewrite (C40 ltac:(lia)) in E. change (Z.land 40 3) with 0 in E. change (UNIT * size_class 40) with 37440 in E.
    cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul Z.sub] in E. fold req' in E.
    destruct (P2 eq_refl) as [U55 U5].
    assert (CASE : forall c, (c = 3 \/ c = 7) ->
              (if negb false && (c <=? 7) then if (req' <? 37440 + UNIT) || ((4 * PGSZ <=? req') && (u <? 2 * c)) then (1, req') else (c, round_up_pg (37440 * c + UNIT))
               else (c, round_up_pg (37440 * c + UNIT))) = (c3, n3) -> c3 = 1).
    { intros c Hc E'. replace (negb false && (c <=? 7)) with true in E' by (symmetry; apply andb_true_iff; split; [reflexivity| apply Z.leb_le; lia]).
      destruct (Z.ltb_spec req' (37440 + UNIT)) as [LT|GE]; cbn [orb] in E'; [inversion E'; reflexivity|].
      unfold UNIT, PGSZ, IB in *. assert (36844 < req) by lia.
      replace (4 * 4096 <=? req') with true in E' by (symmetry; apply Z.leb_le; lia).
      replace (u <? 2 * c) with true in E' by (symmetry; apply Z.ltb_lt; specialize (U5 ltac:(lia)); lia).
      inversion E'; reflexivity. }
    destruct (u <? 4 * 7); cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul Z.sub negb andb] in E; [exact (CASE 3 ltac:(lia) E)| exact (CASE 7 ltac:(lia) E)].
  - rewrite (C40 ltac:(lia)) in E. change (Z.land 44 3) with 0 in E. change (UNIT * size_class 44) with 74880 in E.
    cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul Z.sub] in E. fold req' in E.
    destruct (P3 eq_refl) as [U55 U5].
    assert (CASE : forall c, (c = 3 \/ c = 7) ->
              (if negb false && (c <=? 7) then if (req' <? 74880 + UNIT) || ((4 * PGSZ <=? req') && (u <? 2 * c)) then (1, req') else (c, round_up_pg (74880 * c + UNIT))
               else (c, round_up_pg (74880 * c + UNIT))) = (c3, n3) -> c3 = 1).
    { intros c Hc E'. replace (negb false && (c <=? 7)) with true in E' by (symmetry; apply andb_true_iff; split; [reflexivity| apply Z.leb_le; lia]).
      destruct (Z.ltb_spec req' (74880 + UNIT)) as [LT|GE]; cbn [orb] in E'; [inversion E'; reflexivity|].
      unfold UNIT, PGSZ, IB in *. assert (73708 < req) by lia.
      replace (4 * 4096 <=? req') with true in E' by (symmetry; apply Z.leb_le; lia).
      replace (u <? 2 * c) with true in E' by (symmetry; apply Z.ltb_lt; specialize (U5 ltac:(lia)); lia).
      inversion E'; reflexivity. }
    destruct (u <? 4 * 7); cbn -[round_up_pg Z.ltb Z.leb Z.add Z.mul Z.sub negb andb] in E; [exact (CASE 3 ltac:(lia) E)| exact (CASE 7 ltac:(lia) E)].
Qed.

Lemma K_not_nested sc c : KCLS sc -> 1 <= c -> ~ UNIT * size_class sc * c + UNIT <= PGSZ / 2.
Proof.
  intros K Hc. destruct K as [->|[->| ->]];
    [change (size_class 31) with 511| change (size_class 40) with 2340| change (size_class 44) with 4680]; unfold UNIT, PGSZ; lia.
Qed.

Lemma bounces24_account_bounce sc st :
  (sc = 31 -> bounces st 24 <= 98) -> bounces (step_seq (account_bounce sc st)) 24 <= bounces st 24 + (if sc =? 31 then 1 else 0).
Proof.
  intros H98.
  assert (SS : forall s, bounces (step_seq s) 24 = bounces s 24) by (intros s; unfold step_seq; destruct (_ =? 255); reflexivity).
  rewrite SS. unfold account_bounce.
  destruct (sc_in_seq_range sc) eqn:SR; [| destruct (sc =? 31); lia].
  destruct (negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)); [| destruct (sc =? 31); lia].
  destruct (Z.eqb_spec sc 31) as [->|NE].
  - specialize (H98 eq_refl). change (31 - 7) with 24. replace (bounces st 24 + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold bounces at 1. unfold set_bounce, ctx. cbn [s_ctx upd_ctx]. rewrite c_bounces_set_bounces_map, lookup_insert_eq. cbn. lia.
  - assert (BO : forall v, bounces (set_bounce (sc - 7) v st) 24 = bounces st 24).
    { intros v. unfold bounces at 1. unfold set_bounce, ctx. cbn [s_ctx upd_ctx]. rewrite c_bounces_set_bounces_map, lookup_insert_ne by lia. reflexivity. }
    destruct (_ <? 100); rewrite BO; lia.
Qed.


Definition KGRP (sc req : Z) (st st2 : mstate) (b : aptr) (last : Z) : Prop :=
  KCLS sc -> KPRE sc req (usage st sc) -> bounces st 24 <= 99 ->
  last = 0 /\ s_regions st !! (fst b) = None /\ snd b = 0 /\ gonly0 st2 (fst b)
  /\ (forall b' m' ai', s_groups st2 !! b' = Some (mkGhdr (Some m') ai') -> b' <> b -> OLD st st2 b' m').

Definition AG_POSTF (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ MFR sc st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2 /\ KGRP sc req st st2 b last
  end.

Definition SLOT_POSTF (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
  (forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ MFR sc st st1 /\
  ((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
   \/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
         /\ req + IB <= get_stride (MR st1 g)
         /\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
         /\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
         /\ TF2 st1 /\ XNEW sc req st st1 g bg)).

Definition REC_OKF (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  (forall st1 idx L1 LS1, SLOT_POSTF idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (rec st j req k bail) Post.

Lemma idle_not_gmeta X st L BL LS m b ai : INVL X st L BL LS -> In m (x_idle X) ->
  s_groups st !! b = Some (mkGhdr (Some m) ai) -> False.
Proof.
  intros INV Hin Hb. pose proof (proj1 (proj2 (proj2 INV))) as IM.
  destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & E & Hm & _). cbn in E. inversion E. subst m'.
  pose proof (proj1 (im_idle _ _ _ IM m Hin)) as Z0. unfold MR, get_meta_rec in Hm. rewrite Z0 in Hm. cbn in Hm. discriminate.
Qed.

Lemma MF0_fm_st idle m st L BL LS : INVL (X_as (m :: idle)) st L BL LS -> MF0 st (fm_st st m).
Proof.
  intros INV. split.
  - intros b x ai Hb. unfold fm_st in Hb.
    assert (G : s_groups (queue_st LFree m (put_meta m meta0 st)) = s_groups st).
    { destruct (queue_frame LFree m (put_meta m meta0 st)) as (_ & _ & _ & _ & Q5 & _). rewrite Q5. reflexivity. }
    rewrite G in Hb. split; [exists ai; exact Hb|].
    assert (NE : x <> m) by (intros ->; exact (idle_not_gmeta _ st L BL LS m b ai INV ltac:(cbn; left; reflexivity) Hb)).
    apply same_geo_data. unfold fm_st. rewrite (queue_data LFree m (put_meta m meta0 st) x).
    unfold MR. rewrite get_meta_rec_put_other by exact NE. reflexivity.
  - unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CB).
    unfold bounces, ctx. rewrite (cb_bounces _ _ CB). cbn. lia.
Qed.


Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HM0 : MF0 st0 st1.
Hypothesis HNR : forall q r, s_regions st0 !! q = Some r -> (q < s_next_rid st1)%N.
Hypothesis HKC : KCLS sc -> KPRE sc req (usage st0 sc) -> bounces st0 24 <= 99 -> cnt = 1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POSTF idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma st1'_metas : s_metas st1' = s_metas st1.
Proof.
  destruct (account_bounce_fields sc st1) as (_ & _ & _ & _ & _ & A6 & _). destruct (step_seq_fields (account_bounce sc st1)) as (_ & _ & _ & _ & _ & B6 & _).
  unfold st1'. rewrite B6, A6. reflexivity.
Qed.
Lemma st1'_next_rid : s_next_rid st1' = s_next_rid st1.
Proof.
  destruct (account_bounce_fields sc st1) as (_ & _ & _ & _ & A5 & _). destruct (step_seq_fields (account_bounce sc st1)) as (_ & _ & _ & _ & B5 & _).
  unfold st1'. rewrite B5, A5. reflexivity.
Qed.
Lemma st1'_bounces : (sc = 31 -> bounces st0 24 <= 98) -> bounces st1' 24 <= bounces st0 24 + (if sc =? 31 then 1 else 0).
Proof.
  intros H98. pose proof (proj2 HM0) as B01. unfold st1'.
  pose proof (bounces24_account_bounce sc st1 ltac:(intros E; specialize (H98 E); lia)) as B. destruct (sc =? 31); lia.
Qed.

Theorem ag_mmap_ftF :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
  fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1'.
  pose proof (st1'_groups st1 sc) as GR1. fold st1' in GR1.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (HM1' : MFR sc st0 st1').
  { constructor; [| exact st1'_bounces]. intros b x ai Hb. left. rewrite GR1 in Hb. destruct (proj1 HM0 _ _ _ Hb) as [E G]. split; [exact E|].
    eapply same_geo_trans; [| exact G]. unfold MR, get_meta_rec. rewrite st1'_metas. apply same_geo_refl. }
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    +
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split; [exact (MFR_MF0_r sc _ _ _ HM1' (MF0_fm_st idle m st1' L1 BL LS1 INV1'))|].
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    +
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      set (st' := agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) in *.
      assert (GRX : s_groups st' = <[(rid, 0) := mkGhdr (Some m) (Z.land AI 31)]> (s_groups st1)).
      { unfold st'. rewrite agt_groups. cbn. rewrite Est2. cbn. rewrite GR1. reflexivity. }
      assert (NG1 : forall bq hq, s_groups st1 !! bq = Some hq -> fst bq = rid -> False).
      { intros bq hq Hbq Eq. destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ Hbq) as (rq & Hrq & _).
        rewrite Eq, Erid, st1'_next_rid in Hrq. pose proof (ir_ids _ _ _ (proj1 INV1) _ _ Hrq). lia. }
      assert (OTH : forall b' m' ai', s_groups st' !! b' = Some (mkGhdr (Some m') ai') -> b' <> (rid, 0) ->
                    OLD st0 st' b' m' /\ exists ai1, s_groups st1 !! b' = Some (mkGhdr (Some m') ai1)).
      { intros b' m' ai' Hb' NE. rewrite GRX, lookup_insert_ne in Hb' by congruence.
        destruct (proj1 HM0 _ _ _ Hb') as [E G]. split; [| exists ai'; exact Hb']. split; [exact E|].
        assert (NEm : m' <> m) by (intros ->; exact (idle_not_gmeta _ st1 L1 BL LS1 m b' ai' INV1 ltac:(cbn; left; reflexivity) Hb')).
        eapply same_geo_trans; [| exact G]. unfold st'. rewrite (agt_MR_other _ sc m (rid, 0) cnt AI m' NEm).
        unfold MR. rewrite get_meta_rec_upd_other by exact NEm. rewrite get_meta_rec_upd_ctx. rewrite Est2.
        change (get_meta_rec (fst (new_region RKGroup a needed st1')) m') with (get_meta_rec st1' m'). unfold get_meta_rec. rewrite st1'_metas. apply same_geo_refl. }
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { constructor.
        - intros b' m' ai' Hb'. destruct (decide (b' = (rid, 0))) as [->|NE].
          + right. left. rewrite GR' in Hb'. inversion Hb'. subst m'. rewrite MR'. reflexivity.
          + left. exact (proj1 (OTH _ _ _ Hb' NE)).
        - intros H98. unfold st'. unfold bounces at 1. unfold ctx. rewrite agt_ctx, c_bounces_set_usage_map. cbn [s_ctx upd_meta put_meta set_metas upd_ctx].
          unfold MC. rewrite c_bounces_set_mmap_counter. rewrite Est2. change (c_bounces (s_ctx (fst (new_region RKGroup a needed st1')))) with (c_bounces (s_ctx st1')).
          exact (st1'_bounces H98). }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR st' m) = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| split; [apply TF0_TF2; exact TF'|]]]]].
      4:{ intros HKc HKp HKb. pose proof (HKC HKc HKp HKb) as C1.
          split; [lia|]. split; [| split; [reflexivity| split]].
          - cbn [fst]. destruct (s_regions st0 !! rid) as [r0|] eqn:E0; [| reflexivity]. exfalso. pose proof (HNR _ _ E0). rewrite Erid, st1'_next_rid in H. lia.
          - cbn [fst]. eapply gonly0_top; [exact GRX|]. intros bq hq Hbq Eq. exact (NG1 _ _ Hbq Eq).
          - intros b' m' ai' Hb' NE. exact (proj1 (OTH _ _ _ Hb' NE)). }
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.


Lemma nest_layout_ctrl st g idx j size cnt :
  s_groups (nest_layout st g idx j size cnt) = s_groups st /\ s_metas (nest_layout st g idx j size cnt) = s_metas st
  /\ s_ctx (nest_layout st g idx j size cnt) = s_ctx st.
Proof.
  pose proof (strip_nest_layout st g idx j size cnt) as E. unfold strip in E. injection E. intros. repeat split; assumption.
Qed.

Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKF T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HM0 : MF0 st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HOST : let j := size_to_class (UNIT + cnt * (UNIT * size_class sc) - IB) in j = 15 \/ j = 19 \/ j = 23.
Hypothesis NOTK : ~ KCLS sc.
Hypothesis HK : forall st2 go L2 LS2, AG_POSTF idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_ftF :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  pose proof HOST as Hj. cbn zeta in Hj. fold size in Hj. fold j in Hj.
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - intros st2 idx L2 LS2 (ACT & LIVE & MF2 & RES).
    assert (HB2 : MFR sc st0 st2 /\ bounces st2 24 <= bounces st1 24).
    { destruct (MFR_host sc j st1 st2 Hj MF2) as [H02|[MF2' B2]].
      - split; [exact (MFR_MF0_l sc _ _ _ HM0 (MF0_MFR sc _ _ H02))| exact (proj2 H02)].
      - split; [exact (MFR_MF0_l sc _ _ _ HM0 MF2')| exact B2]. }
    destruct HB2 as [MF02 B2].
    destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2' & XN2)].
    +
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split; [exact (MFR_MF0_r sc _ _ _ MF02 (MF0_fm_st idle m st2 L2 BL LS2 INV2))|].
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      set (st' := agt (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (fst bg, sstart (MR st2 g) idx) cnt (cnt - 1)) in *.
      destruct (nest_layout_ctrl st2 g idx j size cnt) as (NLg & NLm & NLc).
      assert (GRX : s_groups st' = <[(fst bg, sstart (MR st2 g) idx) := mkGhdr (Some m) (Z.land (cnt - 1) 31)]> (s_groups st2)).
      { unfold st'. rewrite agt_groups. cbn [s_groups upd_meta put_meta Malloc.set_metas]. rewrite NLg. reflexivity. }
      assert (MRo : forall m', m' <> m -> MR st' m' = MR st2 m').
      { intros m' NEm. unfold st'. rewrite (agt_MR_other _ sc m _ cnt (cnt - 1) m' NEm). unfold MR. rewrite get_meta_rec_upd_other by exact NEm.
        unfold get_meta_rec. rewrite NLm. reflexivity. }
      assert (MF2x : MFR sc st0 st').
      { constructor.
        - intros b' m' ai' Hb'. destruct (decide (b' = (fst bg, sstart (MR st2 g) idx))) as [->|NE].
          + right. left. rewrite GR' in Hb'. inversion Hb'. subst m'. rewrite MR'. reflexivity.
          + rewrite GRX, lookup_insert_ne in Hb' by congruence.
            assert (NEm : m' <> m) by (intros ->; exact (idle_not_gmeta _ st2 L2 BL LS2 m b' ai' INV2 ltac:(cbn; left; reflexivity) Hb')).
            destruct (mfr_old _ _ _ MF02 _ _ _ Hb') as [[E G]|N]; [left| right].
            * split; [exact E|]. rewrite (MRo m' NEm). exact G.
            * rewrite (MRo m' NEm). exact N.
        - intros H98. pose proof (mfr_bnc _ _ _ MF02 H98) as B02.
          unfold st'. unfold bounces at 1. unfold ctx. rewrite agt_ctx, c_bounces_set_usage_map. cbn [s_ctx upd_meta put_meta Malloc.set_metas].
          rewrite NLc. change (default 0 (c_bounces (s_ctx st2) !! 24)) with (bounces st2 24).
          pose proof (proj2 HM0). destruct (sc =? 31); lia. }
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split; [exact MF2x|].
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'|]. split; [exact TF'|].
      intros HKc. exfalso. exact (NOTK HKc).
Qed.
End NEST_BRANCH.


Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKF T rec sc Post.

Theorem alloc_group_ftF idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  (forall st2 go L2 LS2, AG_POSTF idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
  ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  assert (HNR0 : forall st1, AM_frame st st1 -> forall q r, s_regions st !! q = Some r -> (q < s_next_rid st1)%N).
  { intros st1 AF q r Hq. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). pose proof (amf_next_rid _ _ AF). lia. }
  assert (HM00 : forall st1, AM_frame st st1 -> GEQ st st1 -> MF0 st st1).
  { intros st1 AF GE. apply MF0_of; [intros b h Hb; rewrite (amf_groups _ _ AF) in Hb; exists h; auto| exact GE| unfold bounces, ctx; rewrite (amf_bounces _ _ AF); lia]. }
  eapply (alloc_meta_ftG T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply GEQ_refl| apply lf_refl].
  -
    intros st1 L1 LS1 INV1 AF GE LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (MF0_MFR sc _ _ (HM00 st1 AF GE))|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  -
    intros st1 L1 LS1 m INV1 NIm AF GE LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (HM00 st1 AF GE) as HM0. pose proof (HNR0 st1 AF) as HNR.
    pose proof (amf_usage _ _ AF sc) as HU.
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    +
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns).
      assert (HKU : KCLS sc -> u1 = usage st1 sc).
      { intros [->|[->| ->]]; reflexivity. }
      assert (HKN : KCLS sc -> bounces st 24 <= 99 -> ns = false).
      { intros HKc HKb. unfold ns, is_bouncing. destruct HKc as [->|[->| ->]]; [| reflexivity| reflexivity].
        change (sc_in_seq_range 31) with true. change (31 - 7) with 24. cbn [andb]. apply Z.leb_gt. pose proof (proj2 HM0). lia. }
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        apply (ag_mmap_ftF T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) HM0 HNR); try assumption.
        intros HKc HKp HKb. unfold c2, c1 in E3. rewrite (HKU HKc), (HKN HKc HKb) in E3.
        exact (ag_cn3_K sc req (usage st1 sc) c3 n3 HKc ltac:(rewrite HU; exact HKp) ltac:(rewrite (ia_usage _ (proj1 (proj2 INV1)) sc Hsc); exact (gcnt_nonneg _ _ _ _ _ sc INV1)) Hreq E3). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    +
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      assert (HOST : let j := size_to_class (UNIT + c1 * (UNIT * size_class sc) - IB) in j = 15 \/ j = 19 \/ j = 23).
      { pose proof (nest_host sc (usage st1 sc) Hsc) as NH. cbn zeta in NH. unfold c1, ag_cnt1 in HB |- *. unfold bump in NH. apply NH. lia. }
      assert (NOTK : ~ KCLS sc).
      { intros HKc. apply (K_not_nested sc c1 HKc); [| exact HB]. pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. lia. }
      exact (ag_nest_ftF T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) HM0 NEST HOST NOTK HK).
Qed.
End AG.


Section SLOT.
Variable T : Type.
Variable Post : mled -> T -> Prop.

Theorem alloc_slot_ftF (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall st1 idx L1 LS1, SLOT_POSTF idle sc req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (try_avail_okB T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & [TAF RES] & BLE1).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  pose proof (MF0_taf st st1 sc TAF BLE1) as MF01.
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1 & HO & SG)].
  -
    change (negb (0 =? 0)) with false. cbn iota.
    assert (REC : REC_OKF T (alloc_slot full_lay f) sc Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_ftF T (alloc_slot full_lay f) sc Post REC idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & MF2 & RES2).
    pose proof (MFR_MF0_l sc _ _ _ MF01 MF2) as MF02.
    destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2' & KG2).
      cbn zeta.
      destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                  ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
        as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4 & SG4).
      set (st4 := queue_st (LActive sc) g (upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2)) in *.
      assert (MF24 : MF0 st2 st4).
      { apply MF0_of.
        - intros bb h Hbb. rewrite G4 in Hbb. exists h. auto.
        - intros x. destruct (aptr_eq_dec x g) as [->|NE]; [exact SG4|]. apply same_geo_data. unfold st4. rewrite (queue_data (LActive sc) g _ x).
          unfold MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity.
        - unfold st4. destruct (queue_frame (LActive sc) g (upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CB).
          unfold bounces, ctx. rewrite (cb_bounces _ _ CB). cbn. lia. }
      rewrite EQ. eapply HK. split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
      split; [exact (MFR_MF0_r sc _ _ _ MF02 MF24)|].
      right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
      split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
      split; [exact INV4|]. split; [exact TF4|].
      intros HKc HKp HKb. right.
      destruct (KG2 HKc ltac:(rewrite (taf_usage _ _ _ TAF); exact HKp) ltac:(pose proof (BLE1 24); lia)) as (L0 & R0 & S0 & O0 & OTH).
      split; [rewrite L4; exact L0|]. split; [rewrite <- (taf_regions _ _ _ TAF); exact R0|]. split; [exact S0|].
      split; [exact (gonly0_same _ _ _ G4 O0)|].
      intros b' m' ai' Hb' NE. rewrite G4 in Hb'.
      pose proof (OTH _ _ _ Hb' NE) as O12. destruct (proj1 MF24 _ _ _ ltac:(rewrite G4; exact Hb')) as [_ G24].
      destruct O12 as [[ai1 Hb1] G12]. destruct (proj1 MF01 _ _ _ Hb1) as [E01 G01].
      split; [exact E01|]. eapply same_geo_trans; [exact G24| eapply same_geo_trans; [exact G12| exact G01]].
    + destruct RES2 as [INV2 TF2']. eapply HK. split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
      split; [exact MF02|].
      left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
  -
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx. eapply HK.
    split; [exact ACT1|]. split; [reflexivity|]. split; [exact (MF0_MFR sc _ _ MF01)|]. right.
    pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
    pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
    exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
    split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. split; [apply TF0_TF2; exact TF1|].
    intros _ _ _. left. split; [exact HO| exact SG].
Qed.
End SLOT.
