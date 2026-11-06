(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QYTG QPiB Qatc QSfG QdBa QpFQ Ql2m QjcB QLaA Q1am QoCS QQg5 QPWv QlOh QQCz QcV4 Q7RC QhnL QBv7 Qn5J QhfJ QvVk QwQw Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QPiB Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QdBa.Mq2 QLaA.Mq0 Q1am.Mq0 QoCS QQg5 QQg5.Mq3 QPWv Q1am.Mq1 QQg5.Mq0 QSfG QoCS.Mq0 QlOh.Mq0 QQCz QcV4 Q7RC QSfG.Mq0 QhnL QBv7.
Import Qn5J QhfJ QvVk QwQw.
Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation SHF st := (c_meta_alloc_shift (s_ctx st)).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition FRESHW (SH : Z) : Z := AMW SH + 2 ^ 20.
Definition FRESHD : nat := 5%nat.

Definition AGN (st0 st2 : mstate) : Prop :=
(forall j, active st2 j = active st0 j) /\ s_groups st2 = s_groups st0 /\
(forall b x ai, s_groups st0 !! b = Some (mkGhdr (Some x) ai) -> MR st2 x = MR st0 x).
Definition AGX (st0 st2 : mstate) (m : aptr) (sc cnt needed : Z) : Prop :=
(forall j, active st2 j = active st0 j) /\
(exists b ai, s_groups st2 = <[b := mkGhdr (Some m) ai]> (s_groups st0) /\ s_groups st0 !! b = None /\ m_mem (MR st2 m) = Some b) /\
(forall b x ai, s_groups st0 !! b = Some (mkGhdr (Some x) ai) -> x <> m /\ MR st2 x = MR st0 x) /\
m_sizeclass (MR st2 m) = sc /\
get_stride (MR st2 m) = (if cnt - 1 =? 0 then needed - UNIT else UNIT * size_class sc).

Definition agu (sc : Z) (st : mstate) : Z := if Z.even sc && (sc <? 32) then usage st sc + usage st (sc + 1) else usage st sc.

Definition SLX (st0 st4 : mstate) (sc req : Z) : Prop :=
exists g c3 n3,
ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc (usage st0 sc)) (agu sc st0) (is_bouncing sc st0)) (agu sc st0) (is_bouncing sc st0) = (c3, n3) /\
active st4 sc = Some g /\ (forall j, j <> sc -> active st4 j = active st0 j) /\
(exists b ai, s_groups st4 = <[b := mkGhdr (Some g) ai]> (s_groups st0) /\ s_groups st0 !! b = None /\ m_mem (MR st4 g) = Some b) /\
(forall b x ai, s_groups st0 !! b = Some (mkGhdr (Some x) ai) -> x <> g /\ MR st4 x = MR st0 x) /\
m_next (MR st4 g) = Some g /\ m_sizeclass (MR st4 g) = sc /\
get_stride (MR st4 g) = (if c3 - 1 =? 0 then n3 - UNIT else UNIT * size_class sc).

#[using="Type"] Lemma MR_of_metas st st' x : s_metas st' = s_metas st -> MR st' x = MR st x.
Proof. intros E. unfold MR, get_meta_rec. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma AGN_amf st st1 : AM_frame st st1 -> AGN st st1.
Proof. intros AF. split; [exact (amf_active _ _ AF)| split; [exact (amf_groups _ _ AF)| exact (amf_hmetas _ _ AF)]]. Qed.
#[using="Type"] Lemma AGN_trans sa sb sc : AGN sa sb -> AGN sb sc -> AGN sa sc.
Proof.
intros (A1 & A2 & A3) (B1 & B2 & B3). split; [intros j; rewrite B1; apply A1| split; [congruence|]].
intros b x ai Hb. rewrite <- (A3 b x ai Hb). apply (B3 b x ai). rewrite A2. exact Hb.
Qed.

#[using="Type"] Lemma idle_not_hosted X st L BL LS g b m ai :
INVL X st L BL LS -> In g (x_idle X) -> s_groups st !! b = Some (mkGhdr (Some m) ai) -> m <> g.
Proof.
intros INV Hg Hb ->. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (im_idle _ _ _ IM g Hg) as [E _].
destruct (im_hdr _ _ _ IM b _ Hb) as (m1 & E1 & MM & _). cbn in E1. injection E1 as <-.
unfold MR, get_meta_rec in MM. rewrite E in MM. cbn in MM. discriminate.
Qed.

#[using="Type"] Lemma groups_fresh_rid X st L BL LS o : INVL X st L BL LS -> s_groups st !! (s_next_rid st, o) = None.
Proof.
intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (s_groups st !! (s_next_rid st, o)) as [h|] eqn:E; [| reflexivity]. exfalso.
destruct (ig_region _ _ _ IG _ _ E) as (r & Hr & _). cbn [fst] in Hr. pose proof (ir_ids _ _ _ IR _ _ Hr). lia.
Qed.

#[using="Type"] Lemma fm_st_agn X st L BL LS m : INVL X st L BL LS -> In m (x_idle X) -> AGN st (fm_st st m).
Proof.
intros INV Hm. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). pose proof (inv_L_lists _ _ IL) as LO.
destruct (queue_frame LFree m (put_meta m meta0 st)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & QC).
split; [| split].
- intros j. change (active (fm_st st m) j) with (get_head (fm_st st m) (LActive j)). unfold fm_st. rewrite queue_head.
destruct (decide (LActive j = LFree)); [discriminate| reflexivity].
- unfold fm_st. rewrite Q5. reflexivity.
- intros b x ai Hb.
assert (NX : x <> m) by exact (idle_not_hosted X st L BL LS m b x ai INV Hm Hb).
assert (NXF : ~ In x (LS LFree)).
{ intros Hin. pose proof (il_free _ _ IL x Hin) as E. destruct (im_hdr _ _ _ IM b _ Hb) as (m1 & E1 & MM & _). cbn in E1. injection E1 as <-. rewrite E in MM. cbn in MM. discriminate. }
unfold fm_st, MR, get_meta_rec. rewrite (queue_metas_other LFree m (put_meta m meta0 st) x NX).
+ cbn. rewrite lookup_insert_ne by congruence. reflexivity.
+ intros a Ha. change (get_head (put_meta m meta0 st) LFree) with (get_head st LFree) in Ha.
assert (Hin : In a (LS LFree)).
{ pose proof (il_head _ _ IL LFree) as HH. rewrite Ha in HH. destruct (LS LFree) as [|a' rest]; cbn in HH; [discriminate|]. injection HH as ->. left. reflexivity. }
split; [intros ->; exact (NXF Hin)|].
assert (NAm : a <> m) by (intros ->; exact (proj2 (im_idle _ _ _ IM m Hm) (ex_intro _ LFree Hin))).
unfold MR. rewrite (get_meta_rec_put_other _ _ _ _ NAm). fold (MR st a).
destruct (lists_prev_in st LS LO LFree a Hin) as (y & Hy & HP & _). rewrite HP. intros E. injection E as ->. exact (NXF Hy).
Qed.

Section MMAP_BRANCH_KS.
Context {T : Type} (isS : T -> bool) (P : T -> Prop) (SH : Z).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T).
Variables (κN κS : kind) (Wf W : Z) (Df D : nat).
Hypothesis HW : Wf <= W.
Hypothesis HD : (Df <= D)%nat.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis SH1 : SHF st1 <= SH + 1.
Hypothesis HGR1 : s_groups st1 = s_groups st0.
Hypothesis HHM1 : forall b x ai, s_groups st0 !! b = Some (mkGhdr (Some x) ai) -> MR st1 x = MR st0 x.
Hypothesis HKN : forall st2 L2, AGN st0 st2 -> SHF st2 <= SH + 1 -> KSUM isS P Wf Df L2 (k st2 None) κN W D.
Hypothesis HKS : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 (Some go) L2 LS2 -> AGX st0 st2 go sc cnt needed -> SHF st2 <= SH + 1 -> KSUM isS P Wf Df L2 (k st2 (Some go)) κS W D.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

#[using="SH idle st0 L0 BL LS1 req HW HD INV1 NIm TF1 Hsc Hfit HA1 HA0 HL1 HG1 GRP RED SH1 HGR1 HHM1 HKN HKS"] Theorem ag_mmap_ks :
KSUM isS P Wf Df L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r needed st1' in
ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k))
κS (W + needed) (S D).
Proof.
assert (SH1' : SHF st1' <= SH + 1).
{ unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); cbn; exact SH1. }
destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SHD1 & TK1 & ACT1 & TF1' & RG1 & SS1').
assert (ACT1' : forall sc', active st1' sc' = active st0 sc') by (intros sc'; unfold st1'; rewrite ACT1; apply HA1).
fold st1' in INV1', SHD1, TK1, ACT1, TF1', RG1, SS1'.
assert (GM1' : s_groups st1' = s_groups st0 /\ s_metas st1' = s_metas st1).
{ destruct (account_bounce_fields sc st1) as (_ & _ & _ & _ & _ & A6 & A7 & _). destruct (step_seq_fields (account_bounce sc st1)) as (_ & _ & _ & _ & _ & B6 & B7 & _).
unfold st1'. rewrite B7, A7, B6, A6. split; [exact HGR1| reflexivity]. }
destruct GM1' as [G1' M1'].
pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
assert (RU : round_up_pg needed = needed) by (apply round_up_pg_id; unfold PGSZ; exact G2).
eapply (ks_ev' isS P Wf Df L1 _ _ κN κS _ W D); [reflexivity| | exact HW| | | | intros E; discriminate E| reflexivity].
- cbn [esz_ok]. intros _. rewrite RU. lia.
- cbn [ecost]. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false. cbv iota. rewrite RU. reflexivity.
- intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca. apply negb_false_iff in Ca.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb]. rewrite Ca.
rewrite free_meta_eq. apply HKN.
{ eapply AGN_trans; [| exact (fm_st_agn _ st1' L1 BL LS1 m INV1' ltac:(left; reflexivity))].
split; [exact ACT1'| split; [exact G1'| intros b x ai Hb; rewrite (MR_of_metas st1 st1' x M1'); exact (HHM1 b x ai Hb)]]. }
unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC). rewrite (cb_shift _ _ QC). autorewrite with mst. first [exact SH1'| exact SH1].
- intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca. apply negb_true_iff in Ca.
change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then Qfya.set_metas ((a, needed, 0) :: ld_metas L1) L1 else Qfya.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb]. rewrite Ca.

destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha Ca ltac:(unfold LEN_MAX; lia)) as INV2.
rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
{ rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
assert (NS : s_shadow st2 !! rid = None).
{ rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); apply ACT1').
assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
assert (HAI0 : sc = 0 -> AI = cnt - 1).
{ intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite ag_tail_eq.
change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
destruct (ag_top_ok idle st2 (Qfya.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
= if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
{ rewrite MR'. unfold get_stride. cbn. reflexivity. }
assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
eapply HKS. 3:{ rewrite agt_ctx. cbn. rewrite Est2. cbn. exact SH1'. }
2:{
split; [intros j; rewrite ACT'; apply ACT2|]. split; [| split; [| split]].
- exists (rid, 0), (Z.land AI 31). split; [| split].
+ rewrite agt_groups. f_equal. transitivity (s_groups st2); [reflexivity|].
rewrite Est2. change (s_groups (fst (new_region RKGroup a needed st1'))) with (s_groups st1'). exact G1'.
+ rewrite <- G1', Erid. exact (groups_fresh_rid _ st1' L1 BL LS1 0 INV1').
+ rewrite MR'. reflexivity.
- intros b x ai Hb.
assert (NX : x <> m) by (apply (idle_not_hosted _ st1 L1 BL LS1 m b x ai INV1); [left; reflexivity| rewrite HGR1; exact Hb]).
split; [exact NX|]. rewrite (agt_MR_other _ sc m (rid, 0) cnt AI x NX).
unfold MR at 1. rewrite get_meta_rec_upd, (aptr_eqb_neq x m NX), get_meta_rec_upd_ctx. fold (MR st2 x).
rewrite Est2. change (MR (fst (new_region RKGroup a needed st1')) x) with (MR st1' x).
rewrite (MR_of_metas st1 st1' x M1'). exact (HHM1 b x ai Hb).
- rewrite MR'. reflexivity.
- rewrite STR, E12. reflexivity. }
split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
split.
{ eapply GP_trans; [exact HG1|]. split; [|split].
- intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
- rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'.
- intros HI. rewrite agt_ctx. cbn. rewrite Est2. cbn. rewrite (st1'_init st1 sc). exact HI. }
exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
assert (FB : fresh_beyond (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) (rid, 0)).
{ apply (fresh_beyond_hdr _ (rid, 0) (s_tick st2)); [| cbn; lia| reflexivity]. cbn [fst snd].
unfold agt. autorewrite with mst. unfold hdr_havoc, upd_shadow. autorewrite with mst. rewrite lookup_insert_eq.
unfold get_shadow. autorewrite with mst. rewrite NS. cbn. reflexivity. }
split; [| split; [| split; [| split; [exact INV'| split; [apply TF0_TF2; exact TF'| intros _; exact FB]]]]].
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
Qed.
End MMAP_BRANCH_KS.

Definition big_class (sc : Z) : Prop := 20 <= sc < 48.

Definition bigc_f (sc : Z) : bool :=
forallb (fun c => PGSZ / 2 <? UNIT * size_class sc * bump (UNIT * size_class sc) c + UNIT) (cnt0_list sc).
#[using="Type"] Lemma big_class_check : forallb bigc_f (zrange 20 28) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma big_class_mmap sc u : big_class sc -> PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u + UNIT.
Proof.
intros Hsc. pose proof (forallb_zrange bigc_f 20 28 sc big_class_check ltac:(lia) ltac:(unfold big_class in Hsc; lia)) as C.
unfold bigc_f in C. rewrite forallb_forall in C. specialize (C _ (cnt0_in sc u)). apply Z.ltb_lt in C.
unfold ag_cnt1. cbn zeta. unfold bump in C. exact C.
Qed.

#[using="Type"] Lemma size_to_class_big n : 1004 < n -> n < MMAP_THRESHOLD -> big_class (size_to_class n).
Proof.
intros H1 H2. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. unfold big_class. split; [| lia].
destruct (Z.lt_ge_cases (size_to_class n) 20) as [LT|GE]; [| exact GE]. exfalso.
pose proof (size_class_le (size_to_class n) 19 ltac:(lia) ltac:(lia) ltac:(lia)) as M.
change (size_class 19) with 63 in M. unfold UNIT, IB in FIT. lia.
Qed.

Section FRESH.
Variables (SH : Z) (W : Z) (D : nat).
Hypothesis HSH : 0 <= SH <= 16.

#[using="HSH"] Theorem alloc_group_fresh_ks {T} (isS : T -> bool) (P : T -> Prop) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T)
idle st L BL LS sc req (k : mstate -> optr -> M T) bail (κN κS : kind) :
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> big_class sc -> 0 <= req -> req + IB <= UNIT * size_class sc ->
active st sc = None -> SHF st <= SH ->
(forall st2 L2, AGN st st2 -> SHF st2 <= SH + 1 -> KSUM isS P W D L2 (k st2 None) κN W D) ->
(forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 (Some go) L2 LS2 ->
(exists c3 n3, ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc (usage st sc)) (agu sc st) (is_bouncing sc st)) (agu sc st) (is_bouncing sc st) = (c3, n3)
/\ AGX st st2 go sc c3 n3) ->
SHF st2 <= SH + 1 -> KSUM isS P W D L2 (k st2 (Some go)) κS W D) ->
KSUM isS P W D L (alloc_group T full_lay rec st sc req k bail) κS (W + 2 ^ 20 + AMW SH) (S D + AMD)%nat.
Proof.
intros INV TF ND Hbc Hreq Hfit HA SHC HKN HKS. pose proof Hbc as Hsc. unfold big_class in Hsc.
assert (Hsc' : 0 <= sc < 48) by lia.
unfold alloc_group.
assert (AK : κS = am_kind κN κS st) by reflexivity.
rewrite AK.
eapply (alloc_meta_ks isS P W D BL _ bail (X_as idle) st L κN κS (W + 2 ^ 20) (S D) SH ltac:(lia) HSH);
[ | | exact INV| apply amf_refl| apply lf_refl| exact SHC| split; reflexivity].
-
intros st1 L1 LS1 INV1 AF LF SH1. cbn beta iota. eapply (KSUM_mono isS P W D _ _ _ W D); [apply HKN; [exact (AGN_amf _ _ AF)| exact SH1]| lia| lia].
-
intros st1 L1 LS1 m INV1 NIm AF LF SH1 AMQ1. cbn beta iota zeta.
change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
with (cnt0_of sc (usage st1 sc)).
change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
with (ag_cnt1 sc (usage st1 sc)).
change (lh_nest full_lay) with nest_layout.
assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
pose proof (ag_arith sc req (usage st1 sc)) as AR.
set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
pose proof (big_class_mmap sc (usage st1 sc) Hbc) as HB. fold c1 in HB.
rewrite (proj2 (Z.ltb_lt _ _) HB).
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
assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
KSUM isS P W D L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r n3 st1' in
ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
(let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k))
κS (W + 2 ^ 20) (S D)).
{ intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc' Hreq Hfit) HB E3) as [GRP RED].
pose proof (grp_ok_sound sc c3 n3 GRP) as G. cbn zeta in G. destruct G as (_ & _ & G3 & _).
eapply (KSUM_mono isS P W D _ _ _ (W + n3) (S D)); [| lia| lia].
apply (ag_mmap_ks isS P SH idle st st1 L L1 BL LS1 m sc req c3 n3 k bail κN κS W W D D ltac:(lia) ltac:(lia) INV1 NIm TF1 Hsc' Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED SH1
(amf_groups _ _ AF) (amf_hmetas _ _ AF) HKN).
intros st2 go L2 LS2 AG AX S2. apply (HKS st2 go L2 LS2 AG); [| exact S2]. exists c3, n3. split; [| exact AX].
rewrite <- E3. unfold c2, c1, u1, ns, st1'.
assert (EU : forall j, usage st1 j = usage st j) by (intros j; apply (amf_usage _ _ AF)).
assert (EB : is_bouncing sc st1 = is_bouncing sc st) by (unfold is_bouncing, bounces, ctx; rewrite (amf_bounces _ _ AF); reflexivity).
destruct (account_bounce_fields sc st1) as (_ & _ & _ & _ & _ & _ & _ & AU8). destruct (step_seq_fields (account_bounce sc st1)) as (_ & _ & _ & _ & _ & _ & _ & BU8).
unfold agu. rewrite BU8, AU8, !EU, EB. reflexivity. }
unfold ag_cn3 in GO. cbn zeta in GO.
destruct (negb ns && (c2 <=? 7)).
+ destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
* cbn beta iota. exact (GO _ _ eq_refl).
* cbn beta iota. exact (GO _ _ eq_refl).
+ cbn beta iota. exact (GO _ _ eq_refl).
Qed.

#[using="HSH"] Theorem alloc_slot_fresh_ks {T} (isS : T -> bool) (P : T -> Prop) (f : nat) idle st L BL LS sc req (k : mstate -> Z -> M T) bail (κN κS : kind) :
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> big_class sc -> 0 <= req -> req + IB <= UNIT * size_class sc ->
active st sc = None -> SHF st <= SH ->
(forall st1 L1, AGN st st1 -> SHF st1 <= SH + 1 -> KSUM isS P W D L1 (k st1 (-1)) κN W D) ->
(forall st1 L1 LS1, SLOT_POST idle sc req st L BL st1 0 L1 LS1 -> active st1 sc <> None -> SLX st st1 sc req -> SHF st1 <= SH + 1 -> KSUM isS P W D L1 (k st1 0) κS W D) ->
KSUM isS P W D L (alloc_slot full_lay (S f) st sc req k bail) κS (W + 2 ^ 20 + AMW SH) (S D + AMD)%nat.
Proof.
intros INV TF ND Hbc Hreq Hfit HA SHC HKN HKS. pose proof Hbc as Hsc. unfold big_class in Hsc.
change (alloc_slot full_lay (S f) st sc req k bail) with
(try_avail sc st (fun st1 first =>
if negb (first =? 0) then k st1 (ctz32 first)
else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail) bail).
unfold try_avail. rewrite HA. change (negb (0 =? 0)) with false. cbn iota.
apply (alloc_group_fresh_ks isS P (alloc_slot full_lay f) idle st L BL LS sc req _ bail κN κS INV TF ND Hbc Hreq Hfit HA SHC).
- intros st2 L2 AGN2 SH2. cbn beta iota. apply HKN; [exact AGN2| exact SH2].
- intros st2 g L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) (c3 & n3 & E3 & AX) SH2.
destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2' & AZ2).
cbn zeta.
destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl ltac:(lia)
ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4 & ID4).
rewrite EQ. eapply HKS; [| rewrite HA4; discriminate| |].
3:{ destruct (queue_frame (LActive sc) g (upd_meta g (fun r : meta => m_set_avail (m_avail r - 1) r) st2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC).
rewrite (cb_shift _ _ QC). autorewrite with mst. exact SH2. }
2:{
destruct AX as (XA & (b0 & ai0 & XG & XN & XM) & XH & XSC & XSTR).
set (fav := fun r : meta => m_set_avail (m_avail r - 1) r).
assert (HN2 : get_head (upd_meta g fav st2) (LActive sc) = None).
{ rewrite get_head_upd_meta. change (get_head st2 (LActive sc)) with (active st2 sc). rewrite ACT2 by lia. exact HA. }
exists g, c3, n3. split; [exact E3|]. split; [exact HA4|]. split; [intros j NE; rewrite (ACT4 j NE); apply XA|].
split; [| split; [| split; [| split; [exact SC4| rewrite STR4; exact XSTR]]]].
+ exists b0, ai0. split; [rewrite G4; exact XG|]. split; [exact XN|].
pose proof (queue_data (LActive sc) g (upd_meta g fav st2) g) as QD. apply data_of_eq in QD. destruct QD as (Dm & _). rewrite Dm.
unfold MR. rewrite get_meta_rec_upd, aptr_eqb_refl. exact XM.
+ intros b' x ai' Hb'. destruct (XH b' x ai' Hb') as [NX EX]. split; [exact NX|]. rewrite <- EX.
unfold MR, get_meta_rec. rewrite (queue_metas_other (LActive sc) g (upd_meta g fav st2) x NX); [| intros a Ha; rewrite HN2 in Ha; discriminate].
rewrite s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
+ rewrite (queue_next (LActive sc) g (upd_meta g fav st2) g), HN2, aptr_eqb_refl. reflexivity. }
split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; reflexivity|]. split; [exact LIVE2|].
split; [eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4| exact ID4]]|].
right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
split; [exact INV4|]. split; [exact TF4|].
intros U o Ho. unfold get_shadow. rewrite SH4. unfold undersized in U. rewrite SC4, STR4 in U.
assert (SCg2 : m_sizeclass (MR st2 g) = sc) by (rewrite Em; reflexivity).
apply AZ2; [| exact Ho]. unfold undersized. rewrite SCg2. exact U.
Qed.

#[using="HSH"] Theorem malloc_core_fresh_ks st L BL LS n :
INVL x0 st L BL LS -> TF0 st -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = None -> active st (Z.lor (size_to_class n) 1) = None ->
KSUM isC (PSH SH) W D L (malloc_core full_lay st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV TF Hn SHC HA HA'. unfold FRESHW, FRESHD.
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT, MMAP_THRESHOLD in *; lia).
unfold malloc_core. rewrite Hov. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
pose proof (size_to_class_big n ltac:(lia) ltac:(lia)) as BC.
unfold malloc_small_ctrl. rewrite HA.
set (sc0 := size_to_class n) in *.
set (sc := if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then _ else sc0).
assert (SC' : big_class sc /\ n + IB <= UNIT * size_class sc /\ active st sc = None).
{ subst sc.
destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2.
rewrite (lor1_even sc0 ltac:(lia) EV) in HA' |- *. unfold big_class in BC |- *. split; [lia|]. split; [| exact HA'].
pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
clearbody sc. destruct SC' as (BC' & FIT' & HAsc). pose proof BC' as Hsc. unfold big_class in Hsc.
rewrite HAsc. change (lowbit 0) with 0. cbn [negb Z.eqb].
unfold FUEL. replace (D + 5)%nat with (S D + AMD)%nat by (unfold AMD; lia).
replace (W + (AMW SH + 2 ^ 20)) with (W + 2 ^ 20 + AMW SH) by lia.
apply (alloc_slot_fresh_ks isC (PSH SH) 63 [] st L BL LS sc n _ (ret (st, @None (aptr * Z))) KN KS INV TF); try assumption.
- apply NoDup_nil_2.
- lia.
- intros st1 L1 _ SH1'. change (-1 <? 0) with true. cbv iota. constructor; [exact SH1'| lia| lia].
- intros st1 L1 LS1 _ HA1 _ SH1'. change (0 <? 0) with false. cbv iota. destruct (active st1 sc); [| congruence]. constructor; [exact SH1'| lia| lia].
Qed.

#[using="Type"] Lemma alloc_slot_S {T} lay f st sc req (k : mstate -> Z -> M T) bail :
alloc_slot lay (S f) st sc req k bail =
try_avail sc st (fun st1 first =>
if negb (first =? 0) then k st1 (ctz32 first)
else alloc_group T lay (alloc_slot lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail) bail.
Proof. reflexivity. Qed.

#[using="Type"] Lemma head_self_singleton X st L BL LS sc g :
INVL X st L BL LS -> active st sc = Some g -> m_next (MR st g) = Some g -> LS (LActive sc) = [g].
Proof.
intros INV HA NX. pose proof (proj1 (proj2 (proj2 (proj2 INV)))) as IL.
destruct (hd_list X st L BL LS sc g INV HA) as [rest HL].
pose proof (il_dll _ _ IL (LActive sc)) as DL. pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in DL, ND |- *.
destruct rest as [|r1 rest']; [reflexivity|]. exfalso.
cbn [dll app linked] in DL. destruct DL as (N1 & _ & _). rewrite NX in N1. inversion N1; subst.
inversion ND; subst. apply H1. constructor.
Qed.

#[using="HSH"] Theorem malloc_core_fullhead_ks st L BL LS n g :
INVL x0 st L BL LS -> TF0 st -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = Some g -> m_avail (MR st g) = 0 -> m_freed (MR st g) = 0 -> m_next (MR st g) = Some g ->
KSUM isC (PSH SH) W D L (malloc_core full_lay st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV TF Hn SHC HA AV FR NX. unfold FRESHW, FRESHD.
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT, MMAP_THRESHOLD in *; lia).
unfold malloc_core. rewrite Hov. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
pose proof (size_to_class_big n ltac:(lia) ltac:(lia)) as BC.
set (sc := size_to_class n) in *.
unfold malloc_small_ctrl. cbv zeta. fold sc. rewrite !HA. fold (MR st g). rewrite !AV. change (lowbit 0) with 0. cbn [negb Z.eqb].
unfold FUEL. rewrite alloc_slot_S.
pose proof (head_self_singleton x0 st L BL LS sc g INV HA NX) as HL.
destruct (dequeue_exhausted_ok x0 L BL sc eq_refl eq_refl SC st LS g INV HA AV FR) as (LS' & rest & INV' & HL' & HA' & _).
rewrite HL in HL'. injection HL' as <-. cbn [head_of] in HA'.
unfold try_avail. rewrite HA. fold (MR st g). rewrite AV. cbn [Z.eqb negb]. fold (MR st g). rewrite FR. cbn [Z.eqb].
rewrite HA'. cbn [Z.eqb negb].
set (st' := dequeue (LActive sc) g st) in *.
assert (TF' : TF0 st').
{ destruct (dequeue_frame (LActive sc) g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _). apply (TF0_ctrl st st'); [exact F2| exact F7| exact TF]. }
assert (SHC' : SHF st' <= SH).
{ destruct (dequeue_frame (LActive sc) g st) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FC). unfold st'. rewrite (cb_shift _ _ FC). exact SHC. }
replace (D + 5)%nat with (S D + AMD)%nat by (unfold AMD; lia).
replace (W + (AMW SH + 2 ^ 20)) with (W + 2 ^ 20 + AMW SH) by lia.
apply (alloc_group_fresh_ks isC (PSH SH) (alloc_slot full_lay 63) [] st' L BL LS' sc n _ (ret (st, @None (aptr * Z))) KN KS); try assumption.
- apply NoDup_nil_2.
- lia.
- intros st2 L2 _ SH2. change (-1 <? 0) with true. cbv iota. constructor; [exact SH2| lia| lia].
- intros st2 g' L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) _ SH2.
destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT2 & STR & UND & INV2 & TF2' & AZ2).
cbn zeta.
destruct (slot_finish_ok _ [] st2 L2 BL LS2 g' b ai last sc ml (fun st4 => if 0 <? 0 then ret (st4, None) else match active st4 sc with Some gp => ret (st4, Some (gp, 0)) | None => SVis (EUndef UBadPtr) (fun _ => ret (st, None)) end)
(ret (st, None)) INV2 Hb Em Hai Hl ltac:(lia) ltac:(rewrite ACT2 by lia; exact HA') UND TF2')
as (LS4 & EQ & INV4 & TF4 & HA4 & _).
rewrite EQ. change (0 <? 0) with false. cbv iota. rewrite HA4. constructor; [| lia| lia].
unfold PSH. cbn [fst]. destruct (queue_frame (LActive sc) g' (upd_meta g' (fun r : meta => m_set_avail (m_avail r - 1) r) st2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC).
rewrite (cb_shift _ _ QC). autorewrite with mst. exact SH2.
Qed.

#[using="HSH"] Theorem malloc_fresh_ks st L BL LS n :
INVL x0 st L BL LS -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = None -> active st (Z.lor (size_to_class n) 1) = None ->
KSUM isM (PSH SH) W D L (malloc st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV Hn SHC HA HA'. unfold malloc.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
apply (KSUM_sbind_same isC isM (PSH SH) (PSH SH) W D).
- intros L' [st1 [[g idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_ks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_fresh_ks st0 L BL LS n INV0 TF0' Hn); assumption.
Qed.

#[using="HSH"] Theorem cmalloc_fresh_ks st L BL LS n :
INVL x0 st L BL LS -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = None -> active st (Z.lor (size_to_class n) 1) = None ->
KSUM isCC (PSH SH) W D L (cmalloc (strip st) n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV Hn SHC HA HA'.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PSH SH (snd x)) (PSH SH) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold PSH. cbn [fst]. rewrite <- E. exact (fun H => H).
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PSH SH) W D). apply (malloc_fresh_ks st L BL LS n INV Hn SHC HA HA').
Qed.

#[using="HSH"] Theorem malloc_fullhead_ks st L BL LS n g :
INVL x0 st L BL LS -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = Some g -> m_avail (MR st g) = 0 -> m_freed (MR st g) = 0 -> m_next (MR st g) = Some g ->
KSUM isM (PSH SH) W D L (malloc st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV Hn SHC HA AV FR NX. unfold malloc.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
apply (KSUM_sbind_same isC isM (PSH SH) (PSH SH) W D).
- intros L' [st1 [[g' idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_ks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_fullhead_ks st0 L BL LS n g INV0 TF0' Hn); assumption.
Qed.

#[using="HSH"] Theorem cmalloc_fullhead_ks st L BL LS n g :
INVL x0 st L BL LS -> 1004 < n < MMAP_THRESHOLD -> SHF st <= SH ->
active st (size_to_class n) = Some g -> m_avail (MR st g) = 0 -> m_freed (MR st g) = 0 -> m_next (MR st g) = Some g ->
KSUM isCC (PSH SH) W D L (cmalloc (strip st) n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV Hn SHC HA AV FR NX.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PSH SH (snd x)) (PSH SH) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold PSH. cbn [fst]. rewrite <- E. exact (fun H => H).
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PSH SH) W D). apply (malloc_fullhead_ks st L BL LS n g INV Hn SHC HA AV FR NX).
Qed.

End FRESH.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhfJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhfJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition isF (r : mstate) : bool := true.
Definition PFR (SHV : Z) (r : mstate) : Prop := c_meta_alloc_shift (s_ctx r) = SHV.

Section FREE.
Variables (W : Z) (D : nat).

#[using="Type"] Theorem free_ks st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
KSUM isF (PFR (c_meta_alloc_shift (s_ctx st))) W D L (free st (Some (aadd c (UNIT * off)))) KS W (S D).
Proof.
intros INV Hk.
destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
cbn zeta in *.
set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
unfold free. rewrite FH. cbn [sbind]. unfold free_tail.
rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
fold (MR st1 m).
pose proof (ce_ctx _ _ CE1) as CX1.
destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
- constructor; [| lia| lia]. unfold PFR. cbn. rewrite ?CX1. reflexivity.
- destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
(fun st2 mi => match mi with
| Some (base, len) => if negb (len =? 0)
then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
else ret st2
| None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
as (st2 & mi & LS2 & EQ & _ & (RG2 & SE2 & ID2 & SH2) & RES2).
rewrite EQ.
assert (P2 : PFR (c_meta_alloc_shift (s_ctx st)) st2) by (unfold PFR; rewrite SH2, CX1; reflexivity).
destruct mi as [[base len]|].
+ destruct (Z.eqb_spec len 0) as [->|NZ]; cbn [negb Z.eqb].
* constructor; [exact P2| lia| lia].
* replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbn [negb].
eapply (ks_ev' isF (PFR (c_meta_alloc_shift (s_ctx st))) W D L _ _ KS KS _ W D);
[reflexivity| exact I| lia| cbn; lia| | intros ru Hru C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
intros ru Hru _. cbn [answer_ok] in Hru. rewrite Hru. constructor; [| lia| lia].
unfold PFR, drop_region. cbn. exact P2.
+ constructor; [exact P2| lia| lia].
Qed.

Section CTRL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="pans pupd Hpans"] Theorem cfree_ks (o : O) st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
KSUM isF (PFR (c_meta_alloc_shift (s_ctx st))) W D L (cfree (strip st) (Some c)) KS W (S D).
Proof.
intros INV Hk.
eapply (KSUM_strel (fun x => isF (snd x)) isF (fun x => PFR (c_meta_alloc_shift (s_ctx st)) (snd x)) _ W D (FREL (O:=O)));
[apply (free_control pans pupd st (aadd c (UNIT * off)) c); exact (INVL_hdr_ok pans pupd st L BL LS c off n INV Hk)| | |].
- intros; reflexivity.
- intros [o' st'] cs E HP. unfold FREL in E. cbn [snd] in E, HP |- *. rewrite <- E. exact HP.
- apply (KSUM_prun pans pupd Hpans isF (PFR _) W D). exact (free_ks st L BL LS c off n INV Hk).
Unshelve. all: try exact o.
Qed.
End CTRL.
End FREE.

End RC__1.
