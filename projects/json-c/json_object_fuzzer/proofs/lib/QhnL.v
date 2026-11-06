(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPWv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7RC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7RC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma INVL_set_tick X st L BL LS t : (s_tick st <= t)%N -> INVL X st L BL LS -> INVL X (set_tick t st) L BL LS.
Proof.
intros Ht (IR & IA & IM & IL & IG & IS & ISH).
assert (CE : ctrl_eq st (set_tick t st)) by (constructor; reflexivity).
split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
apply inv_SH_set_tick; [exact Ht| exact ISH].
Qed.

Definition CORE_POST (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
ld_live L1 = ld_live L /\ GP st0 (fst r) /\
match snd r with
| None => exists LS1, INVL x0 (fst r) L1 BL LS1
| Some (g, idx) => exists LS1 bg, let st1 := fst r in
hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
/\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
/\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
/\ (undersized (MR st1 g) -> fresh_beyond st1 bg)
end.

#[using="Type"] Lemma small_stride X st L BL LS bg g : INVL X st L BL LS -> hosts st bg g -> m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < 2 ^ 20.
Proof.
intros INV [ai Hb] Hsc. pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
destruct (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & LT). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of in LT.
pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (ex_intro _ ai Hb)) as [S _]. unfold UNIT in S. nia.
Qed.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

#[using="LS INV TF Hn"] Lemma malloc_small_ft : n < MMAP_THRESHOLD ->
ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POST st n L BL).
Proof.
intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
unfold malloc_small_ctrl.
set (sc0 := size_to_class n) in *.
set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
{ subst sc. destruct (active st sc0); [auto|].
destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2.
rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
clearbody sc. destruct SC' as [SC' FIT'].
destruct (active st sc) as [gp|] eqn:HA.
-
destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
+ rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].

apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
* unfold FUEL. cbn. lia.
* apply NoDup_nil_2.
* intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1 & AZ1)].
-- cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
-- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). split; [unfold IB; lia| exact AZ1].
+
destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|].
pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
{ unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
destruct MRg as (ML & MS & MSS & MSC).
exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
rewrite Esc in STR. split; [lia|].
split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). split; [unfold IB; lia|].

intros U. exfalso. unfold undersized in U. rewrite MSC, Esc in U. destruct U as [U|U]; lia.
-
change (lowbit 0) with 0. cbn [negb Z.eqb].
apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
+ unfold FUEL. cbn. lia.
+ apply NoDup_nil_2.
+ intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1 & AZ1)].
* cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
* replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). split; [unfold IB; lia| exact AZ1].
Qed.

#[using="LS INV TF Hn"] Lemma malloc_big_ft : MMAP_THRESHOLD <= n -> size_overflows n = false ->
ftree L
(SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
if is_err r then ret (st, None) else
let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
let st2 := step_seq st1 in
alloc_meta st2 (fun st3 go =>
match go with
| None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
| Some g =>
let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
(m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
ret (st7, Some (g, 0))
end) (ret (st, @None (aptr * Z)))))
(CORE_POST st n L BL).
Proof.
intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
set (needed := n + IB + UNIT).
assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
apply ftree_vis; [reflexivity| reflexivity| | |].
- cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
unfold LEN_MAX. clear -HN. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then Qfya.set_metas ((a, needed, 0) :: ld_metas L) L else Qfya.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
destruct (is_err a) eqn:ER.
+ cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
+ destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
rewrite <- Est1, <- Erid in INV1.
set (L1 := Qfya.set_groups ((a, needed) :: ld_groups L) L) in *.
assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
assert (NS1 : s_shadow st1 !! rid = None).
{ rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
assert (TF1 : TF0 (step_seq st1)).
{ destruct (step_seq_fields st1) as (A & B & _). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
eapply (alloc_meta_ft (mstate * option (aptr * Z)) BL (CORE_POST st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1);
[ | | exact INV2| apply amf_refl| apply lf_refl].
*
intros st3 L3 LS3 INV3 AF LF. cbn beta iota.
apply ftree_vis; [reflexivity| reflexivity| | |].
-- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
-- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd event_post].
split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
split.
{ split; [|split].
- intros q rq Hq Kq. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions. rewrite lookup_delete_ne.
+ apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
+ intros ->. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). rewrite Erid in H. lia.
- transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity.
- intros HI. transitivity (c_init_done (s_ctx st3)); [reflexivity|]. apply (amf_init _ _ AF).
unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; cbn; exact HI. }
exists LS3.
pose proof (INVL_drop_orph (xorph x0 (Some rid)) st3 L3 BL LS3 rid (mkRegion RKGroup a needed) INV3 eq_refl
(amf_regions _ _ AF rid _ ltac:(rewrite SS4; exact Hr1) eq_refl)) as INV4.
cbn [r_base xorph x_idle x_zomb x_pend x_fresh x_orph] in INV4. exact INV4.
-- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
*
intros st3 L3 LS3 g INV3 NIg AF LF. cbn beta iota zeta.
change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [cbn; exact (lf_live _ _ LF)|].
split.
{ split; [|split].
- intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
- rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity.
- intros HI. transitivity (c_init_done (s_ctx st6)); [reflexivity|]. rewrite CTX6. apply (amf_init _ _ AF).
unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; cbn; exact HI. }
pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
set (st7 := upd_ctx _ st6) in *.
assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
{ unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
rewrite SS0. change (fst (rid, 0)) with rid.
split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _].
split; [unfold needed, IB, UNIT in *; lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]|].
split; [unfold needed, IB, UNIT in *; lia|].

intros _. eapply (fresh_beyond_hdr _ (rid, 0)); [| cbn; lia| reflexivity]. cbn [fst snd].
unfold st7, st6. autorewrite with mst. unfold hdr_havoc, upd_shadow. autorewrite with mst. rewrite lookup_insert_eq.
unfold get_shadow. autorewrite with mst. rewrite NS3. cbn. reflexivity.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

#[using="LS INV TF Hn"] Theorem malloc_core_ft : ftree L (malloc_core full_lay st n) (CORE_POST st n L BL).
Proof.
unfold malloc_core.
destruct (size_overflows n) eqn:Hov.
- cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
- destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
+ exact (malloc_big_ft Hbig Hov).
+ exact (malloc_small_ft Hsmall).
Qed.
End CORE.

#[using="Type"] Theorem malloc_INVL st L BL LS n :
INVL x0 st L BL LS -> 0 <= n ->
ftree L (malloc st n) (fun L' r =>
ld_live L' = ld_live L /\ GP st (fst r) /\
match snd r with
| None => exists LS', INVL x0 (fst r) L' BL LS'
| Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
/\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
end).
Proof.
intros INV Hn. unfold malloc.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
eapply ftree_bind; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)|].
intros L1 [st1 r] (LIVE & GP1 & RES). cbn [fst snd] in RES, GP1 |- *.
assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
destruct r as [[g idx]|].
- destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & _).
apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|]. split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)| rewrite (ce_ctx _ _ CE); reflexivity]]|].
exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
- destruct RES as (LS1 & INV1). cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.

End RC__1.
