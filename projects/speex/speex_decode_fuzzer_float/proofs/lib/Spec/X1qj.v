(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1q8 X1po X1pv X1pf X1pm X1px X1pj X1q4
X1pz X1q0 X1q1 X1q2 X1qg X1pw X1q9 X1qa X1qq X1qr X1qh X1ph X1q6 X1qc
X1qn X1qo X1qp X1qd X1qe X1pg X1pn.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma INVL_set_tick X st L BL LS t : (s_tick st <= t)%N -> INVL X st L BL LS -> INVL X (set_tick t st) L BL LS.
Proof.
intros Ht (IR & IA & IM & IL & IG & IS & ISH).
assert (CE : ctrl_eq st (set_tick t st)) by (constructor; reflexivity).
split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
apply inv_SH_set_tick; [exact Ht| exact ISH].
Qed.

Definition CORE_POST (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
ld_live L1 = ld_live L /\ GPH st0 (fst r) /\
match snd r with
| None => exists LS1, INVL x0 (fst r) L1 BL LS1
| Some (g, idx) => exists LS1 bg, let st1 := fst r in
hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
/\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
/\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
end.

Definition SMALL_REQ (n : Z) : Prop := n + IB <= UNIT * size_class 27.
Definition small_class_ok (st1 : mstate) (g : aptr) : Prop :=
0 <= m_sizeclass (MR st1 g) <= 27 /\ UNIT * size_class (m_sizeclass (MR st1 g)) <= get_stride (MR st1 g).
Definition CORE_POSTX (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
CORE_POST st0 n L BL L1 r /\
match snd r with None => True | Some (g, _) => SMALL_REQ n -> small_class_ok (fst r) g end.

Definition stc27_f (k : Z) : bool := stc_k k <=? 27.
Lemma stc27_b_true : forallb stc27_f (zrange 0 255) = true. Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_le27 n : 0 <= n -> SMALL_REQ n -> size_to_class n <= 27.
Proof.
intros Hn HS. unfold SMALL_REQ in HS. change (size_class 27) with 255 in HS.
rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, UNIT in *.
set (k := (n + 4 - 1) / 2 ^ 4).
assert (Hk : 0 <= k < 255) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
pose proof (forallb_zrange stc27_f 0 255 k stc27_b_true ltac:(lia) ltac:(lia)) as H. unfold stc27_f in H.
apply Z.leb_le in H. exact H.
Qed.

Lemma small_stride X st L BL LS bg g : INVL X st L BL LS -> hosts st bg g -> m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < 2 ^ 20.
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

#[using="LS INV TF Hn"] Lemma malloc_small_ftX : n < MMAP_THRESHOLD ->
ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTX st n L BL).
Proof.
intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
pose proof (size_to_class_le27 n Hn) as LE27.
unfold malloc_small_ctrl.
set (sc0 := size_to_class n) in *.
set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
assert (SC' : (0 <= sc < 48 /\ n + IB <= UNIT * size_class sc) /\ (SMALL_REQ n -> sc <= 27)).
{ subst sc. destruct (active st sc0); [split; [auto| exact LE27]|].
destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| split; [auto| exact LE27]].
match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| split; [auto| exact LE27]].
apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2.
rewrite (lor1_even sc0 ltac:(lia) EV). split; [split; [lia|]|].
- pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia.
- intros HS. specialize (LE27 HS). destruct (Z.eq_dec sc0 27) as [E27|NE27]; [rewrite E27 in EV; discriminate| lia]. }
clearbody sc. destruct SC' as [[SC' FIT'] SC27].
destruct (active st sc) as [gp|] eqn:HA.
-
destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
+ rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].

apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POSTX st n L BL) FUEL sc [] st L BL LS n); try assumption.
* unfold FUEL. cbn. lia.
* apply NoDup_nil_2.
* intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
-- cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd]. split; [| exact I]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
-- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd].
split. 2:{ intros HS. unfold small_class_ok. rewrite SCg, (STR1 ltac:(pose proof (SC27 HS); lia)). pose proof (SC27 HS). lia. }
split; [exact LIVE|]. split; [exact GP1|].
exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
+
destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd].
pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
{ unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
destruct MRg as (ML & MS & MSS & MSC).
split. 2:{ intros HS. unfold small_class_ok. rewrite MSC, MS, Esc. pose proof (SC27 HS). split; [lia|]. rewrite Esc in STR. exact STR. }
split; [reflexivity|]. split; [apply GPH_eq; try reflexivity; apply geo_upd_meta; intros r; reflexivity|].
exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
rewrite Esc in STR. split; [lia|].
split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). unfold IB. lia.
-
change (lowbit 0) with 0. cbn [negb Z.eqb].
apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POSTX st n L BL) FUEL sc [] st L BL LS n); try assumption.
+ unfold FUEL. cbn. lia.
+ apply NoDup_nil_2.
+ intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
* cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd]. split; [| exact I]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
* replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd].
split. 2:{ intros HS. unfold small_class_ok. rewrite SCg, (STR1 ltac:(pose proof (SC27 HS); lia)). pose proof (SC27 HS). lia. }
split; [exact LIVE|]. split; [exact GP1|].
exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
Qed.

#[using="LS INV TF Hn"] Lemma malloc_big_ftX : MMAP_THRESHOLD <= n -> size_overflows n = false ->
ftree L
(SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (s_ceil st) (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
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
(CORE_POSTX st n L BL).
Proof.
intros Hbig Hov.
assert (NSM : ~ SMALL_REQ n) by (unfold SMALL_REQ, IB, UNIT, MMAP_THRESHOLD in *; change (size_class 27) with 255; lia). unfold size_overflows in Hov. apply Z.leb_gt in Hov.
set (needed := n + IB + UNIT).
assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
apply ftree_vis; [reflexivity| reflexivity| | |].
- cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
unfold LEN_MAX. clear -HN. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then X1og.set_metas ((a, needed, 0) :: ld_metas L) L else X1og.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
destruct (is_err a) eqn:ER.
+ cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd]. split; [| exact I]. split; [reflexivity|]. split; [apply GPH_refl|]. exists LS. exact INV.
+ destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
rewrite <- Est1, <- Erid in INV1.
set (L1 := X1og.set_groups ((a, needed) :: ld_groups L) L) in *.
assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
assert (NS1 : s_shadow st1 !! rid = None).
{ rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
assert (TF1 : TF0 (step_seq st1)).
{ destruct (step_seq_fields st1) as (A & B & _). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & SS6 & SS7 & SS8 & SS9).
eapply (alloc_meta_ft (mstate * option (aptr * Z)) BL (CORE_POSTX st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1);
[ | | exact INV2| apply amf_refl| apply lf_refl].
*
intros st3 L3 LS3 INV3 AF LF. cbn beta iota.
apply ftree_vis; [reflexivity| reflexivity| | |].
-- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
-- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd event_post].
split; [| exact I]. split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
assert (HK3 : HK st st3).
{ apply HK_eq.
- rewrite (amf_groups _ _ AF), SS7, Est1. reflexivity.
- rewrite (amf_slots _ _ AF), SS9, Est1. reflexivity.
- rewrite (amf_shadow _ _ AF), SS1, Est1. reflexivity.
- intros x. rewrite (amf_geo _ _ AF). rewrite (MR_ext st1 (step_seq st1) SS6 x). rewrite Est1. reflexivity. }
assert (NS3' : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
split.
{ split; [split|].
- intros q rq Hq Kq. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions. rewrite lookup_delete_ne.
+ apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
+ intros ->. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). rewrite Erid in H. lia.
- transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity.
-
eapply HK_trans; [exact HK3|]. constructor.
+ intros b mo ai0 Hb. exists ai0. exact Hb.
+ intros c gi Hc. exact Hc.
+ intros b g0 ai0 _. reflexivity.
+ intros c k _ _ _. unfold get_shadow, drop_region. rewrite s_shadow_set_shadow.
destruct (N.eq_dec (fst c) rid) as [->|NE]; [rewrite lookup_delete_eq, NS3'; reflexivity| rewrite lookup_delete_ne by congruence; reflexivity].
+ intros c g0 ai0 H1 H2. exfalso. pose proof (eq_trans (eq_sym H1) H2) as XX. discriminate XX. }
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
as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6 & HK6).
match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd]. split; [| intros HS; exact (False_ind _ (NSM HS))]. split; [cbn; exact (lf_live _ _ LF)|].
assert (HK3 : HK st st3).
{ apply HK_eq.
- rewrite (amf_groups _ _ AF), SS7, Est1. reflexivity.
- rewrite (amf_slots _ _ AF), SS9, Est1. reflexivity.
- rewrite (amf_shadow _ _ AF), SS1, Est1. reflexivity.
- intros x. rewrite (amf_geo _ _ AF). rewrite (MR_ext st1 (step_seq st1) SS6 x). rewrite Est1. reflexivity. }
split.
{ split; [split|].
- intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
- rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity.
-   eapply HK_trans; [exact HK3|]. eapply HK_trans; [exact HK6|]. apply HK_eq; reflexivity. }
pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
set (st7 := upd_ctx _ st6) in *.
assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
{ unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
rewrite SS0. change (fst (rid, 0)) with rid.
split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _]. unfold needed, IB, UNIT in *.
split; [lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]| lia].
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

#[using="LS INV TF Hn"] Theorem malloc_core_ftX : ftree L (malloc_core full_lay st n) (CORE_POSTX st n L BL).
Proof.
unfold malloc_core.
destruct (size_overflows n) eqn:Hov.
- cbn [ftree ret]. unfold CORE_POSTX, CORE_POST. cbn [fst snd]. split; [| exact I]. split; [reflexivity|]. split; [apply GPH_refl|]. exists LS. exact INV.
- destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
+ exact (malloc_big_ftX Hbig Hov).
+ exact (malloc_small_ftX Hsmall).
Qed.

#[using="LS INV TF Hn"] Theorem malloc_core_ft : ftree L (malloc_core full_lay st n) (CORE_POST st n L BL).
Proof. eapply ftree_mono; [| exact malloc_core_ftX]. intros L' r [H _]. exact H. Qed.

Section SMALL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
#[using="L BL LS INV TF Hn Hpans"] Theorem malloc_core_small o ans o1 st2 g idx :
SMALL_REQ n ->
follow (prun pans pupd o (malloc_core full_lay st n)) ans = Some (o1, (st2, Some (g, idx))) ->
small_class_ok st2 g.
Proof.
intros HS HF.
pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st n) L _ o malloc_core_ftX) as PT.
destruct (ptree_follow _ L _ ans PT HF) as (L' & _ & [_ X]).
cbn [fst snd] in X. exact (X HS).
Qed.

#[using="L BL LS INV TF Hn Hpans"] Theorem malloc_core_HK o ans o1 st2 r :
follow (prun pans pupd o (malloc_core full_lay st n)) ans = Some (o1, (st2, r)) -> HK st st2.
Proof.
intros HF.
pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st n) L _ o malloc_core_ftX) as PT.
destruct (ptree_follow _ L _ ans PT HF) as (L' & _ & [[_ [[_ X] _]] _]).
cbn [fst snd] in X. exact X.
Qed.

#[using="L LS INV TF Hn Hpans"] Theorem malloc_core_leaf o ans o1 st2 g idx :
follow (prun pans pupd o (malloc_core full_lay st n)) ans = Some (o1, (st2, Some (g, idx))) ->
exists L1 LS1 bg,
hosts st2 bg g /\ 0 <= idx <= m_last_idx (MR st2 g)
/\ INVL (xpend x0 (Some (fst bg, sstart (MR st2 g) idx))) st2 L1 BL LS1
/\ n + IB <= get_stride (MR st2 g) /\ TF2 st2 /\ get_stride (MR st2 g) - IB - n < 2 ^ 32
/\ GPH st st2.
Proof.
intros HF.
pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st n) L _ o malloc_core_ftX) as PT.
destruct (ptree_follow _ L _ ans PT HF) as (L' & _ & [[_ [GP2 RES]] _]).
cbn [fst snd] in RES, GP2. destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
exists L', LS1, bg. repeat (split; [assumption|]). exact GP2.
Qed.

#[using="L LS INV TF Hn Hpans"] Theorem malloc_core_leaf_none o ans o1 st2 :
follow (prun pans pupd o (malloc_core full_lay st n)) ans = Some (o1, (st2, None)) ->
exists L1 LS1, INVL x0 st2 L1 BL LS1 /\ GPH st st2.
Proof.
intros HF.
pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st n) L _ o malloc_core_ftX) as PT.
destruct (ptree_follow _ L _ ans PT HF) as (L' & _ & [[_ [GP2 RES]] _]).
cbn [fst snd] in RES, GP2. destruct RES as (LS1 & INV1). exists L', LS1. split; [exact INV1| exact GP2].
Qed.
End SMALL.
End CORE.

Theorem malloc_INVL st L BL LS n :
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
assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact (proj1 GP1)]).
destruct r as [[g idx]|].
- destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|]. split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]]|].
exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
- destruct RES as (LS1 & INV1). cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.
