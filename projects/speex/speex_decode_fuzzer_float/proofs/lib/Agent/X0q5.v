(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1q8 X1po X1pv X1pf X1pm X1px X1pj X1q3 X1qf
X1q0 X1q6 X1qd X1qj X1q5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0qn X0px X0q2 X0q7 X0q8 X0q9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record hdr_facts {RCEIL : RunCeiling} (st : mstate) (blk : block) (r : region) (g bm : aptr) (ai : Z) (ar : area) (b3 lo hi i off : Z) : Prop := mkHF {

hf_slot : s_slots st !! (blk_slot blk) = Some (g, i);
hf_hosts : s_groups st !! bm = Some (mkGhdr (Some g) ai);
hf_fst : fst bm = fst (blk_slot blk);
hf_reg : s_regions st !! (fst (blk_slot blk)) = Some r;
hf_kind : r_kind r = RKGroup;
hf_rbase : 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling;
hf_mem : m_mem (get_meta_rec st g) = Some bm;
hf_snd : snd (blk_slot blk) = snd bm + UNIT + get_stride (get_meta_rec st g) * i;
hf_b0 : 0 <= snd bm;
hf_b16 : snd bm mod 16 = 0;

hf_off : 0 <= off <= 255;
hf_addr : blk_addr blk = r_base r + snd (blk_slot blk) + UNIT * off;
hf_size : 0 <= blk_size blk;
hf_fit : UNIT * off + blk_size blk <= get_stride (get_meta_rec st g) - IB;
hf_span : snd bm + UNIT + get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r);
hf_stride : UNIT <= get_stride (get_meta_rec st g) /\ get_stride (get_meta_rec st g) mod UNIT = 0;

hf_k4 : cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - 4) = Known 0;
hf_k3 : cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - 3) = Known b3;
hf_k2 : cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - 2) = Known lo;
hf_k1 : cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - 1) = Known hi;
hf_b3 : 0 <= b3 < 256;
hf_lo : 0 <= lo < 256;
hf_hi : 0 <= hi < 256;
hf_idx : Z.land b3 31 = i;
hf_res : Z.shiftr b3 5 = Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - blk_size blk) 5;
hf_off16 : 16 * (lo + 256 * hi) = get_stride (get_meta_rec st g) * i + UNIT * off;

hf_mslot : meta_slot st g;
hf_g0 : 0 <= snd g;
hf_area : s_areas st !! (area_of g) = Some ar;
hf_check : a_check ar = c_secret (ctx st);
hf_secret : 0 <= c_secret (ctx st) < 2^64;

hf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
hf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
hf_li : 0 <= m_last_idx (get_meta_rec st g) <= 31;
hf_freeable : m_freeable (get_meta_rec st g) = 1;
hf_maplen : 0 <= m_maplen (get_meta_rec st g) < 2^35;
hf_sc : (0 <= m_sizeclass (get_meta_rec st g) < 48
/\ (get_stride (get_meta_rec st g) <= UNIT * size_class (m_sizeclass (get_meta_rec st g)) \/ 28 <= m_sizeclass (get_meta_rec st g))
/\ (get_stride (get_meta_rec st g) = UNIT * size_class (m_sizeclass (get_meta_rec st g))
\/ (m_last_idx (get_meta_rec st g) = 0 /\ m_maplen (get_meta_rec st g) <> 0)))
\/ (m_sizeclass (get_meta_rec st g) = 63 /\ m_last_idx (get_meta_rec st g) = 0 /\ m_maplen (get_meta_rec st g) <> 0);
hf_i : 0 <= i <= m_last_idx (get_meta_rec st g);
hf_nav : Z.testbit (m_avail (get_meta_rec st g)) i = false;
hf_nfr : Z.testbit (m_freed (get_meta_rec st g)) i = false;
hf_top : m_maplen (get_meta_rec st g) <> 0 -> snd bm = 0 /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len r);

hf_g16 : m_sizeclass (get_meta_rec st g) < 48 ->
size_class (m_sizeclass (get_meta_rec st g)) * i <= lo + 256 * hi < size_class (m_sizeclass (get_meta_rec st g)) * (i + 1);
hf_g63 : 48 <= m_sizeclass (get_meta_rec st g) -> m_sizeclass (get_meta_rec st g) = 63;
hf_g17 : m_maplen (get_meta_rec st g) <> 0 -> lo + 256 * hi <= m_maplen (get_meta_rec st g) * 256 - 1;

hf_foot : let e := snd (blk_slot blk) + get_stride (get_meta_rec st g) - IB in
let res := e - (snd (blk_slot blk) + UNIT * off) - blk_size blk in
(5 <= res -> cell_read (get_shadow st (fst (blk_slot blk))) (e - 4) = Known (byte_of res 0)
/\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 3) = Known (byte_of res 1)
/\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 2) = Known (byte_of res 2)
/\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 1) = Known (byte_of res 3)
/\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 5) = Known 0 /\ res < 2^32)
/\ (0 < res -> cell_read (get_shadow st (fst (blk_slot blk))) (e - res) = Known 0)
/\ cell_read (get_shadow st (fst (blk_slot blk))) e = Known 0
/\ (forall a, snd (blk_slot blk) + UNIT * off <= a < snd (blk_slot blk) + UNIT * off + blk_size blk ->
exists h, cell_read (get_shadow st (fst (blk_slot blk))) a = Unknown h);

hf_nogrp : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst (blk_slot blk) ->
snd b' + 16 <= snd (blk_slot blk) \/ snd (blk_slot blk) + get_stride (get_meta_rec st g) <= snd b';

hf_init : c_init_done (ctx st) = 1
}.

Section HF.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (LB : list block).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis CR : CORR st LB BL.
Hypothesis LCEIL : ld_ceil L = alloc_ceiling.

#[using="L BL LS INV CR LCEIL"] Lemma hdr_facts_of_inv blk : In blk LB -> exists r g bm ai ar b3 lo hi i off, hdr_facts st blk r g bm ai ar b3 lo hi i off.
Proof.
intros Hb.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as IR IA IM IL IG IS ISH | sf_fb; destruct sfP_ as (IR & IA & IM & IL & IG & IS & ISH) ].
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. symmetry in C1. symmetry in C2. subst c n.
first [ pose proof (block_facts x0 st L BL LS INV (blk_slot blk) off (blk_size blk) Hk) as sfP_; sf_destruct 8%nat sfP_ as m bm i ai a ar ka BF | sf_fb; destruct (block_facts x0 st L BL LS INV (blk_slot blk) off (blk_size blk) Hk) as (m & bm & i & ai & a & ar & ka & BF) ].
destruct (blk_region _ _ _ _ _ ((blk_slot blk, off), blk_size blk) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
assert (Hm : hosts st bm m) by (exists ai; exact Hh).
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
assert (Efst : fst (blk_slot blk) = fst bm) by (rewrite Ec; reflexivity).
pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHK. unfold blk_shadow_ok in SHK. cbn [bslot boff bsize fst snd] in SHK.
rewrite (hosts_gbase _ _ _ IM _ _ Hm) in SHK.
first [ sf_destruct 8%nat SHK as K4 K3 K2 K1 Q F5 FZ UNK | sf_fb; destruct SHK as (K4 & K3 & K2 & K1 & Q & F5 & FZ & UNK) ]. unfold known, unknown, SHd in K4, K3, K2, K1, F5, FZ, UNK. cbn [fst snd] in K4, K3, K2, K1, F5, FZ, UNK.
set (q := (snd (blk_slot blk) + UNIT * off - snd bm - UNIT) / UNIT) in *.
set (res := snd (blk_slot blk) + get_stride (MR st m) - IB - (snd (blk_slot blk) + UNIT * off) - blk_size blk) in *.
first [ pose proof (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as sfP_; sf_destruct 5%nat sfP_ as Ha Hck Hapg Hka Em | sf_fb; destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hapg & Hka & Em) ].
first [ pose proof (ia_areas _ IA _ _ Ha) as sfP_; sf_destruct 4%nat sfP_ as (ra' & Hra & Hmk & Hal & Hpg & Hfr) _ _ _ | sf_fb; destruct (ia_areas _ IA _ _ Ha) as ((ra' & Hra & Hmk & Hal & Hpg & Hfr) & _ & _ & _) ].
first [ pose proof (ir_shape _ _ _ IR _ _ Hr) as sfP_; sf_destruct 6%nat sfP_ as RB0 RBAL RL0 RLM RBC _ | sf_fb; destruct (ir_shape _ _ _ IR _ _ Hr) as (RB0 & RBAL & RL0 & RLM & RBC & _) ].
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM].
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as LI. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B0 B16].
pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML0. pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP.
pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as SC.
destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai' & Hb' & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as sfP_; first [ sf_destruct 6%nat sfP_ as M1 M2 M3 M4 M5 M6 | sf_fb; destruct sfP_ as (M1 & M2 & M3 & M4 & M5 & M6) ]. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Esnd : snd (blk_slot blk) = snd bm + UNIT + get_stride (MR st m) * i)
by (rewrite Ec; cbn [snd]; unfold sstart; rewrite (hosts_gbase _ _ _ IM _ _ Hm); reflexivity).
assert (SI0 : 0 <= get_stride (MR st m) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (Hq : 16 * q = get_stride (MR st m) * i + UNIT * off).
{ subst q. rewrite Esnd. unfold UNIT in *.
replace (snd bm + 16 + get_stride (MR st m) * i + 16 * off - snd bm - 16) with ((get_stride (MR st m) * i + 16 * off)) by lia.
assert (SIM : (get_stride (MR st m) * i) mod 16 = 0) by (rewrite Z.mul_mod, SM, Z.mul_0_l by lia; reflexivity).
clear -SIM SI0 OFF. Z.div_mod_to_equations. lia. }
assert (E4 : m_maplen (MR st m) <> 0 -> snd bm = 0 /\ m_maplen (MR st m) * 4096 = round_up_pg (r_len r)).
{ intros NZ. first [ pose proof (g_top _ _ _ _ _ _ GO NZ) as sfP_; sf_destruct 6%nat sfP_ as S0 r' Hr' _ E4 _ | sf_fb; destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r' & Hr' & _ & E4 & _) ].
rewrite <- Efst, Hr in Hr'. inversion Hr'; subst r'. split; [exact S0| exact E4]. }
assert (SPAN : snd bm + UNIT + get_stride (MR st m) * (m_last_idx (MR st m) + 1) <= round_up_pg (r_len r)).
{ first [ pose proof (group_in_region _ _ _ _ _ INV _ _ Hm) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' _ _ GE | sf_fb; destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r' & Hr' & _ & _ & GE) ].
rewrite <- Efst, Hr in Hr'. inversion Hr'; subst r'.
rewrite (gend_eq st) in GE. unfold sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hm) in GE. exact GE. }
assert (ML35 : m_maplen (MR st m) < 2^35).
{ destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [->|NZ]; [lia|]. destruct (E4 NZ) as [_ E].
pose proof (proj2 (ir_ceil _ _ _ IR)) as CRG; rewrite <- (proj1 (ir_ceil _ _ _ IR)) in CRG; unfold alloc_ceiling_lo, alloc_ceiling_hi in CRG.
pose proof (round_up_pg_ge (r_len r)). clear -E RBC RB0 H CRG. lia. }
assert (RES0 : 0 <= res) by (subst res; unfold UNIT, IB in *; lia).
assert (SEC : 0 <= c_secret (ctx st) < 2^64).
{ destruct (ia_secret _ IA) as [SR [(_ & _ & EA)|[_ E1]]].
- exfalso. rewrite EA in Ha. rewrite lookup_empty in Ha. discriminate.
- unfold ctx. rewrite E1. exact SR. }
unfold MR in *.
first [ unshelve sf_eexists 10%nat; [ exact (r) | exact (m) | exact (bm) | exact (ai) | exact (ar) | exact ((i + 32 * Z.min res 5)) | exact ((byte_of q 0)) | exact ((byte_of q 1)) | exact (i) | exact (off) | ] | sf_fb; exists r, m, bm, ai, ar, (i + 32 * Z.min res 5), (byte_of q 0), (byte_of q 1), i, off ].
constructor.
- exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
- exact Hh.
- symmetry. exact Efst.
- exact Hr.
- exact Kr.
- split; [exact RB0|]. split; [unfold PGSZ in RBAL; exact RBAL| rewrite <- LCEIL; exact RBC].
- exact (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF).
- exact Esnd.
- exact B0.
- unfold UNIT in B16. exact B16.
- exact OFF.
- rewrite C3, (conc_region' st _ r Hr). lia.
- exact N0.
- exact FIT.
- exact SPAN.
- split; [exact S16| exact SM].
- exact K4.
- exact K3.
- exact K2.
- exact K1.
- clear -Hi LI RES0. lia.
- apply byte_of_range; lia.
- apply byte_of_range; lia.
- apply land31_idx; (clear - LI Hi i m st RES0 Hq Esnd ML0 B0 Q bm off blk; lia).
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
replace (i + 32 * Z.min res 5) with (i + Z.min res 5 * 32) by lia. rewrite Z.div_add, Z.div_small by lia. subst res. unfold UNIT, IB. clear. lia.
- rewrite u16_bytes by exact Q. exact Hq.
- first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (ar) | exact (ka) | ] | sf_fb; exists a, ar, ka ]. split; [exact Ha|]. split; [exact Hka| exact Em].
- rewrite Em. unfold mslot, aadd. cbn [snd]. unfold AREA_HDR, META_SIZE, PGSZ in *. clear -Hpg Hka. lia.
- replace (area_of m) with a; [exact Ha|]. rewrite Em. unfold area_of, mslot, aadd. cbn [fst snd].
apply injective_projections; cbn [fst snd]; [reflexivity|].
unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
replace (snd a + (24 + 40 * ka)) with ((24 + 40 * ka) + (snd a / 4096) * 4096) by (clear -Hapg Hka Hpg; Z.div_mod_to_equations; nia).
rewrite Z.mod_add, Z.mod_small by lia. clear -Hapg Hka Hpg. Z.div_mod_to_equations. nia.
- exact Hck.
- exact SEC.
- split; [exact M1|]. apply bits_below_bound; [exact M1| lia|]. intros j Hj Ht. pose proof (M3 j Hj Ht). clear -H AI LI. lia.
- split; [exact M2|]. apply bits_below_bound; [exact M2| lia|]. intros j Hj Ht. pose proof (M4 j Hj Ht). clear -H LI. lia.
- clear -Hi LI. lia.
- exact (g_freeable _ _ _ _ _ _ GO).
- split; [exact ML0| exact ML35].
- destruct SC as [(S1 & S2 & S3)|S63]; [left; split; [exact S1| split; [exact S2| exact S3]]|]. right.
destruct (g_sc _ _ _ _ _ _ GO) as [[A48 _]|(B63 & B0' & BM & _)]; [exfalso; unfold MR in A48; clear -S63 A48; lia| split; [exact B63| split; [exact B0'| exact BM]]].
- exact Hi.
- exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF).
- exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF).
- exact E4.
- intros Hsc. destruct SC as [(S1 & S2 & S3)|S63]; [|exfalso; (clear - Hsc S63 B0 RB0 res Efst r a bm m off blk st RCEIL; lia)].
pose proof (size_class_range (m_sizeclass (get_meta_rec st m)) ltac:(lia)) as SZ.
apply (guard16_arith (size_class (m_sizeclass (get_meta_rec st m))) (get_stride (get_meta_rec st m)) i off (blk_size blk) (byte_of q 0 + 256 * byte_of q 1) (m_last_idx (get_meta_rec st m)));
unfold UNIT, IB in *.
+ clear -SZ. lia.
+ rewrite u16_bytes by exact Q. exact Hq.
+ exact FIT.
+ exact N0.
+ exact OFF.
+ exact Hi.
+ clear -S3. lia.
+ destruct S2 as [S2|S2]; [left; exact S2| right; apply size_class_28; clear -S2 S1; lia].
- intros Hsc. destruct SC as [(S1 & _)|S63]; [exfalso; clear -S1 Hsc; lia| exact S63].
- intros NZ. destruct (E4 NZ) as [S0 GE]. unfold UNIT, IB in *.
enough (X : byte_of q 0 + 256 * byte_of q 1 <= m_maplen (get_meta_rec st m) * 4096 / 16 - 1).
{ replace (m_maplen (get_meta_rec st m) * 4096) with (m_maplen (get_meta_rec st m) * 256 * 16) in X by lia. rewrite Z.div_mul in X by lia. exact X. }
apply (guard17_arith (get_stride (get_meta_rec st m)) i off (blk_size blk) (byte_of q 0 + 256 * byte_of q 1) (m_last_idx (get_meta_rec st m)) (m_maplen (get_meta_rec st m))).
+ clear -S16. lia.
+ rewrite u16_bytes by exact Q. exact Hq.
+ exact FIT.
+ exact N0.
+ clear -OFF. lia.
+ exact Hi.
+ rewrite GE. clear -SPAN S0. lia.
- cbv zeta. split; [|split; [|split]].
+ intros H5. exact (F5 H5).
+ intros H0. exact (FZ H0).
+ pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. unfold known, SHd in H0. cbn [fst snd] in H0.
unfold sstart in H0. rewrite (hosts_gbase _ _ _ IM _ _ Hm) in H0.
rewrite Efst. replace (snd (blk_slot blk) + get_stride (get_meta_rec st m) - IB) with (snd bm + UNIT + get_stride (get_meta_rec st m) * (i + 1) - IB) by (rewrite Esnd; clear; lia).
exact H0.
+ exact UNK.
- intros b2 gh Hb2 Hf2. destruct (im_hdr _ _ _ IM _ _ Hb2) as (m2 & Hgm & _).
assert (H2 : hosts st b2 m2).
{ exists (g_active_idx gh). destruct gh as [gm gai]. cbn in Hgm |- *. subst gm. exact Hb2. }
pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. rewrite Ec in NH.
rewrite Efst in Hf2.
destruct (sep_ghdr' x0 st L BL LS INV m bm i m2 b2 Hm Hi NH H2 Hf2) as [A|A]; rewrite Esnd; unfold MR in A;
[left| right]; unfold sstart in A; rewrite (hosts_gbase _ _ _ IM _ _ Hm) in A; unfold MR in A; lia.
-   pose proof (ia_secret _ IA) as [_ [(_ & _ & E)|[E _]]]; [| exact E].
exfalso. rewrite E, lookup_empty in Ha. discriminate.
Qed.
End HF.

Theorem hdr_facts_of_areach {RCEIL : RunCeiling} {resv} st LB blk :
AREACH_from resv st LB -> In blk LB -> exists r g bm ai ar b3 lo hi i off, hdr_facts st blk r g bm ai ar b3 lo hi i off.
Proof.
intros AR Hb. first [ pose proof (areach_inv_full resv st LB AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV _ [_ LCEIL] _ CR | sf_fb; destruct (areach_inv_full resv st LB AR) as (L & LS & BL & INV & _ & [_ LCEIL] & _ & CR) ].
exact (hdr_facts_of_inv st L BL LS LB INV CR LCEIL blk Hb).
Qed.
