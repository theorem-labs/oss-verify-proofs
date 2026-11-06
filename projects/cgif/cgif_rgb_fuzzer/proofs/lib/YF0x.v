(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF0k YF0o YF0r YF0t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Variables (k : chunk) (off : Z).
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hb : ck_beg k = PPrim off.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hci : st_cache_inited X = true.
Definition X1 : astate := set_chunks (del_chunk (st_chunks X) (ck_beg k)) X.
Let c : Z := prim_class off.
Let x : Z := off - region_off c.
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation base := (ck_base B ly k).
Local Notation u := (ck_base B ly k + ck_rz k).
Local Notation nn := (ck_n k).
Definition Mv : Z := ck_base B ly k + ck_rz k - kChunkHeaderSize.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + KSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DS (a : Z) : Prop := sp - KSTACK <= a < sp.
Definition DK (a : Z) : Prop := (Mv <= a < Mv + 4) \/ (ck_rz k <> 16 /\ ck_base B ly k <= a < ck_base B ly k + 8).
Definition DJ (a : Z) : Prop := T + t_stats + 40 <= a < T + t_stats + 56.
Definition DH (a : Z) : Prop := shadow_addr u <= a < shadow_addr u + (nn + 7) / 8.
Definition D (a : Z) : Prop := DS a \/ DK a \/ DJ a \/ DH a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_sh : forall a, DH a -> rd a <> None -> rd' a = Some shHeapLeftRz.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac geo := clear AG VIS NEW_sh CONST'.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma SPLIT : exists l1 l2, st_chunks X = l1 ++ k :: l2 /\ st_chunks X1 = l1 ++ l2 /\
~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof. geo.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2). exists l1, l2.
split; [img_try (img_exact E)|]. split; [|img_try (split; [img_exact N1 | img_exact N2])]. unfold X1. cbn [st_chunks set_chunks]. rewrite E. img_apply del_chunk_present. img_exact N1.
Qed.
Lemma KF : cfacts B ly X k. Proof. geo. img_exact (chunk_facts B ly X rd k M Hk). Qed.
Lemma DEL : Wf (as_universe B) X1 /\
1 <= c <= 30 /\ 0 <= x < rg_alloc_user (reg X1 c) /\ x mod class_size c = 0 /\ ~ In x (class_elems X1 c) /\
(forall c' y, In y (class_elems X1 c') -> In y (class_elems X c')) /\
4 * (Z.of_nat (length (class_elems X1 c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X1))) <= rg_mapped_fa (reg X1 c).
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (EX : X1 = set_chunks (l1 ++ l2) X) by (img_try (unfold X1; rewrite <- E1; img_refl)).
pose proof (WfP_del_prim (as_universe B) 0 0 0 X l1 k l2 off WF E Hb Hst Hni) as (W1 & G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
rewrite EX. unfold reg in *. cbn [st_regions set_chunks st_nev] in *. fold c x in G1, G2, G3, G4, G5, G6 |- *.
split; [img_try (img_exact W1)|]. split; [img_try (img_exact G1)|]. split; [img_try (img_exact G2)|]. split; [img_try (img_exact G3)|]. split; [img_try (img_exact G4)|]. split; [img_try (img_exact G5) | img_try (img_exact G6)].
Qed.
Lemma WS1 : Wf (as_universe B) X1. Proof. img_exact (proj1 DEL). Qed.
Lemma X1_regions : st_regions X1 = st_regions X. Proof. img_refl. Qed.
Lemma X1_cache : st_cache X1 = st_cache X. Proof. img_refl. Qed.
Lemma X1_cinit : st_cache_inited X1 = true. Proof. img_exact Hci. Qed.
Lemma X1_secs : st_secs X1 = st_secs X. Proof. img_refl. Qed.
Lemma X1_sec_arr : st_sec_arr X1 = st_sec_arr X. Proof. img_refl. Qed.
Lemma X1_sec_res : st_sec_reserved X1 = st_sec_reserved X. Proof. img_refl. Qed.
Lemma X1_fs : st_fs X1 = st_fs X. Proof. img_refl. Qed.
Lemma X1_qglobal : st_qglobal X1 = st_qglobal X. Proof. img_refl. Qed.
Lemma X1_qthread : st_qthread X1 = st_qthread X. Proof. img_refl. Qed.
Lemma X1_depot : st_depot X1 = st_depot X. Proof. img_refl. Qed.
Lemma X1_inited : st_internal_inited X1 = st_internal_inited X. Proof. img_refl. Qed.
Lemma X1_nev : st_nev X1 = st_nev X. Proof. img_refl. Qed.
Lemma reg' : forall c', reg X1 c' = reg X c'. Proof. img_refl. Qed.
Lemma cache' : forall c', cache X1 c' = cache X c'. Proof. img_refl. Qed.
Lemma frames' : frames X1 = frames X. Proof. img_refl. Qed.
Lemma all_batches' : all_batches X1 = all_batches X. Proof. img_refl. Qed.
Lemma fa_poison' : fa_poison_ranges ly X1 = fa_poison_ranges ly X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold fa_poison_ranges, reg. rewrite X1_regions, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. img_refl. Qed.
Lemma sec_extents' : sec_extents ly X1 = sec_extents ly X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_extents. rewrite E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. img_refl. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly X1 A.
Proof. intros A H e He. rewrite sec_extents' in He. img_exact (H e He). Qed.
Lemma aareas' : aareas X1 = aareas X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold aareas, reg. rewrite X1_regions, X1_sec_res, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. img_refl. Qed.
Lemma sec_live' : sec_live_bytes X1 = sec_live_bytes X.
Proof.
geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_live_bytes. rewrite E1, E. clear E E1.
induction l1 as [|y t IH]; cbn; [img_try (rewrite Hb; img_refl) | img_try (rewrite IH; img_refl)].
Qed.
Lemma prim_committed' : prim_committed X1 = prim_committed X. Proof. img_refl. Qed.
Lemma abudget' : abudget X1 = abudget X. Proof. geo. unfold abudget, sec_hulls. rewrite X1_nev, sec_live', X1_secs  . img_refl. Qed.
Lemma geom : 1 <= c <= 30 /\ base = SB + off /\ region_off c = c * 2 ^ 32 /\ base = region_base ly c + x /\ 0 <= x /\ x + class_size c <= rg_alloc_user (reg X c) /\
rg_alloc_user (reg X c) <= rg_mapped_user (reg X c) <= 2 ^ 31 /\ base mod 16 = 0 /\ 16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\
1 <= nn < 2 ^ 28 /\ ck_rz k + nn <= ck_extent k /\ ck_extent k = class_size c /\ 32 <= class_size c /\
kHighMemBeg <= base /\ base + ck_extent k <= ASAN_CEIL /\ sptr_addr B ly (ck_user k) = u /\ x mod class_size c = 0.
Proof. geo.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Hb in CK. cbv zeta in CK. destruct CK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3). pose proof (class_ok (prim_class off) ltac:(img_lia)) as (K1 & K2 & K3 & _).
assert (K0 : 32 <= class_size (prim_class off)) by (img_try (apply Z.mod_divide in K2 as [q Hq]; [|img_lia]; nia)).
fold c x in C1, C4, C5, C6, C7, C8, C9, K0 |- *. unfold ck_n.
assert (EB : base = SB + off) by (img_try (unfold ck_base, sptr_addr; rewrite Hb; img_refl)).
assert (RO : region_off c = c * 2 ^ 32) by (img_try (unfold region_off; rewrite Z.shiftl_mul_pow2 by img_lia; img_refl)).
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (lo_space_in _ LO) as [S1 S2].
unfold region_base in *. unfold MALLOC_MAX in G7. repeat split; try assumption; try img_lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|img_lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|img_lia].
exfalso. img_apply (H (Z.max a c)); img_lia.
Qed.
Lemma ZCH : forall ch, In ch (st_chunks X) -> zone3 (ck_base B ly ch) (ck_extent ch).
Proof. geo.
intros ch Hch. pose proof (chunk_facts B ly X rd ch M Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req ch) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
img_apply (zone3_intro ly (ck_base B ly ch) (ck_extent ch) IMG ltac:(img_try (clear - G5 G8 Q1; img_lia)) G1).
img_apply zdisjoint_of_pointwise; [img_try (clear - G5 G8 Q1; img_lia) | img_try (img_exact (proj1 (proj2 (lo_img _ LO)))) |].
intros y Hy. img_exact (proj1 (chunk_apart B ly X rd ch y M Hch Hy)).
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ 4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x0 sz, nth_error (owned_extents ly) i = Some (x0, sz) -> 0 <= sz -> zone3 x0 sz).
{ intros i x0 sz He Hsz. img_apply (zone3_intro ly x0 sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (img_try (destruct (Nat.lt_ge_cases i 8) as [X0|X0]; [img_try (img_exact X0)|]; assert (X' : nth_error (owned_extents ly) i = None) by (img_apply nth_error_None; cbn; img_lia); rewrite X' in He; discriminate)).
img_exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(img_try (unfold static_extents; rewrite nth_error_app1 by (cbn; img_lia); img_exact He))
ltac:(img_try (unfold static_extents; rewrite nth_error_app2 by (cbn; img_lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; img_lia); img_refl))). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(img_try (unfold kPtrArrayResv; img_lia))) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(img_try (unfold kThreadObjSize; img_lia))) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(img_try (unfold kFakeStackSize; img_lia))) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(img_try (unfold kNodesBlockSize; img_lia))) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(img_try (unfold kStoreBlockSize; img_lia))) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(img_lia)) as ZC. clear Z3 HA HD.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof (aso_cells _ (am_syms B ly X rd M)) as (I1 & I2 & _).
split; [img_try (clear - IP; img_lia)|]. split; [img_try (clear - IP; img_lia)|]. split; [img_try (img_exact ZQ)|]. split; [img_try (clear - ZQ; unfold zone3 in ZQ; img_lia)|].
split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|]. split; [img_try (img_exact ZF)|]. split; [img_try (clear - ZF; unfold zone3 in ZF; img_lia)|].
split; [img_try (img_exact ZNB)|]. split; [img_try (clear - ZNB; unfold zone3 in ZNB; img_lia)|]. split; [img_try (img_exact ZSB)|]. split; [img_try (clear - ZSB; unfold zone3 in ZSB; img_lia)|].
split; [img_try (img_exact ZC)|]. split; [img_try (clear - ZC; unfold zone3 in ZC; img_lia)|]. clear ZQ ZT ZF ZNB ZSB ZC.
repeat split; try assumption; try img_lia.
Qed.
Lemma D_cases : forall a, D a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (base <= a < base + ck_extent k /\ DK a) \/ (T <= a < T + kThreadObjSize /\ DJ a) \/
(kLowShadowBeg <= a < kHighMemBeg /\ DH a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof geom as GE.
destruct Ha as [Y|[Y|[Y|Y]]].
- left. unfold DS, KSTACK in *. img_lia.
- right; left. split; [|img_try (img_exact Y)]. unfold DK, Mv, kChunkHeaderSize in Y. img_lia.
- do 2 right; left. split; [|img_try (img_exact Y)]. unfold DJ, t_stats, kThreadObjSize in *. img_lia.
- do 3 right. split; [|img_try (img_exact Y)]. unfold DH in Y.
destruct HI as (IP1 & IP2 & _). clear - Y GE IP1 IP2. ceil; unfold shadow_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split.
+ pose proof (Z.div_pos u 8 ltac:(img_lia) ltac:(img_lia)). img_lia.
+ assert (LE : u + (nn + 7) / 8 * 8 <= 140737479966720) by (img_try (pose proof (Z.div_mod (nn + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(img_lia)); img_lia)).
assert (Y' : (u + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; [img_lia | img_try (img_exact LE)])).
rewrite Z.div_add in Y' by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y'. img_lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (img_try (clear - HI; unfold zone3 in HI; tauto)); unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. img_apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize, kPrimResvSize,
kPtrArrayResv, kFakeStackSize, kNodesBlockSize, kStoreBlockSize, kLowMemEnd, KSTACK in *.
Ltac tbnum := rewrite ?(ts_inst B TB), ?(ts_depot B TB), ?(ts_store B TB), ?(ts_ial_lo B TB), ?(ts_ial_hi B TB), ?(ts_ial_w B TB), ?(ts_ial_flag B TB) in *;
unfold TFX_INST, TFX_DEPOT, TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; img_lia.
Lemma SX : forall i j x0 y, nth_error (static_extents ly) i = Some x0 -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x0 y.
Proof. geo.
intros i j x0 y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- img_exact (pairwise_nth zdisjoint _ i j x0 y (lo_disj _ LO) Hi Hj H).
- img_apply zdisjoint_sym. img_apply (pairwise_nth zdisjoint _ j i y x0 (lo_disj _ LO) Hj Hi). img_lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. img_exact Hj.
Qed.
Lemma k_prim : ly_prim ly <= base /\ base + ck_extent k <= ly_prim ly + kPrimResvSize /\ region_base ly c <= base /\ base + ck_extent k <= region_base ly c + 2 ^ 31.
Proof. geo.
pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _ & _ & _ & _ & _ & G13 & _).
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & _). img_lia.
Qed.
Lemma ok_low : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [img_try (hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)|]. intros HD. pose proof k_prim as KP.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]]; hnum; unfold TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg in *; img_lia.
Qed.
Lemma ok_lowsh : forall a, kLowShadowBeg <= a < kHighShadowBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD. pose proof k_prim as (KP1 & KP2 & _).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[_ Y]]]]; [img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (hnum; unfold kLowShadowBeg in *; img_lia) |].
unfold DH, shadow_addr in Y. destruct HI as (IP1 & _). pose proof geom as GE. clear - Ha Y KP1 IP1 GE. hnum. unfold SHADOW_OFF in *.
pose proof (Z.div_le_mono 17594333495296 u 8 ltac:(img_lia) ltac:(img_lia)) as X0. img_change (17594333495296 / 8) with 2199291686912 in X0. img_lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DH a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD. pose proof k_prim as KP.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[_ Y]]]]; [img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (img_exact (ND Y))].
Qed.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j [ex esz] a Hj J0 J2 J8 Ha. cbn [fst snd] in Ha. pose proof HIGH as (H1 & H2 & _). pose proof k_prim as KP.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ex, esz)) as HE.
assert (INO : In (ex, esz) (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (img_try (cbn; img_lia)). eapply nth_error_In. img_exact Hj. }
specialize (HE INO). cbn beta in HE. cbn [fst snd] in HE.
pose proof (zone3_intro ly ex esz IMG ltac:(img_lia) HE (SX j 9 _ _ Hj eq_refl ltac:(img_lia))) as (_ & _ & ZZ).
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
unfold in_app in HE. split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SX j 8 _ _ Hj eq_refl ltac:(img_lia)).
- zd (SX 0 j _ _ eq_refl Hj ltac:(img_lia)).
- zd (SX j 2 _ _ Hj eq_refl ltac:(img_lia)).
- hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DJ a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). pose proof k_prim as KP. split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[_ Y]|[Y _]]]].
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- img_exact (ND Y).
- hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (base <= a < base + ck_extent k) -> ok a.
Proof. geo.
intros a Ha NK. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- img_exact (NK Y).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma ok_other : forall y a, In y (st_chunks X) -> ck_beg y <> ck_beg k -> ck_base B ly y <= a < ck_base B ly y + ck_extent y -> ok a.
Proof. geo.
intros y a Hy Hne Ha. pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0.
pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg y) as [|o|r o|c0 p0] eqn:Eby; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _).
img_apply ok_prim; [img_lia | img_try (zd DJ0)].
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (ZCH y Hy) as ZX. pose proof ZX as (_ & _ & ZZ). unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
pose proof HIGH as HI. split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
+ zd (SECX _ 8 _ Gin eq_refl).
+ zd DJ0.
+ zd (SECX _ 2 _ Gin eq_refl).
+ hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma ok_secpage : forall y r o a, In y (st_chunks X) -> ck_beg y = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros y r o a Hy Eby Ha. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Eby in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as HI.
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req y) ltac:(img_lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req y)) IMG ltac:(img_try (clear - Gext G5 G8 Q2; unfold kPage in *; img_lia)) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kHighMemBeg in ZZ.
pose proof (prim_vs_secmap B ly X rd k off _ M Hk Hb Gin) as DJ0.
split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SECX _ 8 _ Gin eq_refl).
- zd DJ0.
- zd (SECX _ 2 _ Gin eq_refl).
- hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists xb, ly_space ly + b_self b2 = region_base ly kBatchClass + xb /\ 0 <= xb /\ xb mod kBatchBytes = 0 /\
xb + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In xb (batch_offs X kBatchClass).
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (xb := b_self b2 - region_off kBatchClass).
assert (INB : In xb (batch_offs X kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b2; auto)).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) xb ltac:(img_try (rewrite !in_app_iff; tauto))) as [B1 B2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL'. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in B2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : xb + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in B2 as [q Hq]; [|img_lia]. apply Z.mod_divide in AA as [q' Hq']; [|img_lia]. assert (q < q') by nia. nia. }
exists xb. splits; try assumption; try img_lia. unfold region_base. (subst xb; cbv beta). img_lia.
Qed.
Lemma batch_vs_k : forall b2, In b2 (all_batches X) -> zdisjoint (ly_space ly + b_self b2, kBatchBytes) (base, ck_extent k).
Proof. geo.
intros b2 Hb2. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _ & _ & _ & _ & G13 & _).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (Z.eq_dec c kBatchClass) as [Ec|Hc0].
- pose proof (In_chunk_offs X k off Hk Hb) as IK. fold c x in IK. rewrite Ec in *.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in *.
assert (x <> xb). { intros E. img_apply (NDx x); [img_try (img_exact IK) | img_try (rewrite E; img_exact INB)]. }
unfold kBatchBytes in *.
assert (Gxm' : x mod 8192 = 0) by (img_try (pose proof geom as GE; do 17 (apply proj2 in GE); rewrite Ec, CS in GE; img_exact GE)).
apply Z.mod_divide in Gxm' as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros E; (subst; cbv beta); img_lia)). rewrite G4. nia.
- pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
destruct (Z.lt_ge_cases c 24).
+ pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
+ pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 Ha. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & _ & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_try (unfold kBatchBytes in *; img_lia) | img_try (zd (batch_vs_k b2 Hb2))].
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof k_prim as KP. pose proof geom as (G1 & _). unfold ly_rinfo in Ha.
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & _). unfold region_base in *. rewrite region_off_eq in * by img_lia.
img_apply ok_prim; [img_try (unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *; img_lia)|]. unfold kRegionInfoOff in *.
assert (c * 2 ^ 32 + 2 ^ 31 <= 2 ^ 37) by nia. img_lia.
Qed.
Lemma ok_fa : forall c', 1 <= c' <= 31 -> okr (fa_base ly c') kFreeArrayMax.
Proof. geo.
intros c' Hc' a Ha. pose proof HIGH as HI. pose proof k_prim as KP. pose proof geom as (G1 & _).
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). unfold fa_base in Ha. unfold region_base in *. rewrite !region_off_eq in * by img_lia.
img_apply ok_prim; [img_try (unfold kFreeArrayOffset, kFreeArrayMax in *; img_lia)|]. unfold kFreeArrayOffset, kFreeArrayMax in *.
destruct (Z.lt_trichotomy c' c) as [L'|[->|L']]; [| img_lia |].
- pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
- pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo. intros a Ha. pose proof HIGH as HI. img_apply ok_low. tbnum. img_lia. Qed.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv. Proof. intros a Ha. img_exact (ok_static 1 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha). Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize. Proof. intros a Ha. img_exact (ok_static 3 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha). Qed.
Definition cell_in (lo len : Z) (ce : acell) : Prop :=
lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len.
Lemma cell_xfer : forall ce, cell_holds B ly rd ce ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) -> cell_holds B ly rd' ce.
Proof. intros ce Hce Hok. eapply (cell_holds_agree B ly rd rd' ce Hce). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall Lc lo len, okr lo len -> Forall (cell_in lo len) Lc -> Forall (cell_holds B ly rd) Lc -> Forall (cell_holds B ly rd') Lc.
Proof.
intros Lc lo len OK IN OLD'. img_apply Forall_forall. intros ce Hce. img_apply cell_xfer; [img_try (img_exact (proj1 (Forall_forall _ _) OLD' ce Hce))|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN ce Hce) as [I1 I2]. img_apply OK. img_lia.
Qed.
Lemma OLD : forall ce, In ce (acells B ly X) -> cell_holds B ly rd ce.
Proof. intros ce Hce. img_exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) ce Hce). Qed.
Ltac old_in := img_apply Forall_forall; intros ? HIN; img_apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. img_refl. Qed.
Ltac fcons := img_apply Forall_cons; [img_try (split; cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells X1) (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells. rewrite reg'.
img_apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. img_apply Forall_nil.
- old_in. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo. intros a Ha. img_apply ok_T; unfold DJ, t_cache, t_stats, kThreadObjSize in *; img_lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells X1) (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold cache_cells. rewrite cache', X1_cinit.
img_apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c' ltac:(img_lia)) as (_ & _ & _ & K4 & _).
rewrite Hci in WC. destruct WC as [PM PL]. unfold cell_in, t_cache. repeat fcons.
img_apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. img_lia.
- old_in. right; left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; img_lia) |]. unfold cache_cells. rewrite Hci. img_exact HIN.
Qed.
Lemma cells_chunk_other : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells y).
Proof.
intros y Hy Hne. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
img_apply (cells_xfer _ (ck_base B ly y) (ck_extent y)); [img_try (intros a Ha; img_exact (ok_other y a Hy Hne Ha)) | |].
- pose proof (req_size_bounds (ck_req y) ltac:(img_lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 y), ?(EA y), ?EA0 by img_exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz y) 16); [img_try (img_apply Forall_nil)|].
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?(EA2 y), ?(EA y), ?EA0 by img_exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
- old_in. do 2 right; left. img_apply in_flat_map. exists y. split; [img_try (img_exact Hy) | img_try (img_exact HIN)].
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks X1)).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite E1, flat_map_app, Forall_app. split.
- img_apply Forall_flat_map'. intros y Hy. img_apply cells_chunk_other; [img_try (rewrite E; img_apply in_app_iff; left; img_exact Hy) | img_try (intros Ey; img_apply N1; rewrite <- Ey; img_apply in_map; img_exact Hy)].
- img_apply Forall_flat_map'. intros y Hy. img_apply cells_chunk_other; [img_try (rewrite E; img_apply in_app_iff; right; right; img_exact Hy) | img_try (intros Ey; img_apply N2; rewrite <- Ey; img_apply in_map; img_exact Hy)].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (img_try (old_in; do 3 right; left; img_exact HIN)).
unfold sec_cells in OLDS |- *. rewrite X1_sec_res, X1_sec_arr, E1. rewrite E in OLDS. rewrite flat_map_app in OLDS |- *. cbn [flat_map] in OLDS. rewrite Hb in OLDS. cbn [app] in OLDS.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_reserved; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_n; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_mutex; img_lia|].
img_apply Forall_app. split.
- img_apply (cells_xfer _ _ _ ok_Q); [|img_try (img_exact O4)]. img_apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_forall. intros ce Hce. pose proof (proj1 (Forall_forall _ _) O5 ce Hce) as Oc. rewrite <- flat_map_app in Hce. apply in_flat_map in Hce as (y & Hy & Hce).
assert (Hy' : In y (st_chunks X)) by (img_try (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; img_apply in_app_iff; [img_try (left; img_exact Hy) | img_try (right; right; img_exact Hy)])).
destruct (ck_beg y) as [|o|r o|c' p] eqn:Eby; try solve [destruct Hce].
assert (OKP : okr (ly_sec ly r) 32) by (img_try (intros a Ha; eapply (ok_secpage y r o a Hy' Eby); unfold kPage; img_lia)).
img_apply (cell_xfer _ Oc). intros j Hj. img_apply OKP. destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; img_lia.
Qed.
Lemma batch_cells_within : forall l ce, In ce (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof. geo.
induction l as [|b2 t IH]; intros ce Hce; [img_try (destruct Hce)|]. cbn [batch_cells] in Hce.
destruct Hce as [<-|[<-|[<-|Hce]]]; try (exists b2; split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)]).
apply in_app_iff in Hce as [Hce|Hce].
- apply in_map_iff in Hce as ([i y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. exists b2. split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)].
- destruct (IH ce Hce) as (b3 & H3 & R3). exists b3. split; [img_try (right; img_exact H3) | img_try (img_exact R3)].
Qed.
Lemma okr_batch : forall b2, In b2 (all_batches X) -> okr (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof. geo.
intros b2 Hb2 a Ha. pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hb2) as [L1 L2]. unfold kBatchSlots in L2.
img_apply (ok_batch b2 a Hb2). unfold kBatchBytes. img_lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells X1).
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
pose proof ok_inst as OKI.
assert (OKQ : okr (T + t_qc) 32) by (img_try (intros a Ha; img_apply ok_T; [img_try (unfold t_qc, kThreadObjSize in *; img_lia)|]; unfold DJ, t_qc, t_stats in *; img_lia)).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite X1_qglobal, X1_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_cmutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_rmutex; img_lia|].
img_apply Forall_app. split.
- apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O4); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O5); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O6); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_forall. intros ce Hce. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OT ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. img_apply (okr_batch b2); [img_try (unfold all_batches; img_apply in_app_iff; left; img_exact I2) | img_lia].
- apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
img_apply Forall_cons; [img_apply (cell_xfer _ G1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G4); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_forall. intros ce Hce. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OG ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. img_apply (okr_batch b2); [img_try (unfold all_batches; img_apply in_app_iff; right; img_exact I2) | img_lia].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells X1).
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (img_try (old_in; do 5 right; left; img_exact HIN)).
unfold fs_cells in OLDF |- *. rewrite X1_fs. img_apply (cells_xfer _ _ _ ok_F); [|img_try (img_exact OLDF)].
unfold cell_in, kFakeStackSize. fcons. fcons.
img_apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly X1).
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (img_try (old_in; do 6 right; left; img_exact HIN)).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite X1_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
img_apply Forall_forall. intros ce Hce. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD ce Hce)). intros j Hj. img_apply ok_low.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0, kLowMemEnd, kHighShadowBeg in *; tbnum; img_lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B X1).
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (img_try (old_in; do 7 right; left; img_exact HIN)).
unfold ialloc_cells in OLDI |- *. rewrite X1_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
img_apply Forall_forall. intros ce Hce. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI ce Hce)). intros j Hj. img_apply ok_low.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold kLowMemEnd, kHighShadowBeg in *; tbnum; img_lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (img_try (old_in; do 8 right; img_exact HIN)).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. img_apply ok_T; [img_try (unfold t_unwinding, kThreadObjSize in *; img_lia)|]. unfold DJ, t_stats, t_unwinding in *; img_lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly X1).
Proof.
unfold acells. rewrite !Forall_app. splits.
- img_exact cells_regions.
- img_exact cells_caches.
- img_exact cells_chunks.
- img_exact cells_sec.
- img_exact cells_quar.
- img_exact cells_fs.
- img_exact cells_depot.
- img_exact cells_ialloc.
- img_exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' X1.
Proof.
intros c' i v Hc' Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [img_try (img_exact (am_fa B ly X rd M c' i v Hc' Hi Hv kk Hkk))|].
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply (ok_fa c' Hc'). img_lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' X1.
Proof.
intros cid pos Hc0 Hp. rewrite frames'. rewrite AGok; [img_try (img_exact (am_flags B ly X rd M cid pos Hc0 Hp))|].
pose proof (flag_off_bounds cid pos Hc0 Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. img_apply ok_F. unfold kFakeStackSize. img_lia.
Qed.
Lemma depot' : depot_ok B ly rd' X1.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as HI.
unfold depot_ok, depot_ids, depot_traces in *. rewrite X1_depot. exists heads, links. split; [|img_try (split; [|img_exact D3])].
- intros b0 Hb0. destruct (D1 b0 Hb0) as [Y1 Y2]. split; [img_try (img_exact Y1)|]. intros kk Hkk. rewrite AGok; [img_try (img_exact (Y2 kk Hkk))|].
img_apply ok_low. unfold d_tab_words, kLowMemEnd, kHighShadowBeg in *. tbnum. img_lia.
- intros id Hid. destruct (D2 id Hid) as (Y1 & Y2 & Y3). split; [img_try (img_exact Y1)|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. img_lia. }
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. img_apply (ok_static 4 _ _ eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)). cbn [fst snd]. unfold kNodesBlockSize. img_lia. }
split; intros kk Hkk; rewrite AGok; auto; [img_try (img_apply OKN; img_lia)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by img_lia. img_apply OKN. img_lia.
Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(img_lia) H1) as X0. img_change (4096 / 8) with 512 in X0.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(img_lia) ltac:(img_lia)) as Y. img_change ((140737488355328 - 8) / 8) with 17592186044415 in Y. img_lia.
Qed.
Lemma u_al8 : u mod 8 = 0 /\ base mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. geo.
pose proof geom as (_ & _ & _ & _ & _ & _ & _ & B16 & _ & R16 & _).
assert (B8 : base mod 8 = 0) by (img_try (pose proof B16 as B0; apply Z.mod_divide in B0 as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists (2 * q); img_lia)).
assert (R8 : ck_rz k mod 8 = 0) by (img_try (pose proof R16 as R0; apply Z.mod_divide in R0 as [q Hq]; [|img_lia]; img_apply Z.mod_divide; [img_lia|]; exists (2 * q); img_lia)).
split; [|img_try (split; [img_exact B8 | img_exact R8])]. apply Z.mod_divide in B8 as [q Hq]; [|img_lia]. apply Z.mod_divide in R8 as [q' Hq']; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q + q'). img_lia.
Qed.
Lemma ext_rounded : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. geo.
pose proof KF as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(img_lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(img_lia)).
apply Z.mod_divide in R2 as [q Hq]; [|img_lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
- pose proof (primary_geometry (ck_req k) ltac:(img_lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. img_lia.
- pose proof (secondary_geometry (ck_req k) ltac:(img_lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
pose proof (rz_size_bounds (ck_req k)). img_lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). img_lia.
Qed.
Lemma DH_iff : forall g, g mod 8 = 0 -> (DH (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof. geo.
intros g Hg. pose proof u_al8 as (U8 & _ & _). unfold DH, shadow_addr.
apply Z.mod_divide in Hg as [c0 Hc0]; [|img_lia]. apply Z.mod_divide in U8 as [a Ha]; [|img_lia]. rewrite Hc0, Ha.
rewrite !Z_div_mult by img_lia. pose proof (Z.div_pos (nn + 7) 8). pose proof geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NN & _). nia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LO ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WF ltac:(img_lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; img_lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. img_lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' X1.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof geom as (_ & _ & _ & _ & _ & _ & _ & _ & RZ & _ & NN & EXT & _). pose proof u_al8 as (U8 & B8 & R8).
intros g v Hg8 HS'. pose proof (am_shadow B ly X rd M g) as SH.
unfold ashadow in HS', SH. rewrite E1, fa_poison' in HS'. rewrite E in SH.
rewrite find_chunk_at_app in HS', SH. cbn [find_chunk_at] in SH.
assert (OTHER : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> ck_base B ly y <= g < ck_base B ly y + ck_extent y ->
rd (shadow_addr g) = Some v -> rd' (shadow_addr g) = Some v).
{ intros y Hy Hne Hgy Hrd. pose proof (chunk_facts B ly X rd y M Hy) as (Y1 & Y2 & _).
rewrite AGok; [img_try (img_exact Hrd)|]. img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. pose proof (Z.div_pos (nn + 7) 8). nia. }
destruct (find_chunk_at B ly l1 g) as [y|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hy Hgy].
img_apply (OTHER y); [img_try (rewrite E; img_apply in_app_iff; left; img_exact Hy) | img_try (intros Ey; img_apply N1; rewrite <- Ey; img_apply in_map; img_exact Hy) | img_try (img_exact Hgy) | img_try (img_exact (SH v Hg8 HS'))].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
+
apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
assert (F2 : find_chunk_at B ly l2 g = None).
{ destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2; [|img_refl]. exfalso. apply find_chunk_at_In in F2 as [Hy Hgy].
assert (Hy' : In y (st_chunks X)) by (img_try (rewrite E; img_apply in_app_iff; right; right; img_exact Hy)).
assert (Hne : ck_beg y <> ck_beg k) by (img_try (intros Ey; img_apply N2; rewrite <- Ey; img_apply in_map; img_exact Hy)).
pose proof (chunks_disjoint B ly X rd y k M Hy' Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
pose proof (chunk_facts B ly X rd y M Hy') as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). pose proof (req_size_bounds (ck_req y) ltac:(img_lia)) as (_ & Q2 & _). img_lia. }
rewrite F2 in HS'. destruct (in_rangesb g (fa_poison_ranges ly X)) eqn:R; [|img_try (discriminate)]. injection HS' as <-.
apply Z.mod_divide in Hg8 as [c0 Hc0]; [|img_lia]. pose proof B8 as B8'. apply Z.mod_divide in B8' as [b0 Hb0]; [|img_lia]. pose proof R8 as R8'. apply Z.mod_divide in R8' as [r0 Hr0]; [|img_lia].
assert (J : (g - ck_base B ly k) / 8 = c0 - b0). { rewrite Hc0, Hb0. replace (c0 * 8 - b0 * 8) with ((c0 - b0) * 8) by img_lia. img_apply Z_div_mult. img_lia. }
assert (RU : ck_rz k / 8 = r0). { rewrite Hr0. img_apply Z_div_mult. img_lia. }
rewrite J in SH. unfold chunk_granule in SH. rewrite RU, Hst in SH.
set (q := (nn + 7) / 8) in *.
destruct (Z_lt_le_dec (c0 - b0) r0) as [C1|C1].
*
rewrite AGok; [img_try (img_apply SH; [rewrite Hc0; img_apply Z_mod_mult|]; replace (c0 - b0 <? r0) with true by (symmetry; img_apply Z.ltb_lt; img_exact C1); img_refl)|].
img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g ltac:(img_try (rewrite Hc0; img_apply Z_mod_mult))) in HD. nia.
* destruct (Z_lt_le_dec (c0 - b0) (r0 + q)) as [C2|C2].
--   img_apply NEW_sh; [img_try (img_apply (DH_iff g ltac:(rewrite Hc0; img_apply Z_mod_mult)); nia)|].
rewrite (SH shHeapFreed); [img_try (discriminate) | img_try (rewrite Hc0; img_apply Z_mod_mult) |].
replace (c0 - b0 <? r0) with false by (img_try (symmetry; img_apply Z.ltb_ge; img_lia)). replace (c0 - b0 <? r0 + q) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)). img_refl.
--
rewrite AGok; [img_try (img_apply SH; [rewrite Hc0; img_apply Z_mod_mult|];
replace (c0 - b0 <? r0) with false by (symmetry; img_apply Z.ltb_ge; img_lia); replace (c0 - b0 <? r0 + q) with false by (symmetry; img_apply Z.ltb_ge; img_lia); img_refl)|].
img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g ltac:(img_try (rewrite Hc0; img_apply Z_mod_mult))) in HD. nia.
+
assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
{ intros X0. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true) by (img_try (img_apply andb_true_intro; split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia)). rewrite TT in TK. discriminate. }
destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hy Hgy].
img_apply (OTHER y); [img_try (rewrite E; img_apply in_app_iff; right; right; img_exact Hy) | img_try (intros Ey; img_apply N2; rewrite <- Ey; img_apply in_map; img_exact Hy) | img_try (img_exact Hgy) | img_try (img_exact (SH v Hg8 HS'))].
* destruct (in_rangesb g (fa_poison_ranges ly X)) eqn:R; [|img_try (discriminate)].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
rewrite AGok; [img_try (img_exact (SH v Hg8 HS'))|]. img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (Z.div_pos (nn + 7) 8). nia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. img_apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [img_try (img_exact Z0)|]. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _). pose proof k_prim as (KP1 & KP2 & _).
pose proof geom as (_ & _ & _ & _ & _ & _ & _ & _ & RZ & _ & NN & EXT & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
-
pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|img_lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by img_lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)) as MD.
img_apply ok_hshadow; [img_try (img_apply hs_bounds; clear - hS1 hS2 Hi MD; unfold kHighMemBeg, kHighMemEnd in *; img_lia)|].
intros HD. apply (DH_iff (ly_stk_lo ly + 8 * i) ltac:(img_try (rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by img_lia; img_apply Z_mod_mult))) in HD.
pose proof (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. pose proof ext_rounded as (ER & _ & QP & _).
set (q := (nn + 7) / 8) in *. clear - HD DJ0 KP1 KP2 RZ NN ER Hi MD QP. unfold kPrimResvSize in *. nia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfx_zero_shadow in Hr.
img_apply ok_lowsh. unfold shadow_addr, SHADOW_OFF, kImgEnd, kLowShadowBeg, kHighShadowBeg.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hi |- *.
all: match goal with |- context [?x0 / 8] => let v := img_ev (x0 / 8) in img_change (x0 / 8) with v end.
all: match type of Hi with context [?x0 / 8] => let v := img_ev (x0 / 8) in img_change (x0 / 8) with v in Hi end.
all: clear - Hi; img_lia.
Qed.
Lemma vis_keep : forall Lr, Forall (range_vis B ly rd) Lr -> Forall (range_vis B ly rd') Lr.
Proof. intros Lr H. img_exact (Forall_range_vis_keep B ly rd rd' Lr VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_junk B ly X rd M) as J.
unfold ajunk in J |- *. unfold quar_junk, cache_junk, cache, sec_junk in J |- *. rewrite all_batches', X1_cinit, X1_cache, X1_sec_arr, X1_sec_res, E1. rewrite Hci, E in J.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J1 i Hi))|].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J2 i Hi))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J3))|]. img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J4))|].
img_apply Forall_app. split.
{ rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [_ J5b].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J5a)) | img_try (img_exact (vis_keep _ J5b))]. }
img_apply Forall_app. split; [|img_try (img_exact (vis_keep _ J))].
apply Forall_cons_iff in J6 as [J6a J6]. apply Forall_cons_iff in J6 as [J6b J6]. apply Forall_cons_iff in J6 as [J6c J6].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J6a i Hi))|]. img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J6b i Hi))|]. img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J6c i Hi))|].
rewrite flat_map_app in J6 |- *. cbn [flat_map] in J6. rewrite Hb in J6. cbn [app] in J6. img_exact (vis_keep _ J6).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas X1).
Proof. rewrite aareas'. img_exact (vis_keep _ (am_areas B ly X rd M)). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_client B ly X rd M) as A.
unfold aclient in A |- *. rewrite frames', E1. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A. unfold chunk_user at 2 in A. rewrite Hst in A. cbn [app] in A.
img_exact (vis_keep _ A).
Qed.
Lemma placed' : sec_placed ly X1.
Proof. unfold sec_placed. rewrite sec_extents'. img_exact (am_placed B ly X rd M). Qed.
Theorem rc_fin_ARm : ARm B ly X1 rd'.
Proof.
constructor.
- img_exact WS1.
- img_exact (am_universe B ly X rd M).
- img_exact (am_syms B ly X rd M).
- img_exact LO.
- img_exact placed'.
- img_exact CONST'.
- img_exact (am_const_owned B ly X rd M).
- img_exact cells_all.
- img_exact fa'.
- img_exact flags'.
- img_exact depot'.
- img_exact shadow'.
- img_exact zshadow'.
- img_exact junk'.
- img_exact areas'.
- img_exact client'.
- pose proof (am_zero B ly X rd M) as ZR. img_apply Forall_forall. intros r Hr i Hi. rewrite AGok; [img_try (img_exact (proj1 (Forall_forall _ _) ZR r Hr i Hi))|].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. img_apply ok_low.
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; unfold kLowMemEnd, kHighShadowBeg in *; tbnum; img_lia.
- img_exact (am_tsd B ly X rd M).
- img_exact (am_static_img B ly X rd M).
Qed.
Lemma ALedger_X1 : forall segs md, ALedger segs ly X md -> ALedger segs ly X1 md.
Proof. geo.
intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14]. constructor; try assumption.
- rewrite sec_extents'. img_exact L7.
- rewrite sec_extents'. img_exact L8.
- rewrite prim_committed', sec_extents'. img_exact L9.
- rewrite sec_extents'. img_exact L12.
Qed.
Lemma own_ext_quar : forall a, base <= a < base + ck_extent k -> aowned B ly X a.
Proof. geo.
intros a Ha. pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Hb in GG. cbv zeta in GG.
destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
assert (NB : forall y, In y (st_chunks X) -> ck_state y = CAllocated ->
~ (ck_base B ly y + ck_rz y <= a < ck_base B ly y + ck_rz y + req_size (ck_req y))).
{ intros y Hy Hsy Hr. pose proof (user_in_extent B ly X rd y a M Hy Hr) as HE.
assert (Hne : ck_beg y <> ck_beg k).
{ intros Eq. destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2).
rewrite E in Hy. apply in_app_iff in Hy as [X0|[<-|X0]]; [img_try (img_apply N1) | img_try (rewrite Hst in Hsy; discriminate) | img_try (img_apply N2)]; rewrite <- Eq; img_apply in_map; img_exact X0. }
pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. img_lia. }
pose proof (region_in_prim ly (prim_class off) LO ltac:(img_lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [img_try (img_exact M) | img_lia | img_try (img_exact NB)].
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
pose proof geom as GE. pose proof k_prim as KP.
intros a Ha0 HD. destruct HD as [Y|[Y|[Y|Y]]].
- right. img_exact Y.
- left. img_apply own_ext_quar. unfold DK, Mv, kChunkHeaderSize in Y. img_lia.
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd]. unfold DJ, t_stats, kThreadObjSize in *. img_lia.
-
left. pose proof u_al8 as (U8 & _ & _). apply Z.mod_divide in U8 as [a0 Hua]; [|img_lia].
unfold DH, shadow_addr in Y. rewrite Hua, Z_div_mult in Y by img_lia.
replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by img_lia. img_lia. }
eapply own_shadow_prim; [img_try (img_exact M)|]. pose proof ext_rounded as (ER & _ & QP & _). pose proof KP as (KP1 & KP2 & _).
pose proof GE as (_ & _ & _ & _ & _ & _ & _ & _ & RZ & _). clear - Y ER QP KP1 KP2 Hua RZ. nia.
Qed.
Lemma aowned_X1 : forall a, aowned B ly X1 a <-> aowned B ly X a.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (CB : forall a, aclient_byte B ly X1 a <-> aclient_byte B ly X a).
{ intros a. unfold aclient_byte. rewrite frames', E1, E. split; intros [(y & Hy & Hsy & Hr)|H2].
- left. exists y. split; [|img_try (split; [img_exact Hsy | img_exact Hr])]. apply in_app_iff in Hy as [Hy|Hy]; img_apply in_app_iff; [img_try (left; img_exact Hy) | img_try (right; right; img_exact Hy)].
- right. img_exact H2.
- left. exists y. split; [|img_try (split; [img_exact Hsy | img_exact Hr])]. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [img_try (img_apply in_app_iff; left; img_exact Hy) | img_try (rewrite Hst in Hsy; discriminate) | img_try (img_apply in_app_iff; right; img_exact Hy)].
- right. img_exact H2. }
intros a. unfold aowned. rewrite sec_extents'. rewrite (CB a). tauto.
Qed.
End f.
End b.
