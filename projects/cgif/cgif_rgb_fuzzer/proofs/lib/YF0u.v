(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0b YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF0k YF0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section k. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (rd rd' : reader).
Hypothesis M : ARm B ly S rd.
Definition S' : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Hypothesis Hev : aregime S.
Local Notation T := (ly_T ly).
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := T + t_unwinding <= a < T + t_unwinding + 1.
Definition DS (a : Z) : Prop := sp - ASTACK <= a < sp.
Definition DI (a : Z) : Prop := (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).
Definition D (a : Z) : Prop := DT a \/ DS a \/ DI a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_unw IAL CONST'.
Ltac geo := drop_mem; clear Hev.
Ltac geo' := geo.
Lemma S'_regions : st_regions S' = st_regions S.   Proof. img_refl. Qed.
Lemma S'_cache : st_cache S' = st_cache S.         Proof. img_refl. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited S. Proof. img_refl. Qed.
Lemma S'_secs : st_secs S' = st_secs S.             Proof. img_refl. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. img_refl. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. img_refl. Qed.
Lemma S'_fs : st_fs S' = st_fs S.                   Proof. img_refl. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal S.    Proof. img_refl. Qed.
Lemma S'_qthread : st_qthread S' = st_qthread S.    Proof. img_refl. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks S.       Proof. img_refl. Qed.
Lemma S'_depot : st_depot S' = st_depot S.          Proof. img_refl. Qed.
Lemma S'_inited : st_internal_inited S' = true.     Proof. img_refl. Qed.
Lemma S'_nev : st_nev S' = st_nev S + 1.            Proof. img_refl. Qed.
Lemma reg' : forall c, reg S' c = reg S c.          Proof. img_refl. Qed.
Lemma cache' : forall c, cache S' c = cache S c.    Proof. img_refl. Qed.
Lemma frames' : frames S' = frames S.               Proof. img_refl. Qed.
Lemma all_batches' : all_batches S' = all_batches S. Proof. img_refl. Qed.
Lemma WF : Wf (as_universe B) S. Proof. img_exact (am_wf B ly S rd M). Qed.
Lemma LO : layout_ok ly. Proof. img_exact (am_layout B ly S rd M). Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. drop_mem. img_apply (WfP_weaken _ 1 1 1); try img_lia. unfold S'. img_apply WfP_set_internal_inited. img_apply WfP_tick; [img_try (img_exact WF) | img_try (img_exact Hev)]. Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo'.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- img_exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- img_apply zdisjoint_sym. img_apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). img_lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly S) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo'.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. img_exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks S) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly S)).
Proof. geo'.
intros y Hy. pose proof (chunk_facts B ly S rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _). exists (prim_class o). splits; img_lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [img_refl | img_lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by img_lia. img_exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks S) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo'.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(img_lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. img_lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. img_lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|img_lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|img_lia].
exfalso. img_apply (H (Z.max a c)); img_lia.
Qed.
Lemma ZCH : forall x, In x (st_chunks S) -> zone3 (ck_base B ly x) (ck_extent x).
Proof. geo'.
intros x Hx. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
img_apply (zone3_intro ly (ck_base B ly x) (ck_extent x) IMG ltac:(img_try (clear - G5 G8 Q1; img_lia)) G1).
img_apply zdisjoint_of_pointwise; [img_try (clear - G5 G8 Q1; img_lia) | img_try (img_exact (proj1 (proj2 (lo_img _ LO)))) |].
intros y Hy. img_exact (proj1 (chunk_apart B ly S rd x y M Hx Hy)).
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof. geo'.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hsz. img_apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (img_try (destruct (Nat.lt_ge_cases i 8) as [X|X]; [img_try (img_exact X)|]; assert (X' : nth_error (owned_extents ly) i = None) by (img_apply nth_error_None; cbn; img_lia); rewrite X' in He; discriminate)).
img_exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(img_try (unfold static_extents; rewrite nth_error_app1 by (cbn; img_lia); img_exact He))
ltac:(img_try (unfold static_extents; rewrite nth_error_app2 by (cbn; img_lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; img_lia); img_refl))). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(img_try (unfold kPtrArrayResv; img_lia))) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(img_try (unfold kThreadObjSize; img_lia))) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(img_try (unfold kFakeStackSize; img_lia))) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(img_try (unfold kNodesBlockSize; img_lia))) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(img_try (unfold kStoreBlockSize; img_lia))) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(img_lia)) as ZC. clear Z3 HA HD.
pose proof ZQ as (ZQ1 & ZQ2 & _). pose proof ZT as (ZT1 & ZT2 & _). pose proof ZF as (ZF1 & ZF2 & _). pose proof ZNB as (ZNB1 & ZNB2 & _). pose proof ZSB as (ZSB1 & ZSB2 & _). pose proof ZC as (ZC1 & ZC2 & _).
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
unfold page_aligned in *. splits; try assumption; try img_lia.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\ rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= 2 ^ 31 /\
In x (batch_offs S kBatchClass).
Proof. geo'.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b2; auto)).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|img_lia]. apply Z.mod_divide in AA as [q' Hq']; [|img_lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try img_lia. unfold region_base. (subst x; cbv beta). img_lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo'.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(img_lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; img_lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. img_lia.
Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo'.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(img_lia) H1) as X. img_change (4096 / 8) with 512 in X.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(img_lia) ltac:(img_lia)) as Y. img_change ((140737488355328 - 8) / 8) with 17592186044415 in Y. img_lia.
Qed.
Lemma LOWD : forall a, DI a \/ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> TFX_IMG_LO <= a < TFX_IMG_END.
Proof. geo'.
intros a Ha. unfold DI in Ha. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB), (ts_depot _ TB), (ts_store _ TB) in Ha.
unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_DEPOT, TFX_STORE, d_map1, TFX_IMG_LO, TFX_IMG_END in *. img_lia.
Qed.
Lemma D_cases : forall a, D a -> (T <= a < T + kThreadObjSize /\ DT a) \/ (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFX_IMG_LO <= a < TFX_IMG_END /\ DI a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. destruct Ha as [X|[X|X]].
- left. split; [|img_try (img_exact X)]. unfold DT, t_unwinding, kThreadObjSize in *. img_lia.
- right; left. unfold DS, ASTACK in *. img_lia.
- right; right. split; [img_try (img_apply LOWD; left; img_exact X) | img_try (img_exact X)].
Qed.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. img_apply AG; assumption. Qed.
Ltac zd H := let X := fresh "ZD" in pose proof H as X; unfold zdisjoint in X; cbn [fst snd] in X; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize in X; img_lia.
Ltac hnum := ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (img_try (clear - HI; unfold zone3 in HI; tauto)); unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZZ. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (SX 1 2 _ _ eq_refl eq_refl ltac:(img_lia))) | img_try (zd (SX 1 8 _ _ eq_refl eq_refl ltac:(img_lia)))].
Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_F ly) kFakeStackSize ZZ. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (SX 3 2 _ _ eq_refl eq_refl ltac:(img_lia))) | img_try (zd (SX 3 8 _ _ eq_refl eq_refl ltac:(img_lia)))].
Qed.
Lemma ok_NB : okr (ly_NB ly) kNodesBlockSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_NB ly) kNodesBlockSize ZZ. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (SX 4 2 _ _ eq_refl eq_refl ltac:(img_lia))) | img_try (zd (SX 4 8 _ _ eq_refl eq_refl ltac:(img_lia)))].
Qed.

Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[X|[X _]]]; hnum; try img_lia; [img_try (img_exact (ND Y)) | img_try (zd (SX 2 8 _ _ eq_refl eq_refl ltac:(img_lia)))].
Qed.
Lemma ok_prim : okr (ly_prim ly) kPrimResvSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia))) | img_try (zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)))].
Qed.
Lemma ok_chunk : forall x a, In x (st_chunks S) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo'.
intros x a Hx Ha. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & _). pose proof (ZCH x Hx) as (ZX1 & ZX2 & ZZ). unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
pose proof HIGH as HI. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (anyX x 2 _ Hx eq_refl ltac:(img_lia))) | img_try (zd (anyX x 8 _ Hx eq_refl ltac:(img_lia)))].
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo'.
intros x r o a Hx Ebx Ha.
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof HIGH as HI. pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req x)) IMG ltac:(img_try (clear - Gext G5 G8 Q2; unfold kPage in *; img_lia)) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
hnum. unfold kPage in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try img_lia; [img_try (zd (SECX _ 2 _ Gin eq_refl)) | img_try (zd (SECX _ 8 _ Gin eq_refl))].
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches S) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo'.
intros b2 a Hb2 Ha. pose proof HIGH as HI.
destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
img_apply ok_prim. unfold kBatchBytes in *. img_lia.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo'. intros a Ha. unfold ly_rinfo, kRegionInfoOff in Ha. pose proof HIGH as HI. unfold kSpaceSize in HI. img_apply ok_prim. img_lia. Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo'.
intros c Hc a Ha. pose proof HIGH as HI. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
unfold region_base in *. img_apply ok_prim. img_lia.
Qed.
Lemma ok_low : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ~ DI a -> ok a.
Proof. geo'.
intros a Ha N1. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[_ Y]]]; hnum; try img_lia. img_exact (N1 Y).
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo'.
intros a Ha. rewrite (ts_inst _ TB) in Ha. img_apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFX_INST, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *; img_lia.
Qed.
Lemma ok_depot_tab : okr (as_depot B) (4 * 2 ^ 20 + 32).
Proof. geo'.
intros a Ha. rewrite (ts_depot _ TB) in Ha. img_apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFX_DEPOT, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *; img_lia.
Qed.
Lemma ok_store : okr (as_store B) 32.
Proof. geo'.
intros a Ha. rewrite (ts_store _ TB) in Ha. img_apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *; img_lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. hnum. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; img_lia.
Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. img_apply Forall_forall. intros c Hc. img_apply cell_xfer; [img_try (img_exact (proj1 (Forall_forall _ _) OLD c Hc))|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. img_apply OK. img_lia.
Qed.
Lemma batch_cells_within : forall l c, In c (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo'.
induction l as [|b2 t IH]; intros c Hc; [img_try (destruct Hc)|]. cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]]; try (exists b2; split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)]).
apply in_app_iff in Hc as [Hc|Hc].
- apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. exists b2. split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)].
- destruct (IH c Hc) as (b3 & H3 & R3). exists b3. split; [img_try (right; img_exact H3) | img_try (img_exact R3)].
Qed.
Lemma OLD : forall c, In c (acells B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd M) c Hc). Qed.
Ltac old_in := img_apply Forall_forall; intros ? HIN; img_apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo'.
intros y d Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo'.
intros y d d' Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo'. img_refl. Qed.
Ltac fcons := img_apply Forall_cons; [img_try (split; cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
img_apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. img_apply Forall_nil.
- old_in. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo'. intros a Ha. img_apply ok_T; unfold DT, t_cache, t_unwinding, kThreadObjSize in *; img_lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite cache', S'_cinit.
img_apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(img_lia)) as (_ & _ & _ & K4 & _).
unfold cell_in, t_cache. destruct (st_cache_inited S).
+ destruct WC as [PM PL]. repeat fcons. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. img_lia.
+ repeat fcons. img_apply Forall_nil.
- old_in. right; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) |]. unfold cache_cells. img_exact HIN.
Qed.
Lemma cells_chunk : forall x, In x (st_chunks S) -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
img_apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [img_try (intros a Ha; img_exact (ok_chunk x a Hx Ha)) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [img_try (img_apply Forall_nil)|].
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
- old_in. do 2 right; left. img_apply in_flat_map. exists x. split; [img_try (img_exact Hx) | img_try (img_exact HIN)].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (img_try (old_in; do 3 right; left; img_exact HIN)).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_reserved; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_n; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_mutex; img_lia|].
img_apply Forall_app. split.
- img_apply (cells_xfer _ _ _ ok_Q); [|img_try (img_exact O4)]. img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (img_try (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; img_lia)).
img_apply (cell_xfer _ Oc). intros j Hj. img_apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; img_lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
pose proof ok_inst as OKI.
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, S'_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
assert (OKQ : okr (T + t_qc) 32) by (img_try (intros a Ha; img_apply ok_T; unfold DT, t_qc, t_unwinding, kThreadObjSize in *; img_lia)).
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_cmutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_rmutex; img_lia|].
img_apply Forall_app. split.
- img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O4); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O5); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O6); intros j Hj; img_apply OKQ; cbn in Hj |- *; img_lia|].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OT c Hc)).
destruct (batch_cells_within (qc_list (st_qthread S)) c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; img_exact I2))) as [L1 L2].
img_apply (ok_batch b2); [img_try (unfold all_batches; img_apply in_app_iff; left; img_exact I2) | img_try (unfold kBatchSlots, kBatchBytes in *; img_lia)].
- img_apply Forall_cons; [img_apply (cell_xfer _ G1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G4); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; img_exact I2))) as [L1 L2].
img_apply (ok_batch b2); [img_try (unfold all_batches; img_apply in_app_iff; right; img_exact I2) | img_try (unfold kBatchSlots, kBatchBytes in *; img_lia)].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (img_try (old_in; do 5 right; left; img_exact HIN)).
unfold fs_cells in OLDF |- *. rewrite S'_fs. img_apply (cells_xfer _ _ _ ok_F); [|img_try (img_exact OLDF)].
unfold cell_in, kFakeStackSize. fcons. fcons.
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly S)) by (img_try (old_in; do 6 right; left; img_exact HIN)).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot.
apply Forall_cons_iff in OLDD as [O1 OLDD]. apply Forall_cons_iff in OLDD as [O2 OLDD]. apply Forall_cons_iff in OLDD as [O3 OLDD]. apply Forall_cons_iff in OLDD as [O4 _].
pose proof ok_depot_tab as OKD. pose proof ok_store as OKS. unfold d_nuniq, d_map1, s_total, s_block0 in *.
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKD; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKD; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKS; cbn in Hj |- *; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O4); intros j Hj; img_apply OKS; cbn in Hj |- *; img_lia|]. img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia].
cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. img_refl.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
Proof.
unfold acells. rewrite S'_chunks. rewrite !Forall_app. splits.
- img_exact cells_regions.
- img_exact cells_caches.
- img_apply Forall_flat_map'. intros x Hx. img_exact (cells_chunk x Hx).
- img_exact cells_sec.
- img_exact cells_quar.
- img_exact cells_fs.
- img_exact cells_depot.
- img_exact (proj1 IAL).
- img_exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [img_try (img_exact (am_fa B ly S rd M c i v Hc Hi Hv kk Hkk))|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply (ok_fa c Hc). img_lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [img_try (img_exact (am_flags B ly S rd M cid pos Hc Hp))|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. img_apply ok_F. unfold kFakeStackSize. img_lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (am_depot B ly S rd M) as Xdepot. img_change (depot_ok B ly rd' S') with (depot_ok B ly rd' S).
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|img_try (split; [|img_exact D3])].
- intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [img_try (img_exact H1)|]. intros kk Hkk. rewrite AGok; [img_try (img_exact (H2 kk Hkk))|].
img_apply ok_depot_tab. unfold d_tab_words in Hb. img_lia.
- intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [img_try (img_exact H1)|].
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly S rd M) as (U1 & _).
unfold DEPOT_MAX in U1. img_lia. }
assert (OR : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)) by (img_try (intros kk Hkk; img_apply ok_NB; unfold kNodesBlockSize; img_lia)).
split; intros kk Hkk; rewrite AGok; auto; [img_try (img_apply OR; img_lia)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by img_lia. img_apply OR. img_lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
intros g v Hg8 HS'. pose proof (am_shadow B ly S rd M g v Hg8) as SH.
assert (E : ashadow B ly S' g = ashadow B ly S g) by img_refl. rewrite E in HS'. specialize (SH HS').
rewrite AGok; [img_try (img_exact SH)|]. img_apply ok_hshadow. img_apply hs_bounds.
- pose proof (AR_dummy := I). unfold ashadow in HS'.
destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
+ apply find_chunk_at_In in F as [Hx Hgx]. pose proof (chunk_facts B ly S rd x M Hx) as (X1 & X2 & _). unfold in_app in X1. img_lia.
+ destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|img_try (discriminate)].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). img_exact (proj1 (fa_poison_high lo len g Hin Hg)).
- unfold ashadow in HS'. pose proof HIGH as HI.
destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
+ apply find_chunk_at_In in F as [Hx Hgx]. pose proof (chunk_facts B ly S rd x M Hx) as (X1 & X2 & _). apply Z.mod_divide in Hg8 as [c Hc]; [|img_lia].
pose proof (proj1 (proj2 (proj2 (chunk_facts B ly S rd x M Hx)))). ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia.
+ destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|img_try (discriminate)].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
apply Z.mod_divide in Hg8 as [c Hc]; [|img_lia]. ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly S rd M) as ZS. unfold zshadow_ok in ZS |- *. img_apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [img_try (img_exact Z0)|]. pose proof HIGH as HI.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|img_lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by img_lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)).
img_apply ok_hshadow. img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; img_lia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfx_zero_shadow in Hr.
img_apply ok_hshadow. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hi |- *.
all: match goal with |- context [?x / 8] => let v := img_ev (x / 8) in img_change (x / 8) with v end.
all: match type of Hi with context [?x / 8] => let v := img_ev (x / 8) in img_change (x / 8) with v in Hi end.
all: img_lia.
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. img_exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof. img_change (ajunk B ly S') with (ajunk B ly S). img_exact (vis_keep _ (am_junk B ly S rd M)). Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. img_change (aareas S') with (aareas S). img_exact (vis_keep _ (am_areas B ly S rd M)). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. img_change (aclient S') with (aclient S). img_exact (vis_keep _ (am_client B ly S rd M)). Qed.
Lemma placed' : sec_placed ly S'.
Proof. img_change (sec_placed ly S') with (sec_placed ly S). img_exact (am_placed B ly S rd M). Qed.
Theorem free_finn_ARm : ARm B ly S' rd'.
Proof.
constructor.
- img_exact WS'.
- img_exact (am_universe B ly S rd M).
- img_exact (am_syms B ly S rd M).
- img_exact LO.
- img_exact placed'.
- img_exact CONST'.
- img_exact (am_const_owned B ly S rd M).
- img_exact cells_all.
- img_exact fa'.
- img_exact flags'.
- img_exact depot'.
- img_exact shadow'.
- img_exact zshadow'.
- img_exact junk'.
- img_exact areas'.
- img_exact client'.
- img_exact (proj2 IAL).
- img_exact (am_tsd B ly S rd M).
- img_exact (am_static_img B ly S rd M).
Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly S md -> ALedger segs ly S' md.
Proof. geo'. intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14]. constructor; try assumption. Qed.
Lemma abudget_le : abudget S <= abudget S'.
Proof. geo'. unfold abudget. img_change (sec_live_bytes S') with (sec_live_bytes S). img_change (sec_hulls S') with (sec_hulls S)  . rewrite S'_nev. unfold EV_A. img_lia. Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly S a \/ DS a.
Proof. drop_mem. clear Hev.
intros a Ha0 HD. pose proof HIGH as HI. destruct HD as [X|[X|X]].
- left. eapply (own_core B ly S rd (T, kThreadObjSize) a M); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd]. unfold DT, t_unwinding, kThreadObjSize in *. img_lia.
- right. img_exact X.
- left. img_apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). unfold DI in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X.
img_apply Exists_exists. exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (unfold Tfx_owned_static; cbn; tauto)|]. unfold in_zr, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in *. cbn [fst snd]. img_lia.
Qed.
End k.
End f.
