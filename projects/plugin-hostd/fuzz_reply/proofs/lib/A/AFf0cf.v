(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFf0.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/AFf0.v (the allocator relation rebuilt after the free interceptor's NULL arm) and ported from cgif's ARm to the event-free instance's ARmcf / ARcf (Reusable/YG0ncf.v). The changes, and nothing else:
   the Context gains {ci : CfImg} {cp : CfParams}, which ARmcf needs; the Section takes the ghost set Hp and M : ARmcf B ly S Hp rd; cgif's Hev : aregime S is replaced by HII : st_internal_inited S = true (the cf invariant has no event bound, and WfP_cf_tick needs no premise);
   the stack window is generalized from ASTACK to Variables (STK sp) with 0 <= STK and ly_stk_lo ly + STK <= sp <= ly_stk_hi ly, DS a := sp - STK <= a < sp (the consumer, Deallocate, uses DFSTACK = 8192);
   am_X -> amc_X, wf_X / wr_X -> wfc_X / wrc_X, chunk_facts / chunk_apart / own_* -> their YG0scf / YG0qcf _cf forms, mapped_user_bound (2 ^ 31) -> mapped_bound_cf (kFreeArrayOffset, still below a region's 2 ^ 32), acells -> acells_cf (region_cells_cf drops the exhausted byte), ajunk -> ajunk_cf, shadow_ok -> shadow_ok_cf, and the added field amc_hp_live;
   conclusions free_finn_ARmcf, D_owned_cf, S'_dtick, ALedger_cf_S', abudget_cf_S' (the cf budget has no event term, so it is unchanged), and after the Section the ARcf assembly free_finn_ARcf (AFg3.v's FINH, first bullet, with ALedger_same_cf and ahs_transfer_cf).
   D_owned_cf finds the owned static area by value over the whole Tfib_owned_static table (ADIfaceImgA.covers_b), where AFf0.v:516-517 typed the area's address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0qcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x AFl0 AFeq AFex.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ADIfaceImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (rd rd' : reader).
Variable Hp : list Z.
Hypothesis M : ARmcf B ly S Hp rd.
Definition S' : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Hypothesis HII : st_internal_inited S = true.
Local Notation T := (ly_T ly).
Variables (STK sp : Z).
Hypothesis HSTK : 0 <= STK.
Hypothesis Hsp : ly_stk_lo ly + STK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := T + t_unwinding <= a < T + t_unwinding + 1.
Definition DS (a : Z) : Prop := sp - STK <= a < sp.
Definition DI (a : Z) : Prop := (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).
Definition D (a : Z) : Prop := DT a \/ DS a \/ DI a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_unw IAL CONST'.
Ltac geo := drop_mem; clear HII.
Ltac geo' := geo.
Lemma S'_regions : st_regions S' = st_regions S.   Proof. reflexivity. Qed.
Lemma S'_cache : st_cache S' = st_cache S.         Proof. reflexivity. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited S. Proof. reflexivity. Qed.
Lemma S'_secs : st_secs S' = st_secs S.             Proof. reflexivity. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. reflexivity. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. reflexivity. Qed.
Lemma S'_fs : st_fs S' = st_fs S.                   Proof. reflexivity. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal S.    Proof. reflexivity. Qed.
Lemma S'_qthread : st_qthread S' = st_qthread S.    Proof. reflexivity. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks S.       Proof. reflexivity. Qed.
Lemma S'_depot : st_depot S' = st_depot S.          Proof. reflexivity. Qed.
Lemma S'_inited : st_internal_inited S' = true.     Proof. reflexivity. Qed.
Lemma S'_nev : st_nev S' = st_nev S + 1.            Proof. reflexivity. Qed.
Lemma reg' : forall c, reg S' c = reg S c.          Proof. reflexivity. Qed.
Lemma cache' : forall c, cache S' c = cache S c.    Proof. reflexivity. Qed.
Lemma frames' : frames S' = frames S.               Proof. reflexivity. Qed.
Lemma all_batches' : all_batches S' = all_batches S. Proof. reflexivity. Qed.
Lemma S'_dtick : S' = set_nev (st_nev S + 1) S.
Proof. unfold S'. generalize HII. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity. Qed.
Lemma WF : Wf_cf (as_universe B) S. Proof. exact (amc_wf B ly S Hp rd M). Qed.
Lemma LO : layout_ok ly. Proof. exact (amc_layout B ly S Hp rd M). Qed.
Lemma WS' : Wf_cf (as_universe B) S'.
Proof. drop_mem. rewrite S'_dtick. exact (WfP_cf_tick _ 0 0 0 S WF). Qed.
(* Positions below index static_extents / owned_extents (Reusable/YG0f.v:297-302), built only from layout fields, never an image table. *)
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo'.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly S) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo'.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks S) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + kFreeArrayOffset /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly S)).
Proof. geo'.
intros y Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _). exists (prim_class o). splits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [reflexivity | lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by lia. exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks S) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo'.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. unfold kFreeArrayOffset in X2. lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Lemma ZCH : forall x, In x (st_chunks S) -> zone3 (ck_base B ly x) (ck_extent x).
Proof. geo'.
intros x Hx. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(clear - G7; lia)) as (_ & Q1 & _).
apply (zone3_intro ly (ck_base B ly x) (ck_extent x) IMG ltac:(clear - G5 G8 Q1; lia) G1).
apply zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
intros y Hy. exact (proj1 (chunk_apart_cf B ly S Hp rd x y M Hx Hy)).
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
{ intros i x sz He Hsz. apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (destruct (Nat.lt_ge_cases i 8) as [X|X]; [exact X|]; assert (X' : nth_error (owned_extents ly) i = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof ZQ as (ZQ1 & ZQ2 & _). pose proof ZT as (ZT1 & ZT2 & _). pose proof ZF as (ZF1 & ZF2 & _). pose proof ZNB as (ZNB1 & ZNB2 & _). pose proof ZSB as (ZSB1 & ZSB2 & _). pose proof ZC as (ZC1 & ZC2 & _).
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
unfold page_aligned in *. splits; try assumption; try lia.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\ rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= kFreeArrayOffset /\
In x (batch_offs S kBatchClass).
Proof. geo'.
intros b2 Hb2. pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try lia. unfold region_base. subst x. lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo'.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfc_classes _ _ _ _ _ WF c ltac:(lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c WF ltac:(lia)) as MB. unfold kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in *. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo'.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(lia) H1) as X. change (4096 / 8) with 512 in X.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(lia) ltac:(lia)) as Y. change ((140737488355328 - 8) / 8) with 17592186044415 in Y. lia.
Qed.
Lemma LOWD : forall a, DI a \/ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof. geo'.
intros a Ha. unfold DI in Ha. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB), (ts_depot _ TB), (ts_store _ TB) in Ha.
unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.
Lemma D_cases : forall a, D a -> (T <= a < T + kThreadObjSize /\ DT a) \/ (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END /\ DI a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. destruct Ha as [X|[X|X]].
- left. split; [|exact X]. unfold DT, t_unwinding, kThreadObjSize in *. lia.
- right; left. unfold DS in *. lia.
- right; right. split; [apply LOWD; left; exact X | exact X].
Qed.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac zd H := let X := fresh "ZD" in pose proof H as X; unfold zdisjoint in X; cbn [fst snd] in X; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize in X; lia.
Ltac hnum := ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZZ. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SX 1 2 _ _ eq_refl eq_refl ltac:(lia)) | zd (SX 1 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_F ly) kFakeStackSize ZZ. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SX 3 2 _ _ eq_refl eq_refl ltac:(lia)) | zd (SX 3 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_NB : okr (ly_NB ly) kNodesBlockSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_NB ly) kNodesBlockSize ZZ. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SX 4 2 _ _ eq_refl eq_refl ltac:(lia)) | zd (SX 4 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_C : okr (ly_C ly) 256.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_C ly) 256 ZZ. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SX 6 2 _ _ eq_refl eq_refl ltac:(lia)) | zd (SX 6 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[X|[X _]]]; hnum; try lia; [exact (ND Y) | zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_prim : okr (ly_prim ly) kPrimResvSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)) | zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia))].
Qed.
Lemma ok_chunk : forall x a, In x (st_chunks S) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo'.
intros x a Hx Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & _). pose proof (ZCH x Hx) as (ZX1 & ZX2 & ZZ). unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
pose proof HIGH as HI. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (anyX x 2 _ Hx eq_refl ltac:(lia)) | zd (anyX x 8 _ Hx eq_refl ltac:(lia))].
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo'.
intros x r o a Hx Ebx Ha.
pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof HIGH as HI. pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req x)) IMG ltac:(clear - Gext G5 G8 Q2; unfold kPage in *; lia) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
hnum. unfold kPage in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; try lia; [zd (SECX _ 2 _ Gin eq_refl) | zd (SECX _ 8 _ Gin eq_refl)].
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches S) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo'.
intros b2 a Hb2 Ha. pose proof HIGH as HI.
destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
apply ok_prim. unfold kBatchBytes, kFreeArrayOffset in *. lia.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo'. intros a Ha. unfold ly_rinfo, kRegionInfoOff in Ha. pose proof HIGH as HI. unfold kSpaceSize in HI. apply ok_prim. lia. Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo'.
intros c Hc a Ha. pose proof HIGH as HI. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
unfold region_base in *. apply ok_prim. lia.
Qed.
Lemma ok_low : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ DI a -> ok a.
Proof. geo'.
intros a Ha N1. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[_ Y]]]; hnum; try lia. exact (N1 Y).
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo'.
intros a Ha. rewrite (ts_inst _ TB) in Ha. apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma ok_depot_tab : okr (as_depot B) (4 * 2 ^ 20 + 32).
Proof. geo'.
intros a Ha. rewrite (ts_depot _ TB) in Ha. apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFIB_DEPOT, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma ok_store : okr (as_store B) 32.
Proof. geo'.
intros a Ha. rewrite (ts_store _ TB) in Ha. apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB);
unfold TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. hnum. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[X _]]]; hnum; lia.
Qed.
(* A byte of the owned static data (asyms_ok's aso_static; inside ly_img by amc_static_img) is untouched unless it is
   in DI: the image extent is apart from the thread object and the stack (static_extents' pairwise disjointness). The
   cf cell rows (errb_ial_apart_t, pf_ial_apart_t, field round 3) supply the ~ DI part. *)
Lemma ok_static : forall a, Exists (in_zr a) (as_owned_static B) -> ~ DI a -> ok a.
Proof. geo'.
intros a HE NDI. apply Exists_exists in HE as (r & Hr & Ha). unfold in_zr in Ha.
pose proof (proj1 (Forall_forall _ _) (amc_static_img B ly S Hp rd M) r (in_or_app _ _ _ (or_introl Hr))) as [S1 S2].
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms B ly S Hp rd M)) r Hr) as (A1 & A2 & A3).
split; [unfold kImgEnd in *; lia|]. intros HD.
apply D_cases in HD as [[X _]|[X|[_ Y]]].
- unfold kThreadObjSize in X. zd (SX 9 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 9 8 _ _ eq_refl eq_refl ltac:(lia)).
- exact (NDI Y).
Qed.
Lemma not_DI : forall a, ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 4) -> ~ DI a.
Proof. intros a [N1 N2] [X|X]; [exact (N1 X) | exact (N2 X)]. Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma batch_cells_within : forall l c, In c (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo'.
induction l as [|b2 t IH]; intros c Hc; [destruct Hc|]. cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hc as [Hc|Hc].
- apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. exists b2. split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH c Hc) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.
Lemma OLD : forall c, In c (acells_cf B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells B ly S Hp rd M) c Hc). Qed.
(* old_in's `do N right; left` follows acells_cf's component order (Reusable/YG0ncf.v:66-69); revisit if a component is added. *)
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLD; unfold acells_cf; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo'.
intros y d Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo'.
intros y d d' Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo'. reflexivity. Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells_cf, region_cells. rewrite reg'. cbn [removelast].
apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo'. intros a Ha. apply ok_T; unfold DT, t_cache, t_unwinding, kThreadObjSize in *; lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite cache', S'_cinit.
apply (cells_xfer _ _ _ okr_cache).
- pose proof (wfc_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
unfold cell_in, t_cache. destruct (st_cache_inited S).
+ destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
+ repeat fcons. apply Forall_nil.
- old_in. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia |]. unfold cache_cells. exact HIN.
Qed.
Lemma cells_chunk : forall x, In x (st_chunks S) -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (ok_chunk x a Hx Ha) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
pose proof (wfc_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer _ _ _ ok_Q); [|exact O4]. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; lia).
apply (cell_xfer _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (old_in; do 4 right; left; exact HIN).
pose proof ok_inst as OKI.
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, S'_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
assert (OKQ : okr (T + t_qc) 32) by (intros a Ha; apply ok_T; unfold DT, t_qc, t_unwinding, kThreadObjSize in *; lia).
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OT c Hc)).
destruct (batch_cells_within (qc_list (st_qthread S)) c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) b2 ltac:(unfold all_batches; apply in_app_iff; left; exact I2)) as [L1 L2].
apply (ok_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
- apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) b2 ltac:(unfold all_batches; apply in_app_iff; right; exact I2)) as [L1 L2].
apply (ok_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite S'_fs. apply (cells_xfer _ _ _ ok_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fcons. fcons.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly S)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot.
apply Forall_cons_iff in OLDD as [O1 OLDD]. apply Forall_cons_iff in OLDD as [O2 OLDD]. apply Forall_cons_iff in OLDD as [O3 OLDD]. apply Forall_cons_iff in OLDD as [O4 _].
pose proof ok_depot_tab as OKD. pose proof ok_store as OKS. unfold d_nuniq, d_map1, s_total, s_block0 in *.
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKD; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKD; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKS; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKS; cbn in Hj |- *; lia|]. apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. reflexivity.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells_cf B ly S').
Proof.
unfold acells_cf. rewrite S'_chunks. rewrite !Forall_app. splits.
- exact cells_regions.
- exact cells_caches.
- apply Forall_flat_map'. intros x Hx. exact (cells_chunk x Hx).
- exact cells_sec.
- exact cells_quar.
- exact cells_fs.
- exact cells_depot.
- exact (proj1 IAL).
- exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [exact (amc_fa B ly S Hp rd M c i v Hc Hi Hv kk Hkk)|].
pose proof (wfc_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
apply (ok_fa c Hc). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hpos. rewrite frames'. rewrite AGok; [exact (amc_flags B ly S Hp rd M cid pos Hc Hpos)|].
pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. apply ok_F. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (amc_depot B ly S Hp rd M) as Xdepot. change (depot_ok B ly rd' S') with (depot_ok B ly rd' S).
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
- intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros kk Hkk. rewrite AGok; [exact (H2 kk Hkk)|].
apply ok_depot_tab. unfold d_tab_words in Hb. lia.
- intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ pose proof (depot_len_bound _ _ (amc_universe B ly S Hp rd M) (wfc_depot _ _ _ _ _ WF)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
assert (OR : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)) by (intros kk Hkk; apply ok_NB; unfold kNodesBlockSize; lia).
split; intros kk Hkk; rewrite AGok; auto; [apply OR; lia|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OR. lia.
Qed.
Lemma shadow' : shadow_ok_cf B ly Hp rd' S'.
Proof.
intros g v Hg8 HS'. pose proof (amc_shadow B ly S Hp rd M g v Hg8) as SH.
assert (E : ashadow B ly S' g = ashadow B ly S g) by reflexivity. rewrite E in HS'. specialize (SH HS').
rewrite AGok; [exact SH|]. apply ok_hshadow. apply hs_bounds.
- pose proof (AR_dummy := I). unfold ashadow in HS'.
destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
+ apply find_chunk_at_In in F as [Hx Hgx]. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (X1 & X2 & _). unfold in_app in X1. lia.
+ destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). exact (proj1 (fa_poison_high lo len g Hin Hg)).
- unfold ashadow in HS'. pose proof HIGH as HI.
destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
+ apply find_chunk_at_In in F as [Hx Hgx]. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (X1 & X2 & _). apply Z.mod_divide in Hg8 as [c Hc]; [|lia].
pose proof (proj1 (proj2 (proj2 (chunk_facts_cf B ly S Hp rd x M Hx)))). ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia.
+ destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (amc_zshadow B ly S Hp rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [exact Z0|]. pose proof HIGH as HI.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
apply ok_hshadow. apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfib_zero_shadow in Hr.
apply ok_hshadow. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
cbn [In] in Hr; repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn [fst snd] in Hi |- *.
all: match goal with |- context [?x / 8] => let v := eval vm_compute in (x / 8) in change (x / 8) with v end.
all: match type of Hi with context [?x / 8] => let v := eval vm_compute in (x / 8) in change (x / 8) with v in Hi end.
all: lia.
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk_cf B ly S').
Proof. change (ajunk_cf B ly S') with (ajunk_cf B ly S). exact (vis_keep _ (amc_junk B ly S Hp rd M)). Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. change (aareas S') with (aareas S). exact (vis_keep _ (amc_areas B ly S Hp rd M)). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. change (aclient S') with (aclient S). exact (vis_keep _ (amc_client B ly S Hp rd M)). Qed.
Lemma placed' : sec_placed ly S'.
Proof. change (sec_placed ly S') with (sec_placed ly S). exact (amc_placed B ly S Hp rd M). Qed.
Lemma hp_live' : Forall (fun p => exists k, In k (st_chunks S') /\ ck_state k = CAllocated /\
p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k) Hp.
Proof. rewrite S'_chunks. exact (amc_hp_live B ly S Hp rd M). Qed.
Theorem free_finn_ARmcf : ARmcf B ly S' Hp rd'.
Proof.
constructor.
- exact WS'.
- exact (amc_universe B ly S Hp rd M).
- exact (amc_syms B ly S Hp rd M).
- exact LO.
- exact placed'.
- exact CONST'.
- exact (amc_const_owned B ly S Hp rd M).
- exact cells_all.
- exact fa'.
- exact flags'.
- exact depot'.
- exact shadow'.
- exact zshadow'.
- exact junk'.
- exact areas'.
- exact client'.
- exact (proj2 IAL).
- exact (amc_tsd B ly S Hp rd M).
- exact (amc_static_img B ly S Hp rd M).
- exact hp_live'.
- change (xs_placed_cf ly S') with (xs_placed_cf ly S). exact (amc_xs_placed B ly S Hp rd M).
- (* amc_exh_cell: the exhausted bytes are in the primary reserve (exh_byte_where_cf), untouched (ok_prim) *)
  pose proof (amc_cells_owned B ly S Hp rd M) as (HX & HO & HI).
  exact (exh_cell_move_cf B ly S S' Hp rd rd' ok M HX (fun c => eq_refl) (fun a _ H => AGok a H)
    (fun c Hc => ok_prim _ (proj2 (exh_byte_where_cf B ly S Hp rd c M HX Hc))) (amc_exh_cell B ly S Hp rd M)).
- (* amc_errb_cells: the errbuf object is owned static and apart from DI (errb_ial_apart_t), so untouched *)
  pose proof (amc_cells_owned B ly S Hp rd M) as (HX & HO & HI).
  exact (errb_cells_move_cf B ly S S' Hp rd rd' ok M HO eq_refl eq_refl eq_refl eq_refl (fun a _ H => AGok a H) VIS
    (fun a Ha => ok_static a (HO a Ha) (not_DI a (HI a Ha))) (amc_errb_cells B ly S Hp rd M)).
- exact (amc_cells_owned B ly S Hp rd M).
- (* amc_pf_cells: the two Printf cells, likewise (pf_cells_static_t's ownership, pf_ial_apart_t) *)
  destruct (amc_pf_owned B ly S Hp rd M) as [PS PI].
  exact (pf_cells_move_cf B ly S Hp rd rd' ok M (amc_pf_owned B ly S Hp rd M) (fun a _ H => AGok a H)
    (fun a Ha => ok_static a (proj1 (PS a Ha)) (not_DI a (PI a Ha))) (amc_pf_cells B ly S Hp rd M)).
- exact (amc_pf_owned B ly S Hp rd M).
Qed.
Lemma ALedger_cf_S' : forall segs md, ALedger_cf segs ly S md -> ALedger_cf segs ly S' md.
Proof. geo'. intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15]. constructor; try assumption. Qed.
Lemma abudget_cf_S' : abudget_cf S' = abudget_cf S.
Proof. geo'. apply abudget_cf_frame; reflexivity. Qed.
Lemma D_owned_cf : forall a, 0 <= a -> D a -> aowned B ly S a \/ DS a.
Proof. drop_mem. clear HII.
intros a Ha0 HD. pose proof HIGH as HI. destruct HD as [X|[X|X]].
- left. eapply (own_core_cf B ly S Hp rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DT, t_unwinding, kThreadObjSize in *. lia.
- right. exact X.
- left. apply (own_static_cf B ly S Hp rd a M). rewrite (ts_owned _ TB). unfold DI in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X.
(* the owned area is found BY VALUE over the whole table (ADIfaceImgA.covers_b), never by its row or a typed address *)
destruct X as [X|X]; refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a X); clear; vm_compute; reflexivity.
Qed.
End k.
End f.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* The ARcf assembly: AFg3.v's FINH, first bullet, over ARcf (ALedger_same_cf, ahs_transfer_cf; amwf_same and the
   *_wvb lemmas are shared). *)
Theorem free_finn_ARcf : forall B, TfibSyms B -> forall ly S Hp (W : world tfibsegs) mem md mem' mat STK sp,
  ARcf tfibsegs B ly S Hp W mem md -> st_internal_inited S = true -> img_cover ly ->
  0 <= STK -> ly_stk_lo ly + STK <= sp <= ly_stk_hi ly ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ D B ly STK sp a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
  aview tfibsegs (w_H W) mem' (ly_T ly + t_unwinding) = Some 0 ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (ialloc_cells B S) /\ Forall (range_zero B ly (aview tfibsegs (w_H W) mem')) (ialloc_zero B) ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly) ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARcf tfibsegs B ly (set_nev (st_nev S + 1) S) Hp W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros B TB ly S Hp W mem md mem' mat STK sp HAR HII IMG HSTK Hsp AG VIS NEW_unw IAL CONST' HSK.
destruct HAR as (M & LED & BUD & MW & HSH).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem') in *.
assert (IAL' : Forall (cell_holds B ly rd') (ialloc_cells B (S' S)) /\ Forall (range_zero B ly rd') (ialloc_zero B))
by (rewrite (S'_dtick S HII); exact IAL).
pose proof (free_finn_ARmcf B TB ly S rd rd' Hp M HII STK sp Hsp IMG AG VIS NEW_unw IAL' CONST') as MF.
rewrite <- (S'_dtick S HII).
split; [exact MF | split; [|split; [|split]]].
- eapply ALedger_same_cf; [exact (ALedger_cf_S' ly S tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- destruct BUD as [BUD PIN]. split; [| exact PIN].
rewrite (abudget_cf_S' S). exact BUD.
- eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
- eapply (ahs_transfer_cf tfibsegs B ly S Hp (S' S) (w_H W) mem mem' (al_img_env_cf tfibsegs ly S md (amc_layout _ _ _ _ _ M) LED) M HSH VIS HSK).
+ intros a _ C. exact C.
+ reflexivity.
+ intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg.
assert (OKg : ok B ly STK sp (shadow_addr g)).
{ apply (ok_hshadow B TB ly S rd Hp M STK sp Hsp IMG).
clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia. }
destruct OKg as [O1 O2]. exact (AG _ O1 O2).
Qed.
End g.
