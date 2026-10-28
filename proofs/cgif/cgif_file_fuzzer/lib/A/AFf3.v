(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m AF0x AFeq AFeu AFex AFez.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
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
split; [exact E|]. split; [|split; [exact N1 | exact N2]]. unfold X1. cbn [st_chunks set_chunks]. rewrite E. apply del_chunk_present. exact N1.
Qed.
Lemma KF : cfacts B ly X k. Proof. geo. exact (chunk_facts B ly X rd k M Hk). Qed.
Lemma DEL : Wf (as_universe B) X1 /\
1 <= c <= 30 /\ 0 <= x < rg_alloc_user (reg X1 c) /\ x mod class_size c = 0 /\ ~ In x (class_elems X1 c) /\
(forall c' y, In y (class_elems X1 c') -> In y (class_elems X c')) /\
4 * (Z.of_nat (length (class_elems X1 c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X1))) <= rg_mapped_fa (reg X1 c).
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (EX : X1 = set_chunks (l1 ++ l2) X) by (unfold X1; rewrite <- E1; reflexivity).
pose proof (WfP_del_prim (as_universe B) 0 0 0 X l1 k l2 off WF E Hb Hst Hni) as (W1 & G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
rewrite EX. unfold reg in *. cbn [st_regions set_chunks st_nev] in *. fold c x in G1, G2, G3, G4, G5, G6 |- *.
split; [exact W1|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5 | exact G6].
Qed.
Lemma WS1 : Wf (as_universe B) X1. Proof. exact (proj1 DEL). Qed.
Lemma X1_regions : st_regions X1 = st_regions X. Proof. reflexivity. Qed.
Lemma X1_cache : st_cache X1 = st_cache X. Proof. reflexivity. Qed.
Lemma X1_cinit : st_cache_inited X1 = true. Proof. exact Hci. Qed.
Lemma X1_secs : st_secs X1 = st_secs X. Proof. reflexivity. Qed.
Lemma X1_sec_arr : st_sec_arr X1 = st_sec_arr X. Proof. reflexivity. Qed.
Lemma X1_sec_res : st_sec_reserved X1 = st_sec_reserved X. Proof. reflexivity. Qed.
Lemma X1_fs : st_fs X1 = st_fs X. Proof. reflexivity. Qed.
Lemma X1_qglobal : st_qglobal X1 = st_qglobal X. Proof. reflexivity. Qed.
Lemma X1_qthread : st_qthread X1 = st_qthread X. Proof. reflexivity. Qed.
Lemma X1_depot : st_depot X1 = st_depot X. Proof. reflexivity. Qed.
Lemma X1_inited : st_internal_inited X1 = st_internal_inited X. Proof. reflexivity. Qed.
Lemma X1_nev : st_nev X1 = st_nev X. Proof. reflexivity. Qed.
Lemma reg' : forall c', reg X1 c' = reg X c'. Proof. reflexivity. Qed.
Lemma cache' : forall c', cache X1 c' = cache X c'. Proof. reflexivity. Qed.
Lemma frames' : frames X1 = frames X. Proof. reflexivity. Qed.
Lemma all_batches' : all_batches X1 = all_batches X. Proof. reflexivity. Qed.
Lemma fa_poison' : fa_poison_ranges ly X1 = fa_poison_ranges ly X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold fa_poison_ranges, reg. rewrite X1_regions, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma sec_extents' : sec_extents ly X1 = sec_extents ly X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_extents. rewrite E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly X1 A.
Proof. intros A H e He. rewrite sec_extents' in He. exact (H e He). Qed.
Lemma aareas' : aareas X1 = aareas X.
Proof. geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold aareas, reg. rewrite X1_regions, X1_sec_res, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma sec_live' : sec_live_bytes X1 = sec_live_bytes X.
Proof.
geo. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_live_bytes. rewrite E1, E. clear E E1.
induction l1 as [|y t IH]; cbn; [rewrite Hb; reflexivity | rewrite IH; reflexivity].
Qed.
Lemma prim_committed' : prim_committed X1 = prim_committed X. Proof. reflexivity. Qed.
Lemma abudget' : abudget X1 = abudget X. Proof. geo. unfold abudget, sec_hulls. rewrite X1_nev, sec_live', X1_secs  . reflexivity. Qed.
Lemma geom : 1 <= c <= 30 /\ base = SB + off /\ region_off c = c * 2 ^ 32 /\ base = region_base ly c + x /\ 0 <= x /\ x + class_size c <= rg_alloc_user (reg X c) /\
rg_alloc_user (reg X c) <= rg_mapped_user (reg X c) <= 2 ^ 31 /\ base mod 16 = 0 /\ 16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\
1 <= nn < 2 ^ 28 /\ ck_rz k + nn <= ck_extent k /\ ck_extent k = class_size c /\ 32 <= class_size c /\
kHighMemBeg <= base /\ base + ck_extent k <= ASAN_CEIL /\ sptr_addr B ly (ck_user k) = u /\ x mod class_size c = 0.
Proof. geo.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Hb in CK. cbv zeta in CK. destruct CK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3). pose proof (class_ok (prim_class off) ltac:(lia)) as (K1 & K2 & K3 & _).
assert (K0 : 32 <= class_size (prim_class off)) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
fold c x in C1, C4, C5, C6, C7, C8, C9, K0 |- *. unfold ck_n.
assert (EB : base = SB + off) by (unfold ck_base, sptr_addr; rewrite Hb; reflexivity).
assert (RO : region_off c = c * 2 ^ 32) by (unfold region_off; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (lo_space_in _ LO) as [S1 S2].
unfold region_base in *. unfold MALLOC_MAX in G7. repeat split; try assumption; try lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Lemma ZCH : forall ch, In ch (st_chunks X) -> zone3 (ck_base B ly ch) (ck_extent ch).
Proof. geo.
intros ch Hch. pose proof (chunk_facts B ly X rd ch M Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req ch) ltac:(clear - G7; lia)) as (_ & Q1 & _).
apply (zone3_intro ly (ck_base B ly ch) (ck_extent ch) IMG ltac:(clear - G5 G8 Q1; lia) G1).
apply zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
intros y Hy. exact (proj1 (chunk_apart B ly X rd ch y M Hch Hy)).
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
{ intros i x0 sz He Hsz. apply (zone3_intro ly x0 sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (destruct (Nat.lt_ge_cases i 8) as [X0|X0]; [exact X0|]; assert (X' : nth_error (owned_extents ly) i = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof (aso_cells _ (am_syms B ly X rd M)) as (I1 & I2 & _).
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZQ|]. split; [clear - ZQ; unfold zone3 in ZQ; lia|].
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|]. split; [exact ZF|]. split; [clear - ZF; unfold zone3 in ZF; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|]. split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|]. clear ZQ ZT ZF ZNB ZSB ZC.
repeat split; try assumption; try lia.
Qed.
Lemma D_cases : forall a, D a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (base <= a < base + ck_extent k /\ DK a) \/ (T <= a < T + kThreadObjSize /\ DJ a) \/
(kLowShadowBeg <= a < kHighMemBeg /\ DH a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof geom as GE.
destruct Ha as [Y|[Y|[Y|Y]]].
- left. unfold DS, KSTACK in *. lia.
- right; left. split; [|exact Y]. unfold DK, Mv, kChunkHeaderSize in Y. lia.
- do 2 right; left. split; [|exact Y]. unfold DJ, t_stats, kThreadObjSize in *. lia.
- do 3 right. split; [|exact Y]. unfold DH in Y.
destruct HI as (IP1 & IP2 & _). clear - Y GE IP1 IP2. ceil; unfold shadow_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split.
+ pose proof (Z.div_pos u 8 ltac:(lia) ltac:(lia)). lia.
+ assert (LE : u + (nn + 7) / 8 * 8 <= 140737479966720) by (pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)); lia).
assert (Y' : (u + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; [lia | exact LE]).
rewrite Z.div_add in Y' by lia. change (140737479966720 / 8) with 17592184995840 in Y'. lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize, kPrimResvSize,
kPtrArrayResv, kFakeStackSize, kNodesBlockSize, kStoreBlockSize, kLowMemEnd, KSTACK in *.
Ltac tbnum := rewrite ?(ts_inst B TB), ?(ts_depot B TB), ?(ts_store B TB), ?(ts_ial_lo B TB), ?(ts_ial_hi B TB), ?(ts_ial_w B TB), ?(ts_ial_flag B TB) in *;
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; lia.
Lemma SX : forall i j x0 y, nth_error (static_extents ly) i = Some x0 -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x0 y.
Proof. geo.
intros i j x0 y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x0 y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x0 (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma k_prim : ly_prim ly <= base /\ base + ck_extent k <= ly_prim ly + kPrimResvSize /\ region_base ly c <= base /\ base + ck_extent k <= region_base ly c + 2 ^ 31.
Proof. geo.
pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _ & _ & _ & _ & _ & G13 & _).
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _). lia.
Qed.
Lemma ok_low : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|]. intros HD. pose proof k_prim as KP.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]]; hnum; unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *; lia.
Qed.
Lemma ok_lowsh : forall a, kLowShadowBeg <= a < kHighShadowBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD. pose proof k_prim as (KP1 & KP2 & _).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[_ Y]]]]; [hnum; unfold kLowShadowBeg in *; lia | hnum; unfold kLowShadowBeg in *; lia | hnum; unfold kLowShadowBeg in *; lia |].
unfold DH, shadow_addr in Y. destruct HI as (IP1 & _). pose proof geom as GE. clear - Ha Y KP1 IP1 GE. hnum. unfold SHADOW_OFF in *.
pose proof (Z.div_le_mono 17594333495296 u 8 ltac:(lia) ltac:(lia)) as X0. change (17594333495296 / 8) with 2199291686912 in X0. lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DH a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD. pose proof k_prim as KP.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[_ Y]]]]; [hnum; unfold kLowShadowBeg in *; lia | hnum; unfold kLowShadowBeg in *; lia | hnum; unfold kLowShadowBeg in *; lia | exact (ND Y)].
Qed.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j [ex esz] a Hj J0 J2 J8 Ha. cbn [fst snd] in Ha. pose proof HIGH as (H1 & H2 & _). pose proof k_prim as KP.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ex, esz)) as HE.
assert (INO : In (ex, esz) (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (cbn; lia). eapply nth_error_In. exact Hj. }
specialize (HE INO). cbn beta in HE. cbn [fst snd] in HE.
pose proof (zone3_intro ly ex esz IMG ltac:(lia) HE (SX j 9 _ _ Hj eq_refl ltac:(lia))) as (_ & _ & ZZ).
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in ZZ.
unfold in_app in HE. split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SX j 8 _ _ Hj eq_refl ltac:(lia)).
- zd (SX 0 j _ _ eq_refl Hj ltac:(lia)).
- zd (SX j 2 _ _ Hj eq_refl ltac:(lia)).
- hnum. unfold kLowShadowBeg in *. lia.
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DJ a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). pose proof k_prim as KP. split; [hnum; lia|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[_ Y]|[Y _]]]].
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- exact (ND Y).
- hnum. unfold kLowShadowBeg in *. lia.
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (base <= a < base + ck_extent k) -> ok a.
Proof. geo.
intros a Ha NK. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [hnum; lia|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)).
- exact (NK Y).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- hnum. unfold kLowShadowBeg in *. lia.
Qed.
Lemma ok_other : forall y a, In y (st_chunks X) -> ck_beg y <> ck_beg k -> ck_base B ly y <= a < ck_base B ly y + ck_extent y -> ok a.
Proof. geo.
intros y a Hy Hne Ha. pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0.
pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg y) as [|o|r o|c0 p0] eqn:Eby; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
apply ok_prim; [lia | zd DJ0].
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (ZCH y Hy) as ZX. pose proof ZX as (_ & _ & ZZ). unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
pose proof HIGH as HI. split; [hnum; lia|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
+ zd (SECX _ 8 _ Gin eq_refl).
+ zd DJ0.
+ zd (SECX _ 2 _ Gin eq_refl).
+ hnum. unfold kLowShadowBeg in *. lia.
Qed.
Lemma ok_secpage : forall y r o a, In y (st_chunks X) -> ck_beg y = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros y r o a Hy Eby Ha. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Eby in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as HI.
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req y)) IMG ltac:(clear - Gext G5 G8 Q2; unfold kPage in *; lia) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kHighMemBeg in ZZ.
pose proof (prim_vs_secmap B ly X rd k off _ M Hk Hb Gin) as DJ0.
split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[Y _]]]].
- zd (SECX _ 8 _ Gin eq_refl).
- zd DJ0.
- zd (SECX _ 2 _ Gin eq_refl).
- hnum. unfold kLowShadowBeg in *. lia.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists xb, ly_space ly + b_self b2 = region_base ly kBatchClass + xb /\ 0 <= xb /\ xb mod kBatchBytes = 0 /\
xb + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In xb (batch_offs X kBatchClass).
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (xb := b_self b2 - region_off kBatchClass).
assert (INB : In xb (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) xb ltac:(rewrite !in_app_iff; tauto)) as [B1 B2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL'. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in B2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : xb + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in B2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists xb. splits; try assumption; try lia. unfold region_base. subst xb. lia.
Qed.
Lemma batch_vs_k : forall b2, In b2 (all_batches X) -> zdisjoint (ly_space ly + b_self b2, kBatchBytes) (base, ck_extent k).
Proof. geo.
intros b2 Hb2. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _ & _ & _ & _ & G13 & _).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (Z.eq_dec c kBatchClass) as [Ec|Hc0].
- pose proof (In_chunk_offs X k off Hk Hb) as IK. fold c x in IK. rewrite Ec in *.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
assert (x <> xb). { intros E. apply (NDx x); [exact IK | rewrite E; exact INB]. }
unfold kBatchBytes in *.
assert (Gxm' : x mod 8192 = 0) by (pose proof geom as GE; do 17 (apply proj2 in GE); rewrite Ec, CS in GE; exact GE).
apply Z.mod_divide in Gxm' as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). rewrite G4. nia.
- pose proof (region_in_prim ly c LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases c 24).
+ pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
+ pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 Ha. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & _ & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
apply ok_prim; [unfold kBatchBytes in *; lia | zd (batch_vs_k b2 Hb2)].
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof k_prim as KP. pose proof geom as (G1 & _). unfold ly_rinfo in Ha.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _). unfold region_base in *. rewrite region_off_eq in * by lia.
apply ok_prim; [unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *; lia|]. unfold kRegionInfoOff in *.
assert (c * 2 ^ 32 + 2 ^ 31 <= 2 ^ 37) by nia. lia.
Qed.
Lemma ok_fa : forall c', 1 <= c' <= 31 -> okr (fa_base ly c') kFreeArrayMax.
Proof. geo.
intros c' Hc' a Ha. pose proof HIGH as HI. pose proof k_prim as KP. pose proof geom as (G1 & _).
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). unfold fa_base in Ha. unfold region_base in *. rewrite !region_off_eq in * by lia.
apply ok_prim; [unfold kFreeArrayOffset, kFreeArrayMax in *; lia|]. unfold kFreeArrayOffset, kFreeArrayMax in *.
destruct (Z.lt_trichotomy c' c) as [L'|[->|L']]; [| lia |].
- pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo. intros a Ha. pose proof HIGH as HI. apply ok_low. tbnum. lia. Qed.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv. Proof. intros a Ha. exact (ok_static 1 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize. Proof. intros a Ha. exact (ok_static 3 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
Definition cell_in (lo len : Z) (ce : acell) : Prop :=
lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len.
Lemma cell_xfer : forall ce, cell_holds B ly rd ce ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) -> cell_holds B ly rd' ce.
Proof. intros ce Hce Hok. eapply (cell_holds_agree B ly rd rd' ce Hce). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall Lc lo len, okr lo len -> Forall (cell_in lo len) Lc -> Forall (cell_holds B ly rd) Lc -> Forall (cell_holds B ly rd') Lc.
Proof.
intros Lc lo len OK IN OLD'. apply Forall_forall. intros ce Hce. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD' ce Hce)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN ce Hce) as [I1 I2]. apply OK. lia.
Qed.
Lemma OLD : forall ce, In ce (acells B ly X) -> cell_holds B ly rd ce.
Proof. intros ce Hce. exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) ce Hce). Qed.
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. reflexivity. Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells X1) (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells. rewrite reg'.
apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo. intros a Ha. apply ok_T; unfold DJ, t_cache, t_stats, kThreadObjSize in *; lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells X1) (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold cache_cells. rewrite cache', X1_cinit.
apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4 & _).
rewrite Hci in WC. destruct WC as [PM PL]. unfold cell_in, t_cache. repeat fcons.
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- old_in. right; left. apply in_flat_map. exists c'. split; [apply In_zseq; lia |]. unfold cache_cells. rewrite Hci. exact HIN.
Qed.
Lemma cells_chunk_other : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells y).
Proof.
intros y Hy Hne. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly y) (ck_extent y)); [intros a Ha; exact (ok_other y a Hy Hne Ha) | |].
- pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz y) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists y. split; [exact Hy | exact HIN].
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks X1)).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite E1, flat_map_app, Forall_app. split.
- apply Forall_flat_map'. intros y Hy. apply cells_chunk_other; [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy].
- apply Forall_flat_map'. intros y Hy. apply cells_chunk_other; [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite X1_sec_res, X1_sec_arr, E1. rewrite E in OLDS. rewrite flat_map_app in OLDS |- *. cbn [flat_map] in OLDS. rewrite Hb in OLDS. cbn [app] in OLDS.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer _ _ _ ok_Q); [|exact O4]. apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros ce Hce. pose proof (proj1 (Forall_forall _ _) O5 ce Hce) as Oc. rewrite <- flat_map_app in Hce. apply in_flat_map in Hce as (y & Hy & Hce).
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
destruct (ck_beg y) as [|o|r o|c' p] eqn:Eby; try solve [destruct Hce].
assert (OKP : okr (ly_sec ly r) 32) by (intros a Ha; eapply (ok_secpage y r o a Hy' Eby); unfold kPage; lia).
apply (cell_xfer _ Oc). intros j Hj. apply OKP. destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma batch_cells_within : forall l ce, In ce (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof. geo.
induction l as [|b2 t IH]; intros ce Hce; [destruct Hce|]. cbn [batch_cells] in Hce.
destruct Hce as [<-|[<-|[<-|Hce]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hce as [Hce|Hce].
- apply in_map_iff in Hce as ([i y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. exists b2. split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH ce Hce) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.
Lemma okr_batch : forall b2, In b2 (all_batches X) -> okr (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof. geo.
intros b2 Hb2 a Ha. pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hb2) as [L1 L2]. unfold kBatchSlots in L2.
apply (ok_batch b2 a Hb2). unfold kBatchBytes. lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells X1).
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (old_in; do 4 right; left; exact HIN).
pose proof ok_inst as OKI.
assert (OKQ : okr (T + t_qc) 32) by (intros a Ha; apply ok_T; [unfold t_qc, kThreadObjSize in *; lia|]; unfold DJ, t_qc, t_stats in *; lia).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite X1_qglobal, X1_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OT ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. apply (okr_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | lia].
- apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OG ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. apply (okr_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | lia].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells X1).
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite X1_fs. apply (cells_xfer _ _ _ ok_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fcons. fcons.
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly X1).
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite X1_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD ce Hce)). intros j Hj. apply ok_low.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0, kLowMemEnd, kHighShadowBeg in *; tbnum; lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B X1).
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (old_in; do 7 right; left; exact HIN).
unfold ialloc_cells in OLDI |- *. rewrite X1_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI ce Hce)). intros j Hj. apply ok_low.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold kLowMemEnd, kHighShadowBeg in *; tbnum; lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (old_in; do 8 right; exact HIN).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. apply Forall_cons; [|apply Forall_nil].
apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. apply ok_T; [unfold t_unwinding, kThreadObjSize in *; lia|]. unfold DJ, t_stats, t_unwinding in *; lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly X1).
Proof.
unfold acells. rewrite !Forall_app. splits.
- exact cells_regions.
- exact cells_caches.
- exact cells_chunks.
- exact cells_sec.
- exact cells_quar.
- exact cells_fs.
- exact cells_depot.
- exact cells_ialloc.
- exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' X1.
Proof.
intros c' i v Hc' Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [exact (am_fa B ly X rd M c' i v Hc' Hi Hv kk Hkk)|].
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
apply (ok_fa c' Hc'). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' X1.
Proof.
intros cid pos Hc0 Hp. rewrite frames'. rewrite AGok; [exact (am_flags B ly X rd M cid pos Hc0 Hp)|].
pose proof (flag_off_bounds cid pos Hc0 Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. apply ok_F. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' X1.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as HI.
unfold depot_ok, depot_ids, depot_traces in *. rewrite X1_depot. exists heads, links. split; [|split; [|exact D3]].
- intros b0 Hb0. destruct (D1 b0 Hb0) as [Y1 Y2]. split; [exact Y1|]. intros kk Hkk. rewrite AGok; [exact (Y2 kk Hkk)|].
apply ok_low. unfold d_tab_words, kLowMemEnd, kHighShadowBeg in *. tbnum. lia.
- intros id Hid. destruct (D2 id Hid) as (Y1 & Y2 & Y3). split; [exact Y1|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. lia. }
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. apply (ok_static 4 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kNodesBlockSize. lia. }
split; intros kk Hkk; rewrite AGok; auto; [apply OKN; lia|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OKN. lia.
Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(lia) H1) as X0. change (4096 / 8) with 512 in X0.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(lia) ltac:(lia)) as Y. change ((140737488355328 - 8) / 8) with 17592186044415 in Y. lia.
Qed.
Lemma u_al8 : u mod 8 = 0 /\ base mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. geo.
pose proof geom as (_ & _ & _ & _ & _ & _ & _ & B16 & _ & R16 & _).
assert (B8 : base mod 8 = 0) by (pose proof B16 as B0; apply Z.mod_divide in B0 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (2 * q); lia).
assert (R8 : ck_rz k mod 8 = 0) by (pose proof R16 as R0; apply Z.mod_divide in R0 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (2 * q); lia).
split; [|split; [exact B8 | exact R8]]. apply Z.mod_divide in B8 as [q Hq]; [|lia]. apply Z.mod_divide in R8 as [q' Hq']; [|lia]. apply Z.mod_divide; [lia|]. exists (q + q'). lia.
Qed.
Lemma ext_rounded : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. geo.
pose proof KF as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(lia)).
apply Z.mod_divide in R2 as [q Hq]; [|lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
- pose proof (primary_geometry (ck_req k) ltac:(lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. lia.
- pose proof (secondary_geometry (ck_req k) ltac:(lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
pose proof (rz_size_bounds (ck_req k)). lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). lia.
Qed.
Lemma DH_iff : forall g, g mod 8 = 0 -> (DH (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof. geo.
intros g Hg. pose proof u_al8 as (U8 & _ & _). unfold DH, shadow_addr.
apply Z.mod_divide in Hg as [c0 Hc0]; [|lia]. apply Z.mod_divide in U8 as [a Ha]; [|lia]. rewrite Hc0, Ha.
rewrite !Z_div_mult by lia. pose proof (Z.div_pos (nn + 7) 8). pose proof geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NN & _). nia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WF ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
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
rewrite AGok; [exact Hrd|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. pose proof (Z.div_pos (nn + 7) 8). nia. }
destruct (find_chunk_at B ly l1 g) as [y|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hy Hgy].
apply (OTHER y); [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy | exact Hgy | exact (SH v Hg8 HS')].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
+
apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
assert (F2 : find_chunk_at B ly l2 g = None).
{ destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2; [|reflexivity]. exfalso. apply find_chunk_at_In in F2 as [Hy Hgy].
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
pose proof (chunks_disjoint B ly X rd y k M Hy' Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
pose proof (chunk_facts B ly X rd y M Hy') as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _). lia. }
rewrite F2 in HS'. destruct (in_rangesb g (fa_poison_ranges ly X)) eqn:R; [|discriminate]. injection HS' as <-.
apply Z.mod_divide in Hg8 as [c0 Hc0]; [|lia]. pose proof B8 as B8'. apply Z.mod_divide in B8' as [b0 Hb0]; [|lia]. pose proof R8 as R8'. apply Z.mod_divide in R8' as [r0 Hr0]; [|lia].
assert (J : (g - ck_base B ly k) / 8 = c0 - b0). { rewrite Hc0, Hb0. replace (c0 * 8 - b0 * 8) with ((c0 - b0) * 8) by lia. apply Z_div_mult. lia. }
assert (RU : ck_rz k / 8 = r0). { rewrite Hr0. apply Z_div_mult. lia. }
rewrite J in SH. unfold chunk_granule in SH. rewrite RU, Hst in SH.
set (q := (nn + 7) / 8) in *.
destruct (Z_lt_le_dec (c0 - b0) r0) as [C1|C1].
*
rewrite AGok; [apply SH; [rewrite Hc0; apply Z_mod_mult|]; replace (c0 - b0 <? r0) with true by (symmetry; apply Z.ltb_lt; exact C1); reflexivity|].
apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g ltac:(rewrite Hc0; apply Z_mod_mult)) in HD. nia.
* destruct (Z_lt_le_dec (c0 - b0) (r0 + q)) as [C2|C2].
--   apply NEW_sh; [apply (DH_iff g ltac:(rewrite Hc0; apply Z_mod_mult)); nia|].
rewrite (SH shHeapFreed); [discriminate | rewrite Hc0; apply Z_mod_mult |].
replace (c0 - b0 <? r0) with false by (symmetry; apply Z.ltb_ge; lia). replace (c0 - b0 <? r0 + q) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
--
rewrite AGok; [apply SH; [rewrite Hc0; apply Z_mod_mult|];
replace (c0 - b0 <? r0) with false by (symmetry; apply Z.ltb_ge; lia); replace (c0 - b0 <? r0 + q) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g ltac:(rewrite Hc0; apply Z_mod_mult)) in HD. nia.
+
assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
{ intros X0. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite TT in TK. discriminate. }
destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hy Hgy].
apply (OTHER y); [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy | exact Hgy | exact (SH v Hg8 HS')].
* destruct (in_rangesb g (fa_poison_ranges ly X)) eqn:R; [|discriminate].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
rewrite AGok; [exact (SH v Hg8 HS')|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (Z.div_pos (nn + 7) 8). nia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [exact Z0|]. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _). pose proof k_prim as (KP1 & KP2 & _).
pose proof geom as (_ & _ & _ & _ & _ & _ & _ & _ & RZ & _ & NN & EXT & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
-
pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as MD.
apply ok_hshadow; [apply hs_bounds; clear - hS1 hS2 Hi MD; unfold kHighMemBeg, kHighMemEnd in *; lia|].
intros HD. apply (DH_iff (ly_stk_lo ly + 8 * i) ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by lia; apply Z_mod_mult)) in HD.
pose proof (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. pose proof ext_rounded as (ER & _ & QP & _).
set (q := (nn + 7) / 8) in *. clear - HD DJ0 KP1 KP2 RZ NN ER Hi MD QP. unfold kPrimResvSize in *. nia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfib_zero_shadow in Hr.
apply ok_lowsh. unfold shadow_addr, SHADOW_OFF, kImgEnd, kLowShadowBeg, kHighShadowBeg.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hi |- *.
all: match goal with |- context [?x0 / 8] => let v := eval vm_compute in (x0 / 8) in change (x0 / 8) with v end.
all: match type of Hi with context [?x0 / 8] => let v := eval vm_compute in (x0 / 8) in change (x0 / 8) with v in Hi end.
all: clear - Hi; lia.
Qed.
Lemma vis_keep : forall Lr, Forall (range_vis B ly rd) Lr -> Forall (range_vis B ly rd') Lr.
Proof. intros Lr H. exact (Forall_range_vis_keep B ly rd rd' Lr VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_junk B ly X rd M) as J.
unfold ajunk in J |- *. unfold quar_junk, cache_junk, cache, sec_junk in J |- *. rewrite all_batches', X1_cinit, X1_cache, X1_sec_arr, X1_sec_res, E1. rewrite Hci, E in J.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (vis_keep _ J3)|]. apply Forall_app. split; [exact (vis_keep _ J4)|].
apply Forall_app. split.
{ rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [_ J5b].
apply Forall_app. split; [exact (vis_keep _ J5a) | exact (vis_keep _ J5b)]. }
apply Forall_app. split; [|exact (vis_keep _ J)].
apply Forall_cons_iff in J6 as [J6a J6]. apply Forall_cons_iff in J6 as [J6b J6]. apply Forall_cons_iff in J6 as [J6c J6].
apply Forall_cons; [intros i Hi; apply VIS; exact (J6a i Hi)|]. apply Forall_cons; [intros i Hi; apply VIS; exact (J6b i Hi)|]. apply Forall_cons; [intros i Hi; apply VIS; exact (J6c i Hi)|].
rewrite flat_map_app in J6 |- *. cbn [flat_map] in J6. rewrite Hb in J6. cbn [app] in J6. exact (vis_keep _ J6).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas X1).
Proof. rewrite aareas'. exact (vis_keep _ (am_areas B ly X rd M)). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_client B ly X rd M) as A.
unfold aclient in A |- *. rewrite frames', E1. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A. unfold chunk_user at 2 in A. rewrite Hst in A. cbn [app] in A.
exact (vis_keep _ A).
Qed.
Lemma placed' : sec_placed ly X1.
Proof. unfold sec_placed. rewrite sec_extents'. exact (am_placed B ly X rd M). Qed.
Theorem rc_fin_ARm : ARm B ly X1 rd'.
Proof.
constructor.
- exact WS1.
- exact (am_universe B ly X rd M).
- exact (am_syms B ly X rd M).
- exact LO.
- exact placed'.
- exact CONST'.
- exact (am_const_owned B ly X rd M).
- exact cells_all.
- exact fa'.
- exact flags'.
- exact depot'.
- exact shadow'.
- exact zshadow'.
- exact junk'.
- exact areas'.
- exact client'.
- pose proof (am_zero B ly X rd M) as ZR. apply Forall_forall. intros r Hr i Hi. rewrite AGok; [exact (proj1 (Forall_forall _ _) ZR r Hr i Hi)|].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. apply ok_low.
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; unfold kLowMemEnd, kHighShadowBeg in *; tbnum; lia.
- exact (am_tsd B ly X rd M).
- exact (am_static_img B ly X rd M).
Qed.
Lemma ALedger_X1 : forall segs md, ALedger segs ly X md -> ALedger segs ly X1 md.
Proof. geo.
intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14]. constructor; try assumption.
- rewrite sec_extents'. exact L7.
- rewrite sec_extents'. exact L8.
- rewrite prim_committed', sec_extents'. exact L9.
- rewrite sec_extents'. exact L12.
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
rewrite E in Hy. apply in_app_iff in Hy as [X0|[<-|X0]]; [apply N1 | rewrite Hst in Hsy; discriminate | apply N2]; rewrite <- Eq; apply in_map; exact X0. }
pose proof (chunks_disjoint B ly X rd y k M Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. lia. }
pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M | lia | exact NB].
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
pose proof geom as GE. pose proof k_prim as KP.
intros a Ha0 HD. destruct HD as [Y|[Y|[Y|Y]]].
- right. exact Y.
- left. apply own_ext_quar. unfold DK, Mv, kChunkHeaderSize in Y. lia.
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DJ, t_stats, kThreadObjSize in *. lia.
-
left. pose proof u_al8 as (U8 & _ & _). apply Z.mod_divide in U8 as [a0 Hua]; [|lia].
unfold DH, shadow_addr in Y. rewrite Hua, Z_div_mult in Y by lia.
replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
eapply own_shadow_prim; [exact M|]. pose proof ext_rounded as (ER & _ & QP & _). pose proof KP as (KP1 & KP2 & _).
pose proof GE as (_ & _ & _ & _ & _ & _ & _ & _ & RZ & _). clear - Y ER QP KP1 KP2 Hua RZ. nia.
Qed.
Lemma aowned_X1 : forall a, aowned B ly X1 a <-> aowned B ly X a.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (CB : forall a, aclient_byte B ly X1 a <-> aclient_byte B ly X a).
{ intros a. unfold aclient_byte. rewrite frames', E1, E. split; intros [(y & Hy & Hsy & Hr)|H2].
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
- right. exact H2.
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
- right. exact H2. }
intros a. unfold aowned. rewrite sec_extents'. rewrite (CB a). tauto.
Qed.
End f.
End b.
