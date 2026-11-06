(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0b YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0z YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF0k YF0q YF0r YF0w YF1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section n. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Variable k : chunk.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)).
Variables (lb : batch) (initr : list batch).
Hypothesis Hrev : rev (qc_list (st_qthread X)) = lb :: initr.
Hypothesis Hroom : Z.of_nat (length (b_items lb)) < kBatchSlots.
Let lb' : batch := mkBatch (b_self lb) (b_items lb ++ [k]).
Definition S' : astate := set_qthread (qc_push (st_qthread X) k None) X.
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Definition QLv : Z := ly_space ly + b_self lb.
Definition CNTv : Z := Z.of_nat (length (b_items lb)).
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + QSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := T + t_qc + 24 <= a < T + t_qc + 32.
Definition DL (a : Z) : Prop := (QLv + 8 <= a < QLv + 24) \/ (QLv + 24 + 8 * CNTv <= a < QLv + 32 + 8 * CNTv).
Definition DS (a : Z) : Prop := sp - QSTACK <= a < sp.
Definition D (a : Z) : Prop := DT a \/ DL a \/ DS a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes (st_qthread X) + nn) 8 i).
Hypothesis NEW_lsz : forall i, (i < 8)%nat -> rd' (QLv + 8 + Z.of_nat i) = Some (YG0h.le_byte (b_bytes lb + nn) 8 i).
Hypothesis NEW_lcnt : forall i, (i < 8)%nat -> rd' (QLv + 16 + Z.of_nat i) = Some (YG0h.le_byte (CNTv + 1) 8 i).
Hypothesis NEW_slot : forall i, (i < 8)%nat -> rd' (QLv + 24 + 8 * CNTv + Z.of_nat i) = Some (YG0h.le_byte (u - 16) 8 i).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_qb NEW_lsz NEW_lcnt NEW_slot CONST'.
Ltac geo := drop_mem.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma E0 : qc_list (st_qthread X) = rev initr ++ [lb].
Proof. geo. rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev. img_refl. Qed.
Lemma Hnb : need_new_batch (st_qthread X) = false.
Proof. geo. unfold need_new_batch. rewrite Hrev. img_apply Z.eqb_neq. img_lia. Qed.
Lemma S'_regions : st_regions S' = st_regions X.   Proof. geo. img_refl. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks X.      Proof. geo. img_refl. Qed.
Lemma S'_secs : st_secs S' = st_secs X.            Proof. geo. img_refl. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr X.   Proof. geo. img_refl. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved X. Proof. geo. img_refl. Qed.
Lemma S'_fs : st_fs S' = st_fs X.                  Proof. geo. img_refl. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal X.   Proof. geo. img_refl. Qed.
Lemma S'_depot : st_depot S' = st_depot X.         Proof. geo. img_refl. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited X. Proof. geo. img_refl. Qed.
Lemma S'_inited : st_internal_inited S' = st_internal_inited X. Proof. geo. img_refl. Qed.
Lemma S'_nev : st_nev S' = st_nev X.               Proof. geo. img_refl. Qed.
Lemma S'_qthread : st_qthread S' = qc_push (st_qthread X) k None. Proof. geo. img_refl. Qed.
Lemma reg' : forall c, reg S' c = reg X c.         Proof. geo. intros c. img_refl. Qed.
Lemma frames' : frames S' = frames X.              Proof. geo. img_refl. Qed.
Lemma cache' : forall c, cache S' c = cache X c.   Proof. geo. intros c. img_refl. Qed.
Lemma qlist' : qc_list (st_qthread S') = rev initr ++ [lb'].
Proof. geo. unfold S'. cbn [st_qthread set_qthread]. unfold qc_push. cbn [qc_list]. rewrite Hrev. img_refl. Qed.
Lemma qbytes' : qc_bytes (st_qthread S') = qc_bytes (st_qthread X) + nn. Proof. geo. img_refl. Qed.
Lemma all_batches_S' : all_batches S' = (rev initr ++ [lb']) ++ qc_list (st_qglobal X).
Proof. geo. unfold all_batches. rewrite qlist', S'_qglobal. img_refl. Qed.
Lemma all_batches_X : all_batches X = (rev initr ++ [lb]) ++ qc_list (st_qglobal X).
Proof. geo. unfold all_batches. rewrite E0. img_refl. Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly X. Proof. geo. img_refl. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. img_exact (H e He). Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly X. Proof. geo. img_refl. Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. geo. unfold Wf, S'. img_exact (WfP_qpush_room _ 0 0 0 X k WF Hk Hst Hnq Hnb). Qed.
Lemma last_in : In lb (all_batches X) /\ YF0w.QLv ly X = QLv.
Proof. geo.
split; [|img_try (unfold YF0w.QLv; rewrite Hrev; img_refl)].
unfold all_batches. img_apply in_app_iff. left. rewrite E0. img_apply in_app_iff. right. left. img_refl.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In x (batch_offs X kBatchClass).
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b2; auto)).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|img_lia]. apply Z.mod_divide in AA as [q' Hq']; [|img_lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try img_lia. unfold region_base. (subst x; cbv beta). img_lia.
Qed.
Lemma batches_nodup : List.NoDup (map b_self (all_batches X)).
Proof. geo.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches X) as [|x t IH]; cbn in *; [img_try (constructor)|].
inversion ND as [|y l N1 N2]; (subst; cbv beta). constructor; [|img_try (img_exact (IH N2))].
intros Hin. img_apply N1. apply in_map_iff in Hin as (x' & E & Hx'). img_apply in_map_iff. exists x'. split; [img_lia | img_try (img_exact Hx')].
Qed.
Lemma batches_apart : forall b1 b2, In b1 (all_batches X) -> In b2 (all_batches X) -> b_self b1 <> b_self b2 ->
zdisjoint (ly_space ly + b_self b1, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof. geo.
intros b1 b2 H1 H2 NE. destruct (batch_geom b1 H1) as (x1 & E1 & P1 & A1 & _). destruct (batch_geom b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros ->; img_apply NE; img_lia)). nia.
Qed.
Lemma batch_vs_chunk : forall b2 x, In b2 (all_batches X) -> In x (st_chunks X) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo.
intros b2 x Hb2 Hx. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs X x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in *.
assert (xk <> xb). { intros E. img_apply (NDx xk); [img_try (img_exact IK) | img_try (rewrite E; img_exact INB)]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros E; (subst; cbv beta); img_lia)). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. img_lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- img_exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- img_apply zdisjoint_sym. img_apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). img_lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. img_exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks X) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly X)).
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _). exists (prim_class o). splits; img_lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [img_refl | img_lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by img_lia. img_exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks X) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(img_lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. img_lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. img_lia.
Qed.
Lemma KX : forall j y, nth_error (static_extents ly) j = Some y -> (j <> 0)%nat -> zdisjoint (ck_base B ly k, ck_extent k) y.
Proof. geo. intros j y Hj Hne. img_exact (anyX k j y Hk Hj Hne). Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|img_lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|img_lia].
exfalso. img_apply (H (Z.max a c)); img_lia.
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_prim ly <= QLv /\ QLv + kBatchBytes <= ly_space ly + kSpaceSize /\ 0 <= CNTv /\ 32 + 8 * CNTv <= kBatchBytes.
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT. clear HA HD IT.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32) by (img_try (unfold region_base; rewrite region_off_eq by (unfold kBatchClass; img_lia); img_refl)).
destruct last_in as [Hin _]. destruct (batch_geom lb Hin) as (xb & Eb' & Pb' & Ab' & Ub' & [AU' MU'] & _). unfold QLv, CNTv.
split; [img_try (clear - IP; img_lia)|]. split; [img_try (clear - IP; img_lia)|]. split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|]. clear ZT.
splits; try assumption; unfold kBatchBytes, kSpaceSize, kBatchSlots in *; img_lia.
Qed.
Lemma D_cases : forall a, D a -> (T <= a < T + kThreadObjSize /\ DT a) \/ (QLv <= a < QLv + kBatchBytes /\ DL a) \/ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof. geo.
intros a Ha. pose proof HIGH as HI. destruct Ha as [Y|[Y|Y]].
- left. split; [|img_try (img_exact Y)]. unfold DT, t_qc, kThreadObjSize in *. img_lia.
- right; left. split; [|img_try (img_exact Y)]. unfold DL, kBatchBytes in *. img_lia.
- do 2 right. unfold DS, QSTACK in *. img_lia.
Qed.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. img_apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; img_lia.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (img_try (clear - HI; unfold zone3 in HI; tauto)); unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kHighMemBeg in Z.
Lemma ok_img : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). zget HI (ly_T ly) kThreadObjSize ZZ.
split; [img_try (hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]]; hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia.
Qed.
Lemma ok_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). zget HI (ly_T ly) kThreadObjSize ZZ.
split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]]; hnum; unfold kLowShadowBeg in *; img_lia.
Qed.
Ltac tsyms := rewrite ?(ts_inst _ TB), ?(ts_depot _ TB), ?(ts_store _ TB), ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_w _ TB), ?(ts_ial_flag _ TB), ?(ts_tp _ TB) in *;
unfold TFX_INST, TFX_DEPOT, TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_IMG_LO, TFX_IMG_END in *.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j e a Hj J0 J2 J8 Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e) as HE.
assert (INO : In e (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (img_try (cbn; img_lia)). eapply nth_error_In. img_exact Hj. }
specialize (HE INO). unfold in_app in HE. cbn [fst snd] in HE. split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
- zd (SX j 2 _ _ Hj eq_refl ltac:(img_lia)).
- pose proof (SX 0 j _ _ eq_refl Hj ltac:(img_lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. img_lia.
- zd (SX j 8 _ _ Hj eq_refl ltac:(img_lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [[Y Z0]|[[Y _]|Y]].
- img_exact (ND Z0).
- pose proof (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. img_lia.
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ DL a -> ok a.
Proof. geo.
intros a Ha NL. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y Z0]|Y]].
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- img_exact (NL Z0).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_chunk : forall x a, In x (st_chunks X) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo.
intros x a Hx Ha. destruct last_in as [Hin _].
destruct (ext_zone x Hx) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- img_apply ok_prim; [img_lia |]. intros Y. pose proof (batch_vs_chunk lb x Hin Hx) as D2. unfold DL, QLv in Y. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C0 & C1). zd D2.
- pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Xin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
split; [img_try (hnum; unfold alloc_ceiling, sp_window_lo, stack_max_size, kPage in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
+ zd (SECX _ 2 _ Xin eq_refl).
+ pose proof (SECX _ 0 _ Xin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. img_lia.
+ zd (SECX _ 8 _ Xin eq_refl).
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks X) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
split; [img_try (hnum; unfold kPage in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
- zd (SECX _ 2 _ Gin eq_refl).
- pose proof (SECX _ 0 _ Gin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. img_lia.
- zd (SECX _ 8 _ Gin eq_refl).
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes ->
(b_self b2 = b_self lb -> ~ DL a) -> ok a.
Proof. geo.
intros b2 a Hb2 Ha NL. destruct (batch_geom b2 Hb2) as (x2 & E2 & P2 & A2 & U2 & [AU MU] & _). destruct last_in as [Hin _].
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_try (unfold kBatchBytes in *; img_lia) |].
destruct (Z.eq_dec (b_self b2) (b_self lb)) as [E|NE]; [img_try (img_exact (NL E))|].
intros Y. pose proof (batches_apart b2 lb Hb2 Hin NE) as D2. unfold DL, QLv in Y. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C0 & C1). zd D2.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo.
intros a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold ly_rinfo, kRegionInfoOff in Ha.
img_apply ok_prim; [img_try (unfold kSpaceSize in *; img_lia) |]. unfold DL. unfold kSpaceSize, kBatchBytes in *. img_lia.
Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo.
intros c Hc a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & _). pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (Q1 & Q2 & _).
destruct last_in as [Hin _]. destruct (batch_geom lb Hin) as (xb & Eb' & Pb' & Ab' & Ub' & [AU MU] & _).
assert (FAR : forall x, 0 <= x -> x + kBatchBytes <= 2 ^ 31 -> ~ (fa_base ly c <= region_base ly kBatchClass + x + kBatchBytes - 1 /\ region_base ly kBatchClass + x < fa_base ly c + kFreeArrayMax)).
{ intros x Hx1 Hx2 [Z1 Z2]. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass in *; img_lia)).
unfold kBatchClass in *. destruct (Z.lt_trichotomy c 24) as [L|[->|L]];
first [ img_lia
| pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)); img_lia
| pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)); img_lia ]. }
img_apply ok_prim.
- clear FAR. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. img_lia.
- unfold DL, QLv. rewrite Eb'. intros Y. img_apply (FAR xb); unfold kBatchBytes in *; img_lia.
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
Lemma OLD : forall c, In c (acells B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. img_exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) c Hc). Qed.
Ltac old_in := img_apply Forall_forall; intros ? HIN; img_apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. img_refl. Qed.
Lemma hdr_addr : forall y, In y (st_chunks X) -> aeval B ly (sptr_exp (ck_hdr y)) = ck_base B ly y + ck_rz y - kChunkHeaderSize.
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_hdr, ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma Hu : u = ck_base B ly k + ck_rz k. Proof. geo. pose proof (chunk_facts B ly X rd k M Hk) as (_ & _ & _ & G4 & _). img_exact G4. Qed.
Ltac fcons := img_apply Forall_cons; [img_try (split; cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
img_apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. img_apply Forall_nil.
- old_in. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)].
Qed.
Lemma okr_cache : forall c, 1 <= c <= 31 -> okr (T + t_cache + 80 * c) 80.
Proof. geo. intros c Hc a Ha. img_apply ok_T; unfold DT, t_cache, t_qc, kThreadObjSize in *; img_lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
assert (OLDC : Forall (cell_holds B ly rd) (cache_cells X c)).
{ old_in. right; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)]. }
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(img_lia)) as (_ & _ & _ & K4 & _).
unfold cache_cells in OLDC |- *. rewrite S'_cinit, cache'. img_apply (cells_xfer _ _ _ (okr_cache c ltac:(img_lia))); [|img_try (img_exact OLDC)].
unfold cell_in, t_cache. destruct (st_cache_inited X); [|img_try (repeat fcons; img_apply Forall_nil)]. destruct WC as [PM PL].
repeat fcons. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. img_lia.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S')).
Proof.
rewrite S'_chunks. img_apply Forall_flat_map'. intros x Hx. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (img_try (old_in; do 3 right; left; img_exact HIN)).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
assert (OKI : okr (as_inst B) 3632) by (img_try (intros a Ha; img_apply ok_img; tsyms; img_lia)).
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_reserved; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_n; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_mutex; img_lia|].
img_apply Forall_app. split.
- refine (cells_xfer _ _ _ (fun a Ha => ok_static 1 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha) _ O4).
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (img_try (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; img_lia)).
img_apply (cell_xfer _ Oc). intros j Hj. img_apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; img_lia.
Qed.
Lemma batch_own_cells_within : forall b2 nx c, In c (batch_own_cells b2 nx) -> cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo.
intros b2 nx c Hc. unfold batch_own_cells in Hc. destruct Hc as [<-|[<-|[<-|Hc]]]; try (unfold cell_in; cbn; img_lia).
apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold cell_in; cbn; img_lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
assert (OKI : okr (as_inst B) 3632) by (img_try (intros a Ha; img_apply ok_img; tsyms; img_lia)).
destruct last_in as [Hlbin _].
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, qlist', qbytes'. rewrite E0 in OLDQ.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_cmutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_rmutex; img_lia|].
assert (OKQ : forall a, T + t_qc <= a < T + t_qc + 24 -> ok a) by (img_try (intros a Ha; img_apply ok_T; unfold DT, t_qc, kThreadObjSize in *; img_lia)).
img_apply Forall_app. split.
-
img_apply Forall_cons. { rewrite length_app in O3 |- *. cbn [length] in O3 |- *. img_apply (cell_xfer _ O3). intros j Hj. img_apply OKQ. cbn in Hj |- *. img_lia. }
img_apply Forall_cons. { replace (match rev initr ++ [lb'] with [] => ANum 0 | b :: _ => batch_exp b end) with (match rev initr ++ [lb] with [] => ANum 0 | b :: _ => batch_exp b end)
by (img_try (destruct (rev initr); img_refl)).
img_apply (cell_xfer _ O4). intros j Hj. img_apply OKQ. cbn in Hj |- *. img_lia. }
img_apply Forall_cons. { rewrite !rev_app_distr. cbn [rev app]. replace (batch_exp lb') with (batch_exp lb) by img_refl. rewrite rev_app_distr in O5. cbn [rev app] in O5.
img_apply (cell_xfer _ O5). intros j Hj. img_apply OKQ. cbn in Hj |- *. img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk.
replace (T + (t_qc + 24)) with (T + t_qc + 24) by img_lia. rewrite NEW_qb by img_exact Hkk. img_refl. }
img_apply Forall_forall. intros c Hc. apply In_batch_cells in Hc as (i & b2 & Hi & Hc).
destruct (Nat.lt_ge_cases i (length (rev initr))) as [LT|GE].
+
rewrite nth_error_app1 in Hi by img_exact LT. pose proof (nth_error_In _ _ Hi) as Hin.
assert (Hin2 : In b2 (all_batches X)) by (img_try (rewrite all_batches_X; img_apply in_app_iff; left; img_apply in_app_iff; left; img_exact Hin)).
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
assert (NX : next_exp (rev initr ++ [lb']) i = next_exp (rev initr ++ [lb]) i).
{ unfold next_exp. destruct (Nat.lt_ge_cases (S i) (length (rev initr))) as [L|L].
- rewrite !nth_error_app1 by img_exact L. img_refl.
- rewrite !nth_error_app2 by img_exact L. replace (S i - length (rev initr))%nat with 0%nat by img_lia. img_refl. }
rewrite NX in Hc.
assert (OLDc : cell_holds B ly rd c).
{ img_apply (proj1 (Forall_forall _ _) OT). img_apply In_batch_cells. exists i, b2. split; [img_try (rewrite nth_error_app1 by img_exact LT; img_exact Hi) | img_try (img_exact Hc)]. }
img_apply (cell_xfer _ OLDc). pose proof (batch_own_cells_within b2 _ c Hc) as [R1 R2].
intros j Hj. img_apply (ok_batch b2); [img_try (img_exact Hin2) | img_try (unfold kBatchBytes; img_lia) |].
intros E. exfalso.
pose proof batches_nodup as ND. rewrite all_batches_X, !map_app in ND. cbn [map] in ND.
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). img_apply (N3 (b_self b2)); [img_try (img_apply in_map; img_exact Hin) | img_try (left; symmetry; img_exact E)].
+
rewrite nth_error_app2 in Hi by img_exact GE. destruct (i - length (rev initr))%nat as [|m] eqn:Em; [|img_try (cbn in Hi; destruct m; discriminate)].
cbn in Hi. injection Hi as <-. assert (EI : i = length (rev initr)) by img_lia. (subst i; cbv beta). rewrite next_exp_app_new in Hc.
assert (OLDL : forall c0, In c0 (batch_own_cells lb (ANum 0)) -> cell_holds B ly rd c0).
{ intros c0 Hc0. img_apply (proj1 (Forall_forall _ _) OT). img_apply In_batch_cells. exists (length (rev initr)), lb.
split; [img_try (rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl) | img_try (rewrite next_exp_app_new; img_exact Hc0)]. }
unfold batch_own_cells in Hc. cbn [b_items b_self lb'] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]].
*   img_apply (cell_xfer _ (OLDL _ ltac:(img_try (unfold batch_own_cells; left; img_refl)))). intros j Hj. cbn in Hj |- *.
img_apply (ok_batch lb); [img_try (img_exact Hlbin) | img_try (unfold kBatchBytes; img_lia) | img_try (intros _; unfold DL, QLv; img_lia)].
*   cbn [cell_holds c_at c_val c_w c8 z8 aeval aoff batch_exp b_self lb']. intros kk Hkk.
replace (ly_space ly + (b_self lb + 8) + Z.of_nat kk) with (QLv + 8 + Z.of_nat kk) by (img_try (unfold QLv; img_lia)). rewrite NEW_lsz by img_exact Hkk. rewrite <- (b_bytes_app1 lb k). img_refl.
*   cbn [cell_holds c_at c_val c_w c8 z8 aeval aoff batch_exp b_self lb']. intros kk Hkk.
replace (ly_space ly + (b_self lb + 16) + Z.of_nat kk) with (QLv + 16 + Z.of_nat kk) by (img_try (unfold QLv; img_lia)). rewrite NEW_lcnt by img_exact Hkk.
rewrite length_app. cbn [length]. unfold CNTv. do 2 f_equal. img_lia.
*
apply in_map_iff in Hc as ([i x] & <- & Hix). rewrite length_app in Hix. cbn [length] in Hix. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl) in Hix.
apply in_app_iff in Hix as [Hix|[Hix|[]]].
--   pose proof Hix as Hix'. apply in_combine_l in Hix'. apply in_seq in Hix'.
apply (cell_xfer _ (OLDL _ ltac:(img_try (unfold batch_own_cells; right; right; right; img_apply in_map_iff; exists (i, x); split; [img_refl | img_try (img_exact Hix)])))).
intros j Hj. cbn [fst snd c_at c_w c8 aeval aoff batch_exp] in Hj |- *.
img_apply (ok_batch lb); [img_try (img_exact Hlbin) | img_try (pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) lb Hlbin) as [L1 L2]; unfold kBatchSlots in L2; unfold kBatchBytes; img_lia) |].
intros _. unfold DL, QLv, CNTv. img_lia.
--   injection Hix as <- <-. cbn [fst snd cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self lb']. intros kk Hkk.
replace (ly_space ly + (b_self lb + (24 + 8 * Z.of_nat (length (b_items lb)))) + Z.of_nat kk) with (QLv + 24 + 8 * CNTv + Z.of_nat kk) by (img_try (unfold QLv, CNTv; img_lia)).
rewrite NEW_slot by img_exact Hkk. rewrite (hdr_addr k Hk), Hu. unfold kChunkHeaderSize. do 2 f_equal; img_lia.
-
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
img_apply Forall_cons; [img_apply (cell_xfer _ G1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G4); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
apply In_batch_cells in Hc as (i & b2 & Hi & Hc). pose proof (nth_error_In _ _ Hi) as Hin.
assert (Hin2 : In b2 (all_batches X)) by (img_try (unfold all_batches; img_apply in_app_iff; right; img_exact Hin)).
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
pose proof (batch_own_cells_within b2 _ c Hc) as [R1 R2].
intros j Hj. img_apply (ok_batch b2); [img_try (img_exact Hin2) | img_try (unfold kBatchBytes; img_lia) |].
intros E. exfalso.
pose proof batches_nodup as ND. rewrite all_batches_X, !map_app in ND. cbn [map] in ND.
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). cbn in N2. inversion N2 as [|y l' N4 N5]; (subst; cbv beta).
img_apply N4. rewrite <- E. img_apply in_map. img_exact Hin.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (img_try (old_in; do 5 right; left; img_exact HIN)).
unfold fs_cells in OLDF |- *. rewrite S'_fs. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
refine (cells_xfer _ _ _ (fun a Ha => ok_static 3 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha) _ OLDF).
unfold cell_in. cbn [fst snd]. unfold kFakeStackSize. fcons. fcons.
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (img_try (old_in; do 6 right; left; img_exact HIN)).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD c Hc)). intros j Hj. img_apply ok_img.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0 in *; tsyms; img_lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S').
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (img_try (old_in; do 7 right; left; img_exact HIN)).
unfold ialloc_cells in OLDI |- *. rewrite S'_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI c Hc)). intros j Hj. img_apply ok_img.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; tsyms; img_lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (img_try (old_in; do 8 right; img_exact HIN)).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. img_apply ok_T; unfold DT, t_qc, t_unwinding, kThreadObjSize in *; img_lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
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
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [img_try (img_exact (am_fa B ly X rd M c i v Hc Hi Hv kk Hkk))|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply (ok_fa c Hc). img_lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [img_try (img_exact (am_flags B ly X rd M cid pos Hc Hp))|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
img_apply (ok_static 3 _ _ eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)). cbn [fst snd]. unfold kFakeStackSize. img_lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
unfold depot_ok, depot_ids, depot_traces in *. rewrite S'_depot. exists heads, links. split; [|img_try (split; [|img_exact D3])].
- intros b0 Hb. destruct (D1 b0 Hb) as [X1 X2]. split; [img_try (img_exact X1)|]. intros kk Hkk. rewrite AGok; [img_try (img_exact (X2 kk Hkk))|].
img_apply ok_img. unfold d_tab_words in *. tsyms. img_lia.
- intros id Hid. destruct (D2 id Hid) as (X1 & X2 & X3). split; [img_try (img_exact X1)|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. img_lia. }
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_NB ly, kNodesBlockSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as [N1 N2]. cbn [fst snd] in N1, N2.
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. img_apply (ok_static 4 _ _ eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)). cbn [fst snd]. unfold kNodesBlockSize. img_lia. }
split; intros kk Hkk; rewrite AGok; auto; [img_try (img_apply OKN; img_lia)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by img_lia. img_apply OKN. img_lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c WF ltac:(img_lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; img_lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. img_lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
intros g v Hg8 HS'. unfold ashadow in HS'. rewrite S'_chunks, fa_poison' in HS'. fold (ashadow B ly X g) in HS'.
rewrite AGok; [img_try (img_exact (am_shadow B ly X rd M g v Hg8 HS'))|].
pose proof (YG0z.ashadow_low B ly X rd g v M HS') as [LO1 LO2]. img_apply ok_shb. split; [|img_try (img_exact LO2)].
clear - LO1. unfold SHADOW_OFF, kLowShadowBeg in *. img_lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. img_apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [img_try (img_exact Z0)|]. img_apply ok_shb.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges B ly X rd M) r ltac:(img_try (rewrite !in_app_iff; tauto))) as (K1 & K2 & K3).
assert (DM : i < (snd r + 7) / 8). { pose proof (Z.div_le_mono (8 * i + 8) (snd r + 7) 8 ltac:(img_lia) ltac:(img_lia)) as DX. replace (8 * i + 8) with ((i + 1) * 8) in DX by img_lia. rewrite Z_div_mult in DX by img_lia. img_lia. }
split; [img_try (unfold shadow_addr, SHADOW_OFF, kLowShadowBeg; pose proof (Z.div_pos (fst r) 8); img_lia)|].
apply (proj2 (owned_shadow_bound B ly X rd (shadow_addr (fst r) + i) M ltac:(img_try (img_apply Exists_exists; exists r; split; [img_try (rewrite !in_app_iff; tauto) | img_try (unfold in_zr; cbn [fst snd]; img_lia)])))).
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. img_exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. img_apply VIS. replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by img_lia.
img_apply V. img_lia.
Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof (am_junk B ly X rd M) as J.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S'. rewrite all_batches_X in J.
unfold sec_junk in J |- *. rewrite S'_sec_arr, S'_sec_res, S'_chunks.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J1 i Hi))|].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J2 i Hi))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J3))|].
img_apply Forall_app. split.
{   img_apply (vis_keep _). img_apply Forall_forall. intros r Hr. img_apply (proj1 (Forall_forall _ _) J4).
apply in_flat_map in Hr as (c & Hc & Hr). img_apply in_flat_map. exists c. split; [img_try (img_exact Hc)|]. unfold cache_junk in Hr |- *. rewrite S'_cinit, cache' in Hr. img_exact Hr. }
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J5))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J6))|].
img_apply Forall_app. split.
{
rewrite !flat_map_app in J7 |- *. cbn [flat_map] in J7 |- *. rewrite !app_nil_r in J7 |- *.
apply Forall_app in J7 as [J7a J7b]. apply Forall_app in J7a as [J7a J7l].
img_apply Forall_app. split; [img_try (img_apply Forall_app; split; [img_exact (vis_keep _ J7a)|]) | img_try (img_exact (vis_keep _ J7b))].
unfold batch_junk in J7l |- *. apply Forall_cons_iff in J7l as [J7l _]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
cbn [b_items b_self lb' batch_exp] in J7l |- *. rewrite length_app. cbn [length].
pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C0 & C1). unfold CNTv in C0, C1.
img_apply (vis_sub _ _ J7l); cbn [fst snd aeval aoff batch_exp b_self lb']; unfold kBatchBytes in *; img_lia.
}
img_exact (vis_keep _ J).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. pose proof (am_areas B ly X rd M) as A. unfold aareas, reg in A |- *. rewrite S'_regions, S'_sec_res, S'_chunks. img_exact (vis_keep _ A). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. pose proof (am_client B ly X rd M) as A. unfold aclient in A |- *. rewrite frames', S'_chunks. img_exact (vis_keep _ A). Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. img_exact (am_placed B ly X rd M). Qed.
Theorem enq_finp_ARm : ARm B ly S' rd'.
Proof.
constructor.
- img_exact WS'.
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
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. img_apply ok_img.
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; tsyms; img_lia.
- img_exact (am_tsd B ly X rd M).
- img_exact (am_static_img B ly X rd M).
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes X. Proof. geo. img_refl. Qed.
Lemma prim_committed' : prim_committed S' = prim_committed X. Proof. geo. img_refl. Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly X md -> ALedger segs ly S' md.
Proof. geo. intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10]. constructor; assumption. Qed.
Lemma abudget_S' : abudget S' = abudget X. Proof. geo. img_refl. Qed.

Lemma qloose_S' : qc_bytes (st_qthread X) + nn <= 2 ^ 29 -> qloose X -> qloose S'.
Proof. geo.
intros Hb (T1 & T2 & T3). unfold qloose. rewrite qbytes', S'_qglobal. split; [img_try (img_exact Hb)|]. split; [img_try (img_exact T2)|].
unfold quar_n in *. rewrite S'_chunks. rewrite queued_n_eq in *. rewrite qlist', S'_qglobal. rewrite E0 in T3.
rewrite !items_n_flat_app in T3 |- *. cbn [flat_map b_items lb'] in T3 |- *. rewrite !app_nil_r in T3 |- *. rewrite items_n_app, items_n_cons, items_n_nil.
assert (NN : 0 <= nn); [|img_lia]. clear - M Hk. pose proof (chunk_facts B ly X rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _).
unfold ck_n. pose proof (req_size_bounds (ck_req k) ltac:(img_lia)). img_lia.
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
intros a Ha0 HD. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C0 & C1). destruct HD as [Y|[Y|Y]].
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd]. unfold DT, t_qc, kThreadObjSize in *. img_lia.
- left. destruct last_in as [Hin _]. eapply own_batch; [img_try (img_exact M) | img_try (img_exact Hin) | img_try (unfold DL, QLv, kBatchBytes in *; img_lia)].
- right. img_exact Y.
Qed.

End n.
End f.
