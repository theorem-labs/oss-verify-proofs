(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t YF3v YF4q YF3i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold zone3, in_app, kLowShadowBeg, TFX_IMG_LO, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFX_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Lemma refill_tree_init : forall c S, st_cache_inited S = false ->
refill_tree c S = refill_tree c (set_cache_inited true (set_cache (init_caches (st_cache S)) S)).
Proof.
intros c S HU. unfold refill_tree, init_cache_if_needed, bind, get, put, ret. cbn [ibind st_cache_inited set_cache_inited set_cache]. rewrite HU.
cbn [ibind]. img_refl.
Qed.
Section j. Context {imgk : img}.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfxsegs) (memU memR : word -> option byte) (md : Model).
Hypothesis TS : TfxSyms B.
Hypothesis HAR : AR tfxsegs B ly S W memU md.
Hypothesis HU : st_cache_inited S = false.
Let T : Z := ly_T ly.
Let rd0 : reader := aview tfxsegs (w_H W) memU.
Let rd' : reader := aview tfxsegs (w_H W) memR.
Hypothesis MEQ : forall x : word, ~ TABW T (bv_unsigned x) -> memR x = memU x.
Hypothesis TBF : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) memR) T i.
Hypothesis TPR : forall a, TABW T a -> apresent (w_H W) memR a.
Definition S1 : astate := set_cache_inited true (set_cache (init_caches (st_cache S)) S).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Lemma caches_empty : forall c, 1 <= c <= 31 -> cache S c = pclass0.
Proof. intros c Hc. pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c Hc)) as X. rewrite HU in X. img_exact X. Qed.
Lemma cache_S1 : forall c, 1 <= c <= 31 -> cache S1 c = mkPC (max_cached c) [].
Proof. intros c Hc. unfold S1. rewrite cache_after_init by img_lia. rewrite caches_empty by img_lia. img_refl. Qed.
Lemma WF1 : Wf (as_universe B) S1.
Proof. img_exact (WfP_init_caches _ 0 0 0 S WF HU). Qed.
Hypothesis IMG : img_cover ly.
Lemma T_facts : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\ zone3 T kThreadObjSize.
Proof.
pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. cbn [fst snd] in IT.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(img_try (unfold kThreadObjSize; img_lia)) IT (pairwise_ij _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
pose proof ZT as (Z1 & Z2 & _). unfold T in *. refine (conj _ (conj _ (conj _ ZT))); img_lia.
Qed.
Lemma Z_low : forall a, (0x10000 <= a < (0x5ff000 + D_1000) \/ 0x7fff7000 <= a < 0x10007fff8000) -> ~ TABW T a.
Proof.
intros a Ha Hx. apply TABW_range in Hx. pose proof T_facts as (_ & _ & _ & ZT).
pose proof (zone3_apart_img _ _ a ZT) as TI. pose proof (zone3_apart_hsh _ _ a ZT) as TH. clear - Ha Hx TI TH. numconst. img_lia.
Qed.
Lemma Z_high : forall a, ~ (T <= a < T + kThreadObjSize) -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. clear - Ha Hx. numconst. img_lia. Qed.
Lemma Z_Tlo : forall a, a < T + 292 -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. img_lia. Qed.
Lemma Z_Thi : forall a, T + 2704 <= a -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. img_lia. Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ TABW T a.
Proof. intros a Ha. img_apply Z_high. pose proof T_facts as (_ & _ & PT). clear - Ha PT. img_lia. Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i <> 2)%nat -> fst e <= a < fst e + snd e -> ~ TABW T a.
Proof.
intros i e a He Hi Ha. img_apply Z_high. pose proof (lo_disj ly LY) as HD. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (img_try (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto)).
assert (D : zdisjoint e (ly_T ly, kThreadObjSize)).
{ destruct (Nat.lt_ge_cases i 2) as [L|L].
- assert (E2 : nth_error (owned_extents ly) (i + Datatypes.S (2 - i - 1)) = Some (ly_T ly, kThreadObjSize)) by (img_try (replace (i + Datatypes.S (2 - i - 1))%nat with 2%nat by img_lia; img_refl)).
img_exact (pairwise_ij _ _ i (2 - i - 1) _ _ HD' He E2).
- assert (Ei : nth_error (owned_extents ly) (2 + Datatypes.S (i - 2 - 1)) = Some e) by (img_try (replace (2 + Datatypes.S (i - 2 - 1))%nat with i by img_lia; img_exact He)).
img_exact (zdisjoint_sym _ _ (pairwise_ij _ _ 2 (i - 2 - 1) _ _ HD' eq_refl Ei)). }
unfold zdisjoint in D. cbn [fst snd] in D. unfold T. clear - D Ha. img_lia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ TABW T a.
Proof.
intros e a He Ha. img_apply Z_high. pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ e (ly_T ly, kThreadObjSize) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(img_try (unfold static_extents, owned_extents; img_apply in_app_iff; left; cbn; tauto))) as D.
unfold zdisjoint in D. cbn [fst snd] in D. unfold T. clear - D Ha. img_lia.
Qed.
Lemma Z_user : forall c' x a, 1 <= c' <= 31 -> 0 <= x -> x <= 2 ^ 32 -> region_base ly c' <= a < region_base ly c' + x -> ~ TABW T a.
Proof.
intros c' x a Hc' Hx0 Hx Ha. pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). img_apply Z_prim. clear - Hx0 Hx Ha R1 R2. img_lia.
Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ TABW T a -> rd' a = rd0 a.
Proof. intros a Ra Hx. unfold rd', rd0. img_apply aview_same. img_apply MEQ. rewrite unsigned_lit_small by img_exact Ra. img_exact Hx. Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ TABW T a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W memU md a HAR Ho) as Ra.
ceil.   img_apply AGREE0; [img_try (clear - Ra CR0; img_lia) | img_try (img_exact Hx)].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; img_exact H. Qed.
Lemma PRES_MONO : forall a, apresent (w_H W) memU a -> apresent (w_H W) memR a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) memU u -> apresent (w_H W) memR u).
{ intros u Ru Hp. destruct (TABW_dec T u) as [Ht|Ht]; [img_try (img_exact (TPR u Ht))|].
eapply apresent_same; [|img_try (img_exact Hp)]. img_apply MEQ. rewrite unsigned_lit_small by img_exact Ru. img_exact Ht. }
intros a Hp. img_apply (proj2 (apresent_word _ _ a)). img_apply G; [img_try (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; img_change (bv_modulus 64) with (2 ^ 64) in R; img_exact R)|].
img_apply (proj1 (apresent_word _ _ a)). img_exact Hp.
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfxsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) memR (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) memU a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [img_try (exfalso; img_apply HV; img_refl)|].
split; [img_refl|]. destruct (memU (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl) | img_try (exfalso; img_apply HV; img_refl)]. }
destruct (PRES_MONO a Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma val_mem_R : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n -> ~ TABW T (a + k)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) memU) a n v -> val_mem tfxsegs (mrestrict (w_H W) memR) a n v.
Proof.
intros a n v Hx Ha Hn HV. eapply val_mem_frame; [|img_try (img_exact HV)]. intros k Hk. img_apply MEQ. rewrite unsigned_lit_small by img_lia. img_apply Hx. img_lia.
Qed.
Lemma val_mem_cell : forall mem e (w : nat) e',
val_mem tfxsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfxsegs (w_H W) mem) (ACell e w (AV e')).
Proof.
intros mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [img_refl|]. unfold YG0h.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ TABW T a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. img_apply Forall_forall. intros cc Hc.
pose proof (proj1 (Forall_forall _ _) RNG cc Hc) as [R1 R2]. cbv beta in R1, R2.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc)))|].
intros k Hk. img_apply AGX.
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- img_apply LOC. img_lia.
Qed.
Lemma keep_cell : forall cc lo len, loc_ok lo len -> In cc (acells B ly S) ->
lo <= aeval B ly (c_at cc) -> aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len -> cell_holds B ly rd' cc.
Proof.
intros cc lo len LOC Hc R1 R2. img_exact (proj1 (Forall_forall _ _) (keep_cells [cc] lo len LOC ltac:(img_try (intros x [<-|[]]; img_exact Hc)) ltac:(img_try (constructor; [img_try (split; assumption) | img_try (constructor)]))) cc (or_introl eq_refl)).
Qed.
Ltac fcons' := img_apply Forall_cons; [img_try (cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S1) (zseq 1 31)).
Proof.
img_change (flat_map (region_cells S1) (zseq 1 31)) with (flat_map (region_cells S) (zseq 1 31)).
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
img_apply (keep_cells _ (ly_space ly + kRegionInfoOff + 128 * c') 128).
+ intros a Ha. img_apply Z_prim. clear - Ha Hc' SP. numconst. img_lia.
+ intros x Hx. unfold acells. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact Hx)].
+ unfold region_cells, kRegionInfoOff. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S1) (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. assert (Hc : 1 <= c' <= 31) by img_lia. clear Hc'.
pose proof T_facts as (F1 & F2 & _). pose proof (class_ok c' Hc) as (K1 & K2 & K3 & K4 & K5). pose proof (max_cached_range c' Hc) as MR.
unfold cache_cells. img_change (st_cache_inited S1) with true. cbv iota. rewrite (cache_S1 c' Hc). cbn [pc_chunks pc_max length seq combine map Z.of_nat].
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c')) d) = T + (t_cache + 80 * c') + d) by (img_try (intros d; cbn; unfold T; img_lia)).
assert (EP0 : aeval B ly (AT (t_cache + 80 * c')) = T + (t_cache + 80 * c')) by (img_try (cbn; unfold T; img_lia)).
destruct (TBF c' Hc) as [TM TSZ].
constructor.
{
img_apply (keep_cell _ (T + 208 + 80 * c') 4).
- intros a Ha. img_apply (TABW_not_count T a c' Hc). img_lia.
- unfold acells. img_apply in_app_iff. right. img_apply in_app_iff. left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; img_lia)|].
unfold cache_cells. rewrite HU. left. img_refl.
- cbn. unfold T, t_cache. img_lia.
- cbn. unfold T, t_cache. img_lia. }
constructor. { img_apply val_mem_cell. rewrite EP. cbn [aeval]. replace (T + (t_cache + 80 * c') + 4) with (T + 212 + 80 * c') by (img_try (unfold t_cache; img_lia)). img_exact TM. }
constructor. { img_apply val_mem_cell. rewrite EP. cbn [aeval]. replace (T + (t_cache + 80 * c') + 8) with (T + 216 + 80 * c') by (img_try (unfold t_cache; img_lia)). img_exact TSZ. }
img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S1)).
Proof.
img_change (st_chunks S1) with (st_chunks S).
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
img_apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (ck_beg k) as [|o|r o|c'' p'] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
apply (Z_user (prim_class o) (rg_alloc_user (reg S (prim_class o)))); [img_lia | img_lia | img_lia | img_lia].
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _). img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Hin) | img_try (cbn [fst snd]; clear - Ha X2 X3 G8 Q2 G5; unfold kPage in *; img_lia)].
+ intros x Hx. unfold acells. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
* repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; img_lia)|]). img_apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [img_try (img_apply Forall_nil)|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|img_lia]. img_lia. }
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S1).
Proof.
img_change (sec_cells S1) with (sec_cells S).
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 (0x5ef000 + D_1000)) by (img_try (intros a Ha; img_apply Z_low; img_lia)).
unfold sec_cells in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved; img_lia | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved, kHighMemBeg; img_lia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_n; img_lia | cbn; rewrite EI; unfold TFX_INST, o_sec_n, kHighMemBeg; img_lia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex; img_lia | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex, kHighMemBeg; img_lia])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. img_apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [img_refl | img_lia | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hx.
+ img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try img_apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
img_apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Gin) | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. rewrite Eb. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ unfold kPage in *. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2.
intros a Ha. img_apply (Z_user kBatchClass (rg_alloc_user (reg S kBatchClass) + 8192)); [img_try (unfold kBatchClass; img_lia) | img_lia | img_try (unfold kUserMapSize, EV_MAX in MB; img_lia) |].
unfold region_base. (subst x; cbv beta). unfold kBatchBytes in Ha. img_lia. }
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; left; img_refl | cbn; img_lia | cbn; unfold kBatchBytes; img_lia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; left; img_refl | cbn; img_lia | cbn; unfold kBatchBytes; img_lia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; right; left; img_refl | cbn; img_lia | cbn; unfold kBatchBytes; img_lia])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ _ _ LOC).
+ intros y Hy. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hy.
+ img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. img_lia.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S1).
Proof.
img_change (quar_cells S1) with (quar_cells S).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 4 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI. pose proof T_facts as (F1 & F2 & _).
assert (LOCI : loc_ok 0x10000 (0x5ef000 + D_1000)) by (img_try (intros a Ha; img_apply Z_low; img_lia)).
assert (LOCT : loc_ok (T + t_qc) 32) by (img_try (intros a Ha; img_apply Z_Tlo; unfold t_qc in *; img_lia)).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST; img_lia | cbn; rewrite EI; unfold TFX_INST, kHighMemBeg; img_lia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST; img_lia | cbn; rewrite EI; unfold TFX_INST, kHighMemBeg; img_lia])|].
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCT); [img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto | cbn; unfold T; img_lia | cbn; unfold T; img_lia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x5ef000 + D_1000) LOCI); [img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFX_INST; img_lia | cbn; rewrite EI; unfold TFX_INST, kHighMemBeg; img_lia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S1).
Proof.
img_change (fs_cells S1) with (fs_cells S).
img_apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_lia | img_try (cbn [fst snd]; img_exact Ha)].
- intros x Hx. unfold acells. do 5 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S1).
Proof.
img_change (depot_cells ly S1) with (depot_cells ly S).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
img_apply (keep_cells _ 0x10000 (0x5ef000 + D_1000)).
- intros a Ha. img_apply Z_low. img_lia.
- intros x Hx. unfold acells. do 6 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold depot_cells. repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?ED, ?ES; unfold TFX_DEPOT, TFX_STORE, d_nuniq, d_map1, s_total, s_block0, kHighMemBeg; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S1).
Proof.
img_change (ialloc_cells B S1) with (ialloc_cells B S).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
img_apply (keep_cells _ 0x10000 (0x5ef000 + D_1000)).
- intros a Ha. img_apply Z_low. img_lia.
- intros x Hx. unfold acells. do 7 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_FLAG.
repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?E1, ?E3; unfold TFX_IAL_LO, TFX_IAL_FLAG, kHighMemBeg; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. constructor; [|img_try (img_apply Forall_nil)]. img_apply (keep_cell _ (T + t_unwinding) 1).
- intros a Ha. img_apply Z_Thi. unfold t_unwinding in *. img_lia.
- unfold acells. do 8 (img_apply in_app_iff; right). left. img_refl.
- cbn. unfold T. img_lia.
- cbn. unfold T. img_lia.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S1).
Proof.
unfold acells.
img_apply Forall_app; split; [img_try (img_exact cells_regions)|]. img_apply Forall_app; split; [img_try (img_exact cells_caches)|]. img_apply Forall_app; split; [img_try (img_exact cells_chunks)|].
img_apply Forall_app; split; [img_try (img_exact cells_sec)|]. img_apply Forall_app; split; [img_try (img_exact cells_quar)|]. img_apply Forall_app; split; [img_try (img_exact cells_fs)|].
img_apply Forall_app; split; [img_try (img_exact cells_depot)|]. img_apply Forall_app; split; [img_try (img_exact cells_ialloc) | img_try (img_exact cells_thread)].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S1.
Proof.
change (fa_entries_ok ly rd' S). intros c' i vv Hc' Hi HV k Hk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [img_try (img_exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk)) | img_try (eapply own_fa; [img_exact MA | img_exact Hc' | clear - Hi Hk FL FB; numconst; img_lia]) |].
img_apply Z_prim. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2. numconst. img_lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S1.
Proof.
change (fs_flags_ok ly rd' S). intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp)) | img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | img_lia]) |].
img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_lia | img_try (cbn [fst snd])].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. img_lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S1.
Proof.
change (depot_ok B ly rd' S). pose proof (ts_depot B TS) as ED.
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). img_lia. }
assert (EZ : forall a, (TFX_DEPOT <= a < TFX_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. img_apply AGX.
- destruct Ha as [Ha|Ha].
+ img_apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
eexists. split; [img_try (right; right; right; left; img_refl)|]. unfold in_zr; cbn. unfold TFX_DEPOT, d_tab_words in Ha. img_lia.
+ img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_lia)].
- destruct Ha as [Ha|Ha]; [img_try (img_apply Z_low; unfold TFX_DEPOT, d_tab_words, kHighMemBeg in *; img_lia)|].
img_apply (Z_ext 4 (ly_NB ly, kNodesBlockSize)); [img_refl | img_lia | img_try (cbn [fst snd]; img_lia)]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|img_try (split; [|img_exact H3])].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [img_try (img_exact Hh)|]. intros k Hk. rewrite EZ; [img_try (img_exact (Hr k Hk))|]. left. rewrite ED. unfold d_tab_words in *. img_lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [img_try (img_exact L1)|]. split.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L2 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L3 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
Qed.
Lemma shadow_low : forall g, 0 <= g < kHighMemEnd -> 0x7fff7000 <= shadow_addr g < 0x10007fff8000.
Proof. intros g Hg. unfold shadow_addr. pose proof (Z.div_mod g 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound g 8 ltac:(img_lia)). numconst. unfold SHADOW_OFF. img_lia. Qed.
Lemma shadow_final : shadow_ok B ly rd' S1.
Proof.
change (shadow_ok B ly rd' S). intros g vv Hg8 HV.
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 HV)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA HV)) |].
img_apply Z_low. right. img_apply shadow_low.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _). clear - Hg0 C1 C2. numconst. img_lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|img_try (discriminate)].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_high ly LY) as IP. unfold in_high in IP.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_lia)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(img_lia)) as MB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base in *; unfold region_base in R1, R2, Hlo; rewrite region_off_eq in Hlo by img_lia; rewrite region_off_eq in R1 by img_lia; rewrite region_off_eq in R2 by img_lia;
clear - Hlo R1 R2 IP FA1 FB MB Hc'; numconst; unfold EV_MAX in *; img_lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. numconst. unfold kPage in *. img_lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)) | img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
img_apply Z_low. right. unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. unfold shadow_addr. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(img_lia)) as D1.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)) as D2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)) as M2.
pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(img_lia)) as M1.
clear - Hi T1 T2 T4 T7 D1 D2 M1 M2. numconst. unfold SHADOW_OFF. img_lia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
unfold shadow_addr. unfold kLowMemEnd in Z5. pose proof (Z.div_mod (fst r) 8 ltac:(img_lia)) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(img_lia)) as D2.
clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2. numconst. unfold SHADOW_OFF. img_lia.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. img_apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [img_try (img_exact H)|]); [img_try (img_exact (am_junk _ _ _ _ MA)) | img_try (img_exact (am_areas _ _ _ _ MA)) | img_try (img_exact (am_client _ _ _ _ MA))].
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S1) /\ Forall (range_vis B ly rd') (aareas S1) /\ Forall (range_vis B ly rd') (aclient S1).
Proof.
split; [|img_try (split)].
-
unfold ajunk. img_change (st_chunks S1) with (st_chunks S).
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. img_refl. }
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. img_refl. }
img_apply Forall_app; split; [img_try (img_apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
unfold cache_junk. img_change (st_cache_inited S1) with true. cbv iota. rewrite (cache_S1 c') by img_lia. cbn [pc_chunks length Z.of_nat].
img_apply vis_keep. left. intros x [<-|[]]. unfold ajunk. do 2 right. img_apply in_app_iff; right. img_apply in_app_iff; left. img_apply in_flat_map. exists c'. split; [img_try (img_apply In_zseq; img_lia)|].
unfold cache_junk. rewrite HU. left. img_refl. }
img_apply Forall_app; split; [img_try (img_apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; do 2 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ img_change (sec_junk S1) with (sec_junk S). img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_exact Hx. }
img_apply Forall_app; split.
{ img_change (quar_junk S1) with (quar_junk S). img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_exact Hx. }
img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (img_apply in_app_iff; right). img_exact Hx.
- img_change (aareas S1) with (aareas S). img_apply vis_keep. right; left. intros x Hx; img_exact Hx.
- img_change (aclient S1) with (aclient S). img_apply vis_keep. right; right. intros x Hx; img_exact Hx.
Qed.
Definition abs_cell_okI {imgk : img} (cc : acell) : bool :=
match c_at cc with
| ANum a => ((0x10000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? (0x5ff000 + D_1000))) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x80050000))
| _ => false
end.
Lemma abs_cells_okI : forallb abs_cell_okI (Tfx_const_abs ++ Tfx_const_shadow) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
img_apply Forall_forall. intros cc Hin.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin))|].
intros k Hk. img_apply AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk))|].
rewrite (ts_const B TS ly) in Hin. unfold Tfx_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfx_const_sym in Hin. cbn [In] in Hin. pose proof T_facts as (F1 & F2 & _).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ img_apply Z_low; clear - Hk; unfold TFX_TP, TFX_INST, TFX_TSD, o_space, o_rinfo, o_sec_chunks; numconst; img_lia
| img_apply Z_Tlo; unfold T in *; clear - Hk; img_lia
| img_apply (Z_ext 6 (ly_C ly, 256) _ eq_refl ltac:(img_lia)); cbn [fst snd]; clear - Hk; img_lia
| img_apply (Z_ext 7 (ly_D ly, 4096) _ eq_refl ltac:(img_lia)); cbn [fst snd]; clear - Hk; img_lia
| img_apply Z_prim; clear - Hk SP; numconst; img_lia ]) |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okI cc Hin) as Hc. unfold abs_cell_okI in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply andb_prop in Hc as [Hz Hc]; apply Z.leb_le in Hz; apply Z.leb_le in Hc; img_apply Z_low; img_lia.
Qed.
Theorem AR_init : AR tfxsegs B ly S1 W memR md.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|img_try (split; [|split; [|split]])].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ img_exact WF1.
+ img_exact Mun.
+ img_exact Msy.
+ img_exact Mly.
+ img_exact Mpl.
+ img_exact const_final.
+ img_exact Mcow.
+ img_exact cells_final.
+ img_exact fa_final.
+ img_exact flags_final.
+ img_exact depot_final.
+ img_exact shadow_final.
+ img_exact zshadow_final.
+ img_exact (proj1 vis_final).
+ img_exact (proj1 (proj2 vis_final)).
+ img_exact (proj2 (proj2 vis_final)).
+
img_apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). img_apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [img_try (img_exact MA) | img_try (cbn; tauto) |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; img_lia.
* img_apply Z_low. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, kHighMemBeg in *; img_lia.
+ img_exact Mts.
+   img_exact Msi.
- destruct L; constructor; assumption.
- img_exact BUD.
- img_exact MW.
-
destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV. pose proof (HS0 a Ha NC HV) as X0. unfold YG0u.w64 in *.
rewrite MEQ; [img_try (img_exact X0)|]. rewrite unsigned_lit_small by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)).
img_apply Z_low. clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. img_lia.
+   img_apply (ahz_keep_same ly S S1 memU memR); [img_refl | | img_try (img_exact HZ0)].
intros a Ha. unfold YG0u.w64. rewrite MEQ; [img_refl|]. rewrite unsigned_lit_small by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)).
img_apply Z_low. clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. img_lia.
Qed.
Lemma refill_leaf_init : forall regs c r W' c',
refill_leaf B ly S1 W regs memR md c r W' c' -> refill_leaf B ly S W regs memU md c r W' c'.
Proof.
intros regs c r W' c' (regs' & mem' & md' & Ec & (AR' & LE & WLE & RP & IO & FR & PR) & A0).
exists regs', mem', md'. split; [img_try (img_exact Ec)|]. split; [|img_try (img_exact A0)].
split; [img_try (img_exact AR')|]. split; [img_try (img_exact LE)|]. split; [img_try (img_exact WLE)|]. split; [img_try (img_exact RP)|]. split; [img_try (img_exact IO)|]. split; [|img_try (img_exact PR)].
intros a Ra NO NO' NS NE. rewrite (FR a Ra NO NO' NS NE). img_apply AGREE0; [img_try (img_exact Ra)|].
intros Ht. img_apply NO. img_apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd])].
apply TABW_range in Ht. unfold T in Ht. clear - Ht. numconst. img_lia.
Qed.
End j.
End f.
