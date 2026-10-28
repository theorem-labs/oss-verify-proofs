(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1 AFhy AFis AFhm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold zone3, in_app, kLowShadowBeg, TFIB_IMG_LO, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFIB_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Lemma refill_tree_init : forall c S, st_cache_inited S = false ->
refill_tree c S = refill_tree c (set_cache_inited true (set_cache (init_caches (st_cache S)) S)).
Proof.
intros c S HU. unfold refill_tree, init_cache_if_needed, bind, get, put, ret. cbn [ibind st_cache_inited set_cache_inited set_cache]. rewrite HU.
cbn [ibind]. reflexivity.
Qed.
Section j.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (memU memR : word -> option byte) (md : Model).
Hypothesis TS : TfibSyms B.
Hypothesis HAR : AR tfibsegs B ly S W memU md.
Hypothesis HU : st_cache_inited S = false.
Let T : Z := ly_T ly.
Let rd0 : reader := aview tfibsegs (w_H W) memU.
Let rd' : reader := aview tfibsegs (w_H W) memR.
Hypothesis MEQ : forall x : word, ~ TABW T (bv_unsigned x) -> memR x = memU x.
Hypothesis TBF : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) memR) T i.
Hypothesis TPR : forall a, TABW T a -> apresent (w_H W) memR a.
Definition S1 : astate := set_cache_inited true (set_cache (init_caches (st_cache S)) S).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Lemma caches_empty : forall c, 1 <= c <= 31 -> cache S c = pclass0.
Proof. intros c Hc. pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c Hc)) as X. rewrite HU in X. exact X. Qed.
Lemma cache_S1 : forall c, 1 <= c <= 31 -> cache S1 c = mkPC (max_cached c) [].
Proof. intros c Hc. unfold S1. rewrite cache_after_init by lia. rewrite caches_empty by lia. reflexivity. Qed.
Lemma WF1 : Wf (as_universe B) S1.
Proof. exact (WfP_init_caches _ 0 0 0 S WF HU). Qed.
Hypothesis IMG : img_cover ly.
Lemma T_facts : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\ zone3 T kThreadObjSize.
Proof.
pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. cbn [fst snd] in IT.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
pose proof ZT as (Z1 & Z2 & _). unfold T in *. refine (conj _ (conj _ (conj _ ZT))); lia.
Qed.
Lemma Z_low : forall a, (0x10000 <= a < 0x5fb000 \/ 0x7fff7000 <= a < 0x10007fff8000) -> ~ TABW T a.
Proof.
intros a Ha Hx. apply TABW_range in Hx. pose proof T_facts as (_ & _ & _ & ZT).
pose proof (zone3_apart_img _ _ a ZT) as TI. pose proof (zone3_apart_hsh _ _ a ZT) as TH. clear - Ha Hx TI TH. numconst. lia.
Qed.
Lemma Z_high : forall a, ~ (T <= a < T + kThreadObjSize) -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. clear - Ha Hx. numconst. lia. Qed.
Lemma Z_Tlo : forall a, a < T + 292 -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. lia. Qed.
Lemma Z_Thi : forall a, T + 2704 <= a -> ~ TABW T a.
Proof. intros a Ha Hx. apply TABW_range in Hx. lia. Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ TABW T a.
Proof. intros a Ha. apply Z_high. pose proof T_facts as (_ & _ & PT). clear - Ha PT. lia. Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i <> 2)%nat -> fst e <= a < fst e + snd e -> ~ TABW T a.
Proof.
intros i e a He Hi Ha. apply Z_high. pose proof (lo_disj ly LY) as HD. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto).
assert (D : zdisjoint e (ly_T ly, kThreadObjSize)).
{ destruct (Nat.lt_ge_cases i 2) as [L|L].
- assert (E2 : nth_error (owned_extents ly) (i + Datatypes.S (2 - i - 1)) = Some (ly_T ly, kThreadObjSize)) by (replace (i + Datatypes.S (2 - i - 1))%nat with 2%nat by lia; reflexivity).
exact (pairwise_ij _ _ i (2 - i - 1) _ _ HD' He E2).
- assert (Ei : nth_error (owned_extents ly) (2 + Datatypes.S (i - 2 - 1)) = Some e) by (replace (2 + Datatypes.S (i - 2 - 1))%nat with i by lia; exact He).
exact (zdisjoint_sym _ _ (pairwise_ij _ _ 2 (i - 2 - 1) _ _ HD' eq_refl Ei)). }
unfold zdisjoint in D. cbn [fst snd] in D. unfold T. clear - D Ha. lia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ TABW T a.
Proof.
intros e a He Ha. apply Z_high. pose proof (am_placed _ _ _ _ MA) as [PL PD].
pose proof (pairwise_In zdisjoint _ e (ly_T ly, kThreadObjSize) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. unfold T. clear - D Ha. lia.
Qed.
Lemma Z_user : forall c' x a, 1 <= c' <= 31 -> 0 <= x -> x <= 2 ^ 32 -> region_base ly c' <= a < region_base ly c' + x -> ~ TABW T a.
Proof.
intros c' x a Hc' Hx0 Hx Ha. pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _). apply Z_prim. clear - Hx0 Hx Ha R1 R2. lia.
Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ TABW T a -> rd' a = rd0 a.
Proof. intros a Ra Hx. unfold rd', rd0. apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Ra. exact Hx. Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ TABW T a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W memU md a HAR Ho) as Ra.
ceil.   apply AGREE0; [clear - Ra CR0; lia | exact Hx].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; exact H. Qed.
Lemma PRES_MONO : forall a, apresent (w_H W) memU a -> apresent (w_H W) memR a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) memU u -> apresent (w_H W) memR u).
{ intros u Ru Hp. destruct (TABW_dec T u) as [Ht|Ht]; [exact (TPR u Ht)|].
eapply apresent_same; [|exact Hp]. apply MEQ. rewrite unsigned_lit_small by exact Ru. exact Ht. }
intros a Hp. apply (proj2 (apresent_word _ _ a)). apply G; [pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R|].
apply (proj1 (apresent_word _ _ a)). exact Hp.
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) memR (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) memU a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV; reflexivity|].
split; [reflexivity|]. destruct (memU (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV; reflexivity]. }
destruct (PRES_MONO a Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma val_mem_R : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n -> ~ TABW T (a + k)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) memU) a n v -> val_mem tfibsegs (mrestrict (w_H W) memR) a n v.
Proof.
intros a n v Hx Ha Hn HV. eapply val_mem_frame; [|exact HV]. intros k Hk. apply MEQ. rewrite unsigned_lit_small by lia. apply Hx. lia.
Qed.
Lemma val_mem_cell : forall mem e (w : nat) e',
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfibsegs (w_H W) mem) (ACell e w (AV e')).
Proof.
intros mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ TABW T a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros cc Hc.
pose proof (proj1 (Forall_forall _ _) RNG cc Hc) as [R1 R2]. cbv beta in R1, R2.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- apply LOC. lia.
Qed.
Lemma keep_cell : forall cc lo len, loc_ok lo len -> In cc (acells B ly S) ->
lo <= aeval B ly (c_at cc) -> aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= lo + len -> cell_holds B ly rd' cc.
Proof.
intros cc lo len LOC Hc R1 R2. exact (proj1 (Forall_forall _ _) (keep_cells [cc] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) cc (or_introl eq_refl)).
Qed.
Ltac fcons' := apply Forall_cons; [cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S1) (zseq 1 31)).
Proof.
change (flat_map (region_cells S1) (zseq 1 31)) with (flat_map (region_cells S) (zseq 1 31)).
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
apply (keep_cells _ (ly_space ly + kRegionInfoOff + 128 * c') 128).
+ intros a Ha. apply Z_prim. clear - Ha Hc' SP. numconst. lia.
+ intros x Hx. unfold acells. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia | exact Hx].
+ unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S1) (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. assert (Hc : 1 <= c' <= 31) by lia. clear Hc'.
pose proof T_facts as (F1 & F2 & _). pose proof (class_ok c' Hc) as (K1 & K2 & K3 & K4 & K5). pose proof (max_cached_range c' Hc) as MR.
unfold cache_cells. change (st_cache_inited S1) with true. cbv iota. rewrite (cache_S1 c' Hc). cbn [pc_chunks pc_max length seq combine map Z.of_nat].
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c')) d) = T + (t_cache + 80 * c') + d) by (intros d; cbn; unfold T; lia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * c')) = T + (t_cache + 80 * c')) by (cbn; unfold T; lia).
destruct (TBF c' Hc) as [TM TSZ].
constructor.
{
apply (keep_cell _ (T + 208 + 80 * c') 4).
- intros a Ha. apply (TABW_not_count T a c' Hc). lia.
- unfold acells. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia|].
unfold cache_cells. rewrite HU. left. reflexivity.
- cbn. unfold T, t_cache. lia.
- cbn. unfold T, t_cache. lia. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. replace (T + (t_cache + 80 * c') + 4) with (T + 212 + 80 * c') by (unfold t_cache; lia). exact TM. }
constructor. { apply val_mem_cell. rewrite EP. cbn [aeval]. replace (T + (t_cache + 80 * c') + 8) with (T + 216 + 80 * c') by (unfold t_cache; lia). exact TSZ. }
apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S1)).
Proof.
change (st_chunks S1) with (st_chunks S).
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (ck_beg k) as [|o|r o|c'' p'] eqn:Eb; try solve [destruct GG].
* cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
apply (Z_user (prim_class o) (rg_alloc_user (reg S (prim_class o)))); [lia | lia | lia | lia].
* destruct GG as (X0 & X1 & X2 & X3 & Hin & _). apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Hin | cbn [fst snd]; clear - Ha X2 X3 G8 Q2 G5; unfold kPage in *; lia].
+ intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
* repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S1).
Proof.
change (sec_cells S1) with (sec_cells S).
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_low; lia).
unfold sec_cells in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved; lia | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved, kHighMemBeg; lia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_n; lia | cbn; rewrite EI; unfold TFIB_INST, o_sec_n, kHighMemBeg; lia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex; lia | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex, kHighMemBeg; lia]|].
apply Forall_app. split.
- apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [reflexivity | lia | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. left. exact Hx.
+ apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
+ unfold kPage in *. repeat fcons'. apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
intros a Ha. apply (Z_user kBatchClass (rg_alloc_user (reg S kBatchClass) + 8192)); [unfold kBatchClass; lia | lia | unfold kUserMapSize, EV_MAX in MB; lia |].
unfold region_base. subst x. unfold kBatchBytes in Ha. lia. }
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; lia | cbn; unfold kBatchBytes; lia]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
+ intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
+ apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. lia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S1).
Proof.
change (quar_cells S1) with (quar_cells S).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI. pose proof T_facts as (F1 & F2 & _).
assert (LOCI : loc_ok 0x10000 0x5eb000) by (intros a Ha; apply Z_low; lia).
assert (LOCT : loc_ok (T + t_qc) 32) by (intros a Ha; apply Z_Tlo; unfold t_qc in *; lia).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; lia | cbn; rewrite EI; unfold TFIB_INST, kHighMemBeg; lia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; lia | cbn; rewrite EI; unfold TFIB_INST, kHighMemBeg; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; unfold T; lia | cbn; unfold T; lia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ 0x10000 0x5eb000 LOCI); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFIB_INST; lia | cbn; rewrite EI; unfold TFIB_INST, kHighMemBeg; lia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S1).
Proof.
change (fs_cells S1) with (fs_cells S).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | lia | cbn [fst snd]; exact Ha].
- intros x Hx. unfold acells. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S1).
Proof.
change (depot_cells ly S1) with (depot_cells ly S).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_low. lia.
- intros x Hx. unfold acells. do 6 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold depot_cells. repeat (apply Forall_cons; [cbn; rewrite ?ED, ?ES; unfold TFIB_DEPOT, TFIB_STORE, d_nuniq, d_map1, s_total, s_block0, kHighMemBeg; lia|]). apply Forall_nil.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S1).
Proof.
change (ialloc_cells B S1) with (ialloc_cells B S).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
apply (keep_cells _ 0x10000 0x5eb000).
- intros a Ha. apply Z_low. lia.
- intros x Hx. unfold acells. do 7 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold TFIB_IAL_LO, TFIB_IAL_FLAG, kHighMemBeg; lia|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. constructor; [|apply Forall_nil]. apply (keep_cell _ (T + t_unwinding) 1).
- intros a Ha. apply Z_Thi. unfold t_unwinding in *. lia.
- unfold acells. do 8 (apply in_app_iff; right). left. reflexivity.
- cbn. unfold T. lia.
- cbn. unfold T. lia.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S1).
Proof.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact cells_depot|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S1.
Proof.
change (fa_entries_ok ly rd' S). intros c' i vv Hc' Hi HV k Hk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk) | eapply own_fa; [exact MA | exact Hc' | clear - Hi Hk FL FB; numconst; lia] |].
apply Z_prim. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2. numconst. lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S1.
Proof.
change (fs_flags_ok ly rd' S). intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | lia] |].
apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | lia | cbn [fst snd]].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S1.
Proof.
change (depot_ok B ly rd' S). pose proof (ts_depot B TS) as ED.
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). lia. }
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. apply AGX.
- destruct Ha as [Ha|Ha].
+ apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. unfold TFIB_DEPOT, d_tab_words in Ha. lia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia].
- destruct Ha as [Ha|Ha]; [apply Z_low; unfold TFIB_DEPOT, d_tab_words, kHighMemBeg in *; lia|].
apply (Z_ext 4 (ly_NB ly, kNodesBlockSize)); [reflexivity | lia | cbn [fst snd]; lia]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. left. rewrite ED. unfold d_tab_words in *. lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
+ intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. right. unfold kNodesBlockSize. lia.
+ intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. right. unfold kNodesBlockSize. lia.
Qed.
Lemma shadow_low : forall g, 0 <= g < kHighMemEnd -> 0x7fff7000 <= shadow_addr g < 0x10007fff8000.
Proof. intros g Hg. unfold shadow_addr. pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). numconst. unfold SHADOW_OFF. lia. Qed.
Lemma shadow_final : shadow_ok B ly rd' S1.
Proof.
change (shadow_ok B ly rd' S). intros g vv Hg8 HV.
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 HV) | exact (ashadow_owned B ly S rd0 g vv MA HV) |].
apply Z_low. right. apply shadow_low.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _). clear - Hg0 C1 C2. numconst. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(lia)) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_high ly LY) as IP. unfold in_high in IP.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [FA1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(lia)) as MB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base in *; unfold region_base in R1, R2, Hlo; rewrite region_off_eq in Hlo by lia; rewrite region_off_eq in R1 by lia; rewrite region_off_eq in R2 by lia;
clear - Hlo R1 R2 IP FA1 FB MB Hc'; numconst; unfold EV_MAX in *; lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. numconst. unfold kPage in *. lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
apply Z_low. right. unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. unfold shadow_addr. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as M2.
pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)) as M1.
clear - Hi T1 T2 T4 T7 D1 D2 M1 M2. numconst. unfold SHADOW_OFF. lia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
unfold shadow_addr. unfold kLowMemEnd in Z5. pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(lia)) as D2.
clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2. numconst. unfold SHADOW_OFF. lia.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S1) /\ Forall (range_vis B ly rd') (aareas S1) /\ Forall (range_vis B ly rd') (aclient S1).
Proof.
split; [|split].
-
unfold ajunk. change (st_chunks S1) with (st_chunks S).
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
unfold cache_junk. change (st_cache_inited S1) with true. cbv iota. rewrite (cache_S1 c') by lia. cbn [pc_chunks length Z.of_nat].
apply vis_keep. left. intros x [<-|[]]. unfold ajunk. do 2 right. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map. exists c'. split; [apply In_zseq; lia|].
unfold cache_junk. rewrite HU. left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ change (sec_junk S1) with (sec_junk S). apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left. exact Hx. }
apply Forall_app; split.
{ change (quar_junk S1) with (quar_junk S). apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left. exact Hx. }
apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (apply in_app_iff; right). exact Hx.
- change (aareas S1) with (aareas S). apply vis_keep. right; left. intros x Hx; exact Hx.
- change (aclient S1) with (aclient S). apply vis_keep. right; right. intros x Hx; exact Hx.
Qed.
Definition abs_cell_okI (cc : acell) : bool :=
match c_at cc with
| ANum a => ((0x10000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x5fb000)) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w cc)) <=? 0x80050000))
| _ => false
end.
Lemma abs_cells_okI : forallb abs_cell_okI (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros cc Hin.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin)|].
intros k Hk. apply AGX; [exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk)|].
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. pose proof T_facts as (F1 & F2 & _).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ apply Z_low; clear - Hk; unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks; numconst; lia
| apply Z_Tlo; unfold T in *; clear - Hk; lia
| apply (Z_ext 6 (ly_C ly, 256) _ eq_refl ltac:(lia)); cbn [fst snd]; clear - Hk; lia
| apply (Z_ext 7 (ly_D ly, 4096) _ eq_refl ltac:(lia)); cbn [fst snd]; clear - Hk; lia
| apply Z_prim; clear - Hk SP; numconst; lia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okI cc Hin) as Hc. unfold abs_cell_okI in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply andb_prop in Hc as [Hz Hc]; apply Z.leb_le in Hz; apply Z.leb_le in Hc; apply Z_low; lia.
Qed.
Theorem AR_init : AR tfibsegs B ly S1 W memR md.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ exact WF1.
+ exact Mun.
+ exact Msy.
+ exact Mly.
+ exact Mpl.
+ exact const_final.
+ exact Mcow.
+ exact cells_final.
+ exact fa_final.
+ exact flags_final.
+ exact depot_final.
+ exact shadow_final.
+ exact zshadow_final.
+ exact (proj1 vis_final).
+ exact (proj1 (proj2 vis_final)).
+ exact (proj2 (proj2 vis_final)).
+
apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
* apply Z_low. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, kHighMemBeg in *; lia.
+ exact Mts.
+   exact Msi.
- destruct L; constructor; assumption.
- exact BUD.
- exact MW.
-
destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV. pose proof (HS0 a Ha NC HV) as X0. unfold YG0n.w64 in *.
rewrite MEQ; [exact X0|]. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
apply Z_low. clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
+   apply (ahz_keep_same ly S S1 memU memR); [reflexivity | | exact HZ0].
intros a Ha. unfold YG0n.w64. rewrite MEQ; [reflexivity|]. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
apply Z_low. clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.
Lemma refill_leaf_init : forall regs c r W' c',
refill_leaf B ly S1 W regs memR md c r W' c' -> refill_leaf B ly S W regs memU md c r W' c'.
Proof.
intros regs c r W' c' (regs' & mem' & md' & Ec & (AR' & LE & WLE & RP & IO & FR & PR) & A0).
exists regs', mem', md'. split; [exact Ec|]. split; [|exact A0].
split; [exact AR'|]. split; [exact LE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split; [|exact PR].
intros a Ra NO NO' NS NE. rewrite (FR a Ra NO NO' NS NE). apply AGREE0; [exact Ra|].
intros Ht. apply NO. apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]].
apply TABW_range in Ht. unfold T in Ht. clear - Ht. numconst. lia.
Qed.
End j.
End f.
