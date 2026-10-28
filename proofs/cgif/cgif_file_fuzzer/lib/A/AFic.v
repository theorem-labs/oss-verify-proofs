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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFIB_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section f.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem mem' : word -> option byte) (md md' : Model).
Variable bsl : Z.
Hypothesis Hbsl : TFIB_INST + 296 <= bsl <= TFIB_INST + 392.
Definition XN (a : Z) : Prop :=
(TFIB_OOM <= a < TFIB_OOM + 1) \/
(ly_T ly + 2768 <= a < ly_T ly + 2824) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) \/ (ly_T ly + 2904 <= a < ly_T ly + 2912) \/ (ly_T ly + 3168 <= a < ly_T ly + 3169) \/
(TFIB_INST + o_sec_reserved <= a < TFIB_INST + o_sec_sorted + 1) \/ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) \/
(bsl <= a < bsl + 8) \/ (TFIB_INST + o_sec_mutex <= a < TFIB_INST + o_sec_mutex + 4) \/ (0xa2c48 <= a < 0xa2c70).
Hypothesis TS : TfibSyms B.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Let rd0 : reader := aview tfibsegs (w_H W) mem.
Let rd' : reader := aview tfibsegs (w_H W) mem'.
Hypothesis AG0 : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ XN a -> rd' a = rd0 a.
Hypothesis VIS : forall a, rd0 a <> None -> rd' a <> None.
Hypothesis CUNW : rd' (ly_T ly + t_unwinding) = Some 0.
Hypothesis CRES : forall k, (k < 8)%nat -> rd' (TFIB_INST + o_sec_reserved + Z.of_nat k) = Some (le_byte (st_sec_reserved S) 8 k).
Hypothesis CNCH : forall k, (k < 8)%nat -> rd' (TFIB_INST + o_sec_n + Z.of_nat k) = Some (le_byte (Z.of_nat (length (st_sec_arr S))) 8 k).
Hypothesis CMTX : forall k, 0 <= k < 4 -> rd' (TFIB_INST + o_sec_mutex + k) = Some 0.
Hypothesis Hvm : m_vmmaps md' = m_vmmaps md.
Hypothesis Hlz : m_vm_lazy md' = m_vm_lazy md.
Hypothesis Heg : eager_used md' = eager_used md.
Hypothesis HK : forall a, in_band_rw a -> w_H W (YG0n.w64 a) = true -> mem' (YG0n.w64 a) = mem (YG0n.w64 a).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Let IMG : img_cover ly := img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)).
Lemma AGX : forall a, aowned B ly S a -> ~ XN a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem md a HAR Ho) as Ra.
ceil.   apply AG0; [clear - Ra CR0; lia | exact Ho | exact Hx].
Qed.
Lemma ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e).
Proof.
intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly LY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)).
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ zone3 (ly_Q ly) kPtrArrayResv /\ zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_F ly) kFakeStackSize /\
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\ ly_prim ly <= ly_space ly.
Proof.
pose proof (lo_high ly LY) as [P _]. pose proof (lo_space_in ly LY) as [SP _].
split; [exact P|].
repeat match goal with |- _ /\ _ => split end; try exact SP;
match goal with |- zone3 ?x ?sz => exact (ZI (x, sz) ltac:(unfold owned_extents; cbn [In]; tauto)) end.
Qed.
Lemma Z_zoneT : forall x sz a, zone3 x sz -> zdisjoint (x, sz) (ly_T ly, kThreadObjSize) -> x <= a < x + sz -> ~ XN a.
Proof.
intros x sz a Z3 D Ha Hx. pose proof (zone3_apart_img x sz a Z3) as XI. unfold zdisjoint in D. cbn [fst snd] in D.
unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize in *. lia.
Qed.
Lemma Z_secx : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XN a.
Proof.
intros e a Hex Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e Hex) as (_ & HIA & _).
assert (D9 : zdisjoint e (ly_img ly)).
{ exact (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)). }
assert (DT : zdisjoint e (ly_T ly, kThreadObjSize)).
{ exact (pairwise_In zdisjoint _ e (ly_T ly, kThreadObjSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto)). }
assert (SZ : 0 <= snd e) by (clear - Ha; lia).
exact (Z_zoneT (fst e) (snd e) a (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(destruct e; exact D9)) ltac:(destruct e; exact DT) Ha).
Qed.
Definition ZH (a : Z) : Prop := kHighMemBeg <= a /\ ~ (ly_T ly + 2768 <= a < ly_T ly + 3169).
Lemma Z_highT : forall a, ZH a -> ~ XN a.
Proof. intros a [Ha Hn] Hx. unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, kHighMemBeg in *. lia. Qed.
Lemma Z_Tlow : forall a, ly_T ly <= a < ly_T ly + 2768 -> ~ XN a.
Proof.
intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI.
unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize in *. lia.
Qed.
Lemma Z_ext : forall i e, nth_error (owned_extents ly) i = Some e -> (i <> 2)%nat -> forall a, fst e <= a < fst e + snd e -> ~ XN a.
Proof.
intros i e Hnth Hi a Ha. pose proof (lo_disj ly LY) as HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (unfold static_extents in HD; apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto).
assert (D : zdisjoint e (ly_T ly, kThreadObjSize)).
{ destruct (Nat.lt_ge_cases i 2) as [L|L].
- assert (E2 : nth_error (owned_extents ly) (i + Datatypes.S (2 - i - 1))%nat = Some (ly_T ly, kThreadObjSize)) by (replace (i + Datatypes.S (2 - i - 1))%nat with 2%nat by lia; reflexivity).
exact (pairwise_ij zdisjoint (owned_extents ly) i (2 - i - 1) e (ly_T ly, kThreadObjSize) HD' Hnth E2).
- apply zdisjoint_sym. assert (Hi' : nth_error (owned_extents ly) (2 + Datatypes.S (i - 2 - 1))%nat = Some e) by (replace (2 + Datatypes.S (i - 2 - 1))%nat with i by lia; exact Hnth).
exact (pairwise_ij zdisjoint (owned_extents ly) 2 (i - 2 - 1) (ly_T ly, kThreadObjSize) e HD' eq_refl Hi'). }
exact (Z_zoneT (fst e) (snd e) a (ZI e (nth_error_In _ _ Hnth)) ltac:(destruct e; exact D) Ha).
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ZH a.
Proof.
intros a Ha. pose proof HI as (P & _). pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij zdisjoint (static_extents ly) 0 1 (ly_prim ly, kPrimResvSize) (ly_T ly, kThreadObjSize) HD eq_refl eq_refl) as D.
unfold zdisjoint, ZH, kThreadObjSize in *. cbn [fst snd] in D. split; lia.
Qed.
Lemma Z_chunk : forall k a, In k (st_chunks S) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XN a.
Proof.
intros k a Hk Ha. pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG].
- destruct GG as (Gc & _ & _ & Gext & Gbase & Gx0 & _ & Gx & Gm). pose proof (region_in_prim ly (prim_class o) LY ltac:(clear - Gc; lia)) as (R1 & R2 & _).
apply Z_highT. apply Z_prim. clear - Ha Gext Gbase Gx0 Gx Gm R1 R2. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _). apply (Z_secx _ a Gin). cbn [fst snd]. clear - Ha Gbase Gext. unfold kPage in *. lia.
Qed.
Lemma Z_low : forall a, 0x10000 <= a < TFIB_INST + o_sec_reserved -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize in *. lia. Qed.
Lemma Z_img : forall a, 0xa2c70 <= a < 0x5fb000 -> a <> TFIB_OOM -> ~ XN a.
Proof. intros a Ha Ho Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize in *. lia. Qed.
Lemma Z_shadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_hsh _ _ a PT) as TH. unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia. Qed.
Lemma Z_gap : forall a, TFIB_INST + o_sec_mutex + 4 <= a < 0xa2c48 -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFIB_OOM, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize in *. lia. Qed.
Lemma Z_quar : forall a, TFIB_INST + o_quar <= a < 0x5fb000 -> a <> TFIB_OOM -> ~ XN a.
Proof. intros a Ha Ho. apply Z_img; [unfold TFIB_INST, o_quar in *; lia | exact Ho]. Qed.
Lemma keep_cells : forall lst (Zn : Z -> Prop), (forall a, Zn a -> ~ XN a) -> incl lst (acells B ly S) ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> Zn (aeval B ly (c_at cc) + k)) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst Zn LOC INC RNG. apply Forall_forall. intros cc Hc.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- apply LOC. exact (proj1 (Forall_forall _ _) RNG cc Hc k Hk).
Qed.
Lemma keep_in : forall lst lo hi, (forall a, lo <= a < hi -> ~ XN a) -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= hi) lst -> Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo hi LOC INC RNG. apply (keep_cells lst (fun a => lo <= a < hi) LOC INC).
eapply Forall_impl; [|exact RNG]. cbv beta. intros cc [R1 R2] k Hk. lia.
Qed.
Tactic Notation "acells_at" integer(n) := intros x Hx; unfold acells; do n (apply in_app_iff; right); first [apply in_app_iff; left; exact Hx | exact Hx].
Lemma cell_of_bytes : forall e (w : nat) v, (forall k, (k < w)%nat -> rd' (aeval B ly e + Z.of_nat k) = Some (le_byte v w k)) -> cell_holds B ly rd' (ACell e w (AV (ANum v))).
Proof. intros e w v H. unfold cell_holds. cbn [c_at c_val c_w aeval]. exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S) (zseq 1 31)).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP). pose proof (lo_space_in ly LY) as [S1 S2].
apply (keep_in _ (ly_prim ly) (ly_prim ly + kPrimResvSize)); [intros a Ha; exact (Z_highT a (Z_prim a Ha)) | acells_at 0 |].
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells, kRegionInfoOff.
unfold kSpaceSize, kPrimResvSize in *. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S) (zseq 1 31)).
Proof.
pose proof HI as (_ & _ & PT & _).
apply (keep_in _ (ly_T ly) (ly_T ly + 2768)); [intros a Ha; exact (Z_Tlow a Ha) | acells_at 1 |].
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4 & _).
unfold cache_cells. destruct (st_cache_inited S).
- destruct WC as [PM PL']. apply Forall_cons; [cbn; unfold t_cache; lia|]. apply Forall_cons; [cbn; unfold t_cache; lia|]. apply Forall_cons; [cbn; unfold t_cache; lia|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hiv). apply in_combine_l in Hiv. apply in_seq in Hiv.
cbn. unfold t_cache. lia.
- repeat (apply Forall_cons; [cbn; unfold t_cache; lia|]). apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (LOC : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XN a).
{ intros a Ha. exact (Z_chunk k a Hk Ha). }
apply (keep_in _ (ck_base B ly k) (ck_base B ly k + ck_extent k) LOC).
- intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. exact (conj Hk Hx).
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|]. assert (32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|lia]; lia).
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S).
Proof.
assert (INC : incl (sec_cells S) (acells B ly S)) by (acells_at 3).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & PQ & _).
unfold sec_cells in *.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]].
-   apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. exact (CRES k Hk).
- apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. exact (CNCH k Hk).
- apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. replace (Z.of_nat k) with 0 by lia. rewrite (CMTX 0) by lia. destruct k; [reflexivity | lia].
- apply Forall_app. split.
+ apply (keep_in _ (ly_Q ly) (ly_Q ly + kPtrArrayResv)); [intros a Ha; exact (Z_ext 1 _ eq_refl ltac:(lia) a Ha) | intros x Hx; apply INC; do 3 right; apply in_app_iff; left; exact Hx|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
+ apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (secondary_geometry (ck_req k) ltac:(lia) ltac:(destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; tauto)) as (_ & _ & SG & _).
apply (keep_in _ (ly_sec ly r) (ly_sec ly r + sec_map_size (ck_req k))); [intros a Ha; exact (Z_secx (ly_sec ly r, sec_map_size (ck_req k)) a Gin Ha) | |].
* intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. exact (conj Hk Hx).
* unfold kPage, kSecRz in *. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
repeat (apply Forall_cons; [cbn [c_at c_w aeval c8 z8]; lia|]). apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
assert (LOC : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ~ XN a).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
intros a Ha. apply Z_highT, Z_prim. clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split]]].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOC ltac:(intros y [<-|[]]; apply INC; cbn; tauto) ltac:(apply Forall_cons; [cbn; unfold kBatchBytes; lia | apply Forall_nil])) cc (or_introl eq_refl))
end.
- apply (keep_in _ _ _ LOC); [intros y Hy; apply INC; do 3 right; apply in_app_iff; left; exact Hy|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b (Hincl b (or_introl eq_refl))) as [L1 L2].
cbn. unfold kBatchBytes, kBatchSlots in *. lia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S).
Proof.
assert (INC : incl (quar_cells S) (acells B ly S)) by (acells_at 4).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & _ & PT & _).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, o_quar, t_qc in *.
assert (LOCI : forall a, TFIB_INST + 728 <= a < TFIB_INST + 1000 -> ~ XN a) by (intros a Ha; apply Z_quar; unfold TFIB_INST, TFIB_OOM, o_quar in *; lia).
assert (LOCT : forall a, ly_T ly + 80 <= a < ly_T ly + 112 -> ~ XN a) by (intros a Ha; apply Z_Tlow; lia).
apply Forall_cons; [|apply Forall_cons].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCI ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z1 c1 aeval]; rewrite EI; cbn; lia | apply Forall_nil]
end.
apply Forall_app. split.
- do 4 (apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCT ltac:(intros y [<-|[]]; apply INC; right; right; apply in_app_iff; left; cbn; tauto) ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) cc (or_introl eq_refl)) end|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCI ltac:(intros x [<-|[]]; apply INC; right; right; apply in_app_iff; right; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z1 c1 aeval aoff]; rewrite EI; cbn; lia | apply Forall_nil] end|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S).
Proof.
apply (keep_in _ (ly_F ly) (ly_F ly + kFakeStackSize)); [intros a Ha; exact (Z_ext 3 _ eq_refl ltac:(lia) a Ha) | acells_at 5 |].
unfold fs_cells, kFakeStackSize. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S).
Proof.
assert (INC : incl (depot_cells ly S) (acells B ly S)) by (acells_at 6).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (LOCD : forall a, TFIB_DEPOT <= a < TFIB_DEPOT + 4 * 2 ^ 20 + 32 -> ~ XN a) by (intros a Ha; apply Z_img; unfold TFIB_DEPOT, TFIB_OOM in *; lia).
assert (LOCS : forall a, TFIB_STORE <= a < TFIB_STORE + 32 -> ~ XN a) by (intros a Ha; apply Z_img; unfold TFIB_STORE, TFIB_OOM in *; lia).
unfold depot_cells in *.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCD ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1 aeval]; rewrite ED; unfold d_nuniq, d_map1 in *; cbn; lia | apply Forall_nil]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCS ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1 aeval]; rewrite ES; unfold s_total, s_block0 in *; cbn; lia | apply Forall_nil]
end.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S).
Proof.
assert (INC : incl (ialloc_cells B S) (acells B ly S)) by (acells_at 7).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3. pose proof (ts_ial_hi B TS) as E4.
apply (keep_cells _ (fun a => 0xa2c70 <= a < 0x5fb000 /\ a <> TFIB_OOM)); [intros a [Ha Ho]; exact (Z_img a Ha Ho) | exact INC |].
unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_INST, o_quar, TFIB_OOM, kHighMemBeg.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold TFIB_IAL_LO, TFIB_IAL_FLAG; intros k Hk; lia|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof. unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. apply cell_of_bytes. intros k Hk. cbn [aeval]. replace (Z.of_nat k) with 0 by lia. rewrite Z.add_0_r. rewrite CUNW. destruct k; [reflexivity | lia]. Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S).
Proof.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact cells_depot|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S.
Proof.
intros c' i vv Hc' Hi HV k Hk. pose proof HI as (P & _).
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk) | eapply own_fa; [exact MA | exact Hc' | clear - Hi Hk FL FB; numconst; lia] |].
apply Z_highT, Z_prim. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2 P. numconst. lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S.
Proof.
intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB. pose proof HI as (_ & _ & _ & PF & _).
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | lia] |].
apply (Z_ext 3 _ eq_refl ltac:(lia)). cbn [fst snd]. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S.
Proof.
pose proof (ts_depot B TS) as ED. pose proof HI as (_ & _ & _ & _ & PNB & _).
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). lia. }
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. apply AGX.
- destruct Ha as [Ha|Ha].
+ apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. unfold TFIB_DEPOT, d_tab_words in Ha. lia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia].
- destruct Ha as [Ha|Ha]; [apply Z_img; unfold d_tab_words, TFIB_DEPOT, TFIB_OOM in *; lia | apply (Z_ext 4 _ eq_refl ltac:(lia)); cbn [fst snd]; lia]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. left. rewrite ED. unfold d_tab_words in *. lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
+ intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. right. unfold kNodesBlockSize. lia.
+ intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. right. unfold kNodesBlockSize. lia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' S.
Proof.
intros g vv Hg8 HV.
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 HV) | exact (ashadow_owned B ly S rd0 g vv MA HV) |].
apply Z_shadow. unfold shadow_addr.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). clear - Hg0 C1 C2 H H0. numconst. unfold in_app, kLowShadowBeg, SHADOW_OFF in *. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). pose proof HI as (P & _).
pose proof (Z.div_mod g 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as MB.
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(lia)) as (R1 & R2 & _ & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(lia)) as MUB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kUserMapSize, EV_MAX in *; clear - Hlo R4 R5 A1 A3 MUB DM MB; numconst; unfold SHADOW_OFF, kLowShadowBeg; lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext DM MB. numconst. unfold in_app, kLowShadowBeg, kPage, SHADOW_OFF in *. lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
apply Z_shadow. unfold shadow_addr.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)).
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
clear - Hi T1 T2 T4 T7 H H0 H1 H2. numconst. unfold SHADOW_OFF, kLowShadowBeg. lia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5). unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)). pose proof (Z.div_mod (snd r) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd r) 8 ltac:(lia)).
clear - Hi Z1 Z2 Z3 Z4 Z5 H H0 H1 H2. numconst. unfold SHADOW_OFF, kLowShadowBeg. lia.
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S) /\ Forall (range_vis B ly rd') (aareas S) /\ Forall (range_vis B ly rd') (aclient S).
Proof.
split; [|split]; (eapply Forall_range_vis_keep; [exact VIS|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Definition abs_cell_okN (cc : acell) : bool :=
match c_at cc with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w cc)) in
((0x10000 <=? a) && (e <=? TFIB_INST + o_sec_reserved) || ((0xa2c70 <=? a) && (e <=? 0x5fb000) && ((e <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a)))
|| ((TFIB_INST + o_sec_mutex + 4 <=? a) && (e <=? 0xa2c48)) || ((0x7fff8000 <=? a) && (e <=? kHighMemBeg)))
|| ((TFIB_INST + o_sec_mutex + 1 <=? a) && (e <=? TFIB_INST + o_sec_mutex + 4) && match c_val cc with AV (ANum 0) => true | _ => false end)
| _ => false
end.
Lemma abs_cells_okN : forallb abs_cell_okN (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros cc Hin. pose proof Hin as Hin0.
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin0)|].
intros k Hk. apply AGX; [exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin0 k Hk)|].
unfold Tfib_const_sym in Hin. cbn [In] in Hin. pose proof HI as (P & PQ & PT & PF & PNB & PSB & PC & PD & SP).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ apply Z_Tlow; clear - Hk; numconst; lia
| apply Z_img; clear - Hk; unfold TFIB_TP, TFIB_TSD, TFIB_OOM; lia
| apply Z_low; clear - Hk; unfold TFIB_INST, o_space, o_rinfo, o_sec_chunks, o_sec_reserved; lia
| apply (Z_ext 7 _ eq_refl ltac:(lia)); cbn [fst snd]; clear - Hk; lia
| apply (Z_ext 6 _ eq_refl ltac:(lia)); cbn [fst snd]; clear - Hk; lia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okN cc Hin) as Hc. unfold abs_cell_okN in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbv zeta in Hc.
apply Bool.orb_prop in Hc as [Hc|Hc].
+
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin0)|].
intros k Hk. rewrite Ea. cbn [aeval]. apply AGX; [pose proof (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin0 k Hk) as O; rewrite Ea in O; exact O|].
apply Bool.orb_prop in Hc as [Hc|Hc]; [apply Bool.orb_prop in Hc as [Hc|Hc]; [apply Bool.orb_prop in Hc as [Hc|Hc]|]|].
* apply andb_prop in Hc as [H0 Hc]; apply Z.leb_le in H0; apply Z.leb_le in Hc; apply Z_low; lia.
* apply andb_prop in Hc as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply Z.leb_le in H1. apply Z.leb_le in H3.
apply Bool.orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; apply Z_img; unfold TFIB_OOM in *; lia.
* apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z_gap. lia.
* apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z_shadow. unfold SHADOW_OFF, kLowShadowBeg. lia.
+
apply andb_prop in Hc as [Hc V0]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (c_val cc) as [e|mk vv] eqn:Ev; rewrite ?Ev in V0; [|discriminate V0]. destruct e; try discriminate V0.
lazymatch type of V0 with context [match ?zz with _ => _ end] => destruct zz; try discriminate V0 end.
unfold cell_holds. rewrite Ea, Ev. cbn [aeval]. intros k Hk.
replace (z + Z.of_nat k) with (TFIB_INST + o_sec_mutex + (z + Z.of_nat k - (TFIB_INST + o_sec_mutex))) by lia.
rewrite CMTX by lia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.
Theorem AR_snull : AR tfibsegs B ly S W mem' md'.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ exact Mwf.
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
* apply Z_quar; unfold ialloc_zero in Hr; pose proof (ts_ial_lo B TS) as E1; pose proof (ts_ial_hi B TS) as E2; pose proof (ts_ial_w B TS) as E3;
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_INST, o_quar, TFIB_OOM, kHighMemBeg in *; lia.
+ exact Mts.
+   exact Msi.
- eapply ALedger_same; [exact L | exact Hvm | exact Hlz | exact Heg].
- exact BUD.
- exact (amwf_same md md' Hvm Hlz MW).
- exact (ahs_transfer tfibsegs B ly S S (w_H W) mem mem' (al_img_env tfibsegs ly S md LY L) M0 HS0 VIS HK ltac:(intros a _ C; exact C) eq_refl
ltac:(intros g Hg Happ HF _; apply AGX; [eapply hfree_shadow_owned; [exact M0 | exact Hg | exact Happ | exact HF]
| apply Z_shadow; pose proof (shadow_addr_band_rw g Happ) as SB; clear - SB; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia])).
Qed.
End f.
End c.
