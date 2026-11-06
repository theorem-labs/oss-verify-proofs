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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF7f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFX_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in *.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Section f. Context {imgk : img}.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfxsegs) (mem mem' : word -> option byte) (md md' : Model).
Variable bsl : Z.
Hypothesis Hbsl : TFX_INST + 296 <= bsl <= TFX_INST + 392.
Definition XN (a : Z) : Prop :=
(TFX_OOM <= a < TFX_OOM + 1) \/
(ly_T ly + 2768 <= a < ly_T ly + 2824) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) \/ (ly_T ly + 2904 <= a < ly_T ly + 2912) \/ (ly_T ly + 3168 <= a < ly_T ly + 3169) \/
(TFX_INST + o_sec_reserved <= a < TFX_INST + o_sec_sorted + 1) \/ (TFX_INST + o_sec_stats <= a < TFX_INST + o_sec_stats + 32) \/
(bsl <= a < bsl + 8) \/ (TFX_INST + o_sec_mutex <= a < TFX_INST + o_sec_mutex + 4) \/ ((0xa6e08 + D_10c0) <= a < (0xa6e30 + D_10c0)).
Hypothesis TS : TfxSyms B.
Hypothesis HAR : AR tfxsegs B ly S W mem md.
Let rd0 : reader := aview tfxsegs (w_H W) mem.
Let rd' : reader := aview tfxsegs (w_H W) mem'.
Hypothesis AG0 : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ XN a -> rd' a = rd0 a.
Hypothesis VIS : forall a, rd0 a <> None -> rd' a <> None.
Hypothesis CUNW : rd' (ly_T ly + t_unwinding) = Some 0.
Hypothesis CRES : forall k, (k < 8)%nat -> rd' (TFX_INST + o_sec_reserved + Z.of_nat k) = Some (le_byte (st_sec_reserved S) 8 k).
Hypothesis CNCH : forall k, (k < 8)%nat -> rd' (TFX_INST + o_sec_n + Z.of_nat k) = Some (le_byte (Z.of_nat (length (st_sec_arr S))) 8 k).
Hypothesis CMTX : forall k, 0 <= k < 4 -> rd' (TFX_INST + o_sec_mutex + k) = Some 0.
Hypothesis Hvm : m_vmmaps md' = m_vmmaps md.
Hypothesis Hlz : m_vm_lazy md' = m_vm_lazy md.
Hypothesis Heg : eager_used md' = eager_used md.
Hypothesis HK : forall a, in_band_rw a -> w_H W (YG0u.w64 a) = true -> mem' (YG0u.w64 a) = mem (YG0u.w64 a).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Let IMG : img_cover ly := img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)).
Lemma AGX : forall a, aowned B ly S a -> ~ XN a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W mem md a HAR Ho) as Ra.
ceil.   img_apply AG0; [img_try (clear - Ra CR0; img_lia) | img_try (img_exact Ho) | img_try (img_exact Hx)].
Qed.
Lemma ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e).
Proof.
intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly LY) as PD.
img_exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(img_try (unfold static_extents; rewrite <- app_assoc; img_refl)) PD ltac:(img_try (img_apply in_app_iff; left; img_exact Hex)) ltac:(img_try (left; img_refl))). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; (subst; cbv beta); cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; img_lia. }
img_exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(img_try (destruct e; img_exact D9))).
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ zone3 (ly_Q ly) kPtrArrayResv /\ zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_F ly) kFakeStackSize /\
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\ ly_prim ly <= ly_space ly.
Proof.
pose proof (lo_high ly LY) as [P _]. pose proof (lo_space_in ly LY) as [SP _].
split; [img_try (img_exact P)|].
repeat match goal with |- _ /\ _ => split end; try img_exact SP;
match goal with |- zone3 ?x ?sz => img_exact (ZI (x, sz) ltac:(img_try (unfold owned_extents; cbn [In]; tauto))) end.
Qed.
Lemma Z_zoneT : forall x sz a, zone3 x sz -> zdisjoint (x, sz) (ly_T ly, kThreadObjSize) -> x <= a < x + sz -> ~ XN a.
Proof.
intros x sz a Z3 D Ha Hx. pose proof (zone3_apart_img x sz a Z3) as XI. unfold zdisjoint in D. cbn [fst snd] in D.
unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize in *. img_lia.
Qed.
Lemma Z_secx : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XN a.
Proof.
intros e a Hex Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e Hex) as (_ & HIA & _).
assert (D9 : zdisjoint e (ly_img ly)).
{ img_exact (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(img_try (unfold static_extents; img_apply in_app_iff; right; cbn; tauto))). }
assert (DT : zdisjoint e (ly_T ly, kThreadObjSize)).
{ img_exact (pairwise_In zdisjoint _ e (ly_T ly, kThreadObjSize) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(img_try (unfold static_extents, owned_extents; img_apply in_app_iff; left; cbn; tauto))). }
assert (SZ : 0 <= snd e) by (img_try (clear - Ha; img_lia)).
img_exact (Z_zoneT (fst e) (snd e) a (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(img_try (destruct e; img_exact D9))) ltac:(img_try (destruct e; img_exact DT)) Ha).
Qed.
Definition ZH (a : Z) : Prop := kHighMemBeg <= a /\ ~ (ly_T ly + 2768 <= a < ly_T ly + 3169).
Lemma Z_highT : forall a, ZH a -> ~ XN a.
Proof. intros a [Ha Hn] Hx. unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, kHighMemBeg in *. img_lia. Qed.
Lemma Z_Tlow : forall a, ly_T ly <= a < ly_T ly + 2768 -> ~ XN a.
Proof.
intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI.
unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize in *. img_lia.
Qed.
Lemma Z_ext : forall i e, nth_error (owned_extents ly) i = Some e -> (i <> 2)%nat -> forall a, fst e <= a < fst e + snd e -> ~ XN a.
Proof.
intros i e Hnth Hi a Ha. pose proof (lo_disj ly LY) as HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (img_try (unfold static_extents in HD; apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto)).
assert (D : zdisjoint e (ly_T ly, kThreadObjSize)).
{ destruct (Nat.lt_ge_cases i 2) as [L|L].
- assert (E2 : nth_error (owned_extents ly) (i + Datatypes.S (2 - i - 1))%nat = Some (ly_T ly, kThreadObjSize)) by (img_try (replace (i + Datatypes.S (2 - i - 1))%nat with 2%nat by img_lia; img_refl)).
img_exact (pairwise_ij zdisjoint (owned_extents ly) i (2 - i - 1) e (ly_T ly, kThreadObjSize) HD' Hnth E2).
- img_apply zdisjoint_sym. assert (Hi' : nth_error (owned_extents ly) (2 + Datatypes.S (i - 2 - 1))%nat = Some e) by (img_try (replace (2 + Datatypes.S (i - 2 - 1))%nat with i by img_lia; img_exact Hnth)).
img_exact (pairwise_ij zdisjoint (owned_extents ly) 2 (i - 2 - 1) (ly_T ly, kThreadObjSize) e HD' eq_refl Hi'). }
img_exact (Z_zoneT (fst e) (snd e) a (ZI e (nth_error_In _ _ Hnth)) ltac:(img_try (destruct e; img_exact D)) Ha).
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ZH a.
Proof.
intros a Ha. pose proof HI as (P & _). pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij zdisjoint (static_extents ly) 0 1 (ly_prim ly, kPrimResvSize) (ly_T ly, kThreadObjSize) HD eq_refl eq_refl) as D.
unfold zdisjoint, ZH, kThreadObjSize in *. cbn [fst snd] in D. split; img_lia.
Qed.
Lemma Z_chunk : forall k a, In k (st_chunks S) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XN a.
Proof.
intros k a Hk Ha. pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG].
- destruct GG as (Gc & _ & _ & Gext & Gbase & Gx0 & _ & Gx & Gm). pose proof (region_in_prim ly (prim_class o) LY ltac:(img_try (clear - Gc; img_lia))) as (R1 & R2 & _).
img_apply Z_highT. img_apply Z_prim. clear - Ha Gext Gbase Gx0 Gx Gm R1 R2. img_lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _). img_apply (Z_secx _ a Gin). cbn [fst snd]. clear - Ha Gbase Gext. unfold kPage in *. img_lia.
Qed.
Lemma Z_low : forall a, 0x10000 <= a < TFX_INST + o_sec_reserved -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize in *. img_lia. Qed.
Lemma Z_img : forall a, (0xa6e30 + D_10c0) <= a < (0x5ff000 + D_1000) -> a <> TFX_OOM -> ~ XN a.
Proof. intros a Ha Ho Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize in *. img_lia. Qed.
Lemma Z_shadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_hsh _ _ a PT) as TH. unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. img_lia. Qed.
Lemma Z_gap : forall a, TFX_INST + o_sec_mutex + 4 <= a < (0xa6e08 + D_10c0) -> ~ XN a.
Proof. intros a Ha Hx. pose proof HI as (_ & _ & PT & _). pose proof (zone3_apart_img _ _ a PT) as TI. unfold XN, TFX_OOM, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize in *. img_lia. Qed.
Lemma Z_quar : forall a, TFX_INST + o_quar <= a < (0x5ff000 + D_1000) -> a <> TFX_OOM -> ~ XN a.
Proof. intros a Ha Ho. img_apply Z_img; [img_try (unfold TFX_INST, o_quar in *; img_lia) | img_try (img_exact Ho)]. Qed.
Lemma keep_cells : forall lst (Zn : Z -> Prop), (forall a, Zn a -> ~ XN a) -> incl lst (acells B ly S) ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> Zn (aeval B ly (c_at cc) + k)) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst Zn LOC INC RNG. img_apply Forall_forall. intros cc Hc.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc)))|].
intros k Hk. img_apply AGX.
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- img_apply LOC. img_exact (proj1 (Forall_forall _ _) RNG cc Hc k Hk).
Qed.
Lemma keep_in : forall lst lo hi, (forall a, lo <= a < hi -> ~ XN a) -> incl lst (acells B ly S) ->
Forall (fun cc => lo <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= hi) lst -> Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo hi LOC INC RNG. img_apply (keep_cells lst (fun a => lo <= a < hi) LOC INC).
eapply Forall_impl; [|img_try (img_exact RNG)]. cbv beta. intros cc [R1 R2] k Hk. img_lia.
Qed.
Tactic Notation "acells_at" integer(n) := intros x Hx; unfold acells; do n (img_apply in_app_iff; right); first [img_apply in_app_iff; left; img_exact Hx | img_exact Hx].
Lemma cell_of_bytes : forall e (w : nat) v, (forall k, (k < w)%nat -> rd' (aeval B ly e + Z.of_nat k) = Some (le_byte v w k)) -> cell_holds B ly rd' (ACell e w (AV (ANum v))).
Proof. intros e w v H. unfold cell_holds. cbn [c_at c_val c_w aeval]. img_exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S) (zseq 1 31)).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP). pose proof (lo_space_in ly LY) as [S1 S2].
img_apply (keep_in _ (ly_prim ly) (ly_prim ly + kPrimResvSize)); [img_try (intros a Ha; img_exact (Z_highT a (Z_prim a Ha))) | img_try (acells_at 0) |].
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells, kRegionInfoOff.
unfold kSpaceSize, kPrimResvSize in *. repeat (img_apply Forall_cons; [img_try (cbn; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S) (zseq 1 31)).
Proof.
pose proof HI as (_ & _ & PT & _).
img_apply (keep_in _ (ly_T ly) (ly_T ly + 2768)); [img_try (intros a Ha; img_exact (Z_Tlow a Ha)) | img_try (acells_at 1) |].
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c' ltac:(img_lia)) as (_ & _ & _ & K4 & _).
unfold cache_cells. destruct (st_cache_inited S).
- destruct WC as [PM PL']. img_apply Forall_cons; [img_try (cbn; unfold t_cache; img_lia)|]. img_apply Forall_cons; [img_try (cbn; unfold t_cache; img_lia)|]. img_apply Forall_cons; [img_try (cbn; unfold t_cache; img_lia)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hiv). apply in_combine_l in Hiv. apply in_seq in Hiv.
cbn. unfold t_cache. img_lia.
- repeat (img_apply Forall_cons; [img_try (cbn; unfold t_cache; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
assert (LOC : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XN a).
{ intros a Ha. img_exact (Z_chunk k a Hk Ha). }
img_apply (keep_in _ (ck_base B ly k) (ck_base B ly k + ck_extent k) LOC).
- intros x Hx. unfold acells. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_apply in_flat_map. exists k. img_exact (conj Hk Hx).
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; img_lia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz k) 16); [img_try (img_apply Forall_nil)|]. assert (32 <= ck_rz k) by (img_try (apply Z.mod_divide in G6 as [q Hq]; [|img_lia]; img_lia)).
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S).
Proof.
assert (INC : incl (sec_cells S) (acells B ly S)) by (img_try (acells_at 3)).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & PQ & _).
unfold sec_cells in *.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons])].
-   img_apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. img_exact (CRES k Hk).
- img_apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. img_exact (CNCH k Hk).
- img_apply cell_of_bytes. intros k Hk. cbn [aeval]. rewrite EI. replace (Z.of_nat k) with 0 by img_lia. rewrite (CMTX 0) by img_lia. destruct k; [img_refl | img_lia].
- img_apply Forall_app. split.
+ img_apply (keep_in _ (ly_Q ly) (ly_Q ly + kPtrArrayResv)); [img_try (intros a Ha; img_exact (Z_ext 1 _ eq_refl ltac:(img_lia) a Ha)) | img_try (intros x Hx; img_apply INC; do 3 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
+ img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try img_apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (secondary_geometry (ck_req k) ltac:(img_lia) ltac:(img_try (destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; tauto))) as (_ & _ & SG & _).
img_apply (keep_in _ (ly_sec ly r) (ly_sec ly r + sec_map_size (ck_req k))); [img_try (intros a Ha; img_exact (Z_secx (ly_sec ly r, sec_map_size (ck_req k)) a Gin Ha)) | |].
* intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. rewrite Eb. img_exact (conj Hk Hx).
* unfold kPage, kSecRz in *. pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w aeval c8 z8]; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
assert (LOC : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ~ XN a).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (img_try (unfold region_base; (subst x; cbv beta); img_lia)).
intros a Ha. apply Z_highT, Z_prim. clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_app; split]])].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOC ltac:(img_try (intros y [<-|[]]; img_apply INC; cbn; tauto)) ltac:(img_try (img_apply Forall_cons; [img_try (cbn; unfold kBatchBytes; img_lia) | img_try (img_apply Forall_nil)]))) cc (or_introl eq_refl))
end.
- img_apply (keep_in _ _ _ LOC); [img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; left; img_exact Hy)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b (Hincl b (or_introl eq_refl))) as [L1 L2].
cbn. unfold kBatchBytes, kBatchSlots in *. img_lia.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S).
Proof.
assert (INC : incl (quar_cells S) (acells B ly S)) by (img_try (acells_at 4)).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & _ & PT & _).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, o_quar, t_qc in *.
assert (LOCI : forall a, TFX_INST + 728 <= a < TFX_INST + 1000 -> ~ XN a) by (img_try (intros a Ha; img_apply Z_quar; unfold TFX_INST, TFX_OOM, o_quar in *; img_lia)).
assert (LOCT : forall a, ly_T ly + 80 <= a < ly_T ly + 112 -> ~ XN a) by (img_try (intros a Ha; img_apply Z_Tlow; img_lia)).
img_apply Forall_cons; [|img_try (img_apply Forall_cons)].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCI ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z1 c1 aeval]; rewrite EI; cbn; img_lia) | img_try (img_apply Forall_nil)]
end.
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCT ltac:(img_try (intros y [<-|[]]; img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto)) ltac:(img_try (img_apply Forall_cons; [img_try (cbn; img_lia) | img_try (img_apply Forall_nil)]))) cc (or_introl eq_refl)) end|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCI ltac:(img_try (intros x [<-|[]]; img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z1 c1 aeval aoff]; rewrite EI; cbn; img_lia) | img_try (img_apply Forall_nil)] end|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S).
Proof.
img_apply (keep_in _ (ly_F ly) (ly_F ly + kFakeStackSize)); [img_try (intros a Ha; img_exact (Z_ext 3 _ eq_refl ltac:(img_lia) a Ha)) | img_try (acells_at 5) |].
unfold fs_cells, kFakeStackSize. img_apply Forall_cons; [img_try (cbn; img_lia)|]. img_apply Forall_cons; [img_try (cbn; img_lia)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S).
Proof.
assert (INC : incl (depot_cells ly S) (acells B ly S)) by (img_try (acells_at 6)).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (LOCD : forall a, TFX_DEPOT <= a < TFX_DEPOT + 4 * 2 ^ 20 + 32 -> ~ XN a) by (img_try (intros a Ha; img_apply Z_img; unfold TFX_DEPOT, TFX_OOM in *; img_lia)).
assert (LOCS : forall a, TFX_STORE <= a < TFX_STORE + 32 -> ~ XN a) by (img_try (intros a Ha; img_apply Z_img; unfold TFX_STORE, TFX_OOM in *; img_lia)).
unfold depot_cells in *.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCD ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1 aeval]; rewrite ED; unfold d_nuniq, d_map1 in *; cbn; img_lia) | img_try (img_apply Forall_nil)]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_in [cc] _ _ LOCS ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1 aeval]; rewrite ES; unfold s_total, s_block0 in *; cbn; img_lia) | img_try (img_apply Forall_nil)]
end.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S).
Proof.
assert (INC : incl (ialloc_cells B S) (acells B ly S)) by (img_try (acells_at 7)).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3. pose proof (ts_ial_hi B TS) as E4.
img_apply (keep_cells _ (fun a => (0xa6e30 + D_10c0) <= a < (0x5ff000 + D_1000) /\ a <> TFX_OOM)); [img_try (intros a [Ha Ho]; img_exact (Z_img a Ha Ho)) | img_try (img_exact INC) |].
unfold ialloc_cells. rewrite E1, E2, E3. unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_FLAG, TFX_INST, o_quar, TFX_OOM, kHighMemBeg.
repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?E1, ?E3; unfold TFX_IAL_LO, TFX_IAL_FLAG; intros k Hk; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof. unfold thread_cells. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply cell_of_bytes. intros k Hk. cbn [aeval]. replace (Z.of_nat k) with 0 by img_lia. rewrite Z.add_0_r. rewrite CUNW. destruct k; [img_refl | img_lia]. Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S).
Proof.
unfold acells.
img_apply Forall_app; split; [img_try (img_exact cells_regions)|]. img_apply Forall_app; split; [img_try (img_exact cells_caches)|]. img_apply Forall_app; split; [img_try (img_exact cells_chunks)|].
img_apply Forall_app; split; [img_try (img_exact cells_sec)|]. img_apply Forall_app; split; [img_try (img_exact cells_quar)|]. img_apply Forall_app; split; [img_try (img_exact cells_fs)|].
img_apply Forall_app; split; [img_try (img_exact cells_depot)|]. img_apply Forall_app; split; [img_try (img_exact cells_ialloc) | img_try (img_exact cells_thread)].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S.
Proof.
intros c' i vv Hc' Hi HV k Hk. pose proof HI as (P & _).
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [img_try (img_exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk)) | img_try (eapply own_fa; [img_exact MA | img_exact Hc' | clear - Hi Hk FL FB; numconst; img_lia]) |].
apply Z_highT, Z_prim. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2 P. numconst. img_lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S.
Proof.
intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB. pose proof HI as (_ & _ & _ & PF & _).
rewrite AGX; [img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp)) | img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | img_lia]) |].
img_apply (Z_ext 3 _ eq_refl ltac:(img_lia)). cbn [fst snd]. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. img_lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S.
Proof.
pose proof (ts_depot B TS) as ED. pose proof HI as (_ & _ & _ & _ & PNB & _).
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). img_lia. }
assert (EZ : forall a, (TFX_DEPOT <= a < TFX_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. img_apply AGX.
- destruct Ha as [Ha|Ha].
+ img_apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
eexists. split; [img_try (right; right; right; left; img_refl)|]. unfold in_zr; cbn. unfold TFX_DEPOT, d_tab_words in Ha. img_lia.
+ img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_lia)].
- destruct Ha as [Ha|Ha]; [img_try (img_apply Z_img; unfold d_tab_words, TFX_DEPOT, TFX_OOM in *; img_lia) | img_try (img_apply (Z_ext 4 _ eq_refl ltac:(img_lia)); cbn [fst snd]; img_lia)]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|img_try (split; [|img_exact H3])].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [img_try (img_exact Hh)|]. intros k Hk. rewrite EZ; [img_try (img_exact (Hr k Hk))|]. left. rewrite ED. unfold d_tab_words in *. img_lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [img_try (img_exact L1)|]. split.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L2 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L3 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' S.
Proof.
intros g vv Hg8 HV.
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 HV)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA HV)) |].
img_apply Z_shadow. unfold shadow_addr.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
pose proof (Z.div_mod g 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound g 8 ltac:(img_lia)). clear - Hg0 C1 C2 H H0. numconst. unfold in_app, kLowShadowBeg, SHADOW_OFF in *. img_lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|img_try (discriminate)].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). pose proof HI as (P & _).
pose proof (Z.div_mod g 8 ltac:(img_lia)) as DM. pose proof (Z.mod_pos_bound g 8 ltac:(img_lia)) as MB.
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(img_lia)) as (R1 & R2 & _ & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_lia)) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(img_lia)) as MUB.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kUserMapSize, EV_MAX in *; clear - Hlo R4 R5 A1 A3 MUB DM MB; numconst; unfold SHADOW_OFF, kLowShadowBeg; img_lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext DM MB. numconst. unfold in_app, kLowShadowBeg, kPage, SHADOW_OFF in *. img_lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)) | img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) |].
img_apply Z_shadow. unfold shadow_addr.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst snd] in *. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(img_lia)).
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)).
clear - Hi T1 T2 T4 T7 H H0 H1 H2. numconst. unfold SHADOW_OFF, kLowShadowBeg. img_lia.
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5). unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (fst r) 8 ltac:(img_lia)). pose proof (Z.div_mod (snd r) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (snd r) 8 ltac:(img_lia)).
clear - Hi Z1 Z2 Z3 Z4 Z5 H H0 H1 H2. numconst. unfold SHADOW_OFF, kLowShadowBeg. img_lia.
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S) /\ Forall (range_vis B ly rd') (aareas S) /\ Forall (range_vis B ly rd') (aclient S).
Proof.
split; [|img_try (split)]; (eapply Forall_range_vis_keep; [img_try (img_exact VIS)|]); [img_try (img_exact (am_junk _ _ _ _ MA)) | img_try (img_exact (am_areas _ _ _ _ MA)) | img_try (img_exact (am_client _ _ _ _ MA))].
Qed.
Definition abs_cell_okN {imgk : img} (cc : acell) : bool :=
match c_at cc with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w cc)) in
((0x10000 <=? a) && (e <=? TFX_INST + o_sec_reserved) || (((0xa6e30 + D_10c0) <=? a) && (e <=? (0x5ff000 + D_1000)) && ((e <=? TFX_OOM) || (TFX_OOM + 1 <=? a)))
|| ((TFX_INST + o_sec_mutex + 4 <=? a) && (e <=? (0xa6e08 + D_10c0))) || ((0x7fff8000 <=? a) && (e <=? kHighMemBeg)))
|| ((TFX_INST + o_sec_mutex + 1 <=? a) && (e <=? TFX_INST + o_sec_mutex + 4) && match c_val cc with AV (ANum 0) => true | _ => false end)
| _ => false
end.
Lemma abs_cells_okN : forallb abs_cell_okN (Tfx_const_abs ++ Tfx_const_shadow) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
img_apply Forall_forall. intros cc Hin. pose proof Hin as Hin0.
rewrite (ts_const B TS ly) in Hin. unfold Tfx_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin0))|].
intros k Hk. img_apply AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin0 k Hk))|].
unfold Tfx_const_sym in Hin. cbn [In] in Hin. pose proof HI as (P & PQ & PT & PF & PNB & PSB & PC & PD & SP).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ img_apply Z_Tlow; clear - Hk; numconst; img_lia
| img_apply Z_img; clear - Hk; unfold TFX_TP, TFX_TSD, TFX_OOM; img_lia
| img_apply Z_low; clear - Hk; unfold TFX_INST, o_space, o_rinfo, o_sec_chunks, o_sec_reserved; img_lia
| img_apply (Z_ext 7 _ eq_refl ltac:(img_lia)); cbn [fst snd]; clear - Hk; img_lia
| img_apply (Z_ext 6 _ eq_refl ltac:(img_lia)); cbn [fst snd]; clear - Hk; img_lia ]) |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okN cc Hin) as Hc. unfold abs_cell_okN in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbv zeta in Hc.
apply Bool.orb_prop in Hc as [Hc|Hc].
+
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin0))|].
intros k Hk. rewrite Ea. cbn [aeval]. img_apply AGX; [img_try (pose proof (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin0 k Hk) as O; rewrite Ea in O; img_exact O)|].
apply Bool.orb_prop in Hc as [Hc|Hc]; [img_try (apply Bool.orb_prop in Hc as [Hc|Hc]; [apply Bool.orb_prop in Hc as [Hc|Hc]|])|].
* apply andb_prop in Hc as [H0 Hc]; apply Z.leb_le in H0; apply Z.leb_le in Hc; img_apply Z_low; img_lia.
* apply andb_prop in Hc as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply Z.leb_le in H1. apply Z.leb_le in H3.
apply Bool.orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; img_apply Z_img; unfold TFX_OOM in *; img_lia.
* apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. img_apply Z_gap. img_lia.
* apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. img_apply Z_shadow. unfold SHADOW_OFF, kLowShadowBeg. img_lia.
+
apply andb_prop in Hc as [Hc V0]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (c_val cc) as [e|mk vv] eqn:Ev; rewrite ?Ev in V0; [|img_try (discriminate V0)]. destruct e; try discriminate V0.
lazymatch type of V0 with context [match ?zz with _ => _ end] => destruct zz; try discriminate V0 end.
unfold cell_holds. rewrite Ea, Ev. cbn [aeval]. intros k Hk.
replace (z + Z.of_nat k) with (TFX_INST + o_sec_mutex + (z + Z.of_nat k - (TFX_INST + o_sec_mutex))) by img_lia.
rewrite CMTX by img_lia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (img_try (img_apply Z.pow_nonzero; img_lia)). rewrite Z.shiftr_0_l. img_refl.
Qed.
Theorem AR_snull : AR tfxsegs B ly S W mem' md'.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|img_try (split; [|split; [|split]])].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ img_exact Mwf.
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
* img_apply Z_quar; unfold ialloc_zero in Hr; pose proof (ts_ial_lo B TS) as E1; pose proof (ts_ial_hi B TS) as E2; pose proof (ts_ial_w B TS) as E3;
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_INST, o_quar, TFX_OOM, kHighMemBeg in *; img_lia.
+ img_exact Mts.
+   img_exact Msi.
- eapply ALedger_same; [img_try (img_exact L) | img_try (img_exact Hvm) | img_try (img_exact Hlz) | img_try (img_exact Heg)].
- img_exact BUD.
- img_exact (amwf_same md md' Hvm Hlz MW).
- img_exact (ahs_transfer tfxsegs B ly S S (w_H W) mem mem' (al_img_env tfxsegs ly S md LY L) M0 HS0 VIS HK ltac:(img_try (intros a _ C; img_exact C)) eq_refl
ltac:(img_try (intros g Hg Happ HF _; img_apply AGX; [img_try (eapply hfree_shadow_owned; [img_exact M0 | img_exact Hg | img_exact Happ | img_exact HF])
| img_try (img_apply Z_shadow; pose proof (shadow_addr_band_rw g Happ) as SB; clear - SB; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; img_lia)]))).
Qed.
End f.
End c.
