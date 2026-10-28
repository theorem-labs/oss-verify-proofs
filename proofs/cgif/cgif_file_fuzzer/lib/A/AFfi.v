(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFff AFeu AFep AFeo AFgk AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST,
A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd, EV_MAX in *.
Section g.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (c off : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : cd_pre B ly X c off W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Definition kcnt : Z := Z.of_nat (length (pc_chunks (cache X c))).
Definition kold : Z := fa_len (rg_free (reg X c)).
Definition kmf : Z := rg_mapped_fa (reg X c).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Lemma IMG : img_cover ly.
Proof. exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hci : st_cache_inited X = true. Proof. exact (proj1 (proj2 PRE)). Qed.
Lemma Hc : 1 <= c <= 30. Proof. exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma AINST : as_inst B = A_ALLOCATOR. Proof. rewrite (ts_inst _ TB). reflexivity. Qed.
Lemma CLS : cls_ok c (reg X c) (cache X c) true (chunk_offs X c) (batch_offs X c).
Proof. pose proof (wf_classes _ _ _ _ _ WF c ltac:(pose proof Hc; lia)) as C. unfold wf_class in C. rewrite Hci in C. exact C. Qed.
Local Notation Pv := (AFgk.Pv ly off).
Local Notation PCv := (AFgk.PCv ly c).
Local Notation MAXv := (AFgk.MAXv c).
Local Notation SZv := (AFgk.SZv c).
Local Notation Nv := (AFgk.Nv c).
Local Notation RIv := (AFgk.RIv ly).
Local Notation RGv := (AFgk.RGv ly c).
Local Notation RBv := (AFgk.RBv ly c).
Local Notation FAv := (AFgk.FAv ly c).
Local Notation RELv := (AFgk.RELv c off).
Lemma class_facts : 32 <= SZv <= kMaxSize /\ SZv mod 32 = 0 /\ 2 <= MAXv <= 16 /\ MAXv mod 2 = 0 /\ 1 <= Nv <= 8 /\ MAXv = 2 * Nv /\
region_off c = c * 2 ^ 32.
Proof.
pose proof (class_ok c ltac:(pose proof Hc; lia)) as (K1 & K2 & K3 & K4 & K5 & K6). unfold AFgk.Nv, AFgk.MAXv, AFgk.SZv, region_off.
rewrite Z.shiftl_mul_pow2 by (pose proof Hc; lia).
assert (32 <= class_size c) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
assert (D1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (D2 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (D3 : max_cached c = 2 * (max_cached c / 2)) by (pose proof (Z.div_mod (max_cached c) 2 ltac:(lia)); lia).
repeat split; lia.
Qed.
Lemma reg_facts : 0 <= kold /\ 4 * kold <= kmf /\ 0 <= kmf <= kFreeArrayMax /\ kmf mod kFreeArrayMapSize = 0 /\
0 <= rg_alloc_user (reg X c) <= rg_mapped_user (reg X c) /\ rg_mapped_user (reg X c) <= kFreeArrayOffset /\
rg_alloc_user (reg X c) mod SZv = 0 /\ 0 <= kcnt <= MAXv /\ pc_max (cache X c) = MAXv.
Proof.
pose proof CLS as CL. pose proof (class_ok c ltac:(pose proof Hc; lia)) as (K1 & K2 & _).
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A3.
pose proof (wr_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as F3. pose proof (wr_fa_len _ _ _ _ _ _ CL) as F4.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0. pose proof (wr_cache _ _ _ _ _ _ CL) as [C1 C2].
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c WF ltac:(pose proof Hc; lia)) as MB.
unfold kold, kmf, kcnt, AFgk.MAXv, AFgk.SZv. unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. repeat split; try assumption; lia.
Qed.
Lemma off_facts : 0 <= RELv /\ RELv + SZv <= rg_alloc_user (reg X c) /\ RELv mod 16 = 0 /\ RELv mod SZv = 0.
Proof.
destruct PRE as (_ & _ & _ & [O1 O2] & O3 & _). pose proof reg_facts as (_ & _ & _ & _ & _ & _ & AL & _). pose proof class_facts as (K1 & K2 & _).
unfold AFgk.RELv, AFgk.SZv in *.
apply Z.mod_divide in O3 as [q Hq]; [|lia]. apply Z.mod_divide in AL as [r Hr]; [|lia]. pose proof K2 as K2'. apply Z.mod_divide in K2 as [s Hs]; [|lia].
splits; [lia | | | apply Z.mod_divide; [lia|]; exists q; lia].
- assert (q < r) by nia. nia.
- apply Z.mod_divide; [lia|]. exists (q * (2 * s)). lia.
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ T mod 4096 = 0.
Proof.
pose proof (lo_high ly LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LO) as HA. pose proof (lo_disj ly LO) as HD0.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT. clear HA IT.
pose proof (lo_space_in ly LO) as HSPC. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_al ly LO) as SAL.
pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
pose proof (aso_cells _ (am_syms B ly X rd0 M)) as (I1 & I2 & _).
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in *.
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear - IP HSPC T1 T2 T3 T4 T5 T6 T7 SAL TAL PT PSTK TSTK I1 I2. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *. repeat split; lia.
Qed.
Lemma derived : 4096 <= PCv /\ PCv + 80 <= T + kThreadObjSize /\     T + t_cache + 80 <= PCv /\ PCv + 80 <= T + t_cache + 2480 /\
RIv = SB + kRegionInfoOff /\ RGv = RIv + 128 * c /\ RIv + 128 <= RGv /\ RGv + 128 <= RIv + 4096 /\ kHighMemBeg <= RIv /\ RIv + 4096 <= ASAN_CEIL /\
RBv = SB + c * 2 ^ 32 /\ FAv = RBv + kFreeArrayOffset /\ SB + 2 ^ 32 <= RBv /\ RBv + 2 ^ 32 <= SB + 31 * 2 ^ 32 /\
Pv = RBv + RELv /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL.
Proof.
pose proof HI as HIx. pose proof Hc as Hcx. pose proof class_facts as (_ & _ & _ & _ & _ & _ & K7).
unfold AFgk.RGv, AFgk.FAv, AFgk.Pv. unfold AFgk.PCv, AFgk.RIv, AFgk.RBv, AFgk.RELv. rewrite K7.
numconst. repeat split; lia.
Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (tfib_const_lookup B TB ly X H0 mem a w x M E). Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (tfib_const_lookup_sym B TB ly X H0 mem e w e' M E). Qed.
Lemma cell_state : forall cc e (w : nat) e', In cc (acells B ly X) -> cc = ACell e w (AV e') -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros cc e w e' Hin ->. apply (cell_holds_val_mem B ly H0 mem e w e'). exact (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall cc e (w : nat) x, In cc (acells B ly X) -> cc = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros cc e w x Hin E. exact (cell_state cc e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) \/ In (e, len) (aclient X) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_client B ly X rd0 M) _ Hin i Hi).
Qed.
Lemma In_acells_cache : forall cc, In cc (cache_cells X c) -> In cc (acells B ly X).
Proof.
intros cc Hcc. unfold acells. rewrite !in_app_iff. right; left. apply in_flat_map. exists c. split; [apply In_zseq; pose proof Hc; lia | exact Hcc].
Qed.
Lemma In_acells_region : forall cc, In cc (region_cells X c) -> In cc (acells B ly X).
Proof.
intros cc Hcc. unfold acells. rewrite !in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; pose proof Hc; lia | exact Hcc].
Qed.
Lemma cache_vals : val_mem tfibsegs m0 PCv 4 kcnt /\ val_mem tfibsegs m0 (PCv + 4) 4 MAXv /\ val_mem tfibsegs m0 (PCv + 8) 8 SZv.
Proof.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * c)) d) = PCv + d) by (intros d; cbn; unfold AFgk.PCv; lia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * c)) = PCv) by (cbn; unfold AFgk.PCv; lia).
unfold kcnt, AFgk.MAXv, AFgk.SZv. splits.
- rewrite <- EP0. eapply cell_stateZ; [apply In_acells_cache; unfold cache_cells; rewrite Hci; left; reflexivity | reflexivity].
- rewrite <- (EP 4). eapply cell_stateZ; [apply In_acells_cache; unfold cache_cells; rewrite Hci; right; left; reflexivity | reflexivity].
- rewrite <- (EP 8). eapply cell_stateZ; [apply In_acells_cache; unfold cache_cells; rewrite Hci; right; right; left; reflexivity | reflexivity].
Qed.
Lemma slot_vals : forall (i : nat) v, nth_error (pc_chunks (cache X c)) i = Some v -> val_mem tfibsegs m0 (PCv + 16 + 4 * Z.of_nat i) 4 (v / 16).
Proof.
intros i v Hi.
replace (PCv + 16 + 4 * Z.of_nat i) with (aeval B ly (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat i))) by (cbn; unfold AFgk.PCv; lia).
eapply cell_stateZ; [|reflexivity]. apply In_acells_cache. unfold cache_cells. rewrite Hci. do 3 right.
apply in_map_iff. exists (i, v). split; [reflexivity|].
assert (L : (i < length (pc_chunks (cache X c)))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
replace (i, v) with (nth i (combine (seq 0 (length (pc_chunks (cache X c)))) (pc_chunks (cache X c))) (0%nat, v)).
2:{ rewrite combine_nth by (rewrite length_seq; reflexivity). rewrite seq_nth by exact L. f_equal. exact (nth_error_nth _ _ _ Hi). }
apply nth_In. rewrite length_combine, length_seq. lia.
Qed.
Lemma region_vals :
val_mem tfibsegs m0 RGv 8 0 /\ val_mem tfibsegs m0 (RGv + 8) 8 0 /\ val_mem tfibsegs m0 (RGv + 16) 8 kold /\ val_mem tfibsegs m0 (RGv + 24) 8 kmf /\
val_mem tfibsegs m0 (RGv + 32) 8 (rg_alloc_user (reg X c)) /\ val_mem tfibsegs m0 (RGv + 40) 8 0 /\ val_mem tfibsegs m0 (RGv + 48) 8 (rg_mapped_user (reg X c)) /\
val_mem tfibsegs m0 (RGv + 56) 8 0 /\ val_mem tfibsegs m0 (RGv + 68) 1 0.
Proof.
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = RGv + d) by (intros d; cbn; unfold AFgk.RGv, AFgk.RIv; lia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = RGv) by (cbn; unfold AFgk.RGv, AFgk.RIv; lia).
unfold kold, kmf. repeat split.
- rewrite <- ER0. eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; left; reflexivity | reflexivity].
- rewrite <- (ER 8). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 1 right; left; reflexivity | reflexivity].
- rewrite <- (ER 16). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 2 right; left; reflexivity | reflexivity].
- rewrite <- (ER 24). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 3 right; left; reflexivity | reflexivity].
- rewrite <- (ER 32). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 4 right; left; reflexivity | reflexivity].
- rewrite <- (ER 40). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 5 right; left; reflexivity | reflexivity].
- rewrite <- (ER 48). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 6 right; left; reflexivity | reflexivity].
- rewrite <- (ER 56). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 7 right; left; reflexivity | reflexivity].
- rewrite <- (ER 68). eapply cell_stateZ; [apply In_acells_region; unfold region_cells; cbv zeta; do 8 right; left; reflexivity | reflexivity].
Qed.
Lemma val_mem_lo4 : forall m a w, 0 <= w < 2 ^ 64 -> val_mem tfibsegs m a 8 w -> val_mem tfibsegs m a 4 (w mod 2 ^ 32).
Proof.
intros m a w Hw H k Hk. rewrite (H k ltac:(lia)). do 2 f_equal. rewrite <- (le_byte_eq w). rewrite <- (le_byte_eq (w mod 2 ^ 32)).
rewrite <- (le_byte_split_lo (w mod 2 ^ 32) (w / 2 ^ 32) k); [| pose proof (Z.mod_pos_bound w (2 ^ 32)); lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] | exact Hk].
f_equal. pose proof (Z.div_mod w (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma const_vals : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfibsegs m0 (A_ALLOCATOR + 48) 8 RIv /\
val_mem tfibsegs m0 (A_ALLOCATOR + 40) 4 4294967295 /\
val_mem tfibsegs m0 0x9df78 8 0x135aa0 /\ val_mem tfibsegs m0 0x135aa0 8 4096 /\ val_mem tfibsegs m0 0x103a0 8 0xafffff00000fffff.
Proof.
pose proof AINST as AI. splits.
- replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (cbn; rewrite AI; reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- replace (A_ALLOCATOR + 48) with (aeval B ly (AInst o_rinfo)) by (cbn; rewrite AI; reflexivity).
replace RIv with (aeval B ly (ASp kRegionInfoOff)) by (cbn; unfold AFgk.RIv; lia). apply cell_sym. vm_compute. reflexivity.
- change 4294967295 with (4294967295 mod 2 ^ 32). apply val_mem_lo4; [lia|]. apply cell_lit. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
Qed.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent H0 mem a.
Proof.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin) | exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin)]. }
destruct (range_vis_mbyte B ly H0 mem e len (a - aeval B ly e) RV ltac:(lia)) as [b Hb].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb by lia. exact (mbyte_off_apresent H0 mem a b Hhi Hb).
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent H0 mem a.
Proof.
intros a Ha. pose proof HI as (_ & _ & F1 & F2 & _).
apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (apply in_or_app; right). do 3 right. left. reflexivity.
- cbn [aeval]. lia.
- exact (zone3_off_img _ _ a F1 Ha).
Qed.
Lemma rinfo_present : forall a, RGv <= a < RGv + 128 -> apresent H0 mem a.
Proof.
intros a Ha. pose proof derived as DR. pose proof Hc as Hcx.
apply (vis_present (ASp kRegionInfoOff) 4096).
- right. unfold aareas. do 3 (apply in_or_app; right). do 4 right. left. reflexivity.
- cbn [aeval]. unfold AFgk.RGv, AFgk.RIv in *. clear - Ha Hcx. numconst. lia.
- apply off_img_high. clear - Ha DR. numconst. lia.
Qed.
Lemma fa_present : forall a, FAv <= a < FAv + kmf -> apresent H0 mem a.
Proof.
intros a Ha. pose proof derived as DR. pose proof reg_facts as (_ & _ & [M0 M1] & _). pose proof Hc as Hcx.
apply (vis_present (ASp (region_off c + kFreeArrayOffset)) (rg_mapped_fa (reg X c))).
- right. unfold aareas. apply in_or_app; left. apply in_flat_map. exists c. split; [apply In_zseq; lia|]. right; left; reflexivity.
- cbn [aeval]. unfold AFgk.FAv, AFgk.RBv, kmf in *. clear - Ha. lia.
- apply off_img_high. unfold kmf in *. clear - Ha DR M0 M1. numconst. lia.
Qed.
Lemma stack_present : forall a, sp0 - KSTACK <= a < sp0 -> apresent H0 mem a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). unfold spZ in HP. exact HP. Qed.
Lemma word_of_present : forall a, (forall i, 0 <= i < 8 -> apresent H0 mem (a + i)) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs m0 a 8 w.
Proof.
intros a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m0 (a + Z.of_nat k) = Some b).
{ intros k Hk. apply apresent_mbyte. apply PR. lia. }
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
split; [lia|].
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YG0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YG0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m0 (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m0 (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.
Lemma junk_vals : exists j80 j88 jst,
(0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 j80) /\ (0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88) /\
(0 <= jst < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_cache + 2576) 8 jst).
Proof.
destruct (word_of_present (RGv + 80)) as (w0 & R0 & V0); [intros i Hi; apply rinfo_present; lia|].
destruct (word_of_present (RGv + 88)) as (w1 & R1 & V1); [intros i Hi; apply rinfo_present; lia|].
destruct (word_of_present (T + t_cache + 2576)) as (w2 & R2 & V2); [intros i Hi; apply thread_present; numconst; lia|].
exists w0, w1, w2. repeat split; assumption || lia.
Qed.
Section h.
Variables (j80 j88 jst : Z).
Hypothesis HJ80 : 0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 j80.
Hypothesis HJ88 : 0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88.
Hypothesis HJST : 0 <= jst < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_cache + 2576) 8 jst.
Local Notation E0 := (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst).
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgk.E2 ly regs c off kcnt kold kmf j80 j88 jst). Qed.
Lemma chunk_lit : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgk.REG0.
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR. pose proof reg_facts as RF. pose proof class_facts as KF.
pose proof cache_vals as (C1 & C2 & C3). pose proof const_vals as (V1 & V2 & V3 & V4 & V5 & V6). pose proof HJST as [J1 J2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
unfold AFgk.REG0, AFgk.R_STK_HI, AFgk.R_STK_LO, AFgk.R_PC, AFgk.R_JST, fatom8, flit8, flit4.
apply Forall_cons.
{ reg_intro. rewrite BV2. split; [clear - S1 S2 HIx; numconst; lia|]. split; [clear - S1 S2 HIx Usp; numconst; lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [clear - S1 S2 HIx Ho; numconst; lia|]. apply stack_present. clear - Ho. numconst. lia. }
apply Forall_cons.
{ reg_intro. rewrite BV2. split; [clear - S1 S2 HIx; numconst; lia|]. split; [clear - S1 S2 HIx Usp; numconst; lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [clear - S1 S2 HIx Ho; numconst; lia|]. apply stack_present. clear - Ho. numconst. lia. }
apply Forall_cons.
{ reg_intro. rewrite AFgk.EqPC. unfold w64. rewrite unsigned_lit_small by (clear - DR HIx; numconst; lia).
split; [clear - DR HIx; numconst; lia|]. split; [clear - DR HIx; numconst; lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); clear - DR Ho; numconst; lia|]. apply thread_present. clear - Ho DR. numconst. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 4 37%nat kcnt); [reflexivity | clear - RF KF; lia | rewrite Z.add_0_r; exact C1 | clear - RF KF; r4 | cbn; lia].
- apply (chunk_atom _ _ 4 38%nat MAXv); [reflexivity | clear - KF; lia | exact C2 | clear - KF; r4 | cbn; lia].
- apply (chunk_atom _ _ 8 39%nat SZv); [reflexivity | clear - KF; numconst; lia | exact C3 | clear - KF; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. rewrite AFgk.EqT. unfold w64. rewrite unsigned_lit_small by (clear - HIx; numconst; lia).
split; [clear - HIx; numconst; lia|]. split; [clear - HIx; numconst; lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); clear - Ho; numconst; lia|]. apply thread_present. clear - Ho. numconst. lia. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom _ _ 8 48%nat jst); [reflexivity | exact J1 | rewrite Z.add_assoc; exact J2 | r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom 0 _ 8 33%nat SB); [reflexivity | clear - DR; numconst; lia | rewrite Z.add_0_l; exact V1 | clear - DR; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom 0 _ 8 49%nat RIv); [reflexivity | clear - DR; numconst; lia | rewrite Z.add_0_l; exact V2 | clear - DR; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 4); [rewrite Z.add_0_l; exact V3 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V4 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V5 | cbn; lia | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V6 | cbn; lia | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgk.REG0.
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold AFgk.REG0, AFgk.R_STK_HI, AFgk.R_STK_LO, AFgk.R_PC, AFgk.R_JST, fatom8, flit8, flit4, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, AFgk.EqPC, AFgk.EqT. unfold w64. fold sp0. numconst. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgk.FFK).
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR. pose proof reg_facts as RF. pose proof class_facts as KF. pose proof off_facts as OFF.
pose proof HJ80 as [A1 _]. pose proof HJ88 as [A2 _]. pose proof HJST as [A3 _]. pose proof Hc as Hcx.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
pose proof HIx as (_ & _ & _ & _ & _ & _ & _ & _ & SAL & _ & _ & _ & _ & _ & TAL).
assert (T16 : exists q, T = 4096 * q) by (apply Z.mod_divide in TAL as [q Hq]; [|lia]; exists q; lia). destruct T16 as [qT HqT].
assert (PC16 : PCv mod 2 ^ 4 = 0).
{ unfold AFgk.PCv, t_cache. rewrite HqT. apply Z.mod_divide; [lia|]. exists (256 * qT + 13 + 5 * c). change (2 ^ 4) with 16. lia. }
assert (P16 : Pv mod 2 ^ 4 = 0).
{ destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _ & _ & _ & EP & _). rewrite EP, RB. destruct OFF as (_ & _ & O3 & _).
apply Z.mod_divide in SAL as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q3 Hq3]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 4096 + c * 2 ^ 28 + q3). change (2 ^ 4) with 16. lia. }
assert (RI12 : RIv mod 2 ^ 12 = 0).
{ destruct DR as (_ & _ & _ & _ & ERI & _). rewrite ERI. apply Z.mod_divide in SAL as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 16 + 2 ^ 25). unfold kRegionInfoOff. change (2 ^ 12) with 4096. lia. }
assert (RG7 : RGv mod 2 ^ 7 = 0).
{ destruct DR as (_ & _ & _ & _ & _ & ERG & _). rewrite ERG. pose proof RI12 as RI12'. apply Z.mod_divide in RI12' as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 32 + c). change (2 ^ 7) with 128. change (2 ^ 12) with 4096 in Hq. lia. }
assert (SLOT4 : AFgk.SLOTv ly c kcnt mod 2 ^ 2 = 0).
{ unfold AFgk.SLOTv, AFgk.PCv, t_cache. rewrite HqT. apply Z.mod_divide; [lia|]. exists (1024 * qT + 52 + 20 * c + 4 + AFgk.CNTPv c kcnt). change (2 ^ 2) with 4. lia. }
assert (DST2 : AFgk.DSTv ly c kold mod 2 ^ 2 = 0 /\ AFgk.SRCv ly c kcnt mod 2 ^ 2 = 0).
{ unfold AFgk.DSTv, AFgk.SRCv. destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & EFA & _). rewrite EFA, RB.
pose proof SAL as SAL'. apply Z.mod_divide in SAL' as [q Hq]; [|lia]. change (2 ^ 2) with 4. split.
- apply Z.mod_divide; [lia|]. exists (q * 16384 + c * 2 ^ 30 + 939524096 + kold). unfold kFreeArrayOffset. rewrite Hq. lia.
- apply Z.mod_divide; [lia|]. unfold AFgk.PCv, t_cache. rewrite HqT. exists (qT * 1024 + 52 + 20 * c + 4 + (kcnt - Nv)). lia. }
destruct DST2 as [DST2 SRC2].
assert (CNTP : 0 <= AFgk.CNTPv c kcnt < MAXv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RF KF e || clear - RF KF n; lia).
cbn [AFgk.FFK f_atoms atoms_ok]. numconst.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 HIx Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [reflexivity| | | |]. all: clear - CR0 HIx TAL; first [lia | change (2 ^ 12) with 4096; exact TAL]. }
split. { apply (AF 33%nat SB); [reflexivity| | | |]. all: clear - CR0 HIx DR SAL; first [lia | apply Z.mod_divide in SAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 16) with 65536; lia]. }
split. { apply (AF 34%nat Pv); [reflexivity| | | |]. all: clear - CR0 HIx DR OFF RF KF P16; first [lia | exact P16]. }
split. { apply (AF 35%nat c); [reflexivity| | | |]. all: clear - CR0 Hcx; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat PCv); [reflexivity| | | |]. all: clear - CR0 HIx DR PC16; first [lia | exact PC16]. }
split. { apply (AF 37%nat kcnt); [reflexivity| | | |]. all: clear - CR0 RF KF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat MAXv); [reflexivity| | | |]. all: clear - CR0 KF; first [lia | change (2 ^ 1) with 2; tauto]. }
split. { apply (AF 39%nat SZv); [reflexivity| | | |]. all: clear - CR0 KF; first [lia | destruct KF as (_ & K2 & _); apply Z.mod_divide in K2 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 5) with 32; lia]. }
split. { apply (AF 40%nat (AFgk.SLOTv ly c kcnt)); [reflexivity| | | |]. all: unfold AFgk.SLOTv in *; clear - CR0 HIx DR CNTP KF SLOT4; first [lia | exact SLOT4]. }
split. { apply (AF 41%nat RGv); [reflexivity| | | |]. all: clear - CR0 DR RG7; first [lia | exact RG7]. }
split. { apply (AF 42%nat kold); [reflexivity| | | |]. all: clear - CR0 RF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat kmf); [reflexivity| | | |]. all: clear - CR0 RF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 44%nat (AFgk.DSTv ly c kold)); [reflexivity| | | |]. all: unfold AFgk.DSTv in *; clear - CR0 DR RF KF DST2; first [lia | exact DST2]. }
split. { apply (AF 45%nat (AFgk.SRCv ly c kcnt)); [reflexivity| | | |]. all: unfold AFgk.SRCv in *; clear - CR0 HIx DR RF KF SRC2; first [lia | exact SRC2]. }
split. { apply (AF 46%nat j80); [reflexivity| | | |]. all: clear - CR0 A1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 47%nat j88); [reflexivity| | | |]. all: clear - CR0 A2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 48%nat jst); [reflexivity| | | |]. all: clear - CR0 A3; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 49%nat RIv); [reflexivity| | | |]. all: clear - CR0 DR RI12; first [lia | exact RI12]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgk.SS0 (restrict (w_H W) (mkst regs (w64 0x33970) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha2 & Ha3). rewrite (ts_tp _ TB) in Htp.
pose proof HI as (_ & _ & hT1 & hT2 & _).
rewrite restrict_mkst_fx. unfold AFgk.SS0, AFgk.SR0, sr_set. cbn [bv_eqb]. unfold AFgk.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate |] | intros XX; discriminate | cbn [sv_denot]; exact Ha1] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqC, Ha2. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqP, Ha3. unfold w64, AFgk.Pv. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH_ok : AFgk.free_hyps W ly regs mem c off kcnt kold kmf j80 j88 jst.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & _ & _ & Hnin & Hroom & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof reg_facts as RF. pose proof class_facts as KF. pose proof off_facts as OFF. pose proof derived as DR. pose proof HI as HIx.
pose proof region_vals as (R0 & _ & R16 & R24 & _). pose proof HJ80 as [A1 B1]. pose proof HJ88 as [A2 B2]. pose proof HJST as [A3 B3].
constructor.
- exact LO.
- exact IMG.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- split; [exact Hlo | exact Hhi].
- exact Hal.
- exact HPRES.
- exact Hc.
- clear - RF. unfold kcnt in *. lia.
- destruct OFF as (O1 & O2 & O3 & _). destruct RF as (_ & _ & _ & _ & AU & MU & _). split; [exact O1|]. split; [clear - O2 AU MU; lia | exact O3].
- intros a Ha. apply thread_present. unfold AFgk.SLOTv in Ha.
assert (CNTP : 0 <= AFgk.CNTPv c kcnt < MAXv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RF KF e || clear - RF KF n; lia).
clear - Ha DR KF CNTP. numconst. lia.
- clear - A1 A2 A3. tauto.
- intros Hf. pose proof Hroom as RM.
assert (LEN : kold + kcnt <= Z.of_nat (length (class_elems X c))).
{ rewrite class_elems_eq, !length_app, !Nat2Z.inj_add, (fa_elems_length (class_size c) (rg_free (reg X c)) (wr_runs _ _ _ _ _ _ CLS)). unfold kold, kcnt. clear. lia. }
unfold kold, kcnt, kmf in *. unfold AFgk.Nv, AFgk.MAXv in *.
split; [clear - RF; lia|]. split; [pose proof (bslack_le c 0 ltac:(lia)) as BS; pose proof (YG0l.return_room _ _ _ _ X c WF ltac:(pose proof Hc; lia) RM) as NEV  ; unfold kold, kcnt, kmf in *; clear - RF KF Hf RM LEN BS NEV; unfold EV_MAX in *; nia|].
split; [clear - RF; lia|]. split; [exact rinfo_present|].
split; [exact R0|]. split; [exact R16|]. split; [exact R24|]. split; [exact B1|]. split; [exact B2|]. split.
+ intros a Ha. apply fa_present. unfold AFgk.DSTv, AFgk.Nv, AFgk.MAXv, kmf in *. pose proof (bslack_le c 0 ltac:(lia)) as BS. pose proof (YG0l.return_room _ _ _ _ X c WF ltac:(pose proof Hc; lia) RM) as NEV  . unfold kold, kcnt, kmf in *. clear - Ha RF KF Hf RM LEN BS NEV. unfold EV_MAX in *. nia.
+ intros a Ha. apply thread_present. unfold AFgk.SRCv, AFgk.Nv, AFgk.MAXv in Ha. clear - Ha DR KF RF Hf. numconst. lia.
- exact SEED_ok.
Qed.
End h.
End g.
End f.
