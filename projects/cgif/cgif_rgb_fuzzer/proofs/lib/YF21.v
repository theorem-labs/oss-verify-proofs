(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0k YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0u YF0w YF2d YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF1e YF0q YF2l YF2m YF30 YF31 YF1y YF20 YF1o YF1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma same_io_wvb2 : forall md md' mat mat', same_io (with_vm_backing (m_vm_lazy md) mat md) md' -> same_io md (with_vm_backing (m_vm_lazy md') mat' md').
Proof.
intros [fd [maps lazy mat0] io fs proc lim tm] [fd' [maps' lazy' mat0'] io' fs' proc' lim' tm'] mat mat'. unfold same_io. cbn. intros (I1 & I2 & I3 & I4). repeat split; congruence.
Qed.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Hypothesis Hl0 : pc_chunks (cache X kBatchClass) = [].
Hypothesis R1 : tfx_refill_spec B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). img_exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). img_exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). img_exact Hnq. Qed.
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma HQL : qloose X.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL). img_exact QL. Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). img_exact (img_cover_of_ledger ly X md LED). Qed.
Local Notation jst := (YF1k.jst ly W mem).
Local Notation cell_sym := (YF1k.cell_sym B TB ly X W mem M).
Local Notation cell_lit := (YF1k.cell_lit B TB ly X W mem M).
Local Notation cell_state := (YF1k.cell_state B ly X W mem M).
Local Notation cell_stateZ := (YF1k.cell_stateZ B ly X W mem M).
Local Notation val_mem_present := (YF1k.val_mem_present W mem).
Local Notation jst_val := (YF1k.jst_val B ly X W mem sp0 M HSP).
Local Notation root_vals := (YF1k.root_vals B ly X W mem M).
Local Notation count_val := (YF1k.count_val B ly X W mem M).
Local Notation u_facts := (YF1k.u_facts B ly X W mem k M Hk).
Local Notation u_zone := (YF1k.u_zone B ly X W mem k M IMG Hk).
Local Notation q_facts := (YF1k.q_facts B ly X W mem sp0 k M HSP Hk HQL).
Local Notation last_facts := (YF1k.last_facts B ly X W mem sp0 M HSP HNB).
Local Notation chunk_lit := (YF1k.chunk_lit W mem).
Local Notation chunk_lit_at := (YF1k.chunk_lit_at W mem).
Local Notation chunk_atom := (YF1k.chunk_atom W mem).
Local Notation val_mem_writable := (YF1k.val_mem_writable W mem).
Local Notation GEO := (YF1k.GEO B ly X W mem M).
Lemma HI0 : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
kHighMemBeg <= region_base ly kBatchClass /\ region_base ly kBatchClass + 2 ^ 32 <= ASAN_CEIL /\ region_base ly kBatchClass mod 65536 = 0.
Proof.
pose proof (lo_high ly LO) as [P1 P2].
pose proof (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear; unfold kThreadObjSize; img_lia)) IT (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)) as T1.
assert (T2 : T + kThreadObjSize <= ASAN_CEIL) by (img_try (clear - T1; unfold zone3 in T1; img_lia)). clear IT.
pose proof (lo_top ly LO) as (_ & _ & _ & S4 & _ & _ & S7). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1' & R2 & R3 & R4 & R5).
splits; assumption.
Qed.
Ltac offw := first [ img_lia | img_apply off_img_high; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; img_lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI0)))); unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, YF2l.CSLv, YF2m.CSLv in *; img_lia ].
Local Notation E0 := (YF2l.E0 ly regs u nn q 0 0 jst).
Local Notation QSZv := (YF2l.QSZv q).
Local Notation QFv := (YF2l.QFv ly q).
Local Notation QLv := (YF2l.QLv ly q).
Local Notation QBv := (YF2l.QBv q).
Local Notation NBv := (YF2l.NBv ly 0).
Local Notation CSLv := (YF2l.CSLv ly 0).
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2l.E2 ly regs u nn q 0 0 jst). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. img_refl. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. img_refl. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. img_refl. Qed.
Lemma EqQSZ : ew E0 36 = w64 QSZv. Proof. img_refl. Qed.
Lemma EqQF : ew E0 37 = w64 QFv. Proof. img_refl. Qed.
Lemma EqQL : ew E0 38 = w64 QLv. Proof. img_refl. Qed.
Lemma EqQB : ew E0 39 = w64 QBv. Proof. img_refl. Qed.
Lemma EqCNT : ew E0 40 = w64 0. Proof. img_refl. Qed.
Lemma EqCP : ew E0 41 = w64 0. Proof. img_refl. Qed.
Lemma EqJST : ew E0 42 = w64 jst. Proof. img_refl. Qed.
Lemma EqNB : ew E0 43 = w64 NBv. Proof. img_refl. Qed.
Lemma EqCSL : ew E0 44 = w64 CSLv. Proof. img_refl. Qed.
Lemma count0 : val_mem tfxsegs m0 (T + t_cache + 1920) 4 0.
Proof. pose proof count_val as C. rewrite Hl0 in C. destruct (st_cache_inited X); img_exact C. Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4 := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Local Ltac lit_region :=
reg_intro; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2l.REG0.
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hR1 & hR2 & _). pose proof HSP as [S1 S2].
pose proof root_vals as (V1 & V2 & V3 & V4). pose proof count0 as C1. pose proof jst_val as [J1 J1R]. pose proof q_facts as (Qa & Qb & Qc & Qd). assert (Qc0 : 0 <= QSZv) by (img_try (unfold YF2l.QSZv; clear; img_lia)).
assert (QLR : 0 <= QLv < ASAN_CEIL).
{ unfold YF2l.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [img_try (ceil; unfold ASAN_CEIL; img_lia)|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & _). unfold YF2l.QLv in L1, L2. rewrite Hrev in L1, L2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. img_lia. }
pose proof u_facts as (Ua & Ub & Uc & Ud).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hR1, hR2, S1, S2, QLR, Qb, Qd, Ua, Ub.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold YF2l.REG0, YF2l.R_ROOT, YF2l.R_CNT, YF2l.R_JST, flit4, flit8, fatom8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- 64)); [img_try (rewrite E2; img_refl) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia) | img_try (img_apply HPRES; clear -Ha; unfold QSTACK in *; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_qc in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [img_try (img_apply (val_mem_writable _ _ _ _ V1)) | img_try (destruct (Z_lt_le_dec o 96); [img_apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [img_apply (val_mem_writable _ _ _ _ V3) | img_apply (val_mem_writable _ _ _ _ V4)]])];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom E0 _ _ 8 36%nat 0 QSZv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact V1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom E0 _ _ 8 37%nat 0 QFv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V2 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom E0 _ _ 8 38%nat 0 QLv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V3 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom E0 _ _ 8 39%nat 0 QBv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V4 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom E0 _ _ 4 40%nat 0 0); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact C1 | img_lia]) | img_try (r4) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom E0 _ _ 8 42%nat 0 jst); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J1 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom E0 0 _ 8 33%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | | img_try (r8) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TB); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
do 3 (img_apply Forall_cons; [img_try (lit_region)|]). img_apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2l.REG0.
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents. unfold YF2l.REG0, YF2l.R_ROOT, YF2l.R_CNT, YF2l.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
fold sp0. rewrite !unsigned_lit_small by img_lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; img_lia | clear - hT1 CR0; img_lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2l.FFQ).
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hR1 & hR2 & hR3). pose proof HSP as [S1 S2].
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as (Qa & Qb & Qc & Qd). pose proof jst_val as [_ JR].
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QLR : 0 <= QLv < ASAN_CEIL /\ QLv mod 8192 = 0).
{ unfold YF2l.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [img_try (ceil; unfold ASAN_CEIL; split; [img_lia | img_refl])|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & _). unfold YF2l.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [img_lia | img_try (img_exact L3)]. }
destruct QLR as [QLR QLA].
assert (ENB : NBv = region_base ly kBatchClass) by (img_try (unfold YF2l.NBv, region_base; img_lia)).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hR1, hR2, S1, S2, U1, U2, QLR, Qb, Qd.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2l.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EqT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat SB); [img_try (img_exact EqSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 34%nat u); [img_try (img_exact EqU)| | | |]. all: clear - CR0 U1 U2 U3 U4; first [img_lia | img_change (2 ^ 4) with 16; img_exact U3]. }
split. { img_apply (AF 35%nat nn); [img_try (img_exact EqN)| | | |]. all: clear - CR0 U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat QSZv); [img_try (img_exact EqQSZ)| | | |]. all: clear - CR0 Qc; unfold YF2l.QSZv in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat QFv); [img_try (img_exact EqQF)| | | |]. all: clear - CR0 Qd; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat QLv); [img_try (img_exact EqQL)| | | |]. all: clear - CR0 QLR QLA; first [img_lia | img_change (2 ^ 13) with 8192; img_exact QLA]. }
split. { img_apply (AF 39%nat QBv); [img_try (img_exact EqQB)| | | |]. all: clear - CR0 Qa Qb U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat 0); [img_try (img_exact EqCNT)| | | |]. all: clear; first [img_lia | img_refl]. }
split. { img_apply (AF 41%nat 0); [img_try (img_exact EqCP)| | | |]. all: clear; first [img_lia | img_refl]. }
split. { img_apply (AF 42%nat jst); [img_try (img_exact EqJST)| | | |]. all: clear - CR0 JR; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 43%nat NBv); [img_try (img_exact EqNB)| | | |]. all: rewrite ?ENB; clear - CR0 hR1 hR2 hR3; first [img_lia | img_change (2 ^ 13) with 8192; apply Z.mod_divide in hR3 as [c Hc]; [|img_lia]; rewrite Hc; img_apply Z.mod_divide; [img_lia|]; exists (8 * c); img_lia]. }
split; [|img_try (img_exact I)]. { img_apply (AF 44%nat CSLv); [img_try (img_exact EqCSL)| | | |]. all: clear - CR0 hT1 hT2 TAL; unfold YF2l.CSLv, t_cache in *;
first [img_lia | img_change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|img_lia]; rewrite Hc; img_apply Z.mod_divide; [img_lia|]; exists (1024 * c + 535); img_lia]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2l.SS0 (restrict (w_H W) (mkst regs (w64 (0x35dd8 + D_150)) mem (seg_rom tfxsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha3 & Ha4 & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
rewrite restrict_mkst_fx. unfold YF2l.SS0, YF2l.SR0, sr_set. cbn [bv_eqb]. unfold YF2l.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Htp] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q 0 0 jst). rewrite EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q 0 0 jst). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q 0 0 jst). rewrite EqU, Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q 0 0 jst). rewrite EqN, Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH0_ok : YF2l.free_hyps W ly regs mem u nn q 0 0 jst.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as QF. pose proof jst_val as [_ JR].
constructor.
- img_exact LO.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- img_exact Hra4.
- split; [img_try (img_exact Hlo) | img_try (img_exact Hhi)].
- img_exact Hal.
- img_exact HPRES.
- split; [img_try (img_exact u_zone) | img_try (img_exact U3)].
- img_exact IMG.
- img_exact U4.
- img_exact QF.
- img_exact HNB.
- intros lb initr Hrev. pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). splits; assumption.
- img_lia.
- intros Hc. exfalso. img_lia.
- img_exact JR.
- img_exact SEED_ok.
Qed.
Lemma val_mem_agree : forall (Hh : word -> bool) m m' a (n : nat) v i,
val_mem tfxsegs (mrestrict Hh m) a n v -> val_mem tfxsegs (mrestrict Hh m') a n v -> 0 <= i < Z.of_nat n ->
aview tfxsegs Hh m' (a + i) = aview tfxsegs Hh m (a + i).
Proof.
intros Hh m m' a n v i V V' Hi. unfold aview.
pose proof (V (Z.to_nat i) ltac:(img_lia)) as E. pose proof (V' (Z.to_nat i) ltac:(img_lia)) as E'. rewrite Z2Nat.id in E, E' by img_lia.
rewrite E, E'. img_refl.
Qed.
Lemma val_mem_some : forall (Hh : word -> bool) m a (n : nat) v i,
val_mem tfxsegs (mrestrict Hh m) a n v -> 0 <= i < Z.of_nat n -> aview tfxsegs Hh m (a + i) <> None.
Proof.
intros Hh m a n v i V Hi. unfold aview. pose proof (V (Z.to_nat i) ltac:(img_lia)) as E. rewrite Z2Nat.id in E by img_lia. rewrite E. discriminate.
Qed.
Lemma aview_raw_some : forall (Hh : word -> bool) m a, 0 <= a < 2 ^ 64 -> aview tfxsegs Hh m a <> None -> TFX_IMG_END <= a -> m (w64 a) <> None /\ Hh (w64 a) = false.
Proof.
intros Hh m a Ha Hv Himg. unfold aview, mbyte, mrestrict in Hv. unfold w64.
rewrite (seg_rom_none_high a ltac:(img_lia)) in Hv.
destruct (Hh (Z_to_bv 64 a)) eqn:Hx; [img_try (exfalso; img_apply Hv; img_refl)|].
destruct (m (Z_to_bv 64 a)) eqn:E; [img_try (split; [congruence | img_refl]) | img_try (exfalso; img_apply Hv; img_refl)].
Qed.
Section f.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat : list word).
Let md1 := with_vm_backing (m_vm_lazy md) mat md.
Hypothesis R_ra : getr regs1 1 = w64 (0x35f2c + D_150).
Hypothesis R_sp : getr regs1 2 = w64 (sp0 - 64).
Hypothesis R_gp : getr regs1 3 = getr regs 3.
Hypothesis R_tp : getr regs1 4 = getr regs 4.
Hypothesis R_a0 : getr regs1 10 = w64 (T + t_cache).
Hypothesis R_a1 : getr regs1 11 = w64 (T + t_cache + 1920).
Hypothesis R_a2 : getr regs1 12 = w64 (0xa6b58 + D_10c0).
Hypothesis R_a3 : getr regs1 13 = w64 24.
Hypothesis MQ1 : YF2l.MEQ0 ly regs mem mem1.
Hypothesis PR1 : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a.
Hypothesis V1 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc) 8 QSZv.
Hypothesis V2 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 8) 8 QFv.
Hypothesis V3 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 16) 8 QLv.
Hypothesis V4 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 24) 8 QBv.
Hypothesis V5 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_cache + 1920) 4 0.
Hypothesis V6 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_cache_stats + 16) 8 jst.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> aview tfxsegs (w_H W) mem1 a = aview tfxsegs (w_H W) mem a.
Proof.
intros a Ha Hs. pose proof root_vals as (W1 & W2 & W3 & W4). pose proof count0 as W5. pose proof jst_val as [W6 _].
assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
destruct (EM (T + t_qc) (T + t_qc + 8)) as [C|C1]; [img_try (replace a with (T + t_qc + (a - (T + t_qc))) by img_lia; img_apply (val_mem_agree _ _ _ _ 8 _ _ W1 V1); img_lia)|].
destruct (EM (T + t_qc + 8) (T + t_qc + 16)) as [C|C2]; [img_try (replace a with (T + t_qc + 8 + (a - (T + t_qc + 8))) by img_lia; img_apply (val_mem_agree _ _ _ _ 8 _ _ W2 V2); img_lia)|].
destruct (EM (T + t_qc + 16) (T + t_qc + 24)) as [C|C3]; [img_try (replace a with (T + t_qc + 16 + (a - (T + t_qc + 16))) by img_lia; img_apply (val_mem_agree _ _ _ _ 8 _ _ W3 V3); img_lia)|].
destruct (EM (T + t_qc + 24) (T + t_qc + 32)) as [C|C4]; [img_try (replace a with (T + t_qc + 24 + (a - (T + t_qc + 24))) by img_lia; img_apply (val_mem_agree _ _ _ _ 8 _ _ W4 V4); img_lia)|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C5]; [img_try (replace a with (T + t_cache + 1920 + (a - (T + t_cache + 1920))) by img_lia; img_apply (val_mem_agree _ _ _ _ 4 _ _ W5 V5); img_lia)|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C6]; [img_try (replace a with (T + t_cache_stats + 16 + (a - (T + t_cache_stats + 16))) by img_lia; img_apply (val_mem_agree _ _ _ _ 8 _ _ W6 V6); img_lia)|].
img_apply aview_same. img_apply MQ1. rewrite unsigned_lit_small by img_exact Ha. unfold YF2l.WIN0, YF2l.WINT. fold sp0. clear - Hs C1 C2 C3 C4 C5 C6. img_lia.
Qed.
Lemma PRES1 : forall a, sp0 - QSTACK <= a < sp0 -> apresent (w_H W) mem1 a.
Proof.
intros a Ha. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & _ & HPRES & _). unfold spZ in *. fold sp0 in Hlo, HPRES.
destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb]; [|img_try (img_apply PR1; img_lia)].
img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Ha)]. img_apply MQ1.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _). pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _). pose proof HSP as [S1 S2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha S1 hS1 Usp; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
unfold YF2l.WIN0, YF2l.WINT. fold sp0. clear - Ha Hb G_TS S1 S2 hT1 hT2. unfold QSTACK, kThreadObjSize, t_qc, t_cache, t_cache_stats in *. img_lia.
Qed.
Lemma VIS_T : forall a, YF2l.WINT ly a -> aview tfxsegs (w_H W) mem1 a <> None.
Proof.
intros a Hw. unfold YF2l.WINT in Hw.
assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
destruct (EM (T + t_qc) (T + t_qc + 8)) as [C|C1]; [img_try (replace a with (T + t_qc + (a - (T + t_qc))) by img_lia; img_apply (val_mem_some _ _ _ 8 _ _ V1); img_lia)|].
destruct (EM (T + t_qc + 8) (T + t_qc + 16)) as [C|C2]; [img_try (replace a with (T + t_qc + 8 + (a - (T + t_qc + 8))) by img_lia; img_apply (val_mem_some _ _ _ 8 _ _ V2); img_lia)|].
destruct (EM (T + t_qc + 16) (T + t_qc + 24)) as [C|C3]; [img_try (replace a with (T + t_qc + 16 + (a - (T + t_qc + 16))) by img_lia; img_apply (val_mem_some _ _ _ 8 _ _ V3); img_lia)|].
destruct (EM (T + t_qc + 24) (T + t_qc + 32)) as [C|C4]; [img_try (replace a with (T + t_qc + 24 + (a - (T + t_qc + 24))) by img_lia; img_apply (val_mem_some _ _ _ 8 _ _ V4); img_lia)|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C5]; [img_try (replace a with (T + t_cache + 1920 + (a - (T + t_cache + 1920))) by img_lia; img_apply (val_mem_some _ _ _ 4 _ _ V5); img_lia)|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C6]; [img_try (replace a with (T + t_cache_stats + 16 + (a - (T + t_cache_stats + 16))) by img_lia; img_apply (val_mem_some _ _ _ 8 _ _ V6); img_lia)|].
exfalso. clear - Hw C1 C2 C3 C4 C5 C6. img_lia.
Qed.
Lemma AR1 : AR tfxsegs B ly X W mem1 md1.
Proof.
destruct ENQ as (HAR & _). pose proof HSP as [S1 S2]. pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply (AR_frame_law_ok tfxsegs B ly X W mem md mem1 md1 HAR).
- intros a Ha Ho. img_apply AG1; [img_try (img_exact Ha)|]. intros Hs. img_apply (AR_stack_law_ok tfxsegs B ly X W mem md a HAR); [|img_try (img_exact Ho)]. clear - Hs S1 S2. unfold QSTACK in *. img_lia.
- intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem1 x); discriminate)|].
destruct (mem1 x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (Z_lt_le_dec a' (sp0 - 64)) as [Hb|Hb]; [|img_try (destruct (Z_lt_le_dec a' sp0) as [Hc|Hc])].
2:{ destruct (PR1 a' ltac:(img_lia)) as [_ [bb Hbb]]. unfold w64 in Hbb. rewrite Ex in Hbb. congruence. }
all: pose proof (AG1 a' Ha' ltac:(img_lia)) as A; unfold aview, mbyte, mrestrict in A; rewrite Ex, Hx, E', E0, ROM in A; cbn in A; discriminate.
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Hb Hx. img_apply (MQ1 (w64 a)). assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
unfold w64. rewrite unsigned_lit_small by img_exact Ha'. intros Hw. unfold YF2l.WIN0 in Hw. fold sp0 in Hw. destruct Hw as [Hw|Hw].
+ destruct (PR1 a Hw) as [Hh _]. unfold w64 in Hh, Hx. rewrite Hx in Hh. discriminate.
+ destruct (aview_raw_some (w_H W) mem1 a Ha' (VIS_T a Hw) ltac:(img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia))) as [_ Hh].
unfold w64 in Hh, Hx. rewrite Hx in Hh. discriminate.
Qed.
Lemma REFILL_PRE : refill_pre B ly X W regs1 mem1 md1 kBatchClass.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES. pose proof HSP as [S1 S2]. pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (SP1 : spZ regs1 = sp0 - 64).
{ unfold spZ. rewrite R_sp. unfold w64. img_apply unsigned_lit_small. clear - Usp S1 hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. img_lia. }
unfold refill_pre. rewrite SP1. unfold raZ. rewrite R_ra, R_gp, R_tp, R_a0, R_a1, R_a2, R_a3.
split; [img_try (img_exact AR1)|]. split; [img_try (img_exact Hbud)|]. split; [img_try (img_exact Hpev)|]. split; [img_try (img_exact QL)|].
split; [img_try ((img_case; vm_compute); img_refl)|]. split; [img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)|].
split; [img_try (clear - Hal; replace (sp0 - 64) with (sp0 + (-4) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal)|].
split; [img_try (clear - S1; unfold QSTACK, RSTACK in *; img_lia)|]. split; [img_lia|].
split; [img_try (intros a Ha; img_apply PRES1; clear - Ha; unfold QSTACK, RSTACK in *; img_lia)|].
split; [img_try (img_exact Hgp)|]. split; [img_try (img_exact Htp)|]. split; [img_refl|]. split; [img_try (unfold kBatchClass; f_equal; img_lia)|].
split; [img_refl|]. split; [img_refl|]. split; [img_try (unfold kBatchClass; img_lia) | img_try (img_exact Hl0)].
Qed.
End f.
Lemma amreal_spin_sj {R} : forall pc (W5 : world tfxsegs) c (Q : R -> world tfxsegs -> config -> Prop),
SRr tfxsegs W5 c (fun W' c' => is_self_jump tfxsegs (cfg_ms c') = true) -> amreal tfxsegs (ISpin pc) W5 c Q.
Proof.
clear. intros pc W5 c Q H. cbn [amreal]. intros HI. img_apply (H false HI t_nil). intros W' c' _ HI' HJ. img_apply srz_spinning.
split; [img_try (img_apply is_self_jump_to_spin; img_exact HJ) | img_try (img_exact (AI_halted _ _ _ _ HI'))].
Qed.
Lemma SPIN : forall (W5 : world tfxsegs) regs5 mem5 md5 mat5 X5,
ARm B ly X5 (aview tfxsegs (w_H W5) mem5) -> getr regs5 10 = w64 0 ->
SRr tfxsegs W5 (mkCfg (mkst regs5 (w64 (0x35f2c + D_150)) mem5 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md5) mat5 md5))
(fun W' c' => is_self_jump tfxsegs (cfg_ms c') = true).
Proof.
intros W5 regs5 mem5 md5 mat5 X5 M5 HA0. pose proof Hwx_tfa as Hwx.
assert (HS : st_ok tfxsegs (Ereg regs5 (@nil word))
(mkSS (0x35f2c + D_150) (sr_set sr_atoms 10%bv (SLit 0)) [flit8 (0xa21a0 + D_10f0) 1; flit8 (0xa21a8 + D_10f0) (0x13bcdc + D_10c0); flit4 (0x13bcdc + D_10c0) 0] None (mkFacts [] [] []))
(restrict (w_H W5) (mkst regs5 (w64 (0x35f2c + D_150)) mem5 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold sr_set. cbn [bv_eqb]. unfold w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros XX; discriminate) | img_try (cbn [sv_denot]; img_exact HA0)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. unfold flit4, flit8.
repeat (img_apply Forall_cons; [img_try (unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val];
split; [img_lia|]; split; [img_lia|]; split; [intros o Ho; img_lia|];
repeat (img_apply Forall_cons; [img_apply (YF1k.chunk_lit W5 mem5); [img_apply (YF1k.cell_lit B TB ly X5 W5 mem5 M5); (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia] |]); img_apply Forall_nil) |]).
img_apply Forall_nil.
- img_apply pairwise_disjoint_of_extents. unfold flit4, flit8, extent_of_region. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [img_try (img_exact I) | img_try (split; img_exact I)]. }
srr_run_to_sh tfxtbl_rtF_ok HS (0x35f68 + D_150).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W5) _ _ _ HS eq_refl) as Hsh. cbn [ss_pc] in Hsh.
img_apply SRr_ret. cbn [cfg_ms]. rewrite Hsh. unfold is_self_jump. cbn [ms_svc_pending ms_pc YK11.mkst].
unfold w64. unfold ms_pc. cbn [ms_pc_val YK11.mkst]. rewrite (tfxtbl_rtF_ok (0x35f68 + D_150) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl.
Qed.
Lemma val_mem_xfer : forall (Hh Hh' : word -> bool) m m' a (n : nat) v,
(forall i, 0 <= i < Z.of_nat n -> aview tfxsegs Hh' m' (a + i) = aview tfxsegs Hh m (a + i)) ->
val_mem tfxsegs (mrestrict Hh m) a n v -> val_mem tfxsegs (mrestrict Hh' m') a n v.
Proof.
clear. intros Hh Hh' m m' a n v AG V kk Hk. rewrite <- (V kk Hk). img_apply (YF2m.aview_eq_mbyte Hh Hh' m m'). img_apply AG. img_lia.
Qed.
Section h.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat : list word).
Let md1 := with_vm_backing (m_vm_lazy md) mat md.
Hypothesis R_ra : getr regs1 1 = w64 (0x35f2c + D_150).
Hypothesis R_sp : getr regs1 2 = w64 (sp0 - 64).
Hypothesis R_gp : getr regs1 3 = getr regs 3.
Hypothesis R_tp : getr regs1 4 = getr regs 4.
Hypothesis R_s0 : getr regs1 8 = w64 (T + t_cache + 1920).
Hypothesis R_s1 : getr regs1 9 = w64 (T + t_cache).
Hypothesis R_s2 : getr regs1 18 = w64 (u - 16).
Hypothesis R_s3 : getr regs1 19 = w64 (T + t_qc).
Hypothesis R_s4 : getr regs1 20 = getr regs 12.
Hypothesis R_s5 : getr regs1 21 = w64 nn.
Hypothesis R_hi : forall r : bv 5, In r [22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r.
Hypothesis MQ1 : YF2l.MEQ0 ly regs mem mem1.
Hypothesis PR1 : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a.
Hypothesis F1 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 8) 8 (bv_unsigned (getr regs 1)).
Hypothesis F2 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 16) 8 (bv_unsigned (getr regs 8)).
Hypothesis F3 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 24) 8 (bv_unsigned (getr regs 9)).
Hypothesis F4 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 32) 8 (bv_unsigned (getr regs 18)).
Hypothesis F5 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 40) 8 (bv_unsigned (getr regs 19)).
Hypothesis F6 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 48) 8 (bv_unsigned (getr regs 20)).
Hypothesis F7 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 56) 8 (bv_unsigned (getr regs 21)).
Hypothesis G1 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc) 8 QSZv.
Hypothesis G2 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 8) 8 QFv.
Hypothesis G3 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 16) 8 QLv.
Hypothesis G4 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_qc + 24) 8 QBv.
Hypothesis G5 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_cache + 1920) 4 0.
Hypothesis G6 : val_mem tfxsegs (mrestrict (w_H W) mem1) (T + t_cache_stats + 16) 8 jst.
Variables (W5 : world tfxsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (X1 : astate).
Hypothesis POST : acall_post tfxsegs B RSTACK ly X W regs1 mem1 md1 (fun _ => False) ly X1 W5 regs' mem' md'.
Hypothesis RO : regs_only X X1.
Hypothesis CI : st_cache_inited X1 = true.
Hypothesis HA0 : getr regs' 10 = w64 1.
Variables (o1 : Z) (l1' : list Z).
Hypothesis El1 : pc_chunks (cache X1 kBatchClass) = o1 :: l1'.
Local Notation l1 := (o1 :: l1').
Local Notation rd5 := (aview tfxsegs (w_H W5) mem').
Local Notation m5 := (mrestrict (w_H W5) mem').
Local Notation q1 := (st_qthread X1).
Definition cnt1 : Z := Z.of_nat (length l1).
Definition coff1 : Z := last l1 0.
Local Notation jst1 := (YF1k.jst ly W5 mem').
Local Notation ra0 := (bv_unsigned (getr regs 1)).
Local Notation s00 := (bv_unsigned (getr regs 8)).
Local Notation s10 := (bv_unsigned (getr regs 9)).
Local Notation s20 := (bv_unsigned (getr regs 18)).
Local Notation s30 := (bv_unsigned (getr regs 19)).
Local Notation s40 := (bv_unsigned (getr regs 20)).
Local Notation s50 := (bv_unsigned (getr regs 21)).
Lemma M1 : ARm B ly X1 rd5. Proof. img_exact (proj1 (proj1 POST)). Qed.
Lemma Hk1 : In k (st_chunks X1). Proof. destruct RO as (Rck & _). rewrite Rck. img_exact Hk. Qed.
Lemma Hq1 : st_qthread X1 = st_qthread X. Proof. destruct RO as (_ & _ & _ & _ & Rqt & _). img_exact Rqt. Qed.
Lemma HQL1 : qloose X1.
Proof. destruct RO as (Rck & _ & _ & _ & Rqt & Rqg & _). pose proof HQL as Q0. unfold qloose, quar_n, queued_n, q_items, all_batches in *. rewrite Rck, Rqt, Rqg. img_exact Q0. Qed.
Lemma HNB1 : need_new_batch (st_qthread X1) = true. Proof. rewrite Hq1. img_exact HNB. Qed.
Lemma Hl1ne : l1 <> []. Proof. discriminate. Qed.
Local Notation cell_sym1 := (YF1k.cell_sym B TB ly X1 W5 mem' M1).
Local Notation cell_lit1 := (YF1k.cell_lit B TB ly X1 W5 mem' M1).
Local Notation jst_val1 := (YF1k.jst_val B ly X1 W5 mem' sp0 M1 HSP).
Local Notation root_vals1 := (YF1k.root_vals B ly X1 W5 mem' M1).
Local Notation u_facts1 := (YF1k.u_facts B ly X1 W5 mem' k M1 Hk1).
Local Notation u_zone1 := (YF1k.u_zone B ly X1 W5 mem' k M1 IMG Hk1).
Local Notation q_facts1 := (YF1k.q_facts B ly X1 W5 mem' sp0 k M1 HSP Hk1 HQL1).
Local Notation last_facts1 := (YF1k.last_facts B ly X1 W5 mem' sp0 M1 HSP HNB1).
Local Notation chunk_lit1 := (YF1k.chunk_lit W5 mem').
Local Notation chunk_atom1 := (YF1k.chunk_atom W5 mem').
Local Notation val_mem_writable1 := (YF1k.val_mem_writable W5 mem').
Local Notation HI1 := (YF1k.HI B ly X1 W5 mem' sp0 M1 HSP IMG l1 El1 Hl1ne).
Local Notation cache_vals1 := (YF1k.cache_vals B ly X1 W5 mem' M1 l1 El1 Hl1ne).
Local Notation hit_facts1 := (YF1k.hit_facts B ly X1 W5 mem' sp0 M1 HSP IMG HNB1 l1 El1 Hl1ne).
Local Notation ER := (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50).
Local Notation QSZ1 := (YF2m.QSZv q1).
Local Notation QF1 := (YF2m.QFv ly q1).
Local Notation QL1 := (YF2m.QLv ly q1).
Local Notation QB1 := (YF2m.QBv q1).
Local Notation CP1 := (YF2m.CPv coff1).
Local Notation NB1 := (YF2m.NBv ly coff1).
Local Notation CSL1 := (YF2m.CSLv ly cnt1).
Lemma SP' : getr regs' 2 = w64 (sp0 - 64).
Proof. destruct POST as (_ & _ & _ & CS & _). rewrite <- R_sp. img_exact (CS 2 ltac:(img_try (unfold acallee_saved; img_lia))). Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. img_apply u64_range. Qed.
Lemma SPv : bv_unsigned (getr regs' 2) = sp0 - 64.
Proof. rewrite SP'. unfold w64. img_apply unsigned_lit_small. pose proof HSP as [S1 _]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. img_lia. Qed.
Lemma CSV : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs1 r.
Proof. intros r Hr. destruct POST as (_ & _ & _ & CS & _). rewrite <- (Z_to_bv_bv_unsigned 5 r) at 1 2. img_exact (CS (bv_unsigned r) Hr). Qed.
Lemma FRAME_AG : forall a, sp0 - 64 <= a < sp0 -> aview tfxsegs (w_H W5) mem' a = aview tfxsegs (w_H W) mem1 a.
Proof.
intros a Ha. destruct POST as (AR5 & _ & _ & _ & _ & FR & _). pose proof HSP as [S1 S2]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp as U.
img_apply FR.
- clear - Ha S1 hS1 U. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly X W mem md a (proj1 ENQ)). clear - Ha S1 S2. unfold QSTACK in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly X1 W5 mem' md' a AR5). clear - Ha S1 S2. unfold QSTACK in *. img_lia.
- unfold ascratch, spZ. rewrite R_sp, (ts_errno _ TB). unfold w64. rewrite unsigned_lit_small by (img_try (clear - S1 hS1 U; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)).
clear - Ha S1 hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_ERRNO, QSTACK, kHighMemBeg in *. img_lia.
- intros [].
Qed.
Lemma FRAME_PRES : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W5) mem' a.
Proof.
intros a Ha. pose proof HSP as [S1 S2]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp as U.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha S1 hS1 U; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)).
destruct (PR1 a Ha) as [Hh [b Hb]].
assert (V : aview tfxsegs (w_H W5) mem' a <> None).
{ rewrite (FRAME_AG a Ha). unfold aview, mbyte, mrestrict. unfold w64 in Hh, Hb. rewrite Hh, Hb. cbn. discriminate. }
destruct (aview_raw_some (w_H W5) mem' a Ha' V ltac:(img_try (clear - Ha S1 hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, QSTACK, kHighMemBeg in *; img_lia))) as [Hm Hh5].
split; [img_try (img_exact Hh5)|]. destruct (mem' (w64 a)) as [b'|] eqn:E; [img_try (exists b'; img_exact E) | img_try (exfalso; img_exact (Hm eq_refl))].
Qed.
Lemma FRAME_VAL : forall a v, sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfxsegs (mrestrict (w_H W) mem1) a 8 v -> val_mem tfxsegs m5 a 8 v.
Proof. intros a v H1 H2 V. img_apply (val_mem_xfer (w_H W) (w_H W5) mem1 mem' a 8 v); [|img_try (img_exact V)]. intros i Hi. img_apply FRAME_AG. img_lia. Qed.
Lemma E2R : ew ER 2 = getr regs' 2. Proof. img_exact (YF2m.E2 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). Qed.
Lemma REqT : ew ER 32 = w64 T. Proof. img_refl. Qed.
Lemma REqSB : ew ER 33 = w64 SB. Proof. img_refl. Qed.
Lemma REqU : ew ER 34 = w64 u. Proof. img_refl. Qed.
Lemma REqN : ew ER 35 = w64 nn. Proof. img_refl. Qed.
Lemma REqQSZ : ew ER 36 = w64 QSZ1. Proof. img_refl. Qed.
Lemma REqQF : ew ER 37 = w64 QF1. Proof. img_refl. Qed.
Lemma REqQL : ew ER 38 = w64 QL1. Proof. img_refl. Qed.
Lemma REqQB : ew ER 39 = w64 QB1. Proof. img_refl. Qed.
Lemma REqCNT : ew ER 40 = w64 cnt1. Proof. img_refl. Qed.
Lemma REqCP : ew ER 41 = w64 CP1. Proof. img_refl. Qed.
Lemma REqJST : ew ER 42 = w64 jst1. Proof. img_refl. Qed.
Lemma REqNB : ew ER 43 = w64 NB1. Proof. img_refl. Qed.
Lemma REqCSL : ew ER 44 = w64 CSL1. Proof. img_refl. Qed.
Lemma REqRA : ew ER 45 = w64 ra0. Proof. img_refl. Qed.
Lemma REqS0 : ew ER 46 = w64 s00. Proof. img_refl. Qed.
Lemma REqS1 : ew ER 47 = w64 s10. Proof. img_refl. Qed.
Lemma REqS2 : ew ER 48 = w64 s20. Proof. img_refl. Qed.
Lemma REqS3 : ew ER 49 = w64 s30. Proof. img_refl. Qed.
Lemma REqS4 : ew ER 50 = w64 s40. Proof. img_refl. Qed.
Lemma REqS5 : ew ER 51 = w64 s50. Proof. img_refl. Qed.
Lemma BV2R : bv_unsigned (ew ER 2) = sp0 - 64. Proof. rewrite E2R. img_exact SPv. Qed.
Local Ltac wfq2wfr :=
img_change (YF2l.QSZv q1) with QSZ1 in *; img_change (YF2l.QFv ly q1) with QF1 in *; img_change (YF2l.QLv ly q1) with QL1 in *;
img_change (YF2l.QBv q1) with QB1 in *; img_change (YF2l.CPv (YF1k.coff l1)) with CP1 in *;
img_change (YF2l.NBv ly (YF1k.coff l1)) with NB1 in *; img_change (YF2l.CSLv ly (YF1k.cnt l1)) with CSL1 in *;
img_change (YF1k.cnt l1) with cnt1 in *; img_change (YF1k.coff l1) with coff1 in *.
Local Ltac reg_introR := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8R := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4R := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Local Ltac lit_regionR :=
reg_introR; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit1; [img_apply cell_lit1; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma QLR1 : 0 <= QL1 < ASAN_CEIL /\ QL1 mod 8192 = 0.
Proof.
pose proof HI1 as (hP1 & hP2 & _ & _ & _ & _ & hSP1 & hSP2 & _).
unfold YF2m.QLv. destruct (rev (qc_list q1)) as [|lb initr] eqn:Hrev; [img_try (ceil; unfold ASAN_CEIL; split; [img_lia | img_refl])|].
pose proof (last_facts1 lb initr Hrev) as (L1 & L2 & L3 & _). unfold YF2l.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [img_lia | img_try (img_exact L3)].
Qed.
Lemma REG0R_ok : Forall (region_ok tfxsegs ER m5) YF2m.REG0.
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof root_vals1 as (V1 & V2 & V3 & V4). pose proof cache_vals1 as (C1 & C2 & C3 & C4 & C5). pose proof jst_val1 as [J1 J1R]. pose proof q_facts1 as (Qa & Qb & Qc & Qd).
wfq2wfr. assert (Qc0 : 0 <= QSZ1) by (img_try (unfold YF2m.QSZv; clear; img_lia)).
pose proof QLR1 as [QLR _]. pose proof u_facts1 as (Ua & Ub & Uc & Ud). pose proof Usp as U.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, QLR, Qb, Qd, Ua, Ub.
unfold YF2m.REG0, YF2m.R_FRAME, YF2m.R_ROOT, YF2m.R_CNT, YF2m.R_JST, flit4, flit8, fatom8.
img_apply Forall_cons.
{   reg_introR. rewrite BV2R.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]]]]])].
- img_apply (chunk_atom1 ER _ _ 8 51%nat 0 s50); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 56) _ ltac:(img_lia) ltac:(img_lia) F7) | img_lia]) | img_try (pose proof (u64_range (getr regs 21)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 50%nat 0 s40); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 48) _ ltac:(img_lia) ltac:(img_lia) F6) | img_lia]) | img_try (pose proof (u64_range (getr regs 20)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 49%nat 0 s30); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 40) _ ltac:(img_lia) ltac:(img_lia) F5) | img_lia]) | img_try (pose proof (u64_range (getr regs 19)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 48%nat 0 s20); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 32) _ ltac:(img_lia) ltac:(img_lia) F4) | img_lia]) | img_try (pose proof (u64_range (getr regs 18)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 47%nat 0 s10); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 24) _ ltac:(img_lia) ltac:(img_lia) F3) | img_lia]) | img_try (pose proof (u64_range (getr regs 9)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 46%nat 0 s00); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 16) _ ltac:(img_lia) ltac:(img_lia) F2) | img_lia]) | img_try (pose proof (u64_range (getr regs 8)); r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 45%nat 0 ra0); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (rewrite Z.sub_0_r; img_apply u64_range) | img_try (eapply val_mem_addr; [img_exact (FRAME_VAL (sp0 - 8) _ ltac:(img_lia) ltac:(img_lia) F1) | img_lia]) | img_try (pose proof (u64_range (getr regs 1)); r8R) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_qc in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [img_try (img_apply (val_mem_writable1 _ _ _ _ V1)) | img_try (destruct (Z_lt_le_dec o 96); [img_apply (val_mem_writable1 _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [img_apply (val_mem_writable1 _ _ _ _ V3) | img_apply (val_mem_writable1 _ _ _ _ V4)]])];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom1 ER _ _ 8 36%nat 0 QSZ1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact V1) | img_try (r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 37%nat 0 QF1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V2 | img_lia]) | img_try (r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 38%nat 0 QL1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V3 | img_lia]) | img_try (r8R) | img_try (cbn; img_lia)].
- img_apply (chunk_atom1 ER _ _ 8 39%nat 0 QB1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V4 | img_lia]) | img_try (r8R) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable1 _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom1 ER _ _ 4 40%nat 0 cnt1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact C1 | img_lia]) | img_try (r4R) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable1 _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom1 ER _ _ 8 42%nat 0 jst1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J1 | img_lia]) | img_try (r8R) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_introR. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom1 ER 0 _ 8 33%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | | img_try (r8R) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TB); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply cell_sym1. img_case; vm_compute. all: img_refl. }
do 3 (img_apply Forall_cons; [img_try (lit_regionR)|]). img_apply Forall_nil.
Qed.
Lemma PAIRSR_ok : pairwise_disjoint ER YF2m.REG0.
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _). pose proof Usp as U.
img_apply pairwise_disjoint_of_extents. unfold YF2m.REG0, YF2m.R_FRAME, YF2m.R_ROOT, YF2m.R_CNT, YF2m.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite BV2R, REqT. unfold w64. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
rewrite !unsigned_lit_small by img_lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; img_lia | clear - hT1 CR0; img_lia].
Qed.
Lemma FACTSR_ok : atoms_ok ER (f_atoms YF2m.FFQ).
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2]. pose proof Usp as U.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof q_facts1 as (Qa & Qb & Qc & Qd). pose proof jst_val1 as [_ JR].
pose proof cache_vals1 as (_ & _ & _ & C4 & C5). pose proof hit_facts1 as (F1' & F2' & F3' & F4' & F5' & F6' & _). wfq2wfr.
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
pose proof QLR1 as [QLR QLA].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK, RSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, U1, U2, QLR, F2', F4', F5', Qb, Qd.
assert (E2' : ew ER 2 = w64 (sp0 - 64)) by (img_try (rewrite E2R; img_exact SP')).
assert (AF : forall k0 Xv lo hi al, ew ER k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok ER k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2m.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK, RSTACK.
split. { img_apply (AF 2%nat (sp0 - 64)); [img_try (img_exact E2')| | | |]. all: clear - CR0 U S1 S2 hS1 hS2 Hal; first [img_lia | img_change (2 ^ 4) with 16; replace (sp0 - 64) with (sp0 + (-4) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact REqT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat SB); [img_try (img_exact REqSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 34%nat u); [img_try (img_exact REqU)| | | |]. all: clear - CR0 U1 U2 U3 U4; first [img_lia | img_change (2 ^ 4) with 16; img_exact U3]. }
split. { img_apply (AF 35%nat nn); [img_try (img_exact REqN)| | | |]. all: clear - CR0 U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat QSZ1); [img_try (img_exact REqQSZ)| | | |]. all: clear - CR0 Qc; unfold YF2m.QSZv in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat QF1); [img_try (img_exact REqQF)| | | |]. all: clear - CR0 Qd; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat QL1); [img_try (img_exact REqQL)| | | |]. all: clear - CR0 QLR QLA; first [img_lia | img_change (2 ^ 13) with 8192; img_exact QLA]. }
split. { img_apply (AF 39%nat QB1); [img_try (img_exact REqQB)| | | |]. all: clear - CR0 Qa Qb U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat cnt1); [img_try (img_exact REqCNT)| | | |]. all: clear - CR0 C4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 41%nat CP1); [img_try (img_exact REqCP)| | | |]. all: clear - CR0 F1' F2' F3'; unfold YF2m.CPv; first [pose proof (Z.div_pos coff1 16); pose proof (Z.div_lt_upper_bound coff1 16 (2 ^ 27)); img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 42%nat jst1); [img_try (img_exact REqJST)| | | |]. all: clear - CR0 JR; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 43%nat NB1); [img_try (img_exact REqNB)| | | |]. all: clear - CR0 F4' F5' F6' hP1 hP2 hSP1 hSP2; first [img_lia | img_change (2 ^ 13) with 8192; img_exact F6']. }
split. { img_apply (AF 44%nat CSL1); [img_try (img_exact REqCSL)| | | |]. all: clear - CR0 C4 C5 hT1 hT2 TAL; unfold YF2m.CSLv, t_cache in *;
first [img_lia | img_change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|img_lia]; rewrite Hc; img_apply Z.mod_divide; [img_lia|]; exists (1024 * c + 536 + (cnt1 - 1)); img_lia]. }
split. { img_apply (AF 45%nat ra0); [img_try (img_exact REqRA) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 1)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 46%nat s00); [img_try (img_exact REqS0) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 8)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 47%nat s10); [img_try (img_exact REqS1) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 9)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 48%nat s20); [img_try (img_exact REqS2) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 18)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 49%nat s30); [img_try (img_exact REqS3) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 19)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 50%nat s40); [img_try (img_exact REqS4) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 20)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split; [|img_try (img_exact I)]. { img_apply (AF 51%nat s50); [img_try (img_exact REqS5) | img_try (img_apply u64_range) | img_try (pose proof (u64_range (getr regs 21)); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
Qed.
Lemma SEEDR_ok : st_ok tfxsegs ER YF2m.SS0 (restrict (w_H W5) (mkst regs' (w64 (0x35f2c + D_150)) mem' (seg_rom tfxsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
assert (P4 : getr regs' 4 = w64 TFX_TP) by (img_try (rewrite (CSV 4%bv ltac:(img_change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; img_lia)), R_tp; img_exact Htp)).
assert (P8 : getr regs' 8 = w64 (T + t_cache + 1920)) by (img_try (rewrite (CSV 8%bv ltac:(img_change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; img_lia)); img_exact R_s0)).
assert (P9 : getr regs' 9 = w64 (T + t_cache)) by (img_try (rewrite (CSV 9%bv ltac:(img_change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; img_lia)); img_exact R_s1)).
assert (P18 : getr regs' 18 = w64 (u - 16)) by (img_try (rewrite (CSV 18%bv ltac:(img_change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; img_lia)); img_exact R_s2)).
assert (P19 : getr regs' 19 = w64 (T + t_qc)) by (img_try (rewrite (CSV 19%bv ltac:(img_change (bv_unsigned (19%bv : bv 5)) with 19; unfold acallee_saved; img_lia)); img_exact R_s3)).
assert (P21 : getr regs' 21 = w64 nn) by (img_try (rewrite (CSV 21%bv ltac:(img_change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; img_lia)); img_exact R_s5)).
rewrite restrict_mkst_fx. unfold YF2m.SS0, YF2m.SR0, sr_set. cbn [bv_eqb]. unfold YF2m.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg
| intros XX; discriminate | cbn [sv_denot]; img_exact P4]
| intros XX; discriminate | cbn [sv_denot]; img_exact HA0]
| intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P8. unfold w64. rewrite Zbv_add_unsigned. f_equal; unfold t_cache; img_lia.
+ cbn [sv_denot]. fold (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P9. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqU, P18. unfold w64. rewrite Zbv_add_unsigned. f_equal; img_lia.
+ cbn [sv_denot]. fold (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P19. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2m.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqN, P21. unfold w64. rewrite Zbv_add_unsigned. f_equal; img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0R_ok.
- img_exact PAIRSR_ok.
- split; [img_try (img_exact FACTSR_ok) | img_try (split; img_exact I)].
Qed.
Theorem FHR_ok : YF2m.free_hyps W5 ly regs' mem' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof q_facts1 as QF. pose proof jst_val1 as [_ JR]. pose proof cache_vals1 as (C1 & C2 & C3 & C4 & C5).
pose proof hit_facts1 as (F1' & F2' & F3' & F4' & F5' & F6' & F7' & F8'). wfq2wfr.
constructor.
- img_exact LO.
- rewrite (CSV 4%bv ltac:(img_try (img_change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; img_lia))), R_tp. rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- unfold YK0s.ret_ok in *. unfold w64. rewrite Z_to_bv_bv_unsigned. img_exact Hra.
- img_exact Hra4.
- rewrite SPv. unfold QSTACK, RSTACK in *. img_lia.
- rewrite SPv. replace (sp0 - 64) with (sp0 + (-4) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal.
- rewrite SPv. intros a Ha. img_apply FRAME_PRES. img_lia.
- rewrite SPv. splits; (eapply val_mem_addr; [img_try (img_apply FRAME_VAL; [| | eassumption]; img_lia) | img_lia]).
- splits; img_apply u64_range.
- split; [img_try (img_exact u_zone1) | img_try (img_exact U3)].
- img_exact IMG.
- img_exact U4.
- img_exact QF.
- img_exact HNB1.
- intros lb initr Hrev. pose proof (last_facts1 lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). wfq2wfr. splits; assumption.
- clear - C4 C5. img_lia.
- intros _. splits; try assumption.
- img_exact JR.
- img_exact SEEDR_ok.
Qed.
Local Notation WINr := (YF2m.WIN ly q1 cnt1 coff1).
Local Notation S'1 := (YF0w.S' X1 k l1).
Lemma WINR_zone : forall a, WINr a -> (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & HL). wfq2wfr.
unfold YF2m.WIN, YF2m.WINT, YF2m.WINA in Hw.
destruct Hw as [Hw|[[_ Hw]|[Hq Hw]]].
- left. clear - Hw. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. img_lia.
- right. clear - Hw hN1 hN2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
- right. destruct (rev (qc_list q1)) as [|lb initr] eqn:Hrev.
+ exfalso. img_apply Hq. rewrite <- (rev_involutive (qc_list q1)), Hrev. img_refl.
+ pose proof (HL lb initr eq_refl) as [L1 L2]. unfold YF2l.QLv, YF2m.QLv in L1, L2, Hw. rewrite ?Hrev in Hw, L1, L2.
clear - Hw L1 L2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
Qed.
Lemma WINR_dec : forall a, WINr a \/ ~ WINr a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
pose proof cache_vals1 as (_ & _ & _ & _ & C5). wfq2wfr.
assert (LQ : qc_list q1 = [] \/ qc_list q1 <> []) by (img_try (destruct (qc_list q1); [img_try (left; img_refl) | img_try (right; discriminate)])).
unfold YF2m.WIN, YF2m.WINT, YF2m.WINA.
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C1]; [img_try (left; left; left; img_exact C)|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C2]; [img_try (left; left; right; left; img_exact C)|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C3]; [img_try (left; left; right; right; img_exact C)|].
destruct (EM NB1 (NB1 + 32)) as [C|C4]; [img_try (left; right; left; split; [img_exact C5 | img_exact C])|].
destruct LQ as [LQ|LQ].
- right. intros [[Y1|[Y2|Y3]]|[[_ Y4]|[Y5 _]]]; [img_try (img_exact (C1 Y1)) | img_try (img_exact (C2 Y2)) | img_try (img_exact (C3 Y3)) | img_try (img_exact (C4 Y4)) | img_try (img_exact (Y5 LQ))].
- destruct (EM QL1 (QL1 + 8)) as [C|C6]; [img_try (left; right; right; split; [img_exact LQ | img_exact C])|].
right. intros [[Y1|[Y2|Y3]]|[[_ Y4]|[_ Y5]]]; [img_try (img_exact (C1 Y1)) | img_try (img_exact (C2 Y2)) | img_try (img_exact (C3 Y3)) | img_try (img_exact (C4 Y4)) | img_try (img_exact (C6 Y5))].
Qed.
Lemma CONST_OUTR : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINr (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YF20.Tfx_const_locq ly) c Hc) as K. unfold YF20.const_loc_okq in K.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINr a).
{ intros a Hn Hw. img_exact (Hn (WINR_zone a Hw)). }
assert (LOW : forall a, YF20.low_okq a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINr (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold YF20.low_okq in L.
split; [img_try (img_apply ZN)|]; clear - L Hi hP1 hT1; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi hT1 hT2 G_PT; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; img_lia.
- split; [img_try (img_apply ZN)|]; clear - K Hi C1 C2 G_PC G_TC; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi D1 D2 G_PD G_TD; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; img_lia.
Qed.
Lemma aowned_same : forall S1 S2 a, st_chunks S2 = st_chunks S1 -> st_fs S2 = st_fs S1 -> aowned B ly S2 a -> aowned B ly S1 a.
Proof. clear. intros S1 S2 a E1 E2 H. unfold aowned, aclient_byte, sec_extents, frames in *. rewrite E1, E2 in H. img_exact H. Qed.
Lemma FINR : forall W6 c6, YF31.at_RETR W5 ly regs' mem' md' u nn q1 cnt1 coff1 ra0 s00 s10 s20 s30 s40 s50 W6 c6 ->
enq_leaf B ly X W regs mem md k (tt, S'1) W6 c6.
Proof.
intros W6 c6 HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL0).
destruct HAR as (M0 & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof POST as POST'. destruct POST' as (AR5 & LLE & WLE & CS & SIO & FR & PRS). destruct AR5 as (M5 & LED5 & BUD5 & MW5 & HSH5).
destruct HR as (-> & regs6 & mem6 & mat6 & -> & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QCS & MEQ6 & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
set (rd6 := aview tfxsegs (w_H W5) mem6).
pose proof Usp as U. pose proof HSP as HSP'. pose proof cache_vals1 as (_ & _ & _ & C4 & C5). wfq2wfr.
destruct RO as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
assert (ENB : NB1 = SB + (region_off kBatchClass + last l1 0)) by (img_try (unfold YF2m.NBv, coff1; img_lia)).
assert (SPR : spZ regs1 = sp0 - 64).
{ unfold spZ. rewrite R_sp. unfold w64. img_apply unsigned_lit_small. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). clear - U hS1 HSP'. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. img_lia. }
assert (WD : forall a, WINr a -> YF0w.D ly X1 l1 sp0 a).
{ intros a Hw. unfold YF0w.D, YF0w.DT, YF0w.DN, YF0w.DL, YF0w.DS.
unfold YF2m.WIN, YF2m.WINT, YF2m.WINA in Hw. rewrite ENB in Hw.
destruct Hw as [Hw|[[_ Hw]|[Hq Hw]]].
- left. img_exact Hw.
- right; left. img_exact Hw.
- right; right; left. split; [img_try (img_exact Hq)|]. unfold YF0w.QLv. unfold YF2m.QLv in Hw. img_exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0w.D ly X1 l1 sp0 a -> rd6 a = rd5 a).
{ intros a Ha ND. (subst rd6; cbv beta). img_apply aview_same. img_apply (MEQ6 (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WD a X')). }
assert (VIS : forall a, rd5 a <> None -> rd6 a <> None).
{ intros a Hv HN. (subst rd6; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W5 x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem6 x); discriminate)|].
destruct (mem6 x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem' x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (WINR_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ6 x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W5 (w64 a) = true -> mem6 (w64 a) = mem' (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (WINR_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- img_apply (MEQ6 x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W5) mem6) a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd6 (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd6; cbv beta). img_exact (YF20.val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd6 (T + t_qc + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length (qc_list q1)) + 1) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V1); [img_refl | img_try (unfold YF2m.QSZv; img_refl)]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd6 (T + t_qc + 8 + Z.of_nat i) =
Some (YG0h.le_byte (match qc_list q1 with [] => SB + (region_off kBatchClass + last l1 0) | b0 :: _ => SB + b_self b0 end) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V2); [img_refl|]. unfold YF31.QF', YF2m.QFv. rewrite ENB. destruct (qc_list q1); img_refl. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd6 (T + t_qc + 16 + Z.of_nat i) = Some (YG0h.le_byte (SB + (region_off kBatchClass + last l1 0)) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V3); [img_refl | img_try (img_exact ENB)]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd6 (T + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes q1 + nn + kBatchBytes) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V4); [img_refl | img_try (unfold YF2m.QBv; img_refl)]. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd6 (T + t_cache + 1920 + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length l1) - 1) 4 i)).
{ img_apply (VM _ _ 4%nat _ _ V5); [img_refl | img_try (unfold cnt1; img_refl)]. }
assert (NEW_n0 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + Z.of_nat i) = Some (YG0h.le_byte 0 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V6); [img_try (img_exact ENB) | img_refl]. }
assert (NEW_n8 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 8 + Z.of_nat i) = Some (YG0h.le_byte (nn + kBatchBytes) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V7); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_n16 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 16 + Z.of_nat i) = Some (YG0h.le_byte 1 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V8); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_n24 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 24 + Z.of_nat i) = Some (YG0h.le_byte (u - 16) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V9); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_lnext : forall lb initr, rev (qc_list q1) = lb :: initr ->
forall i, (i < 8)%nat -> rd6 (SB + b_self lb + Z.of_nat i) = Some (YG0h.le_byte (SB + (region_off kBatchClass + last l1 0)) 8 i)).
{ intros lb initr Hrev. img_apply (VM _ _ 8%nat _ _ (VL lb initr Hrev)); [| img_try (img_exact ENB)]. unfold YF2m.QLv. rewrite Hrev. img_refl. }
assert (CONST' : Forall (cell_holds B ly rd6) (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd5); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly X1 _ M5) c Hc))|].
intros i Hi. (subst rd6; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUTR c Hc i Hi) as [X1' X2]. img_apply aview_same.
img_apply (MEQ6 (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. img_exact X1'. }
assert (Hnq1 : ~ In (ck_beg k) (map ck_beg (q_items X1))).
{ unfold q_items, all_batches. rewrite Rqt, Rqg. img_exact Hnq. }
assert (Hbev1 : Z.of_nat (length (all_batches X1)) + 1 <= st_nev X1) by (img_try (unfold all_batches; rewrite Rqt, Rqg, Rnev; img_exact Hbev)).
pose proof (YF0w.enq_fin_ARm B TB ly X1 rd5 rd6 M5 k Hk1 Hst Hnq1 HNB1   CI l1 El1 Hl1ne sp0 HSP' IMG AG VIS
NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST' Hbev1) as MF.
exists regs6, mem6, (with_vm_backing (m_vm_lazy md') mat6 md'), (Some (region_off kBatchClass + last l1 0)). split.
{ unfold cfg_at, raZ, w64. img_refl. }
split.
2:{ split; [img_try (cbn; rewrite Rqt; img_refl)|]. split; [img_try (img_exact HNB)|]. split; [img_try (cbn; img_exact Rck)|]. split; [img_try (cbn; img_exact Rqg) | img_try (cbn; img_exact Rfs)]. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_exact WLE | split; [|split; [|split]]]])].
- split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0w.ALedger_S' ly X1 k l1 tfxsegs md' LED5)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD5 as [BUD5 PIN5]. split; [| img_try (img_exact (YF0w.asecA_S' ly X1 k l1 _ PIN5))].
eapply Z.le_trans; [img_try (img_exact BUD5)|]. rewrite <- (YF0w.abudget_S' X1 k l1). img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW5)].
+ eapply (ahs_transfer tfxsegs B ly X1 _ (w_H W5) mem' mem6 (al_img_env tfxsegs ly X1 _ (am_layout B ly X1 _ M5) LED5) M5 HSH5 VIS HSK).
* eapply (aclient_band_same_frames B ly X1); [img_try (img_exact MF) | img_refl].
*   img_refl.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. (subst rd6; cbv beta). img_apply aview_same. img_apply (MEQ6 (Z_to_bv 64 _)).
rewrite unsigned_lit_small by (img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)). intros Hw. pose proof (WINR_zone _ Hw) as Z3.
pose proof HI1 as (hP1 & _ & hT1 & _). clear - Z3 SBg hP1 hT1. unfold zone3, zone3cases, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_IMG_LO, TFX_IMG_END, kHighMemBeg, kThreadObjSize, kPrimResvSize in *. img_lia.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ (r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)) by img_lia.
destruct RR as [->|[->|[->|[->|[->|[->|[->|RR]]]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q2, SPv. unfold w64, sp0. replace (bv_unsigned (getr regs 2) - 64 + 64) with (bv_unsigned (getr regs 2)) by img_lia. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q8. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q9. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q18. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q19. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q20. img_apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (symmetry; img_apply bv_eq; (img_case; vm_compute); img_refl)). rewrite Q21. img_apply Z_to_bv_bv_unsigned.
+ assert (E6 : getr regs6 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ img_apply QCS. clear - RR. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
rewrite E6, (CS r ltac:(img_try (unfold acallee_saved; clear - RR; img_lia))).
clear - RR R_gp R_tp R_hi. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; (subst r; cbv beta);
first [img_exact R_gp | img_exact R_tp | img_apply R_hi; cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right])].
-   img_exact (same_io_wvb2 md md' mat mat6 SIO).
-
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly X1 a) by (img_try (intros O; img_apply NO; img_exact (aowned_same X X1 a Rck Rfs O))).
assert (NDS : ~ YF0w.DS sp0 a) by (img_try (intros O; img_apply NS; unfold ascratch, spZ; left; img_exact O)).
rewrite AG; [| img_try (img_exact Ha) | img_try (intros HD; destruct (YF0w.D_owned B ly X1 rd5 M5 k CI l1 El1 Hl1ne sp0 HSP' a (proj1 Ha) HD) as [O|O]; [img_exact (NO1 O) | img_exact (NDS O)])].
rewrite FR; [| img_try (img_exact Ha) | img_try (img_exact NO) | img_try (img_exact NO1) | | img_try (intros [])].
2:{ unfold ascratch in NS |- *. rewrite SPR. unfold spZ in NS. fold sp0 in NS. intros [O|O]; img_apply NS; [img_try (left; clear - O; unfold QSTACK, RSTACK in *; img_lia) | img_try (right; img_exact O)]. }
img_apply (AG1 mem1 MQ1 G1 G2 G3 G4 G5 G6 a Ha). intros O. img_apply NS. unfold ascratch, spZ. left. fold sp0. clear - O. unfold QSTACK. img_lia.
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ img_apply (apresent_same (w_H W5) mem'); [|img_try (img_apply PRS; rewrite SPR; clear - Ha Hb; unfold QSTACK, RSTACK in *; img_lia)]. img_apply MEQ6.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha U HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WINR_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. img_lia.
+ img_apply (apresent_same (w_H W5) mem'); [|img_try (img_apply FRAME_PRES; img_lia)]. img_apply MEQ6.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha U HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WINR_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. img_lia.
Qed.
Lemma TAIL_SRr : forall mat', SRr tfxsegs W5 (mkCfg (mkst regs' (w64 (0x35f2c + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md') mat' md'))
(enq_leaf B ly X W regs mem md k (tt, S'1)).
Proof.
intros mat'. eapply SRr_mono; [img_try (img_exact (YF31.segT W5 ly regs' mem' md' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50 mat' FHR_ok))|].
intros W6 c6 _ HR. img_exact (FINR W6 c6 HR).
Qed.
End h.
Lemma WfX1 : WfP (as_universe B) 1 0 0 X.
Proof.
destruct ENQ as (_ & _ & Hbev & (Hpev & _) & _).
img_apply (YF0w.WfP_reslack _ 0 0 0 1 0 X WF ltac:(img_lia) ltac:(img_lia)); [img_lia| |img_try (img_exact (wf_fa_room _ _ _ _ _ WF))]. pose proof (wf_batches_ev _ _ _ _ _ WF). img_lia.
Qed.
Theorem tfx_enqueue_miss_arm :
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
img_apply (amreal_enqueue_nb k X W _ _ HNB).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
img_apply amreal_after_SRr. eapply SRr_mono; [img_try (img_exact (YF30.segR1 W ly regs mem md u nn q 0 0 jst (m_vm_materialized md) FH0_ok eq_refl))|].
intros W' c' _ HC. destruct HC as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 & R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
pose proof (R1 ly X W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass
(REFILL_PRE regs1 mem1 mat R_ra R_sp R_gp R_tp R_a0 R_a1 R_a2 R_a3 MQ1 PR1 V1 V2 V3 V4 V5 V6)) as RR.
unfold cfg_at, A_Refill in RR.
pose proof (refill_tree_apost (as_universe B) 1 0 0 X kBatchClass WfX1 ltac:(img_try (unfold kBatchClass; img_lia)) ltac:(img_lia) (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 ENQ))))))) as APOST.
pose proof (amreal_apost tfxsegs (refill_tree kBatchClass X) _ W _ _ APOST RR) as RR2. clear RR.
eapply amreal_mono; [|img_try (img_exact RR2)]. cbv beta. intros [[] X1] W5 c5 [(WX1 & RO & CI) HL]. cbn [fst snd] in WX1, RO, CI, HL.
destruct HL as (regs' & mem' & md' & -> & POST & HA0).
unfold enq_after_refill. cbn [snd].
destruct (pc_chunks (cache X1 kBatchClass)) as [|o1 l1'] eqn:El1.
-
cbn [snd] in HA0. rewrite El1 in HA0. destruct POST as (AR5 & _). destruct AR5 as (M1 & _).
unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1. rewrite unsigned_lit_small by img_lia. rewrite <- (wvb_self md') at 1.
img_apply amreal_spin_sj. img_exact (SPIN W5 regs' mem' md' (m_vm_materialized md') X1 M1 HA0).
-
cbn [snd] in HA0. rewrite El1 in HA0.
unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1. rewrite unsigned_lit_small by img_lia. rewrite <- (wvb_self md') at 1.
img_exact (TAIL_SRr regs1 mem1 mat R_sp R_gp R_tp R_s0 R_s1 R_s2 R_s3 R_s5 R_hi MQ1 PR1 F1 F2 F3 F4 F5 F6 F7 V1 V2 V3 V4 V5 V6
W5 regs' mem' md' X1 POST RO CI HA0 o1 l1' El1 (m_vm_materialized md')).
Qed.
End e.
Theorem tfx_enqueue_miss {imgk : img} : forall B, TfxSyms B -> tfx_refill_spec B -> forall ly X W regs mem md k,
enq_pre B ly X W regs mem md k -> need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) = [] ->
ly_tsd ly = TFX_TSD ->
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
intros B TB R1 ly X W regs mem md k ENQ HNB Hl0 HTSD.
img_exact (tfx_enqueue_miss_arm B TB ly X W regs mem md k ENQ HNB Hl0 R1 HTSD).
Qed.
Theorem tfx_enqueue_nb {imgk : img} : forall B, TfxSyms B -> tfx_refill_spec B -> tfx_enqueue_spec_nb B true.
Proof.
intros B TB R1 ly X W regs mem md k HNB ENQ.
assert (HT : ly_tsd ly = TFX_TSD).
{ destruct ENQ as ((M & _) & _). rewrite (am_tsd B ly X _ M). img_exact (ts_tsd _ TB). }
destruct (pc_chunks (cache X kBatchClass)) as [|o l0] eqn:E.
- img_exact (tfx_enqueue_miss B TB R1 ly X W regs mem md k ENQ HNB E HT).
- img_apply (tfx_enqueue_hit B TB ly X W regs mem md k ENQ HNB); [img_try (rewrite E; discriminate) | img_try (img_exact HT)].
Qed.
End d.
