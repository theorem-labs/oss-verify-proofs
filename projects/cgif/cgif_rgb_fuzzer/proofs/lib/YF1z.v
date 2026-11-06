(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0r YF1p YF0w YF1k YF1j YF2k YF2y YF0v.
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
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. img_refl. Qed.
Lemma same_io_wvb : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; img_refl. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = false.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Local Notation QSZv := (YF2l.QSZv q).
Local Notation QBv := (YF2l.QBv q).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). img_exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). img_exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). img_exact Hnq. Qed.
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma HQL : qloose X. Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL). img_exact QL. Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). img_exact (img_cover_of_ledger ly X md LED). Qed.
Lemma ZT : zone3 T kThreadObjSize.
Proof.
pose proof (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
img_exact (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear; unfold kThreadObjSize; img_lia)) IT (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)).
Qed.
Definition lb : batch := match rev (qc_list q) with b :: _ => b | [] => mkBatch 0 [] end.
Definition initr : list batch := match rev (qc_list q) with _ :: t => t | [] => [] end.
Lemma Hrev : rev (qc_list q) = lb :: initr.
Proof. unfold lb, initr. unfold need_new_batch in HNB. destruct (rev (qc_list q)); [img_try (discriminate) | img_refl]. Qed.
Lemma E0 : qc_list q = rev initr ++ [lb]. Proof. rewrite <- (rev_involutive (qc_list q)), Hrev. img_refl. Qed.
Lemma lb_in : In lb (all_batches X).
Proof. unfold all_batches. img_apply in_app_iff. left. rewrite E0. img_apply in_app_iff. right. left. img_refl. Qed.
Definition QLv : Z := SB + b_self lb.
Definition CNTv : Z := Z.of_nat (length (b_items lb)).
Definition BSZv : Z := b_bytes lb.
Local Notation SLv := (YF2k.SLv QLv CNTv).
Lemma Hroom : CNTv < kBatchSlots.
Proof.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) lb lb_in) as [L1 L2].
unfold need_new_batch in HNB. rewrite Hrev in HNB. apply Z.eqb_neq in HNB. unfold CNTv, kBatchSlots in *. img_lia.
Qed.
Lemma last_geom : ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\ kHighMemBeg <= QLv /\ QLv + kBatchBytes <= ASAN_CEIL.
Proof.
destruct (YF0w.batch_geom B ly X rd0 M [] sp0 HSP lb lb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as [P1 P2].
unfold QLv. rewrite Eb. unfold region_base in *. rewrite region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). ceil; unfold kBatchClass, kBatchBytes, kSpaceSize, kPrimResvSize, kHighMemBeg, ASAN_CEIL in *.
splits; img_lia.
Qed.
Lemma last_cells : val_mem tfxsegs m0 (QLv + 8) 8 BSZv /\ val_mem tfxsegs m0 (QLv + 16) 8 CNTv.
Proof.
assert (IN : forall c, In c (batch_cells (qc_list q)) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. left. unfold qc_cells. do 4 right. img_exact Hc. }
assert (OWN : forall c, In c (batch_own_cells lb (ANum 0)) -> In c (batch_cells (qc_list q))).
{ intros c Hc. img_apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [img_try (rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)|].
rewrite next_exp_app_new. img_exact Hc. }
unfold BSZv, CNTv, QLv. split.
- replace (SB + b_self lb + 8) with (aeval B ly (aoff (batch_exp lb) 8)) by (img_try (cbn; img_lia)).
apply (YF1k.cell_stateZ B ly X W mem M _ _ 8 _ (IN _ (OWN _ ltac:(img_try (unfold batch_own_cells; right; left; img_refl)))) eq_refl).
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (img_try (cbn; img_lia)).
apply (YF1k.cell_stateZ B ly X W mem M _ _ 8 _ (IN _ (OWN _ ltac:(img_try (unfold batch_own_cells; right; right; left; img_refl)))) eq_refl).
Qed.
Lemma bsz_range : kBatchBytes <= BSZv /\ BSZv <= QBv.
Proof.
unfold BSZv, YF2l.QBv. split; [img_try (img_exact (YF1k.b_bytes_ge B ly X W mem M lb lb_in))|].
rewrite (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)), E0, sum_bytes_app. cbn [sum_bytes fold_right].
pose proof (YF1k.sum_bytes_ge B ly X W mem M (rev initr) ltac:(img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; rewrite E0; img_apply in_app_iff; left; img_exact Hb))). img_lia.
Qed.
Lemma slot_present : forall a, SLv + 24 <= a < SLv + 32 -> apresent H0 mem a.
Proof.
intros a Ha. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR. unfold YF2k.SLv in Ha.
assert (JI : In (aoff (batch_exp lb) (24 + 8 * CNTv), kBatchBytes - 24 - 8 * CNTv) (ajunk B ly X)).
{ unfold ajunk. do 2 right. rewrite !in_app_iff. do 4 right. left. unfold quar_junk. img_apply in_flat_map. exists lb. split; [img_try (img_exact lb_in)|]. unfold batch_junk, CNTv. left. img_refl. }
pose proof (YF1k.vis_range B ly X W mem M _ _ (a - (SLv + 24)) (or_introl JI)) as V. cbn [aeval aoff batch_exp] in V.
specialize (V ltac:(img_try (unfold YF2k.SLv, CNTv, kBatchBytes, kBatchSlots in *; img_lia))).
replace (SB + (b_self lb + (24 + 8 * CNTv)) + (a - (SLv + 24))) with a in V by (img_try (unfold YF2k.SLv, QLv; img_lia)).
img_apply YF1p.vis_apresent; [| img_try (img_exact V)]. ceil; unfold YF2k.SLv, QLv, CNTv, kBatchBytes, kBatchSlots, kHighMemBeg, ASAN_CEIL, TFX_IMG_END in *. img_lia.
Qed.
Local Notation E0' := (YF2k.E0 ly regs u nn QSZv QLv QBv CNTv BSZv).
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac nums := ceil; unfold YF2k.SLv, CNTv, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, QSTACK, TFX_IMG_END, t_qc in *.
Lemma chunk_atom8 : forall (E : env) m base a k0 x, ew E k0 = w64 x -> 0 <= x < 2 ^ 64 -> val_mem tfxsegs m (base + a) 8 x ->
YQ0b.chunk_ok tfxsegs E m base (YQ0b.mkChunk a (CVal 8 (SOff k0 0))).
Proof.
intros E m base a k0 x Hk0 Hx Hm. eapply chunk_ok_val; [| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact Hx) | img_try (cbn; img_lia) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Theorem FH_ok : YF2k.free_hyps W ly regs mem u nn QSZv QLv QBv CNTv BSZv.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES. rewrite (ts_tp _ TB) in Htp.
pose proof (YF1k.u_facts B ly X W mem k M Hk) as (U1 & U2 & U3 & U4). pose proof (YF1k.u_zone B ly X W mem k M IMG Hk) as UZ.
pose proof (YF1k.q_facts B ly X W mem sp0 k M HSP Hk HQL) as (Qa & Qb & Qc & Qd).
pose proof (YF1k.root_vals B ly X W mem M) as (V1 & V2 & V3 & V4).
pose proof (YF1k.GEO B ly X W mem M) as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & _).
pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof last_cells as [C8 C16]. pose proof bsz_range as [B1 B2]. pose proof Hroom as HR. pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QSZ1 : 1 <= QSZv) by (img_try (unfold YF2l.QSZv; rewrite E0, length_app; cbn [length]; img_lia)).
assert (C0 : 0 <= CNTv) by (img_try (unfold CNTv; img_lia)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
constructor.
- img_exact LO.
- img_exact Htp.
- img_exact Hra.
- img_exact Hra4.
- split; [img_try (img_exact Hlo) | img_try (img_exact Hhi)].
- img_exact Hal.
- img_exact HPRES.
- split; [img_try (img_exact UZ) | img_try (img_exact U3)].
- img_exact IMG.
- img_exact U4.
- nums. splits; img_lia.
- splits; [img_try (img_exact L1) | img_try (img_exact L2) | img_try (img_exact L3) | img_try (img_exact C0) | img_try (img_exact HR) | img_try (nums; img_lia) | img_try (nums; img_lia) | |].
+ intros a Ha. destruct (Z_lt_le_dec a (QLv + 16)).
* replace a with (QLv + 8 + (a - (QLv + 8))) by img_lia. img_apply (YF1k.val_mem_present W mem _ 8 _ _ C8); [img_lia | img_try (img_apply off_img_high; nums; img_lia)].
* replace a with (QLv + 16 + (a - (QLv + 16))) by img_lia. img_apply (YF1k.val_mem_present W mem _ 8 _ _ C16); [img_lia | img_try (img_apply off_img_high; nums; img_lia)].
+ img_exact slot_present.
-
rewrite restrict_mkst_fx. unfold YF2k.SS0, YF2k.SR0, sr_set. cbn [bv_eqb]. unfold YF2k.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ repeat (img_apply regs_ok_pin; [| img_try (intros XX; discriminate) |]); [img_try (img_apply regs_ok_Ereg) | ..]; cbn [sv_denot].
* img_exact Htp.
* img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (Z_to_bv 64 T). rewrite Ha0. unfold w64. rewrite Zbv_add_unsigned. img_refl.
* img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (Z_to_bv 64 T). rewrite Ha1. unfold w64. rewrite Zbv_add_unsigned. img_refl.
* img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 34) with (Z_to_bv 64 u). rewrite Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. img_refl.
* img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 35) with (Z_to_bv 64 nn). rewrite Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. set (E := Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)).
assert (BV2 : bv_unsigned (ew E 2) = sp0) by (img_try (rewrite (YF2k.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew E 2 = getr regs 2); img_refl)).
assert (BV32 : bv_unsigned (ew E 32) = T) by (img_try (img_change (ew E 32) with (w64 T); unfold w64; img_apply unsigned_lit_small; clear - H1; nums; img_lia)).
assert (BV38 : bv_unsigned (ew E 38) = QLv) by (img_try (img_change (ew E 38) with (w64 QLv); unfold w64; img_apply unsigned_lit_small; clear - L4 L5; nums; img_lia)).
assert (BV47 : bv_unsigned (ew E 47) = SLv) by (img_try (img_change (ew E 47) with (w64 SLv); unfold w64; img_apply unsigned_lit_small; clear - L4 L5 C0 HR; nums; img_lia)).
unfold YF2k.REG0, YF2k.R_ROOT, YF2k.R_LAST, YF2k.R_SLOT.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E m0 2 sp0 (- 64)); [img_try (img_exact BV2) | img_try (nums; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (nums; img_lia) | img_try (img_apply HPRES; clear -Ha; nums; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite BV32. unfold t_qc in *.
split; [img_try (nums; img_lia)|]. split; [img_try (nums; img_lia)|]. split.
{ intros o Ho. img_apply (YF1k.val_mem_writable W mem _ _ _ _ V4); [img_try (cbn; img_lia) | img_try (img_apply (zone3_off_img _ _ _ ZT); nums; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply (chunk_atom8 E _ _ _ 36%nat QSZv); [img_refl | img_lia | img_try (img_exact V1)].
- img_apply (chunk_atom8 E _ _ _ 38%nat QLv); [img_refl | img_try (nums; img_lia) |].
replace QLv with (YF2l.QLv ly q) by (img_try (unfold YF2l.QLv, QLv; rewrite Hrev; img_refl)). eapply val_mem_addr; [img_try (img_exact V3) | img_lia].
- img_apply (chunk_atom8 E _ _ _ 39%nat QBv); [img_refl | img_try (nums; img_lia) | img_try (eapply val_mem_addr; [img_exact V4 | img_lia])]. }
img_apply Forall_cons.
{   reg_intro. rewrite BV38.
split; [img_try (nums; img_lia)|]. split; [img_try (nums; img_lia)|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 16).
- img_apply (YF1k.val_mem_writable W mem _ _ _ _ C8); [img_try (cbn; img_lia) | img_try (img_apply off_img_high; nums; img_lia)].
- img_apply (YF1k.val_mem_writable W mem _ _ _ _ C16); [img_try (cbn; img_lia) | img_try (img_apply off_img_high; nums; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom8 E _ _ _ 46%nat BSZv); [img_refl | img_try (nums; img_lia) | img_try (img_exact C8)].
- img_apply (chunk_atom8 E _ _ _ 45%nat CNTv); [img_refl | img_try (nums; img_lia) | img_try (img_exact C16)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. rewrite BV47.
split; [img_try (nums; img_lia)|]. split; [img_try (nums; img_lia)|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable; [img_try (nums; img_lia)|]. img_apply slot_present. img_lia. }
+ img_apply pairwise_disjoint_of_extents. unfold YF2k.REG0, YF2k.R_ROOT, YF2k.R_LAST, YF2k.R_SLOT, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (YF2k.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 2 = getr regs 2). fold sp0.
img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (w64 T).
img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 38) with (w64 QLv).
img_change (ew (Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)) 47) with (w64 SLv).
unfold w64. rewrite !unsigned_lit_small by (img_try (nums; img_lia)).
unfold t_qc. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold YF2k.SLv, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kBatchBytes, kBatchSlots, kSpaceSize, kPrimResvSize, QSTACK in *.
repeat split; img_lia.
+ split; [|img_try (split; img_exact I)]. cbn [YF2k.FFP f_atoms atoms_ok].
set (E := Ereg regs (YF2k.XW ly u nn QSZv QLv QBv CNTv BSZv)).
assert (E2' : ew E 2 = w64 sp0) by (img_try (rewrite (YF2k.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew E 2 = getr regs 2); unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (AF : forall k0 Xv lo hi al, ew E k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, QSTACK in *.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp Hlo Hhi T4 T7 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_refl| | | |]. all: clear - CR0 TAL H1; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 34%nat u); [img_refl| | | |]. all: clear - CR0 U1 U2 U3 U4; first [img_lia | img_change (2 ^ 4) with 16; img_exact U3]. }
split. { img_apply (AF 35%nat nn); [img_refl| | | |]. all: clear - CR0 U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat QSZv); [img_refl| | | |]. all: clear - CR0 Qc QSZ1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat QLv); [img_refl| | | |]. all: clear - CR0 L3 L4 L5; first [img_lia | img_change (2 ^ 13) with 8192; img_exact L3]. }
split. { img_apply (AF 39%nat QBv); [img_refl| | | |]. all: clear - CR0 Qa Qb U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 45%nat CNTv); [img_refl| | | |]. all: clear - CR0 C0 HR; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 46%nat BSZv); [img_refl| | | |]. all: clear - CR0 B1 B2 Qa Qb U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 47%nat SLv); [img_refl| | | |]. all: clear - CR0 L3 L4 L5 C0 HR; unfold YF2k.SLv; first [img_lia | img_change (2 ^ 3) with 8; img_lia]. }
Qed.
Local Notation WINp := (YF2k.WIN ly regs QLv CNTv).
Local Notation S' := (YF0v.S' X k).
Lemma WIN_zone : forall a, WINp a -> (sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR. pose proof (lo_space_in ly LO) as [SI1 SI2].
unfold YF2k.WIN, YF2k.SLv in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- left. img_exact Hw.
- right; left. clear - Hw. unfold t_qc, kThreadObjSize in *. img_lia.
- right; right. clear - Hw L1 L2 SI2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
- right; right. clear - Hw L1 L2 SI2 HR. unfold CNTv, kBatchBytes, kBatchSlots, kSpaceSize, kPrimResvSize in *. img_lia.
Qed.
Lemma WIN_dec : forall a, WINp a \/ ~ WINp a.
Proof.
intros a. unfold YF2k.WIN. fold sp0.
destruct (Z_le_gt_dec (sp0 - 64) a); destruct (Z_lt_ge_dec a sp0); destruct (Z_le_gt_dec (T + t_qc + 24) a); destruct (Z_lt_ge_dec a (T + t_qc + 32));
destruct (Z_le_gt_dec (QLv + 8) a); destruct (Z_lt_ge_dec a (QLv + 24)); destruct (Z_le_gt_dec (SLv + 24) a); destruct (Z_lt_ge_dec a (SLv + 32)); img_lia.
Qed.
Definition low_okp {imgk : img} (a w : Z) : bool :=
((TFX_IMG_LO <=? a) && (a + w <=? TFX_IMG_END)) || ((SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)).
Definition const_loc_okp {imgk : img} (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okp a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okp (TFX_TSD + o) w
| ATp o => low_okp (TFX_TP + o) w
| AInst o => low_okp (TFX_INST + o) w
| _ => false
end.
Lemma Tfx_const_locp : forallb const_loc_okp (Tfx_const ly) = true.
Proof. clear. img_case; vm_compute. all: img_refl. Qed.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINp (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_locp c Hc) as K. unfold const_loc_okp in K.
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (YF1k.GEO B ly X W mem M) as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINp a).
{ intros a Hn Hw. img_exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okp a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINp (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_okp in L.
split; [img_try (img_apply ZN)|]; clear - L Hi H H1 T7 S1; unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, QSTACK, kThreadObjSize in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi H1 T4 T7 S1 S2 G_PT G_TS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
- split; [img_try (img_apply ZN)|]; clear - K Hi C1 C2 S1 S2 T4 T7 G_PC G_TC G_CS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi D1 D2 S1 S2 T4 T7 G_PD G_TD G_DS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma FINPH : forall W' c', YF2k.at_RETP W ly regs mem md u nn QLv QBv CNTv BSZv W' c' -> enq_leaf B ly X W regs mem md k (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL').
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS). cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (WD : forall a, WINp a -> YF0v.D ly lb sp0 a).
{ intros a Hw. unfold YF0v.D, YF0v.DT, YF0v.DL, YF0v.DS. unfold YF0v.QLv, YF0v.CNTv.
unfold YF2k.WIN, YF2k.SLv in Hw. fold sp0 in Hw. unfold QLv, CNTv in Hw.
destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [img_try (do 2 right; clear - Hw; unfold QSTACK; img_lia) | img_try (left; img_exact Hw) | img_try (right; left; left; img_exact Hw) | img_try (right; left; right; img_lia)]. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0v.D ly lb sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (mem' x) as [b'|] eqn:E'; [img_try (cbn in HN; discriminate)|].
destruct (mem x) as [b0|] eqn:Eb0; [|img_try (img_exact (Hv HN))].
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- img_apply (MEQ' x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes q + nn) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V1); [img_refl | img_try (unfold YF2l.QBv; img_refl)]. }
assert (NEW_lsz : forall i, (i < 8)%nat -> rd' (YF0v.QLv ly lb + 8 + Z.of_nat i) = Some (YG0h.le_byte (b_bytes lb + nn) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V2); [img_try (unfold YF0v.QLv, QLv; img_refl) | img_try (unfold BSZv; img_refl)]. }
assert (NEW_lcnt : forall i, (i < 8)%nat -> rd' (YF0v.QLv ly lb + 16 + Z.of_nat i) = Some (YG0h.le_byte (YF0v.CNTv lb + 1) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V3); [img_try (unfold YF0v.QLv, QLv; img_refl) | img_try (unfold YF0v.CNTv, CNTv; img_refl)]. }
assert (NEW_slot : forall i, (i < 8)%nat -> rd' (YF0v.QLv ly lb + 24 + 8 * YF0v.CNTv lb + Z.of_nat i) = Some (YG0h.le_byte (u - 16) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V4); [img_try (unfold YF2k.SLv, YF0v.QLv, YF0v.CNTv, QLv, CNTv; img_lia) | img_refl]. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc))|].
intros i Hi. (subst rd rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as [X1 X2]. img_apply aview_same.
img_apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. img_exact X1. }
pose proof (YF0v.enq_finp_ARm B TB ly X rd rd' M' k Hk Hst Hnq lb initr Hrev Hroom sp0 HSP' IMG AG VIS NEW_qb NEW_lsz NEW_lcnt NEW_slot CONST') as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md), None. split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split.
2:{ split; [img_refl|]. split; [img_try (img_exact HNB)|]. split; [img_refl|]. split; img_refl. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
- split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0v.ALedger_S' ly X k tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0v.asecA_S' ly X k _ PIN))].
eapply Z.le_trans; [img_try (img_exact BUD)|]. rewrite <- (YF0v.abudget_S' X k). img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) | img_refl].
* img_refl.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
pose proof ZT as hT. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize in hT.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold YF0v.D, YF0v.DT, YF0v.DL, YF0v.DS, YF0v.QLv, YF0v.CNTv. unfold QLv in L4.
clear - SBg hT L4 T7 HSP' HR. unfold kHighMemBeg, QSTACK, CNTv, kBatchSlots, t_qc in *. intros [Y|[[Y|Y]|Y]]; img_lia.
- intros r Hr'. img_apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear - R. unfold YF2k.CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]).
- img_apply same_io_wvb.
- intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0v.D_owned B ly X rd M' lb initr Hrev Hroom sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Ha)]. img_apply MEQ'.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Usp HSP' T7; unfold QSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof (YF1k.GEO B ly X W mem M) as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' H H1. ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. img_lia.
+ img_apply PRESW. unfold YF2k.WIN. left. fold sp0. img_lia.
Qed.
Theorem tfx_enqueue_room_arm :
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
rewrite (enqueue_room_eq k X HNB). img_change (set_qthread (qc_push q k None) X) with S'. cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- img_exact (YF2y.segP W ly regs mem md u nn QSZv QLv QBv CNTv BSZv (m_vm_materialized md) FH_ok).
- intros W' c' _ HR. img_exact (FINPH W' c' HR).
Qed.
End e.
Theorem tfx_enqueue_room {imgk : img} : forall B, TfxSyms B -> tfx_enqueue_spec_nb B false.
Proof.
intros B TB ly X W regs mem md k HNB ENQ. pose proof ENQ as ((M0 & _) & _).
img_exact (tfx_enqueue_room_arm B TB ly X W regs mem md k ENQ HNB ltac:(img_try (rewrite (am_tsd B ly X _ M0); img_apply (ts_tsd _ TB)))).
Qed.
End d.
