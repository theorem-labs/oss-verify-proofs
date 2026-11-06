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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0j YF0i YF2j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
Definition oRI : nat := 32.
Definition oC : nat := 33.
Definition oRG : nat := 34.
Definition oNF : nat := 35.
Definition oJ80 : nat := 36.
Definition oJ88 : nat := 37.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (ri c nf j80 j88 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x34958 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W regs0 mem0 ri c nf j80 j88.
Local Notation RGv := (YF2j.RGv ri c).
Local Notation XW := (YF2j.XW ri c nf j80 j88).
Local Notation E0 := (YF2j.E0 regs0 ri c nf j80 j88).
Local Notation Er := (YF2j.Er regs0 ri c nf j80 j88).
Local Notation E2 := (YF2j.E2 regs0 ri c nf j80 j88).
Local Notation E1 := (YF2j.E1 regs0 ri c nf j80 j88).
Local Notation EqRI := (YF2j.EqRI regs0 ri c nf j80 j88).
Local Notation EqC := (YF2j.EqC regs0 ri c nf j80 j88).
Local Notation EqRG := (YF2j.EqRG regs0 ri c nf j80 j88).
Local Notation EqNF := (YF2j.EqNF regs0 ri c nf j80 j88).
Local Notation EqJ80 := (YF2j.EqJ80 regs0 ri c nf j80 j88).
Local Notation EqJ88 := (YF2j.EqJ88 regs0 ri c nf j80 j88).
Local Notation R_RGO := YF2j.R_RGO.
Local Notation REG0 := YF2j.REG0.
Local Notation FFO := YF2j.FFO.
Local Notation SR0 := YF2j.SR0.
Local Notation SS0 := YF2j.SS0.
Local Notation derived_ranges := (YF2j.derived_ranges W regs0 mem0 ri c nf j80 j88 FH).
Local Notation WIN := (YF2j.WIN regs0).
Local Notation win_sub := YF2j.win_sub.
Local Notation win_sub_sound := (YF2j.win_sub_sound regs0).
Local Notation WSK0 := YF2j.WSK0.
Local Notation sk_ok := (YF2j.sk_ok regs0).
Local Notation WSK0_ok := (YF2j.WSK0_ok W regs0 mem0 ri c nf j80 j88 FH).
Local Notation windows_WIN := (YF2j.windows_WIN regs0).
Local Notation MEQ := (YF2j.MEQ regs0 mem0).
Local Notation MEQ_frame := (YF2j.MEQ_frame regs0 mem0).
Local Notation MEQ_0 := (YF2j.MEQ_0 regs0 mem0).
Local Notation at_RETO := (YF2j.at_RETO W regs0 mem0 md0).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hra Hsp Hsp_al Hpres Hc Hri Hvals Hdisj SEED].
Ltac off_by tac :=
first [ img_apply off_img_high; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac fin_O SK0 Hwx Hra BV2 Usp Hlo :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
eapply (SRr_ret_at tfxsegs tfxtbl_rtK tfxtbl_rtK_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |];
let mat' := fresh "mat'" in
intros mat'; split; [img_refl|]; exists (ms_regs msx), (ms_mem msx), mat'; cbn [ms_regs ms_mem mkst];
let Q1 := fresh "Q1" in
rreg HS (1%bv : bv 5) Q1; rewrite E1 in Q1;
split; [img_try (rewrite Q1; unfold YK0s.ret_ok in Hra; rewrite Hra; img_refl)|];
split; [img_try (eapply (regs_preserved_of_st_ok tfxsegs E0 _ _ regs0 XW HS); [img_apply env_agree_refl | (img_case; vm_compute); img_refl])|];
split; [lazymatch goal with M : MEQ _ |- _ => img_exact M end|];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; unfold YF2j.WIN in Ha;
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
[img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo; numconst; zlia)) ]
end
end.
Lemma segO : SRr tfxsegs W cfg0 at_RETO.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
pose proof derived_ranges as DR. pose proof DR as (dK1 & dK2 & dI1 & dI2 & dG0 & dG1 & dG2 & dC & dN & dJ1 & dJ2).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = ri) by (img_try (unfold rho_of; rewrite EqRI; unfold w64; img_apply unsigned_lit_small; clear - dI1 dI2; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = c) by (img_try (unfold rho_of; rewrite EqC; unfold w64; img_apply unsigned_lit_small; clear - dC; zlia)).
assert (R34 : rho_of E0 34%nat = RGv) by (img_try (unfold rho_of; rewrite EqRG; unfold w64; img_apply unsigned_lit_small; clear - dI1 dI2 dG1 dG2; numconst; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV34 : bv_unsigned (ew E0 34) = RGv) by img_exact R34.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SK0. dbg HS.
srr_branch_sh tfxtbl_rtK_ok HS.
all: unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
all: srr_run_to_sh tfxtbl_rtK_ok HS (0x349e4 + D_150); meq_acc SK0; dbg HS.
all: apply (st_ok_pin_regU _ _ _ 22%bv (SOff 34%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R34, ?R32, ?R33, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id c) by (img_try (clear - dC; unfold M64; zlia)); rewrite ?Z.shiftl_mul_pow2 by zlia;
unfold YF2j.RGv; clear - dC dI1 dI2; numconst; zcanon_simp; zlia ].
all: cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
all: srr_run_sh tfxtbl_rtK_ok HS; meq_acc SK0; dbg HS.
all: srr_branch_sh tfxtbl_rtK_ok HS.
all: unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
all: dbg HS.
all: srr_run_sh tfxtbl_rtK_ok HS; meq_acc SK0; dbg HS.
all: try (srr_branch_sh tfxtbl_rtK_ok HS; unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfxtbl_rtK_ok HS; meq_acc SK0).
all: fin_O SK0 Hwx Hra BV2 Usp Hlo.
Qed.
End WK.
End b.
