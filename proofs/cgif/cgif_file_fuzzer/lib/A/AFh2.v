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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
Definition oRI : nat := 32.
Definition oC : nat := 33.
Definition oRG : nat := 34.
Definition oNF : nat := 35.
Definition oJ80 : nat := 36.
Definition oJ88 : nat := 37.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (ri c nf j80 j88 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34350) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W regs0 mem0 ri c nf j80 j88.
Local Notation RGv := (AFgo.RGv ri c).
Local Notation XW := (AFgo.XW ri c nf j80 j88).
Local Notation E0 := (AFgo.E0 regs0 ri c nf j80 j88).
Local Notation Er := (AFgo.Er regs0 ri c nf j80 j88).
Local Notation E2 := (AFgo.E2 regs0 ri c nf j80 j88).
Local Notation E1 := (AFgo.E1 regs0 ri c nf j80 j88).
Local Notation EqRI := (AFgo.EqRI regs0 ri c nf j80 j88).
Local Notation EqC := (AFgo.EqC regs0 ri c nf j80 j88).
Local Notation EqRG := (AFgo.EqRG regs0 ri c nf j80 j88).
Local Notation EqNF := (AFgo.EqNF regs0 ri c nf j80 j88).
Local Notation EqJ80 := (AFgo.EqJ80 regs0 ri c nf j80 j88).
Local Notation EqJ88 := (AFgo.EqJ88 regs0 ri c nf j80 j88).
Local Notation R_RGO := AFgo.R_RGO.
Local Notation REG0 := AFgo.REG0.
Local Notation FFO := AFgo.FFO.
Local Notation SR0 := AFgo.SR0.
Local Notation SS0 := AFgo.SS0.
Local Notation derived_ranges := (AFgo.derived_ranges W regs0 mem0 ri c nf j80 j88 FH).
Local Notation WIN := (AFgo.WIN regs0).
Local Notation win_sub := AFgo.win_sub.
Local Notation win_sub_sound := (AFgo.win_sub_sound regs0).
Local Notation WSK0 := AFgo.WSK0.
Local Notation sk_ok := (AFgo.sk_ok regs0).
Local Notation WSK0_ok := (AFgo.WSK0_ok W regs0 mem0 ri c nf j80 j88 FH).
Local Notation windows_WIN := (AFgo.windows_WIN regs0).
Local Notation MEQ := (AFgo.MEQ regs0 mem0).
Local Notation MEQ_frame := (AFgo.MEQ_frame regs0 mem0).
Local Notation MEQ_0 := (AFgo.MEQ_0 regs0 mem0).
Local Notation at_RETO := (AFgo.at_RETO W regs0 mem0 md0).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hra Hsp Hsp_al Hpres Hc Hri Hvals Hdisj SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac fin_O SK0 Hwx Hra BV2 Usp Hlo :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
eapply (SRr_ret_at tfibsegs tfibtbl_rtK tfibtbl_rtK_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat'" in
intros mat'; split; [reflexivity|]; exists (ms_regs msx), (ms_mem msx), mat'; cbn [ms_regs ms_mem mkst];
let Q1 := fresh "Q1" in
rreg HS (1%bv : bv 5) Q1; rewrite E1 in Q1;
split; [rewrite Q1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
split; [eapply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs0 XW HS); [apply env_agree_refl | vm_compute; reflexivity]|];
split; [lazymatch goal with M : MEQ _ |- _ => exact M end|];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; unfold AFgo.WIN in Ha;
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
[reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Usp Hlo; numconst; zlia) ]
end
end.
Lemma segO : SRr tfibsegs W cfg0 at_RETO.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
pose proof derived_ranges as DR. pose proof DR as (dK1 & dK2 & dI1 & dI2 & dG0 & dG1 & dG2 & dC & dN & dJ1 & dJ2).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = ri) by (unfold rho_of; rewrite EqRI; unfold w64; apply unsigned_lit_small; clear - dI1 dI2; numconst; zlia).
assert (R33 : rho_of E0 33%nat = c) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - dC; zlia).
assert (R34 : rho_of E0 34%nat = RGv) by (unfold rho_of; rewrite EqRG; unfold w64; apply unsigned_lit_small; clear - dI1 dI2 dG1 dG2; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV34 : bv_unsigned (ew E0 34) = RGv) by exact R34.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SK0. dbg HS.
srr_branch_sh tfibtbl_rtK_ok HS.
all: unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
all: srr_run_to_sh tfibtbl_rtK_ok HS 0x343dc; meq_acc SK0; dbg HS.
all: apply (st_ok_pin_regU _ _ _ 22%bv (SOff 34%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R34, ?R32, ?R33, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id c) by (clear - dC; unfold M64; zlia); rewrite ?Z.shiftl_mul_pow2 by zlia;
unfold AFgo.RGv; clear - dC dI1 dI2; numconst; zcanon_simp; zlia ].
all: cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
all: srr_run_sh tfibtbl_rtK_ok HS; meq_acc SK0; dbg HS.
all: srr_branch_sh tfibtbl_rtK_ok HS.
all: unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
all: dbg HS.
all: srr_run_sh tfibtbl_rtK_ok HS; meq_acc SK0; dbg HS.
all: try (srr_branch_sh tfibtbl_rtK_ok HS; unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfibtbl_rtK_ok HS; meq_acc SK0).
all: fin_O SK0 Hwx Hra BV2 Usp Hlo.
Qed.
End WK.
End b.
