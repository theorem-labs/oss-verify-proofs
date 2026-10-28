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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFgp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn qsz ql qb cnt bsz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x357d0) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 u nn qsz ql qb cnt bsz.
Local Notation SLv := (AFgp.SLv ql cnt).
Local Notation XW := (AFgp.XW ly u nn qsz ql qb cnt bsz).
Local Notation E0 := (AFgp.E0 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation Er := (AFgp.Er ly regs0 u nn qsz ql qb cnt bsz).
Local Notation E2 := (AFgp.E2 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation E1 := (AFgp.E1 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqT := (AFgp.EqT ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqU := (AFgp.EqU ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqN := (AFgp.EqN ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQSZ := (AFgp.EqQSZ ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQL := (AFgp.EqQL ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQB := (AFgp.EqQB ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqCNT := (AFgp.EqCNT ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqBSZ := (AFgp.EqBSZ ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqSL := (AFgp.EqSL ly regs0 u nn qsz ql qb cnt bsz).
Local Notation R_ROOT := AFgp.R_ROOT.
Local Notation R_LAST := AFgp.R_LAST.
Local Notation R_SLOT := AFgp.R_SLOT.
Local Notation REG0 := AFgp.REG0.
Local Notation FFP := AFgp.FFP.
Local Notation SR0 := AFgp.SR0.
Local Notation SS0 := AFgp.SS0.
Local Notation LYB := (AFgp.LYB W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation derived_ranges := (AFgp.derived_ranges W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation WIN := (AFgp.WIN ly regs0 ql cnt).
Local Notation win_sub := AFgp.win_sub.
Local Notation win_sub_sound := (AFgp.win_sub_sound ly regs0).
Local Notation WSK0 := AFgp.WSK0.
Local Notation sk_ok := (AFgp.sk_ok ly regs0 ql cnt).
Local Notation WSK0_ok := (AFgp.WSK0_ok W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation windows_WIN := (AFgp.windows_WIN ly regs0 ql cnt).
Local Notation WIN_zone := (AFgp.WIN_zone W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation WIN_off := (AFgp.WIN_off W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation MEQ := (AFgp.MEQ ly regs0 mem0 ql cnt).
Local Notation MEQ_frame := (AFgp.MEQ_frame ly regs0 mem0 ql cnt).
Local Notation MEQ_0 := (AFgp.MEQ_0 ly regs0 mem0 ql cnt).
Local Notation CALLEE_SAVED := AFgp.CALLEE_SAVED.
Local Notation at_RETP := (AFgp.at_RETP W ly regs0 mem0 md0 u nn ql qb cnt bsz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hra4096 Hsp Hsp_al Hpres Hu IMG Hnn Hq Hlast SEED].
Local Notation off_T := (AFgp.off_T W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
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
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtF ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
Lemma segP : SRr tfibsegs W cfg0 at_RETP.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQB1 & dQB2 & dQL1 & dQL2 & dQLal & dCNT & dBSZ1 & dBSZ2 & dSL & dT1 & dT2 & dS1 & dS2).
destruct Hlast as (L1 & L2 & L3 & L4 & L5 & L6 & PresL & PresS).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R36 : rho_of E0 36%nat = qsz) by (unfold rho_of; rewrite EqQSZ; unfold w64; apply unsigned_lit_small; clear - dQSZ; zlia).
assert (R45 : rho_of E0 45%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - dCNT; numconst; zlia).
assert (R38 : rho_of E0 38%nat = ql) by (unfold rho_of; rewrite EqQL; unfold w64; apply unsigned_lit_small; clear - dQL1 dQL2; numconst; zlia).
assert (R47 : rho_of E0 47%nat = SLv) by (unfold rho_of; rewrite EqSL; unfold w64; apply unsigned_lit_small; clear - dQL1 dQL2 dSL dCNT; numconst; zlia).
assert (R39 : rho_of E0 39%nat = qb) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - dQB1 dQB2 dN; zlia).
assert (R35 : rho_of E0 35%nat = nn) by (unfold rho_of; rewrite EqN; unfold w64; apply unsigned_lit_small; clear - dN; zlia).
assert (R46 : rho_of E0 46%nat = bsz) by (unfold rho_of; rewrite EqBSZ; unfold w64; apply unsigned_lit_small; clear - dBSZ1 dBSZ2 dN; zlia).
assert (R34 : rho_of E0 34%nat = u) by (unfold rho_of; rewrite EqU; unfold w64; apply unsigned_lit_small; clear - dU1 dU2 dN; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV32 : bv_unsigned (ew E0 32) = T) by (rewrite EqT; unfold w64; apply unsigned_lit_small; clear - dT1 dT2; numconst; zlia).
assert (BV38 : bv_unsigned (ew E0 38) = ql) by exact R38.
assert (BV47 : bv_unsigned (ew E0 47) = SLv) by exact R47.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 47%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, R47, R38, R45;
change (Z.land (zcanon 3) 63) with 3; rewrite Z.shiftl_mul_pow2 by zlia; unfold AFgp.SLv; clear - dQL1 dQL2 dCNT; numconst; zcanon_simp;
unfold zcanon, M64; zlia ].
unpin HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (RA : getr (ms_regs msR) 1 = getr regs0 1) by (reg_entry HS (1%bv : bv 5) 1%nat).
split. { rewrite RA. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { intros r Hr. cbn [AFgp.CALLEE_SAVED In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
first [ reg_entry HS (2%bv : bv 5) 2%nat | reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat | reg_entry HS (19%bv : bv 5) 19%nat
| reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat
| reg_entry HS (24%bv : bv 5) 24%nat | reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { exact MQ. }
split. { intros a Ha. unfold AFgp.WIN in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; unfold sp0 in *; zlia | off_by ltac:(clear - Ha Usp dS1 dS2; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha dT1 dT2; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV38; clear - Ha; zlia | off_by ltac:(clear - Ha dQL1 dQL2; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV47; clear - Ha; zlia | off_by ltac:(clear - Ha dQL1 dQL2 dSL dCNT; numconst; zlia) ]. }
cbv zeta.
split. { memvo HS 1%nat 104; [rewrite BV32; numconst; zlia
| apply denot_by_zev; [reflexivity | clear - dQB1 dQB2 dN; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R39, ?R35; clear - dQB1 dQB2 dN; zcanon_simp; zlia]
| clear - dQB1 dQB2 dN; zlia]. }
split. { memvo HS 2%nat 8; [rewrite BV38; zlia
| apply denot_by_zev; [reflexivity | clear - dBSZ1 dBSZ2 dN; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R46, ?R35; clear - dBSZ1 dBSZ2 dN; zcanon_simp; zlia]
| clear - dBSZ1 dBSZ2 dN; zlia]. }
split. { memvo HS 2%nat 16; [rewrite BV38; zlia
| apply denot_by_zev; [reflexivity | clear - dCNT; numconst; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R45; clear - dCNT; numconst; zcanon_simp; zlia]
| clear - dCNT; numconst; zlia]. }
memvo HS 3%nat 24; [rewrite BV47; zlia
| cbn [sv_denot]; rewrite EqU; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia
| clear - dU1 dU2 dN; numconst; zlia].
Qed.
End WK.
End b.
