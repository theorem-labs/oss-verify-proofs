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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF2k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn qsz ql qb cnt bsz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x35dd8 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 u nn qsz ql qb cnt bsz.
Local Notation SLv := (YF2k.SLv ql cnt).
Local Notation XW := (YF2k.XW ly u nn qsz ql qb cnt bsz).
Local Notation E0 := (YF2k.E0 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation Er := (YF2k.Er ly regs0 u nn qsz ql qb cnt bsz).
Local Notation E2 := (YF2k.E2 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation E1 := (YF2k.E1 ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqT := (YF2k.EqT ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqU := (YF2k.EqU ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqN := (YF2k.EqN ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQSZ := (YF2k.EqQSZ ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQL := (YF2k.EqQL ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqQB := (YF2k.EqQB ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqCNT := (YF2k.EqCNT ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqBSZ := (YF2k.EqBSZ ly regs0 u nn qsz ql qb cnt bsz).
Local Notation EqSL := (YF2k.EqSL ly regs0 u nn qsz ql qb cnt bsz).
Local Notation R_ROOT := YF2k.R_ROOT.
Local Notation R_LAST := YF2k.R_LAST.
Local Notation R_SLOT := YF2k.R_SLOT.
Local Notation REG0 := YF2k.REG0.
Local Notation FFP := YF2k.FFP.
Local Notation SR0 := YF2k.SR0.
Local Notation SS0 := YF2k.SS0.
Local Notation LYB := (YF2k.LYB W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation derived_ranges := (YF2k.derived_ranges W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation WIN := (YF2k.WIN ly regs0 ql cnt).
Local Notation win_sub := YF2k.win_sub.
Local Notation win_sub_sound := (YF2k.win_sub_sound ly regs0).
Local Notation WSK0 := YF2k.WSK0.
Local Notation sk_ok := (YF2k.sk_ok ly regs0 ql cnt).
Local Notation WSK0_ok := (YF2k.WSK0_ok W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation windows_WIN := (YF2k.windows_WIN ly regs0 ql cnt).
Local Notation WIN_zone := (YF2k.WIN_zone W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation WIN_off := (YF2k.WIN_off W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Local Notation MEQ := (YF2k.MEQ ly regs0 mem0 ql cnt).
Local Notation MEQ_frame := (YF2k.MEQ_frame ly regs0 mem0 ql cnt).
Local Notation MEQ_0 := (YF2k.MEQ_0 ly regs0 mem0 ql cnt).
Local Notation CALLEE_SAVED := YF2k.CALLEE_SAVED.
Local Notation at_RETP := (YF2k.at_RETP W ly regs0 mem0 md0 u nn ql qb cnt bsz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hra4096 Hsp Hsp_al Hpres Hu IMG Hnn Hq Hlast SEED].
Local Notation off_T := (YF2k.off_T W ly regs0 mem0 u nn qsz ql qb cnt bsz FH).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
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
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtF ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YQ0b.mkChunk ?o _) :: ?t => let e := img_ev (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := img_ev (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := img_ev (YQ0b.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. img_apply bv_eq. rewrite Z_to_bv_unsigned. img_change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. img_apply Z.mod_small. img_exact Hv.
Qed.
Lemma segP : SRr tfxsegs W cfg0 at_RETP.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
pose proof DR as (dU1 & dU2 & dN & dQSZ & dQB1 & dQB2 & dQL1 & dQL2 & dQLal & dCNT & dBSZ1 & dBSZ2 & dSL & dT1 & dT2 & dS1 & dS2).
destruct Hlast as (L1 & L2 & L3 & L4 & L5 & L6 & PresL & PresS).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R36 : rho_of E0 36%nat = qsz) by (img_try (unfold rho_of; rewrite EqQSZ; unfold w64; img_apply unsigned_lit_small; clear - dQSZ; zlia)).
assert (R45 : rho_of E0 45%nat = cnt) by (img_try (unfold rho_of; rewrite EqCNT; unfold w64; img_apply unsigned_lit_small; clear - dCNT; numconst; zlia)).
assert (R38 : rho_of E0 38%nat = ql) by (img_try (unfold rho_of; rewrite EqQL; unfold w64; img_apply unsigned_lit_small; clear - dQL1 dQL2; numconst; zlia)).
assert (R47 : rho_of E0 47%nat = SLv) by (img_try (unfold rho_of; rewrite EqSL; unfold w64; img_apply unsigned_lit_small; clear - dQL1 dQL2 dSL dCNT; numconst; zlia)).
assert (R39 : rho_of E0 39%nat = qb) by (img_try (unfold rho_of; rewrite EqQB; unfold w64; img_apply unsigned_lit_small; clear - dQB1 dQB2 dN; zlia)).
assert (R35 : rho_of E0 35%nat = nn) by (img_try (unfold rho_of; rewrite EqN; unfold w64; img_apply unsigned_lit_small; clear - dN; zlia)).
assert (R46 : rho_of E0 46%nat = bsz) by (img_try (unfold rho_of; rewrite EqBSZ; unfold w64; img_apply unsigned_lit_small; clear - dBSZ1 dBSZ2 dN; zlia)).
assert (R34 : rho_of E0 34%nat = u) by (img_try (unfold rho_of; rewrite EqU; unfold w64; img_apply unsigned_lit_small; clear - dU1 dU2 dN; numconst; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV32 : bv_unsigned (ew E0 32) = T) by (img_try (rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - dT1 dT2; numconst; zlia)).
assert (BV38 : bv_unsigned (ew E0 38) = ql) by img_exact R38.
assert (BV47 : bv_unsigned (ew E0 47) = SLv) by img_exact R47.
srr_run_sh tfxtbl_rtF_ok HS. meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 47%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, R47, R38, R45;
img_change (Z.land (zcanon 3) 63) with 3; rewrite Z.shiftl_mul_pow2 by zlia; unfold YF2k.SLv; clear - dQL1 dQL2 dCNT; numconst; zcanon_simp;
unfold zcanon, M64; zlia) ].
unpin HS.
srr_run_sh tfxtbl_rtF_ok HS. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtF tfxtbl_rtF_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (RA : getr (ms_regs msR) 1 = getr regs0 1) by (img_try (reg_entry HS (1%bv : bv 5) 1%nat)).
split. { rewrite RA. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { intros r Hr. cbn [YF2k.CALLEE_SAVED In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
first [ reg_entry HS (2%bv : bv 5) 2%nat | reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat | reg_entry HS (19%bv : bv 5) 19%nat
| reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat
| reg_entry HS (24%bv : bv 5) 24%nat | reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { img_exact MQ. }
split. { intros a Ha. unfold YF2k.WIN in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; unfold sp0 in *; zlia) | img_try (off_by ltac:(clear - Ha Usp dS1 dS2; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; numconst; zlia) | img_try (off_by ltac:(clear - Ha dT1 dT2; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV38; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha dQL1 dQL2; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV47; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha dQL1 dQL2 dSL dCNT; numconst; zlia)) ]. }
cbv zeta.
split. { memvo HS 1%nat 104; [img_try (rewrite BV32; numconst; zlia)
| img_try (img_apply denot_by_zev; [img_refl | clear - dQB1 dQB2 dN; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R39, ?R35; clear - dQB1 dQB2 dN; zcanon_simp; zlia])
| img_try (clear - dQB1 dQB2 dN; zlia)]. }
split. { memvo HS 2%nat 8; [img_try (rewrite BV38; zlia)
| img_try (img_apply denot_by_zev; [img_refl | clear - dBSZ1 dBSZ2 dN; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R46, ?R35; clear - dBSZ1 dBSZ2 dN; zcanon_simp; zlia])
| img_try (clear - dBSZ1 dBSZ2 dN; zlia)]. }
split. { memvo HS 2%nat 16; [img_try (rewrite BV38; zlia)
| img_try (img_apply denot_by_zev; [img_refl | clear - dCNT; numconst; zlia | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R45; clear - dCNT; numconst; zcanon_simp; zlia])
| img_try (clear - dCNT; numconst; zlia)]. }
memvo HS 3%nat 24; [img_try (rewrite BV47; zlia)
| img_try (cbn [sv_denot]; rewrite EqU; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia)
| img_try (clear - dU1 dU2 dN; numconst; zlia)].
Qed.
End WK.
End b.
