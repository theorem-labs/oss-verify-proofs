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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0j YF0i YF2f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
Definition kT : nat := 32.
Definition kSB : nat := 33.
Definition kP : nat := 34.
Definition kC : nat := 35.
Definition kPC : nat := 36.
Definition kCNT : nat := 37.
Definition kMAX : nat := 38.
Definition kSZ : nat := 39.
Definition kSLOT : nat := 40.
Definition kRG : nat := 41.
Definition kOLD : nat := 42.
Definition kMF : nat := 43.
Definition kDST : nat := 44.
Definition kSRC : nat := 45.
Definition kJ80 : nat := 46.
Definition kJ88 : nat := 47.
Definition kJST : nat := 48.
Definition kRI : nat := 49.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33f78 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst.
Local Notation Pv := (YF2f.Pv ly off).
Local Notation PCv := (YF2f.PCv ly c).
Local Notation MAXv := (YF2f.MAXv c).
Local Notation SZv := (YF2f.SZv c).
Local Notation Nv := (YF2f.Nv c).
Local Notation CNTPv := (YF2f.CNTPv c cnt).
Local Notation SLOTv := (YF2f.SLOTv ly c cnt).
Local Notation RIv := (YF2f.RIv ly).
Local Notation RGv := (YF2f.RGv ly c).
Local Notation RBv := (YF2f.RBv ly c).
Local Notation FAv := (YF2f.FAv ly c).
Local Notation DSTv := (YF2f.DSTv ly c old).
Local Notation SRCv := (YF2f.SRCv ly c cnt).
Local Notation RELv := (YF2f.RELv c off).
Local Notation XW := (YF2f.XW ly c off cnt old mf j80 j88 jst).
Local Notation E0 := (YF2f.E0 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation Er := (YF2f.Er ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E2 := (YF2f.E2 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E1 := (YF2f.E1 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqT := (YF2f.EqT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSB := (YF2f.EqSB ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqP := (YF2f.EqP ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqC := (YF2f.EqC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqPC := (YF2f.EqPC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqCNT := (YF2f.EqCNT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMAX := (YF2f.EqMAX ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSZ := (YF2f.EqSZ ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSLOT := (YF2f.EqSLOT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRG := (YF2f.EqRG ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqOLD := (YF2f.EqOLD ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMF := (YF2f.EqMF ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqDST := (YF2f.EqDST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSRC := (YF2f.EqSRC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ80 := (YF2f.EqJ80 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ88 := (YF2f.EqJ88 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJST := (YF2f.EqJST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRI := (YF2f.EqRI ly regs0 c off cnt old mf j80 j88 jst).
Local Notation R_PC := YF2f.R_PC.
Local Notation R_JST := YF2f.R_JST.
Local Notation R_STK_HI := YF2f.R_STK_HI.
Local Notation R_STK_LO := YF2f.R_STK_LO.
Local Notation REG0 := YF2f.REG0.
Local Notation R_SLOT := YF2f.R_SLOT.
Local Notation R_RGA := YF2f.R_RGA.
Local Notation R_RGB := YF2f.R_RGB.
Local Notation R_RGC := YF2f.R_RGC.
Local Notation WRG := (YF2f.WRG ly c).
Local Notation FFK := YF2f.FFK.
Local Notation SR0 := YF2f.SR0.
Local Notation SS0 := YF2f.SS0.
Local Notation LYB := (YF2f.LYB W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation class_facts := (YF2f.class_facts W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation derived_ranges := (YF2f.derived_ranges W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINF := (YF2f.WINF ly c cnt).
Local Notation WINR := (YF2f.WINR ly c cnt old).
Local Notation WIN := (YF2f.WIN ly regs0 c cnt old).
Local Notation win_sub := YF2f.win_sub.
Local Notation win_sub_sound := (YF2f.win_sub_sound ly regs0).
Local Notation WSK0 := YF2f.WSK0.
Local Notation WSKR := YF2f.WSKR.
Local Notation sk_ok := (YF2f.sk_ok ly regs0 c cnt old).
Local Notation WSK0_ok := (YF2f.WSK0_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WSKR_ok := (YF2f.WSKR_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WIN := (YF2f.windows_WIN ly regs0 c cnt old).
Local Notation WIN_zone := (YF2f.WIN_zone W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WIN_off := (YF2f.WIN_off W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation MEQ := (YF2f.MEQ ly regs0 mem0 c cnt old).
Local Notation MEQ_frame := (YF2f.MEQ_frame ly regs0 mem0 c cnt old).
Local Notation MEQ_0 := (YF2f.MEQ_0 ly regs0 mem0 c cnt old).
Local Notation WINX := (YF2f.WINX ly regs0 c cnt).
Local Notation WINX_WIN := (YF2f.WINX_WIN ly regs0 c cnt old).
Local Notation sk_okX := (YF2f.sk_okX ly regs0 c cnt).
Local Notation WSKX := YF2f.WSKX.
Local Notation WSKX_okX := (YF2f.WSKX_okX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINX := (YF2f.windows_WINX ly regs0 c cnt).
Local Notation MEQX := (YF2f.MEQX ly regs0 mem0 c cnt).
Local Notation MEQX_frame := (YF2f.MEQX_frame ly regs0 mem0 c cnt).
Local Notation MEQX_0 := (YF2f.MEQX_0 ly regs0 mem0 c cnt).
Local Notation MEQX_MEQ := (YF2f.MEQX_MEQ ly regs0 mem0 c cnt old).
Local Notation DST_notWINX := (YF2f.DST_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation SRC_notWINX := (YF2f.SRC_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINY := (YF2f.WINY ly regs0 c cnt).
Local Notation WINY_WIN := (YF2f.WINY_WIN ly regs0 c cnt old).
Local Notation WINX_WINY := (YF2f.WINX_WINY ly regs0 c cnt).
Local Notation DST_notWINY := (YF2f.DST_notWINY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation sk_okY := (YF2f.sk_okY ly regs0 c cnt).
Local Notation WSKR_okY := (YF2f.WSKR_okY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINY := (YF2f.windows_WINY ly regs0 c cnt).
Local Notation MEQY := (YF2f.MEQY ly regs0 c cnt).
Local Notation MEQY_frame := (YF2f.MEQY_frame ly regs0 c cnt).
Local Notation MEQY_0 := (YF2f.MEQY_0 ly regs0 c cnt).
Local Notation all_disjoint_of_forall := YF2f.all_disjoint_of_forall.
Local Notation SREGS := YF2f.SREGS.
Local Notation at_RETK := (YF2f.at_RETK W ly regs0 mem0 md0 c off cnt old mf).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
Local Notation off_T := (YF2f.off_T W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
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
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
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
Lemma segK1 : cnt < MAXv -> SRr tfxsegs W cfg0 at_RETK.
Proof.
intros HLT. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (HCP : CNTPv = cnt) by (img_try (unfold YF2f.CNTPv; destruct (Z.eqb_spec cnt MAXv); [img_try (zlia) | img_refl])).
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - LB; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = SB) by (img_try (unfold rho_of; rewrite EqSB; unfold w64; img_apply unsigned_lit_small; clear - LB; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = Pv) by (img_try (unfold rho_of; rewrite EqP; unfold w64; img_apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia)).
assert (R35 : rho_of E0 35%nat = c) by (img_try (unfold rho_of; rewrite EqC; unfold w64; img_apply unsigned_lit_small; clear - Hc; zlia)).
assert (R36 : rho_of E0 36%nat = PCv) by (img_try (unfold rho_of; rewrite EqPC; unfold w64; img_apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia)).
assert (R37 : rho_of E0 37%nat = cnt) by (img_try (unfold rho_of; rewrite EqCNT; unfold w64; img_apply unsigned_lit_small; clear - Hcnt K3; zlia)).
assert (R38 : rho_of E0 38%nat = MAXv) by (img_try (unfold rho_of; rewrite EqMAX; unfold w64; img_apply unsigned_lit_small; clear - K3; zlia)).
assert (R39 : rho_of E0 39%nat = SZv) by (img_try (unfold rho_of; rewrite EqSZ; unfold w64; img_apply unsigned_lit_small; clear - K1; numconst; zlia)).
assert (R40 : rho_of E0 40%nat = SLOTv) by (img_try (unfold rho_of; rewrite EqSLOT; unfold w64; img_apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia)).
assert (R48 : rho_of E0 48%nat = jst) by (img_try (unfold rho_of; rewrite EqJST; unfold w64; img_apply unsigned_lit_small; clear - Hjunk; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV32 : bv_unsigned (ew E0 32) = T) by img_exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = PCv) by img_exact R36.
assert (BV40 : bv_unsigned (ew E0 40) = SLOTv) by img_exact R40.
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | img_refl
| img_try (unfold YF2f.R_SLOT, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV40;
split; [clear - DR; numconst; zlia|]; split; [clear - DR; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - DR Ho; numconst; zlia) | img_apply Hslot; zlia] | img_apply Forall_nil])
| img_try (unfold YF2f.R_SLOT; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV2;
clear - LB DR Hlo Hhi; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfxtbl_rtK_ok HS (0x33fac + D_150). meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 36%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R36, ?R32, ?R35, ?Z.add_0_r; land_lits;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2f.PCv; clear - Hc dT1 dT2; numconst; zcanon_simp; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. clear - Hc0 DR R37 R38 HLT K3 Hcnt. zbranch Hc0. apply Z.eqb_eq in Hc0. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfxtbl_rtK_ok HS (0x33fec + D_150). meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 40%nat (-16))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R40, ?R36, ?R37, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id cnt) by (img_try (clear - Hcnt K3; unfold M64; zlia));
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; img_change (2 ^ 2) with 4;
unfold YF2f.SLOTv; rewrite HCP; clear - dC1 dC2 dT1 dT2 Hcnt K3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtK tfxtbl_rtK_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { reg_entry HS (2%bv : bv 5) 2%nat. }
split. { intros r Hr. cbn [YF2f.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let RR := fresh "RR" in rreg HS r RR; rewrite RR end;
first [ img_apply Er; img_refl | rewrite Htp; img_refl ]). }
split. { img_exact MQ. }
split. { intros a Ha. unfold YF2f.WIN, YF2f.WINF, YF2f.WINR in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hf _]]]; [ | | | | img_try (exfalso; clear - Hf HLT; zlia) ].
- destruct (Z_lt_le_dec a (sp0 - 240)).
+ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV36; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV40; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 4 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; numconst; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ]. }
cbv zeta.
split. { memv HS 3%nat 0%nat; [img_try (rewrite BV36; zlia) | img_try (cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; rewrite HCP; zlia) | img_try (rewrite HCP; clear - Hcnt K3; zlia)]. }
split. { memv HS 0%nat 0%nat; [rewrite BV40; zlia
| img_apply denot_by_zev; [img_refl | unfold YF2f.RELv in *; clear - O1 O2 K1; split; [img_try (img_apply Z.div_pos; zlia) | img_try (img_apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia)]
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R34, ?R35, ?R33; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftr_div_pow2 by zlia; img_change (2 ^ 4) with 16;
unfold YF2f.Pv, YF2f.RELv in *; clear - O1 O2 K1 K7 K8 K9 dS1 dS2; rewrite K8 in *; unfold SB in *; numconst; zcanon_simp; unfold zcanon, M64; replace (-1 mod 2 ^ 64) with 18446744073709551615 by img_refl; zlia ]
| unfold YF2f.RELv in *; clear - O1 O2 K1; split; [img_try (img_apply Z.div_pos; zlia) | img_try (img_apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia)] ]. }
intros Hf. exfalso. clear - Hf HLT. zlia.
Qed.
End WK.
End b.
