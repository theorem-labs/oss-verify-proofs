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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0j YF0i YF2j YF2x YF1i YF2f.
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
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
| M : MEQX ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQX_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
| M : MEQY ?m3 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQY_frame E _ rs m3 ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac reg_zevK HS r tac :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) _ _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := img_ev (sr_get sr rr) in img_change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
img_apply denot_by_zev; [ img_refl | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; tac ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
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
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Lemma val_mem_move : forall (Hh : word -> bool) (m m' : word -> option byte) a a' (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a' + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a' + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> off_img (a + Z.of_nat k)) -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfxsegs (mrestrict Hh m) a n v -> val_mem tfxsegs (mrestrict Hh m') a' n v.
Proof.
clear. intros Hh m m' a a' n v He Hd Hs Ha Han Hv k Hk. pose proof (Hv k Hk) as E.
unfold mbyte, mrestrict in E |- *. rewrite (Hd k Hk), (He k Hk). rewrite (Hs k Hk) in E.
destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [img_try (img_exact E)|].
rewrite (seg_rom_none_off (a + Z.of_nat k) (Ha k Hk)) in E. discriminate.
Qed.
Lemma segK2 : cnt = MAXv -> SRr tfxsegs W cfg0 at_RETK.
Proof.
intros HFULL. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQX_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSKX_okX E0 HE0 HFULL) as SK0.
assert (HCP : CNTPv = cnt - Nv) by (img_try (unfold YF2f.CNTPv; destruct (Z.eqb_spec cnt MAXv); [img_refl | img_try (zlia)])).
destruct (Hfull HFULL) as (F1 & F2 & F3 & Frg & Vmx & Vold & Vmf & V80 & V88 & Pdst & Psrc).
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
assert (R41 : rho_of E0 41%nat = RGv) by (img_try (unfold rho_of; rewrite EqRG; unfold w64; img_apply unsigned_lit_small; clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia)).
assert (R42 : rho_of E0 42%nat = old) by (img_try (unfold rho_of; rewrite EqOLD; unfold w64; img_apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia)).
assert (R43 : rho_of E0 43%nat = mf) by (img_try (unfold rho_of; rewrite EqMF; unfold w64; img_apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia)).
assert (R46 : rho_of E0 46%nat = j80) by (img_try (unfold rho_of; rewrite EqJ80; unfold w64; img_apply unsigned_lit_small; clear - Hjunk; zlia)).
assert (R47 : rho_of E0 47%nat = j88) by (img_try (unfold rho_of; rewrite EqJ88; unfold w64; img_apply unsigned_lit_small; clear - Hjunk; zlia)).
assert (R49 : rho_of E0 49%nat = RIv) by (img_try (unfold rho_of; rewrite EqRI; unfold w64; img_apply unsigned_lit_small; clear - dI1 dI3; numconst; zlia)).
assert (BV41 : bv_unsigned (ew E0 41) = RGv) by img_exact R41.
apply (st_ok_add_region _ _ _ R_RGC) in HS;
[ | img_refl
| img_try (unfold YF2f.R_RGC; unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | img_apply Frg; zlia]|];
img_apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ80; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; img_exact V80]|];
img_apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ88; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; img_exact V88]|];
img_apply Forall_nil)
| img_try (unfold YF2f.R_RGC; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGB) in HS;
[ | img_refl
| img_try (unfold YF2f.R_RGB; unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | img_apply Frg; zlia]|];
img_apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqOLD; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; img_exact Vold]|];
img_apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqMF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; img_exact Vmf]|];
img_apply Forall_nil)
| img_try (unfold YF2f.R_RGB, YF2f.R_RGC; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGA) in HS;
[ | img_refl
| img_try (unfold YF2f.R_RGA; unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | img_apply Frg; zlia]|];
img_apply Forall_cons; [eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia | rewrite Z.add_0_r; img_exact Vmx]|];
img_apply Forall_nil)
| img_try (unfold YF2f.R_RGA, YF2f.R_RGB, YF2f.R_RGC; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof SK0 as SKR.
srr_run_to_sh tfxtbl_rtK_ok HS (0x33fac + D_150). meq_acc SKR.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 36%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R36, ?R32, ?R35, ?Z.add_0_r; land_lits;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2f.PCv; clear - Hc dT1 dT2; numconst; zcanon_simp; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfxtbl_rtK_ok HS.
2:{ exfalso. clear - Hc0 R37 R38 HFULL K3 Hcnt. zbranch Hc0. apply Z.eqb_neq in Hc0. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. clear - Hc1 R37 R38 HFULL K3 K4 K5 K6 Hcnt. zbranch Hc1. apply Z.ltb_lt in Hc1. unfold YF2f.Nv, YF2f.MAXv in *. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfxtbl_rtK_ok HS (0x34540 + D_150). meq_acc SKR. dbg HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 41%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R41, ?R49, ?R35, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id c) by (img_try (clear - Hc; unfold M64; zlia)); rewrite ?Z.shiftl_mul_pow2 by zlia;
unfold YF2f.RGv; clear - Hc dI1 dI3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfxtbl_rtK_ok HS.
2:{ exfalso. clear - Hc2 R42 R43 R38 F1 F2 F3 K3 K4 K5 K6. zbranch Hc2. apply Bool.negb_false_iff in Hc2. apply Z.ltb_lt in Hc2. unfold YF2f.Nv, YF2f.MAXv in *. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfxtbl_rtK_ok HS (0x3462c + D_150). meq_acc SKR.
assert (USRC : PCv + 16 <= SRCv /\ SRCv + 4 * Nv <= PCv + 80) by (img_try (unfold YF2f.SRCv, YF2f.Nv, YF2f.MAXv in *; clear - dC1 dC2 dT1 HFULL K3 K4 K5 K6 Hcnt; numconst; zlia)).
assert (UDST : kHighMemBeg <= DSTv /\ DSTv + 4 * Nv <= ASAN_CEIL) by (img_try (unfold YF2f.DSTv, YF2f.FAv in *; clear - dB0 dB1 dB2 dS1 dS2 F1 F2 F3 K5; numconst; zlia)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msL end.
assert (VSRC : getr (ms_regs msL) 22 = Z_to_bv 64 SRCv).
{ reg_zevK HS (22%bv : bv 5) ltac:(img_try (unfold YF2f.SRCv, YF2f.Nv, YF2f.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia)). }
assert (VDST : getr (ms_regs msL) 25 = Z_to_bv 64 DSTv).
{ reg_zevK HS (25%bv : bv 5) ltac:(img_try (unfold YF2f.DSTv, YF2f.FAv, YF2f.RBv in *; rewrite ?K8 in *; try unfold SB in *; clear - dB0 dB1 dB2 dS1 dS2 F1 F2 F3 K5 K7 K9 Hc; numconst; zcanon_simp; unfold zcanon, M64; zlia)). }
assert (VEND : getr (ms_regs msL) 10 = Z_to_bv 64 (SRCv + 4 * Nv)).
{ reg_zevK HS (10%bv : bv 5) ltac:(img_try (unfold YF2f.SRCv, YF2f.Nv, YF2f.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia)). }
idtac "CURSORS-OK".
assert (PdstL : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W) (ms_mem msL) a).
{ intros a Ha. destruct (Pdst a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply MQ.
rewrite unsigned_lit_small by (img_try (clear - Ha UDST; numconst; zlia)). img_exact (DST_notWINX HFULL a Ha). }
assert (PsrcL : forall a, SRCv <= a < SRCv + 4 * Nv -> apresent (w_H W) (ms_mem msL) a).
{ intros a Ha. destruct (Psrc a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply MQ.
rewrite unsigned_lit_small by (img_try (clear - Ha USRC dC1 dT1 dC2 dT2; numconst; zlia)). img_exact (SRC_notWINX HFULL a Ha). }
assert (DISJ : DSTv + 4 * Nv <= SRCv \/ SRCv + 4 * Nv <= DSTv).
{ unfold YF2f.DSTv, YF2f.FAv in *; try unfold T in *; try unfold SB in *. clear - USRC dC1 dC2 dT2 dB1 dB2 dS1 dS2 F1 F2 F3 LB K5. numconst.
zlia. }
eapply (cpyk_stretch W aHAVf E0 _ msL _ DSTv SRCv (4 * Nv));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (img_exact VSRC) | img_try (img_exact VDST) | img_try (img_exact VEND)
| img_try (clear - K5; zlia) | img_try (clear - K5; rewrite Z.mul_comm; img_apply Z_mod_mult)
| img_try (clear - UDST; numconst; zlia) | img_try (clear - UDST K5; numconst; zlia)
| img_try (clear - USRC dC1 dT1; numconst; zlia) | img_try (clear - USRC dC2 dT2 K5; numconst; zlia)
| img_try (img_exact DISJ)
| img_try (img_exact PdstL) | img_try (img_exact PsrcL)
| img_try (intros r Hr) | img_try (intros r a Hr) | ].
1-2: cbn [ss_mem In] in Hr;
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?BV2, ?BV32, ?BV36, ?BV41;
unfold YF2f.DSTv in *; try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - UDST USRC DR LB K5 F1 F2 F3 Hlo Hhi Usp; numconst; zlia.
all: idtac "SIDE-LEFT".
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hcp3. rewrite wvb_collapse.
lazymatch type of HS3 with st_ok _ ?e ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS3; set (E' := e) in HS3 end.
clear HS. rename HS3 into HS.
assert (HEn : forall k, (k < aHAVf)%nat -> ew E' k = ew E0 k) by (img_try (intros k Hk; (subst E'; cbv beta); img_apply ew_havoc_old; img_exact Hk)).
pose proof (MEQY_0 mem3) as MQ3. rename MQ into MQX. rename MQ3 into MQ.
pose proof (WSKR_okY E' HEn HFULL) as SKR'.
repeat match goal with R : rho_of E0 ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E' k = v) by (img_try (unfold rho_of; rewrite (HEn k ltac:((img_case; cbv); zlia)); img_exact R)); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E0 ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E' k) = v) by (img_try (rewrite (HEn k ltac:((img_case; cbv); zlia)); img_exact B)); clear B; rename B' into B end.
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | img_refl
| img_try (unfold YF2f.R_SLOT, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst]; rewrite BV40;
split; [clear - DR; numconst; zlia|]; split; [clear - DR; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - DR Ho; numconst; zlia) | img_apply Hpr3; img_apply PsrcL; unfold YF2f.SLOTv, YF2f.SRCv in *; rewrite HCP in *; clear - Ho K5; zlia] | img_apply Forall_nil])
| img_try (unfold YF2f.R_SLOT; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfxtbl_rtK_ok HS (0x34958 + D_150). meq_acc SKR'. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
assert (QSP : getr (ms_regs msC) 2 = Z_to_bv 64 (sp0 - 240)).
{ let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2. first [img_refl | f_equal; unfold sp0; zlia]. }
assert (USP : bv_unsigned (getr (ms_regs msC) 2) = sp0 - 240) by (img_try (rewrite QSP; img_apply unsigned_lit_small; clear - Usp dK1; numconst; zlia)).
assert (PRESC : forall a, sp0 - 320 <= a < sp0 - 240 -> apresent (w_H W) (ms_mem msC) a).
{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E' _ _ 5 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha Usp dK1; numconst; zlia)) ]. }
assert (J80 : 0 <= (j80 + Nv) mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; zlia)).
assert (FHO : YF2j.free_hyps W (ms_regs msC) (ms_mem msC) RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88).
{ img_apply FHO_ok.
- let Q := fresh "Q" in rreg HS (1%bv : bv 5) Q; rewrite Q. unfold YK0s.ret_ok. img_refl.
- rewrite USP. clear - Hlo Hhi LB; numconst; zlia.
- rewrite USP. clear - Hsp_al. replace (sp0 - 240) with (sp0 + (-15) * 16) by zlia. rewrite Z_mod_plus_full. img_exact Hsp_al.
- rewrite USP. intros a Ha. img_apply PRESC. clear - Ha. zlia.
- img_exact Hc.
- clear - dI1 dI2 dI3 dSal. split; [img_try (img_exact dI1)|]. split; [img_try (img_exact dI3)|]. rewrite dI2. numconst.
apply Z.mod_divide in dSal as [q Hq]; [|img_try (zlia)]. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * 16 + 2 ^ 25). zlia.
- clear - F1 F2 F3 K5 dJ3 dJ4 J80. numconst. zlia.
- rewrite USP. fold RGv. try unfold SB in *; try unfold sp0 in *. clear - LB Hlo Hhi dG0 dG1 dG2 dI1 dI2 dI3 dS1 dS2. numconst. zlia.
- let Q := fresh "Q" in rreg HS (10%bv : bv 5) Q; rewrite Q. img_refl.
- let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 35%nat ltac:(img_try ((img_case; cbv); zlia))), EqC. first [img_refl | unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]].
- let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q. img_refl.
- fold RGv. memvo HS 2%nat 16; [ rewrite BV41; zlia
| img_apply denot_by_zev; [ img_refl | clear - F1 F2 F3 K5; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold YF2f.Nv, YF2f.MAXv in *;
clear - F1 F2 F3 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| clear - F1 F2 F3 K5; numconst; zlia ].
- fold RGv. memvo HS 3%nat 80; [ rewrite BV41; zlia
| img_apply denot_by_zev; [ img_refl | img_exact J80
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold YF2f.Nv, YF2f.MAXv in *;
clear - K3 K4 K5 K6 dJ1 dJ2; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| img_exact J80 ].
- fold RGv. memvo HS 3%nat 88; [ img_try (rewrite BV41; zlia) | img_try (cbn [sv_denot]; rewrite (HEn 47%nat ltac:((img_case; cbv); zlia)), EqJ88; first [img_refl | unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]]) | img_try (img_exact (conj dJ3 dJ4)) ].
- memvo HS 9%nat (A_ALLOCATOR + 48); [ img_refl | img_try (cbn [sv_denot]; rewrite (HEn 49%nat ltac:((img_case; cbv); zlia)), EqRI; first [img_refl | unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]]) | img_try (clear - dI1 dI3; numconst; zlia) ].
- memvo HS 10%nat (A_ALLOCATOR + 40); [ img_refl | img_refl | img_try (zlia) ].
- memvo HS 11%nat (0xa2140 + D_10f0); [ img_refl | img_refl | img_try (zlia) ].
- memvo HS 12%nat (0x139c60 + D_10c0); [ img_refl | img_refl | img_try (zlia) ]. }
idtac "FHO-OK".
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mat _)) _ => pose proof (segO W ly (ms_regs msC) (ms_mem msC) md0 RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88 mat FHO) as SEGO end.
rewrite Hshape. rewrite Hshape in HS.
lazymatch type of HS with st_ok _ _ ?ss _ =>
let rs := img_ev (match ss_mem ss with r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: rest => r0 :: r1 :: r2 :: r3 :: r4 :: rest | l => l end) in
eapply (call_stretch W 57%nat E' ss _ _ md0 rs (0x34664 + D_150) (YF2j.WIN (ms_regs msC)) _ HS);
[ img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (do 5 (img_apply submem_keep; [img_apply subregion_refl|]); img_apply submem_drop; img_apply submem_refl)
| img_refl | img_try (zlia)
| img_try (intros r a Hr Ha) | img_try (intros r Hr) | img_try (img_exact SEGO) | ] end.
{ unfold YF2j.WIN. rewrite USP. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha; rewrite ?BV2, ?BV32, ?BV36, ?BV40, ?BV41 in Ha;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - Ha DR LB K5 F1 F2 F3 Hlo Hhi Usp; numconst; zlia. }
{ cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn; zlia. }
idtac "CALL-OK".
clear SEGO. intros regs4 mem4 mat4 HS4 HP4 Hfr4 Hpr4.
lazymatch type of HS4 with st_ok _ ?e ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS4; set (E'' := e) in HS4 end.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew E'' k = ew E0 k) by (img_try (intros k Hk; (subst E''; cbv beta); rewrite ew_havoc_old by (unfold aHAVf in Hk; zlia); img_apply HEn; img_exact Hk)).
clear HS Hshape. rename HS4 into HS.
repeat match goal with R : rho_of E' ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E'' k = v) by (img_try (unfold rho_of; rewrite (HEn4 k ltac:((img_case; cbv); zlia)); rewrite <- (HEn k ltac:((img_case; cbv); zlia)); img_exact R)); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E' ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E'' k) = v) by (img_try (rewrite (HEn4 k ltac:((img_case; cbv); zlia)); rewrite <- (HEn k ltac:((img_case; cbv); zlia)); img_exact B)); clear B; rename B' into B end.
unfold YF2j.WIN in Hfr4, Hpr4. rewrite USP in Hfr4, Hpr4. cbn [ms_mem ms_regs mkst] in Hfr4, Hpr4, HP4.
assert (MQ4 : MEQY mem3 mem4).
{ intros x Hx. rewrite (Hfr4 x) by (img_try (intros HD; img_apply Hx; left; clear - HD; zlia)). img_exact (MQ x Hx). }
clear MQ. rename MQ4 into MQ.
pose proof (WSKR_okY E'' HEn4 HFULL) as SKR4.
apply (st_ok_add_region _ _ _ R_STK_LO) in HS;
[ | img_refl
| img_try (unfold YF2f.R_STK_LO, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst]; rewrite BV2;
split; [clear - Usp dK1; numconst; zlia|]; split; [clear - Usp dK1 dK2; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - Usp dK1 Ho; numconst; zlia) | img_apply Hpr4; clear - Ho; zlia] | img_apply Forall_nil])
| img_try (unfold YF2f.R_STK_LO; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
idtac "READD-OK".
srr_run_to_sh tfxtbl_rtK_ok HS (0x33fec + D_150). meq_acc SKR4. dbg HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 40%nat (-16))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := img_ev (2 ^ k) in img_change (2 ^ k) with cc end;
unfold YF2f.SLOTv, YF2f.Nv, YF2f.MAXv in *; rewrite HCP; clear - dC1 dC2 dT1 dT2 Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | img_try (zlia) | img_try (unfold M64; zlia) ]); zcanon_simp; unfold zcanon, M64; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
idtac "PIN2-OK".
srr_run_sh tfxtbl_rtK_ok HS. meq_acc SKR4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtK tfxtbl_rtK_ok Hwx W E''); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (Er4 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E'' k = getr regs0 r).
{ intros k r Hk. rewrite (HEn4 k) by (img_try (pose proof (u5_range r); unfold aHAVf; zlia)). img_exact (Er k r Hk). }
rreg HS (1%bv : bv 5) Q1. rewrite (Er4 1%nat 1%bv eq_refl) in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. img_apply Er4. img_refl. }
split. { intros r Hr. cbn [YF2f.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let RR := fresh "RR" in rreg HS r RR; rewrite RR end;
first [ img_apply Er4; img_refl | rewrite Htp; img_refl ]). }
assert (DPRES : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W) mem3 a) by (img_try (intros a Ha; img_apply Hpr3; img_apply PdstL; img_exact Ha)).
split. { intros x Hx. rewrite (MQ x) by (img_try (intros HY; img_apply Hx; img_exact (WINY_WIN _ HY))).
rewrite (Hfr3 x) by (img_try (intros HD; img_apply Hx; right; right; split; [img_try (img_exact HFULL) | img_try (right; img_exact HD)])).
img_apply MQX. intros HX. img_apply Hx. img_exact (WINX_WIN _ HX). }
split. { intros a Ha. unfold YF2f.WIN, YF2f.WINF, YF2f.WINR in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[_ [[Ha|[Ha|Ha]]|Ha]]]].
- destruct (Z_lt_le_dec a (sp0 - 240)).
+ eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 5 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 6 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV36; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV40; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 7 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; numconst; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV41; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV41; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 4 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV41; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha DR; numconst; zlia)) ].
- destruct (DPRES a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply MQ.
rewrite unsigned_lit_small by (img_try (clear - Ha UDST; numconst; zlia)). img_exact (DST_notWINY HFULL a Ha). }
cbv zeta.
Ltac zevR tac :=
img_apply denot_by_zev; [ img_refl | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := img_ev (2 ^ k) in img_change (2 ^ k) with cc end; tac ].
split. { idtac "F1". memvo HS 6%nat 0; [ img_try (rewrite BV36; zlia)
| img_try (zevR ltac:(unfold YF2f.CNTPv, YF2f.Nv, YF2f.MAXv in *; rewrite ?HCP; clear - Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; try zlia))
| img_try (rewrite HCP; clear - Hcnt HFULL K3 K5 K6; zlia) ]. }
split. { idtac "F2". memvo HS 1%nat 0; [ img_try (rewrite BV40; zlia)
| img_try (zevR ltac:(unfold YF2f.Pv, YF2f.RELv in *; rewrite ?K8 in *; try unfold SB in *; clear - O1 O2 K1 K7 K9 dS1 dS2 Hc;
first [ split; [img_apply Z.div_pos; zlia | img_apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia]
| numconst; zcanon_simp; unfold zcanon, M64; replace (-1 mod 2 ^ 64) with 18446744073709551615 by img_refl; zlia ]))
| img_try (unfold YF2f.RELv in *; clear - O1 O2 K1; split; [img_apply Z.div_pos; zlia | img_apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia]) ]. }
intros _. split. { idtac "F3". memvo HS 2%nat 0; [ img_try (rewrite BV41; zlia) | img_refl | img_try (zlia) ]. }
split. { idtac "F4". memvo HS 3%nat 16; [ img_try (rewrite BV41; zlia)
| img_try (zevR ltac:(unfold YF2f.Nv, YF2f.MAXv in *; clear - F1 F2 F3 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia))
| img_try (clear - F1 F2 F3 K5; numconst; zlia) ]. }
split. { idtac "F5". memvo HS 3%nat 24; [ img_try (rewrite BV41; zlia) | img_try (cbn [sv_denot]; rewrite (HEn4 43%nat ltac:((img_case; cbv); zlia)), EqMF; first [img_refl | unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]]) | img_try (clear - F1 F2 F3 K5; numconst; zlia) ]. }
idtac "F6".
intros i v Hi Hv. img_apply (val_mem_move (w_H W) mem0 (ms_mem msR) (SRCv + 4 * i) (DSTv + 4 * i) 4 v); try img_exact Hv.
- intros k Hk. rewrite (MQ _) by (img_try (rewrite unsigned_lit_small by (clear - Hi Hk UDST K5; numconst; zlia); img_apply (DST_notWINY HFULL); clear - Hi Hk; zlia)).
replace (DSTv + 4 * i + Z.of_nat k) with (DSTv + (4 * i + Z.of_nat k)) by zlia. unfold YG0u.w64, w64 in Hcp3. rewrite (Hcp3 (4 * i + Z.of_nat k)) by (img_try (clear - Hi Hk; zlia)).
replace (SRCv + (4 * i + Z.of_nat k)) with (SRCv + 4 * i + Z.of_nat k) by zlia.
img_apply MQX. rewrite unsigned_lit_small by (img_try (clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5; numconst; zlia)). img_apply (SRC_notWINX HFULL). clear - Hi Hk; zlia.
- intros k Hk. img_exact (proj1 (DPRES (DSTv + 4 * i + Z.of_nat k) ltac:(img_try (clear - Hi Hk; zlia)))).
- intros k Hk. img_exact (proj1 (Psrc (SRCv + 4 * i + Z.of_nat k) ltac:(img_try (clear - Hi Hk; zlia)))).
- intros k Hk. img_apply off_T. clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5. numconst. zlia.
- clear - Hi USRC dC2 dT2 K5. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. numconst. zlia.
Qed.
End WK.
End d.
