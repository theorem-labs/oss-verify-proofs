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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgo AFh2 AFfo AFgk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33970) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst.
Local Notation Pv := (AFgk.Pv ly off).
Local Notation PCv := (AFgk.PCv ly c).
Local Notation MAXv := (AFgk.MAXv c).
Local Notation SZv := (AFgk.SZv c).
Local Notation Nv := (AFgk.Nv c).
Local Notation CNTPv := (AFgk.CNTPv c cnt).
Local Notation SLOTv := (AFgk.SLOTv ly c cnt).
Local Notation RIv := (AFgk.RIv ly).
Local Notation RGv := (AFgk.RGv ly c).
Local Notation RBv := (AFgk.RBv ly c).
Local Notation FAv := (AFgk.FAv ly c).
Local Notation DSTv := (AFgk.DSTv ly c old).
Local Notation SRCv := (AFgk.SRCv ly c cnt).
Local Notation RELv := (AFgk.RELv c off).
Local Notation XW := (AFgk.XW ly c off cnt old mf j80 j88 jst).
Local Notation E0 := (AFgk.E0 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation Er := (AFgk.Er ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E2 := (AFgk.E2 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E1 := (AFgk.E1 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqT := (AFgk.EqT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSB := (AFgk.EqSB ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqP := (AFgk.EqP ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqC := (AFgk.EqC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqPC := (AFgk.EqPC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqCNT := (AFgk.EqCNT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMAX := (AFgk.EqMAX ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSZ := (AFgk.EqSZ ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSLOT := (AFgk.EqSLOT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRG := (AFgk.EqRG ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqOLD := (AFgk.EqOLD ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMF := (AFgk.EqMF ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqDST := (AFgk.EqDST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSRC := (AFgk.EqSRC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ80 := (AFgk.EqJ80 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ88 := (AFgk.EqJ88 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJST := (AFgk.EqJST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRI := (AFgk.EqRI ly regs0 c off cnt old mf j80 j88 jst).
Local Notation R_PC := AFgk.R_PC.
Local Notation R_JST := AFgk.R_JST.
Local Notation R_STK_HI := AFgk.R_STK_HI.
Local Notation R_STK_LO := AFgk.R_STK_LO.
Local Notation REG0 := AFgk.REG0.
Local Notation R_SLOT := AFgk.R_SLOT.
Local Notation R_RGA := AFgk.R_RGA.
Local Notation R_RGB := AFgk.R_RGB.
Local Notation R_RGC := AFgk.R_RGC.
Local Notation WRG := (AFgk.WRG ly c).
Local Notation FFK := AFgk.FFK.
Local Notation SR0 := AFgk.SR0.
Local Notation SS0 := AFgk.SS0.
Local Notation LYB := (AFgk.LYB W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation class_facts := (AFgk.class_facts W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation derived_ranges := (AFgk.derived_ranges W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINF := (AFgk.WINF ly c cnt).
Local Notation WINR := (AFgk.WINR ly c cnt old).
Local Notation WIN := (AFgk.WIN ly regs0 c cnt old).
Local Notation win_sub := AFgk.win_sub.
Local Notation win_sub_sound := (AFgk.win_sub_sound ly regs0).
Local Notation WSK0 := AFgk.WSK0.
Local Notation WSKR := AFgk.WSKR.
Local Notation sk_ok := (AFgk.sk_ok ly regs0 c cnt old).
Local Notation WSK0_ok := (AFgk.WSK0_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WSKR_ok := (AFgk.WSKR_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WIN := (AFgk.windows_WIN ly regs0 c cnt old).
Local Notation WIN_zone := (AFgk.WIN_zone W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WIN_off := (AFgk.WIN_off W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation MEQ := (AFgk.MEQ ly regs0 mem0 c cnt old).
Local Notation MEQ_frame := (AFgk.MEQ_frame ly regs0 mem0 c cnt old).
Local Notation MEQ_0 := (AFgk.MEQ_0 ly regs0 mem0 c cnt old).
Local Notation WINX := (AFgk.WINX ly regs0 c cnt).
Local Notation WINX_WIN := (AFgk.WINX_WIN ly regs0 c cnt old).
Local Notation sk_okX := (AFgk.sk_okX ly regs0 c cnt).
Local Notation WSKX := AFgk.WSKX.
Local Notation WSKX_okX := (AFgk.WSKX_okX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINX := (AFgk.windows_WINX ly regs0 c cnt).
Local Notation MEQX := (AFgk.MEQX ly regs0 mem0 c cnt).
Local Notation MEQX_frame := (AFgk.MEQX_frame ly regs0 mem0 c cnt).
Local Notation MEQX_0 := (AFgk.MEQX_0 ly regs0 mem0 c cnt).
Local Notation MEQX_MEQ := (AFgk.MEQX_MEQ ly regs0 mem0 c cnt old).
Local Notation DST_notWINX := (AFgk.DST_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation SRC_notWINX := (AFgk.SRC_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINY := (AFgk.WINY ly regs0 c cnt).
Local Notation WINY_WIN := (AFgk.WINY_WIN ly regs0 c cnt old).
Local Notation WINX_WINY := (AFgk.WINX_WINY ly regs0 c cnt).
Local Notation DST_notWINY := (AFgk.DST_notWINY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation sk_okY := (AFgk.sk_okY ly regs0 c cnt).
Local Notation WSKR_okY := (AFgk.WSKR_okY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINY := (AFgk.windows_WINY ly regs0 c cnt).
Local Notation MEQY := (AFgk.MEQY ly regs0 c cnt).
Local Notation MEQY_frame := (AFgk.MEQY_frame ly regs0 c cnt).
Local Notation MEQY_0 := (AFgk.MEQY_0 ly regs0 c cnt).
Local Notation all_disjoint_of_forall := AFgk.all_disjoint_of_forall.
Local Notation SREGS := AFgk.SREGS.
Local Notation at_RETK := (AFgk.at_RETK W ly regs0 mem0 md0 c off cnt old mf).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
Local Notation off_T := (AFgk.off_T W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
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
| M : MEQX ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQX_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
| M : MEQY ?m3 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQY_frame E _ rs m3 ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac reg_zevK HS r tac :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) _ _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; tac ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
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
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Lemma val_mem_move : forall (Hh : word -> bool) (m m' : word -> option byte) a a' (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a' + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a' + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> off_img (a + Z.of_nat k)) -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfibsegs (mrestrict Hh m) a n v -> val_mem tfibsegs (mrestrict Hh m') a' n v.
Proof.
clear. intros Hh m m' a a' n v He Hd Hs Ha Han Hv k Hk. pose proof (Hv k Hk) as E.
unfold mbyte, mrestrict in E |- *. rewrite (Hd k Hk), (He k Hk). rewrite (Hs k Hk) in E.
destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [exact E|].
rewrite (seg_rom_none_off (a + Z.of_nat k) (Ha k Hk)) in E. discriminate.
Qed.
Lemma segK2 : cnt = MAXv -> SRr tfibsegs W cfg0 at_RETK.
Proof.
intros HFULL. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQX_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSKX_okX E0 HE0 HFULL) as SK0.
assert (HCP : CNTPv = cnt - Nv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec cnt MAXv); [reflexivity | zlia]).
destruct (Hfull HFULL) as (F1 & F2 & F3 & Frg & Vmx & Vold & Vmf & V80 & V88 & Pdst & Psrc).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R33 : rho_of E0 33%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R34 : rho_of E0 34%nat = Pv) by (unfold rho_of; rewrite EqP; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R35 : rho_of E0 35%nat = c) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - Hc; zlia).
assert (R36 : rho_of E0 36%nat = PCv) by (unfold rho_of; rewrite EqPC; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R37 : rho_of E0 37%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - Hcnt K3; zlia).
assert (R38 : rho_of E0 38%nat = MAXv) by (unfold rho_of; rewrite EqMAX; unfold w64; apply unsigned_lit_small; clear - K3; zlia).
assert (R39 : rho_of E0 39%nat = SZv) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - K1; numconst; zlia).
assert (R40 : rho_of E0 40%nat = SLOTv) by (unfold rho_of; rewrite EqSLOT; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R48 : rho_of E0 48%nat = jst) by (unfold rho_of; rewrite EqJST; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = PCv) by exact R36.
assert (BV40 : bv_unsigned (ew E0 40) = SLOTv) by exact R40.
assert (R41 : rho_of E0 41%nat = RGv) by (unfold rho_of; rewrite EqRG; unfold w64; apply unsigned_lit_small; clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia).
assert (R42 : rho_of E0 42%nat = old) by (unfold rho_of; rewrite EqOLD; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R43 : rho_of E0 43%nat = mf) by (unfold rho_of; rewrite EqMF; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R46 : rho_of E0 46%nat = j80) by (unfold rho_of; rewrite EqJ80; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R47 : rho_of E0 47%nat = j88) by (unfold rho_of; rewrite EqJ88; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R49 : rho_of E0 49%nat = RIv) by (unfold rho_of; rewrite EqRI; unfold w64; apply unsigned_lit_small; clear - dI1 dI3; numconst; zlia).
assert (BV41 : bv_unsigned (ew E0 41) = RGv) by exact R41.
apply (st_ok_add_region _ _ _ R_RGC) in HS;
[ | reflexivity
| unfold AFgk.R_RGC; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ80; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact V80]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ88; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact V88]|];
apply Forall_nil
| unfold AFgk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGB) in HS;
[ | reflexivity
| unfold AFgk.R_RGB; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqOLD; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact Vold]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqMF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact Vmf]|];
apply Forall_nil
| unfold AFgk.R_RGB, AFgk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGA) in HS;
[ | reflexivity
| unfold AFgk.R_RGA; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_r; exact Vmx]|];
apply Forall_nil
| unfold AFgk.R_RGA, AFgk.R_RGB, AFgk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof SK0 as SKR.
srr_run_to_sh tfibtbl_rtK_ok HS 0x339a4. meq_acc SKR.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 36%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R36, ?R32, ?R35, ?Z.add_0_r; land_lits;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold AFgk.PCv; clear - Hc dT1 dT2; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfibtbl_rtK_ok HS.
2:{ exfalso. clear - Hc0 R37 R38 HFULL K3 Hcnt. zbranch Hc0. apply Z.eqb_neq in Hc0. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfibtbl_rtK_ok HS.
{ exfalso. clear - Hc1 R37 R38 HFULL K3 K4 K5 K6 Hcnt. zbranch Hc1. apply Z.ltb_lt in Hc1. unfold AFgk.Nv, AFgk.MAXv in *. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x33f38. meq_acc SKR. dbg HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 41%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R41, ?R49, ?R35, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id c) by (clear - Hc; unfold M64; zlia); rewrite ?Z.shiftl_mul_pow2 by zlia;
unfold AFgk.RGv; clear - Hc dI1 dI3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfibtbl_rtK_ok HS.
2:{ exfalso. clear - Hc2 R42 R43 R38 F1 F2 F3 K3 K4 K5 K6. zbranch Hc2. apply Bool.negb_false_iff in Hc2. apply Z.ltb_lt in Hc2. unfold AFgk.Nv, AFgk.MAXv in *. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x34024. meq_acc SKR.
assert (USRC : PCv + 16 <= SRCv /\ SRCv + 4 * Nv <= PCv + 80) by (unfold AFgk.SRCv, AFgk.Nv, AFgk.MAXv in *; clear - dC1 dC2 dT1 HFULL K3 K4 K5 K6 Hcnt; numconst; zlia).
assert (UDST : kHighMemBeg <= DSTv /\ DSTv + 4 * Nv <= ASAN_CEIL) by (unfold AFgk.DSTv, AFgk.FAv in *; clear - dB0 dB1 dB2 dS1 dS2 F1 F2 F3 K5; numconst; zlia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msL end.
assert (VSRC : getr (ms_regs msL) 22 = Z_to_bv 64 SRCv).
{ reg_zevK HS (22%bv : bv 5) ltac:(unfold AFgk.SRCv, AFgk.Nv, AFgk.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
assert (VDST : getr (ms_regs msL) 25 = Z_to_bv 64 DSTv).
{ reg_zevK HS (25%bv : bv 5) ltac:(unfold AFgk.DSTv, AFgk.FAv, AFgk.RBv in *; rewrite ?K8 in *; try unfold SB in *; clear - dB0 dB1 dB2 dS1 dS2 F1 F2 F3 K5 K7 K9 Hc; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
assert (VEND : getr (ms_regs msL) 10 = Z_to_bv 64 (SRCv + 4 * Nv)).
{ reg_zevK HS (10%bv : bv 5) ltac:(unfold AFgk.SRCv, AFgk.Nv, AFgk.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
idtac "CURSORS-OK".
assert (PdstL : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W) (ms_mem msL) a).
{ intros a Ha. destruct (Pdst a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
rewrite unsigned_lit_small by (clear - Ha UDST; numconst; zlia). exact (DST_notWINX HFULL a Ha). }
assert (PsrcL : forall a, SRCv <= a < SRCv + 4 * Nv -> apresent (w_H W) (ms_mem msL) a).
{ intros a Ha. destruct (Psrc a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
rewrite unsigned_lit_small by (clear - Ha USRC dC1 dT1 dC2 dT2; numconst; zlia). exact (SRC_notWINX HFULL a Ha). }
assert (DISJ : DSTv + 4 * Nv <= SRCv \/ SRCv + 4 * Nv <= DSTv).
{ unfold AFgk.DSTv, AFgk.FAv in *; try unfold T in *; try unfold SB in *. clear - USRC dC1 dC2 dT2 dB1 dB2 dS1 dS2 F1 F2 F3 LB K5. numconst.
zlia. }
eapply (cpyk_stretch W aHAVf E0 _ msL _ DSTv SRCv (4 * Nv));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact VSRC | exact VDST | exact VEND
| clear - K5; zlia | clear - K5; rewrite Z.mul_comm; apply Z_mod_mult
| clear - UDST; numconst; zlia | clear - UDST K5; numconst; zlia
| clear - USRC dC1 dT1; numconst; zlia | clear - USRC dC2 dT2 K5; numconst; zlia
| exact DISJ
| exact PdstL | exact PsrcL
| intros r Hr | intros r a Hr | ].
1-2: cbn [ss_mem In] in Hr;
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2, ?BV32, ?BV36, ?BV41;
unfold AFgk.DSTv in *; try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - UDST USRC DR LB K5 F1 F2 F3 Hlo Hhi Usp; numconst; zlia.
all: idtac "SIDE-LEFT".
intros regs3 mem3 mat3 HS3 Hfr3 Hpr3 Hcp3. rewrite wvb_collapse.
lazymatch type of HS3 with st_ok _ ?e ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS3; set (E' := e) in HS3 end.
clear HS. rename HS3 into HS.
assert (HEn : forall k, (k < aHAVf)%nat -> ew E' k = ew E0 k) by (intros k Hk; subst E'; apply ew_havoc_old; exact Hk).
pose proof (MEQY_0 mem3) as MQ3. rename MQ into MQX. rename MQ3 into MQ.
pose proof (WSKR_okY E' HEn HFULL) as SKR'.
repeat match goal with R : rho_of E0 ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E' k = v) by (unfold rho_of; rewrite (HEn k ltac:(cbv; zlia)); exact R); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E0 ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E' k) = v) by (rewrite (HEn k ltac:(cbv; zlia)); exact B); clear B; rename B' into B end.
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | reflexivity
| unfold AFgk.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite BV40;
split; [clear - DR; numconst; zlia|]; split; [clear - DR; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - DR Ho; numconst; zlia) | apply Hpr3; apply PsrcL; unfold AFgk.SLOTv, AFgk.SRCv in *; rewrite HCP in *; clear - Ho K5; zlia] | apply Forall_nil]
| unfold AFgk.R_SLOT; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x34350. meq_acc SKR'. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
assert (QSP : getr (ms_regs msC) 2 = Z_to_bv 64 (sp0 - 240)).
{ let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 2%nat ltac:(cbv; zlia)), E2. first [reflexivity | f_equal; unfold sp0; zlia]. }
assert (USP : bv_unsigned (getr (ms_regs msC) 2) = sp0 - 240) by (rewrite QSP; apply unsigned_lit_small; clear - Usp dK1; numconst; zlia).
assert (PRESC : forall a, sp0 - 320 <= a < sp0 - 240 -> apresent (w_H W) (ms_mem msC) a).
{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E' _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Usp dK1; numconst; zlia) ]. }
assert (J80 : 0 <= (j80 + Nv) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; zlia).
assert (FHO : AFgo.free_hyps W (ms_regs msC) (ms_mem msC) RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88).
{ apply FHO_ok.
- let Q := fresh "Q" in rreg HS (1%bv : bv 5) Q; rewrite Q. unfold YK0s.ret_ok. reflexivity.
- rewrite USP. clear - Hlo Hhi LB; numconst; zlia.
- rewrite USP. clear - Hsp_al. replace (sp0 - 240) with (sp0 + (-15) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite USP. intros a Ha. apply PRESC. clear - Ha. zlia.
- exact Hc.
- clear - dI1 dI2 dI3 dSal. split; [exact dI1|]. split; [exact dI3|]. rewrite dI2. numconst.
apply Z.mod_divide in dSal as [q Hq]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * 16 + 2 ^ 25). zlia.
- clear - F1 F2 F3 K5 dJ3 dJ4 J80. numconst. zlia.
- rewrite USP. fold RGv. try unfold SB in *; try unfold sp0 in *. clear - LB Hlo Hhi dG0 dG1 dG2 dI1 dI2 dI3 dS1 dS2. numconst. zlia.
- let Q := fresh "Q" in rreg HS (10%bv : bv 5) Q; rewrite Q. reflexivity.
- let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 35%nat ltac:(cbv; zlia)), EqC. first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]].
- let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q. reflexivity.
- fold RGv. memvo HS 2%nat 16; [ rewrite BV41; zlia
| apply denot_by_zev; [ reflexivity | clear - F1 F2 F3 K5; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold AFgk.Nv, AFgk.MAXv in *;
clear - F1 F2 F3 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| clear - F1 F2 F3 K5; numconst; zlia ].
- fold RGv. memvo HS 3%nat 80; [ rewrite BV41; zlia
| apply denot_by_zev; [ reflexivity | exact J80
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold AFgk.Nv, AFgk.MAXv in *;
clear - K3 K4 K5 K6 dJ1 dJ2; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| exact J80 ].
- fold RGv. memvo HS 3%nat 88; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite (HEn 47%nat ltac:(cbv; zlia)), EqJ88; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | exact (conj dJ3 dJ4) ].
- memvo HS 9%nat (A_ALLOCATOR + 48); [ reflexivity | cbn [sv_denot]; rewrite (HEn 49%nat ltac:(cbv; zlia)), EqRI; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - dI1 dI3; numconst; zlia ].
- memvo HS 10%nat (A_ALLOCATOR + 40); [ reflexivity | reflexivity | zlia ].
- memvo HS 11%nat 0x9df78; [ reflexivity | reflexivity | zlia ].
- memvo HS 12%nat 0x135aa0; [ reflexivity | reflexivity | zlia ]. }
idtac "FHO-OK".
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mat _)) _ => pose proof (segO W ly (ms_regs msC) (ms_mem msC) md0 RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88 mat FHO) as SEGO end.
rewrite Hshape. rewrite Hshape in HS.
lazymatch type of HS with st_ok _ _ ?ss _ =>
let rs := eval vm_compute in (match ss_mem ss with r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: rest => r0 :: r1 :: r2 :: r3 :: r4 :: rest | l => l end) in
eapply (call_stretch W 57%nat E' ss _ _ md0 rs 0x3405c (AFgo.WIN (ms_regs msC)) _ HS);
[ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| do 5 (apply submem_keep; [apply subregion_refl|]); apply submem_drop; apply submem_refl
| reflexivity | zlia
| intros r a Hr Ha | intros r Hr | exact SEGO | ] end.
{ unfold AFgo.WIN. rewrite USP. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?BV2, ?BV32, ?BV36, ?BV40, ?BV41 in Ha;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - Ha DR LB K5 F1 F2 F3 Hlo Hhi Usp; numconst; zlia. }
{ cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn; zlia. }
idtac "CALL-OK".
clear SEGO. intros regs4 mem4 mat4 HS4 HP4 Hfr4 Hpr4.
lazymatch type of HS4 with st_ok _ ?e ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS4; set (E'' := e) in HS4 end.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew E'' k = ew E0 k) by (intros k Hk; subst E''; rewrite ew_havoc_old by (unfold aHAVf in Hk; zlia); apply HEn; exact Hk).
clear HS Hshape. rename HS4 into HS.
repeat match goal with R : rho_of E' ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E'' k = v) by (unfold rho_of; rewrite (HEn4 k ltac:(cbv; zlia)); rewrite <- (HEn k ltac:(cbv; zlia)); exact R); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E' ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E'' k) = v) by (rewrite (HEn4 k ltac:(cbv; zlia)); rewrite <- (HEn k ltac:(cbv; zlia)); exact B); clear B; rename B' into B end.
unfold AFgo.WIN in Hfr4, Hpr4. rewrite USP in Hfr4, Hpr4. cbn [ms_mem ms_regs mkst] in Hfr4, Hpr4, HP4.
assert (MQ4 : MEQY mem3 mem4).
{ intros x Hx. rewrite (Hfr4 x) by (intros HD; apply Hx; left; clear - HD; zlia). exact (MQ x Hx). }
clear MQ. rename MQ4 into MQ.
pose proof (WSKR_okY E'' HEn4 HFULL) as SKR4.
apply (st_ok_add_region _ _ _ R_STK_LO) in HS;
[ | reflexivity
| unfold AFgk.R_STK_LO, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite BV2;
split; [clear - Usp dK1; numconst; zlia|]; split; [clear - Usp dK1 dK2; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp dK1 Ho; numconst; zlia) | apply Hpr4; clear - Ho; zlia] | apply Forall_nil]
| unfold AFgk.R_STK_LO; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
idtac "READD-OK".
srr_run_to_sh tfibtbl_rtK_ok HS 0x339e4. meq_acc SKR4. dbg HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 40%nat (-16))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := eval vm_compute in (2 ^ k) in change (2 ^ k) with cc end;
unfold AFgk.SLOTv, AFgk.Nv, AFgk.MAXv in *; rewrite HCP; clear - dC1 dC2 dT1 dT2 Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
idtac "PIN2-OK".
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtK tfibtbl_rtK_ok Hwx W E''); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (Er4 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E'' k = getr regs0 r).
{ intros k r Hk. rewrite (HEn4 k) by (pose proof (u5_range r); unfold aHAVf; zlia). exact (Er k r Hk). }
rreg HS (1%bv : bv 5) Q1. rewrite (Er4 1%nat 1%bv eq_refl) in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. apply Er4. reflexivity. }
split. { intros r Hr. cbn [AFgk.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let RR := fresh "RR" in rreg HS r RR; rewrite RR end;
first [ apply Er4; reflexivity | rewrite Htp; reflexivity ]). }
assert (DPRES : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W) mem3 a) by (intros a Ha; apply Hpr3; apply PdstL; exact Ha).
split. { intros x Hx. rewrite (MQ x) by (intros HY; apply Hx; exact (WINY_WIN _ HY)).
rewrite (Hfr3 x) by (intros HD; apply Hx; right; right; split; [exact HFULL | right; exact HD]).
apply MQX. intros HX. apply Hx. exact (WINX_WIN _ HX). }
split. { intros a Ha. unfold AFgk.WIN, AFgk.WINF, AFgk.WINR in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[_ [[Ha|[Ha|Ha]]|Ha]]]].
- destruct (Z_lt_le_dec a (sp0 - 240)).
+ eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV36; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV40; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 7 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E'' _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- destruct (DPRES a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
rewrite unsigned_lit_small by (clear - Ha UDST; numconst; zlia). exact (DST_notWINY HFULL a Ha). }
cbv zeta.
Ltac zevR tac :=
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := eval vm_compute in (2 ^ k) in change (2 ^ k) with cc end; tac ].
split. { idtac "F1". memvo HS 6%nat 0; [ rewrite BV36; zlia
| zevR ltac:(unfold AFgk.CNTPv, AFgk.Nv, AFgk.MAXv in *; rewrite ?HCP; clear - Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; try zlia)
| rewrite HCP; clear - Hcnt HFULL K3 K5 K6; zlia ]. }
split. { idtac "F2". memvo HS 1%nat 0; [ rewrite BV40; zlia
| zevR ltac:(unfold AFgk.Pv, AFgk.RELv in *; rewrite ?K8 in *; try unfold SB in *; clear - O1 O2 K1 K7 K9 dS1 dS2 Hc;
first [ split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia]
| numconst; zcanon_simp; unfold zcanon, M64; replace (-1 mod 2 ^ 64) with 18446744073709551615 by reflexivity; zlia ])
| unfold AFgk.RELv in *; clear - O1 O2 K1; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia] ]. }
intros _. split. { idtac "F3". memvo HS 2%nat 0; [ rewrite BV41; zlia | reflexivity | zlia ]. }
split. { idtac "F4". memvo HS 3%nat 16; [ rewrite BV41; zlia
| zevR ltac:(unfold AFgk.Nv, AFgk.MAXv in *; clear - F1 F2 F3 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia)
| clear - F1 F2 F3 K5; numconst; zlia ]. }
split. { idtac "F5". memvo HS 3%nat 24; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite (HEn4 43%nat ltac:(cbv; zlia)), EqMF; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - F1 F2 F3 K5; numconst; zlia ]. }
idtac "F6".
intros i v Hi Hv. apply (val_mem_move (w_H W) mem0 (ms_mem msR) (SRCv + 4 * i) (DSTv + 4 * i) 4 v); try exact Hv.
- intros k Hk. rewrite (MQ _) by (rewrite unsigned_lit_small by (clear - Hi Hk UDST K5; numconst; zlia); apply (DST_notWINY HFULL); clear - Hi Hk; zlia).
replace (DSTv + 4 * i + Z.of_nat k) with (DSTv + (4 * i + Z.of_nat k)) by zlia. unfold YG0n.w64, w64 in Hcp3. rewrite (Hcp3 (4 * i + Z.of_nat k)) by (clear - Hi Hk; zlia).
replace (SRCv + (4 * i + Z.of_nat k)) with (SRCv + 4 * i + Z.of_nat k) by zlia.
apply MQX. rewrite unsigned_lit_small by (clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5; numconst; zlia). apply (SRC_notWINX HFULL). clear - Hi Hk; zlia.
- intros k Hk. exact (proj1 (DPRES (DSTv + 4 * i + Z.of_nat k) ltac:(clear - Hi Hk; zlia))).
- intros k Hk. exact (proj1 (Psrc (SRCv + 4 * i + Z.of_nat k) ltac:(clear - Hi Hk; zlia))).
- intros k Hk. apply off_T. clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5. numconst. zlia.
- clear - Hi USRC dC2 dT2 K5. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. numconst. zlia.
Qed.
End WK.
End d.
