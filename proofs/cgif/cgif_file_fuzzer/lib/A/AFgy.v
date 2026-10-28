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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgk.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
end.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
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
Lemma segK1 : cnt < MAXv -> SRr tfibsegs W cfg0 at_RETK.
Proof.
intros HLT. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (HCP : CNTPv = cnt) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec cnt MAXv); [zlia | reflexivity]).
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
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | reflexivity
| unfold AFgk.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV40;
split; [clear - DR; numconst; zlia|]; split; [clear - DR; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - DR Ho; numconst; zlia) | apply Hslot; zlia] | apply Forall_nil]
| unfold AFgk.R_SLOT; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV2;
clear - LB DR Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x339a4. meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 36%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R36, ?R32, ?R35, ?Z.add_0_r; land_lits;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold AFgk.PCv; clear - Hc dT1 dT2; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtK_ok HS.
{ exfalso. clear - Hc0 DR R37 R38 HLT K3 Hcnt. zbranch Hc0. apply Z.eqb_eq in Hc0. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x339e4. meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 40%nat (-16))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R40, ?R36, ?R37, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id cnt) by (clear - Hcnt K3; unfold M64; zlia);
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; change (2 ^ 2) with 4;
unfold AFgk.SLOTv; rewrite HCP; clear - dC1 dC2 dT1 dT2 Hcnt K3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtK tfibtbl_rtK_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { reg_entry HS (2%bv : bv 5) 2%nat. }
split. { intros r Hr. cbn [AFgk.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let RR := fresh "RR" in rreg HS r RR; rewrite RR end;
first [ apply Er; reflexivity | rewrite Htp; reflexivity ]). }
split. { exact MQ. }
split. { intros a Ha. unfold AFgk.WIN, AFgk.WINF, AFgk.WINR in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hf _]]]; [ | | | | exfalso; clear - Hf HLT; zlia ].
- destruct (Z_lt_le_dec a (sp0 - 240)).
+ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV36; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV40; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ]. }
cbv zeta.
split. { memv HS 3%nat 0%nat; [rewrite BV36; zlia | cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; rewrite HCP; zlia | rewrite HCP; clear - Hcnt K3; zlia]. }
split. { memv HS 0%nat 0%nat; [rewrite BV40; zlia
| apply denot_by_zev; [reflexivity | unfold AFgk.RELv in *; clear - O1 O2 K1; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia]
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R34, ?R35, ?R33; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftr_div_pow2 by zlia; change (2 ^ 4) with 16;
unfold AFgk.Pv, AFgk.RELv in *; clear - O1 O2 K1 K7 K8 K9 dS1 dS2; rewrite K8 in *; unfold SB in *; numconst; zcanon_simp; unfold zcanon, M64; replace (-1 mod 2 ^ 64) with 18446744073709551615 by reflexivity; zlia ]
| unfold AFgk.RELv in *; clear - O1 O2 K1; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia] ]. }
intros Hf. exfalso. clear - Hf HLT. zlia.
Qed.
End WK.
End b.
