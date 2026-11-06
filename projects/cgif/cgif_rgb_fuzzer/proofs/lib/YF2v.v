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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF2g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition lB : nat := 32.
Definition lNX : nat := 33.
Definition lBS : nat := 34.
Definition lQB : nat := 35.
Definition lNR : nat := 36.
Definition lNP : nat := 37.
Definition lLP : nat := 38.
Definition lTBY : nat := 39.
Definition lTFI : nat := 40.
Definition lGL : nat := 41.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bs qb nr np lp tby tfi gl : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x337d0 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl.
Local Notation XW := (YF2g.XW b nx bs qb nr np lp tby tfi gl).
Local Notation E0 := (YF2g.E0 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation Er := (YF2g.Er regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation E2 := (YF2g.E2 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation E1 := (YF2g.E1 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqB := (YF2g.EqB regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNX := (YF2g.EqNX regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqBS := (YF2g.EqBS regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqQB := (YF2g.EqQB regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNR := (YF2g.EqNR regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNP := (YF2g.EqNP regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqLP := (YF2g.EqLP regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqTBY := (YF2g.EqTBY regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqTFI := (YF2g.EqTFI regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqGL := (YF2g.EqGL regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation R_STK := YF2g.R_STK.
Local Notation R_QW := YF2g.R_QW.
Local Notation R_QG := YF2g.R_QG.
Local Notation R_B := YF2g.R_B.
Local Notation REG0 := YF2g.REG0.
Local Notation R_LPN := YF2g.R_LPN.
Local Notation FFL := YF2g.FFL.
Local Notation SR0 := YF2g.SR0.
Local Notation SS0 := YF2g.SS0.
Local Notation LYB := (YF2g.LYB W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation derived_ranges := (YF2g.derived_ranges W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation WINF := (YF2g.WINF b).
Local Notation WINA := (YF2g.WINA np lp).
Local Notation WIN := (YF2g.WIN regs0 b np lp).
Local Notation win_sub := YF2g.win_sub.
Local Notation win_sub_sound := (YF2g.win_sub_sound ly regs0).
Local Notation WSK0 := YF2g.WSK0.
Local Notation WSKL := YF2g.WSKL.
Local Notation sk_ok := (YF2g.sk_ok regs0 b np lp).
Local Notation WSK0_ok := (YF2g.WSK0_ok W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation WSKL_ok := (YF2g.WSKL_ok W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation windows_WIN := (YF2g.windows_WIN ly regs0 b np lp).
Local Notation WIN_cases := (YF2g.WIN_cases W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation MEQ := (YF2g.MEQ regs0 mem0 b np lp).
Local Notation MEQ_frame := (YF2g.MEQ_frame ly regs0 mem0 b np lp).
Local Notation MEQ_0 := (YF2g.MEQ_0 regs0 mem0 b np lp).
Local Notation WIN0 := (YF2g.WIN0 regs0 b).
Local Notation WIN0_WIN := (YF2g.WIN0_WIN regs0 b np lp).
Local Notation sk_ok0 := (YF2g.sk_ok0 regs0 b).
Local Notation WSK0_ok0 := (YF2g.WSK0_ok0 W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation MEQ0 := (YF2g.MEQ0 regs0 mem0 b).
Local Notation MEQ0_frame := (YF2g.MEQ0_frame W ly regs0 mem0 b).
Local Notation MEQ0_0 := (YF2g.MEQ0_0 regs0 mem0 b).
Local Notation MEQ0_MEQ := (YF2g.MEQ0_MEQ regs0 mem0 b np lp).
Local Notation SREGS := YF2g.SREGS.
Local Notation GLn := (YF2g.GLn nx gl).
Local Notation TFIn := (YF2g.TFIn b np tfi).
Local Notation at_CONT := (YF2g.at_CONT W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Local Notation at_EXIT := (YF2g.at_EXIT W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Local Notation postL := (YF2g.postL W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hsp Hsp_al Hpres Hb Hnx Hcnt Hby Hgl Htfi Hlp SEED].
Ltac off_by tac :=
first [ img_apply off_img_high; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let m1 := img_ev (ss_mem ss) in idtac "MEM" m1;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
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
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | img_try (zlia) | img_try (unfold M64; zlia) ]); zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YQ0b.r_base]; rewrite ?Z.add_0_l;
first [ img_refl | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 32) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 38) = _ |- _ => rewrite B end; numconst; zlia ].
Ltac tV EGL ETFI := first
[ img_refl
| cbn [sv_denot]; rewrite ?YF2g.EqB, ?YF2g.EqNX, ?YF2g.EqBS, ?YF2g.EqQB, ?YF2g.EqNR, ?YF2g.EqNP,
?YF2g.EqLP, ?YF2g.EqTBY, ?YF2g.EqTFI, ?YF2g.EqGL; unfold w64; rewrite ?Zbv_add_unsigned;
first [ img_refl | f_equal; rewrite ?EGL, ?ETFI; zlia
| first [ rewrite (YF2g.Er _ _ _ _ _ _ _ _ _ _ _ 1 1%bv eq_refl) | rewrite (YF2g.Er _ _ _ _ _ _ _ _ _ _ _ 2 2%bv eq_refl)
| rewrite (YF2g.Er _ _ _ _ _ _ _ _ _ _ _ 12 12%bv eq_refl) | rewrite (YF2g.Er _ _ _ _ _ _ _ _ _ _ _ 13 13%bv eq_refl) ];
rewrite ?Z.add_0_r; first [ img_refl | img_apply Z_to_bv_bv_unsigned | f_equal; zlia ] ]
| img_apply denot_by_zev; [ img_refl | rewrite ?EGL, ?ETFI; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
rewrite ?EGL, ?ETFI; land_lits; numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | img_try (zlia) | img_try (unfold M64; zlia) ]); zcanon_simp; zlia ] ].
Ltac tR EGL ETFI := first [ zlia | rewrite ?EGL, ?ETFI; numconst; zlia | img_apply u64_range
].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; img_refl.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac reg_zev HS r EGL ETFI :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := img_ev (sr_get sr rr) in img_change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
img_apply denot_by_zev; [ img_refl | rewrite ?EGL, ?ETFI; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
rewrite ?EGL, ?ETFI; land_lits; numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | img_try (zlia) | img_try (unfold M64; zlia) ]); zcanon_simp; zlia ].
Ltac reg_val HS r EGL ETFI := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV EGL ETFI | reg_zev HS r EGL ETFI ].
Ltac sregs HS Htp :=
intros r Hr; cbn [YF2g.SREGS In] in Hr;
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Ltac presL HS iS iB BV2 BV32 BV38 DR Usp tLPH :=
intros a Ha Hh; unfold YF2g.WIN, YF2g.WINF, YF2g.WINA in Ha;
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hne Ha]]];
[ img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Hh Usp DR; numconst; zlia) ])
| img_try (exfalso; clear - Ha Hh; numconst; zlia) | img_try (exfalso; clear - Ha Hh; numconst; zlia)
| img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iB _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ])
| img_try (tLPH Hne Ha) ].
Ltac fin_CONT HS EGL ETFI Htp iS iW iG iB tPRES tLP :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|]; split; [img_try (assumption)|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [img_try (rewrite HshR at 1; img_refl)|];
split; [img_try (reg_entry HS (2%bv : bv 5) 2%nat)|];
split; [img_try (reg_lit HS (10%bv : bv 5))|];
split; [img_try (let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; img_refl)|];
split; [img_try (reg_entry HS (12%bv : bv 5) 12%nat)|];
split; [img_try (reg_entry HS (13%bv : bv 5) 13%nat)|];
split; [img_try (reg_val HS (14%bv : bv 5) EGL ETFI)|];
split; [img_try (reg_val HS (15%bv : bv 5) EGL ETFI)|];
split; [img_try (reg_val HS (16%bv : bv 5) EGL ETFI)|];
split; [img_try (reg_val HS (5%bv : bv 5) EGL ETFI)|];
split; [img_try (reg_entry HS (1%bv : bv 5) 1%nat)|];
split; [img_try (sregs HS Htp)|];
split; [img_try (assumption)|];
split; [img_try (tPRES)|];
cbv zeta;
split; [img_try (memvo HS iW (A_QUAR + 152); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iW (A_QUAR + 153); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E0 _ msx iW _ 2 _ _ a HS); [img_refl | img_refl | cbn [base_val YQ0b.r_base]; clear - Ha; numconst; zlia])|];
split; [img_try (memvo HS iG (A_QUAR + 160); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 168); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 176); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 184); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iB 0; [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (tLP)|];
split; [img_try (memvo HS iS 8; [tA | tV EGL ETFI | tR EGL ETFI])|];
memvo HS iS 24; [img_try (tA) | img_try (tV EGL ETFI) | img_try (tR EGL ETFI)]
end.
Ltac fin_EXIT HS EGL ETFI Htp iS iW iG iB tPRES tLP :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|]; split; [img_try (assumption)|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [img_try (rewrite HshR at 1; img_refl)|];
split; [img_try (reg_entry HS (2%bv : bv 5) 2%nat)|];
split; [img_try (reg_lit HS (10%bv : bv 5))|];
split; [img_try (reg_entry HS (11%bv : bv 5) 2%nat)|];
split; [img_try (reg_entry HS (12%bv : bv 5) 12%nat)|];
split; [img_try (reg_entry HS (13%bv : bv 5) 13%nat)|];
split; [img_try (reg_lit HS (1%bv : bv 5))|];
split; [img_try (sregs HS Htp)|];
split; [img_try (assumption)|];
split; [img_try (tPRES)|];
cbv zeta;
split; [img_try (intros a Ha;
let C := fresh "C" in
assert (C : a = A_QUAR + 152 \/ a = A_QUAR + 153 \/ A_QUAR + 154 <= a < A_QUAR + 156) by (clear - Ha; zlia);
destruct C as [-> |[-> |C]];
[ let V := fresh "V" in
assert (V : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 1 0) by (memvo HS iW (A_QUAR + 152); [tA | img_refl | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in V; img_exact V
| let V := fresh "V" in
assert (V : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 153) 1 0) by (memvo HS iW (A_QUAR + 153); [tA | img_refl | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in V; img_exact V
| eapply (st_ok_chunk_zero (w_H W) E0 _ msx iW _ 2 _ _ a HS); [img_refl | img_refl | cbn [base_val YQ0b.r_base]; clear - C; numconst; zlia] ])|];
split; [img_try (memvo HS iG (A_QUAR + 160); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 168); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 176); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iG (A_QUAR + 184); [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iB 0; [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (tLP)|];
split; [img_try (memvo HS iS 0; [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iS 8; [tA | tV EGL ETFI | tR EGL ETFI])|];
split; [img_try (memvo HS iS 16; [tA | tV EGL ETFI | tR EGL ETFI])|];
memvo HS iS 24; [img_try (tA) | img_try (tV EGL ETFI) | img_try (tR EGL ETFI)]
end.
Ltac iter_tail HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY :=
srr_branch_sh tfxtbl_rtG_ok HS;
[
let Hn := fresh "HNX" in
match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
assert (Hn : nx <> 0) by (img_try (clear - Hb0 DR R33; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.eqb_neq in Hb0; img_exact Hb0)); clear Hb0 end;
let EGL := fresh "EGL" in
assert (EGL : GLn = gl) by (img_try (unfold YF2g.GLn; destruct (Z.eqb_spec nx 0); [img_try (exfalso; zlia) | img_refl]));
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfxtbl_rtG_ok HS; meq_acc SKW;
iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL
|
let Hn := fresh "HNX" in
match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
assert (Hn : nx = 0) by (img_try (clear - Hb0 DR R33; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.eqb_eq in Hb0; img_exact Hb0)); clear Hb0 end;
let EGL := fresh "EGL" in
assert (EGL : GLn = 0) by (img_try (unfold YF2g.GLn; rewrite Hn, Z.eqb_refl; img_refl));
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfxtbl_rtG_ok HS; meq_acc SKW;
iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL ]
with iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL :=
srr_branch_sh tfxtbl_rtG_ok HS;
[ first [ exfalso; match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
clear - Hb0 DR R37 HNP; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.eqb_neq in Hb0; img_exact (Hb0 HNP) end
| match goal with Hb0 : branch_taken _ _ _ = true |- _ => clear Hb0 end;
let ETFI := fresh "ETFI" in
assert (ETFI : TFIn = tfi) by (img_try (unfold YF2g.TFIn; destruct (Z.eqb_spec np 0); [img_try (exfalso; zlia) | img_refl]));
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfxtbl_rtG_ok HS; meq_acc SKW;
iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI ]
| first [ exfalso; match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
clear - Hb0 DR R37 HNP; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.eqb_eq in Hb0; img_exact (HNP Hb0) end
| match goal with Hb0 : branch_taken _ _ _ = false |- _ => clear Hb0 end;
let ETFI := fresh "ETFI" in
assert (ETFI : TFIn = b) by (img_try (unfold YF2g.TFIn; rewrite HNP, Z.eqb_refl; img_refl));
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfxtbl_rtG_ok HS; meq_acc SKW;
iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI ] ]
with iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI :=
srr_branch_sh tfxtbl_rtG_ok HS;
[
match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
assert (qb - bs <= kQuarantineMin) by (img_try (clear - Hb0 DR R34 R35 HBY; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.ltb_ge in Hb0; zlia)); clear Hb0 end;
unfold YF2g.postL; destruct (Z.ltb_spec kQuarantineMin (qb - bs)); [img_try (exfalso; zlia)|];
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfxtbl_rtG_ok HS (0x33a3c + D_150); meq_acc SKW;
fin_EXIT HS EGL ETFI Htp iS iW iG iB tPRES tLP
|
match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
assert (kQuarantineMin < qb - bs) by (img_try (clear - Hb0 DR R34 R35 HBY; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.ltb_lt in Hb0; zlia)); clear Hb0 end;
unfold YF2g.postL; destruct (Z.ltb_spec kQuarantineMin (qb - bs)); [|img_try (exfalso; zlia)];
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfxtbl_rtG_ok HS (0x337d0 + D_150); meq_acc SKW;
fin_CONT HS EGL ETFI Htp iS iW iG iB tPRES tLP ].
Lemma segL : SRr tfxsegs W cfg0 postL.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = b) by (img_try (unfold rho_of; rewrite EqB; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = nx) by (img_try (unfold rho_of; rewrite EqNX; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = bs) by (img_try (unfold rho_of; rewrite EqBS; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R35 : rho_of E0 35%nat = qb) by (img_try (unfold rho_of; rewrite EqQB; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R36 : rho_of E0 36%nat = nr) by (img_try (unfold rho_of; rewrite EqNR; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R37 : rho_of E0 37%nat = np) by (img_try (unfold rho_of; rewrite EqNP; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R38 : rho_of E0 38%nat = lp) by (img_try (unfold rho_of; rewrite EqLP; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R39 : rho_of E0 39%nat = tby) by (img_try (unfold rho_of; rewrite EqTBY; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R40 : rho_of E0 40%nat = tfi) by (img_try (unfold rho_of; rewrite EqTFI; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R41 : rho_of E0 41%nat = gl) by (img_try (unfold rho_of; rewrite EqGL; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (BV32 : bv_unsigned (ew E0 32) = b) by img_exact R32.
assert (BV38 : bv_unsigned (ew E0 38) = lp) by img_exact R38.
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfxsegs m0 a n v -> val_mem tfxsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HMq Hn Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(img_try (zlia))) as [N1 N2].
img_apply HMq. rewrite unsigned_lit_small by img_exact N2. img_exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HMq Hn Ha Hp. img_apply (apresent_same (w_H W) mem0); [|img_try (img_exact Hp)]. img_apply HMq. rewrite unsigned_lit_small by img_exact Ha. img_exact Hn. }
assert (NW0 : forall a, ~ (sp0 <= a < sp0 + 32) -> ~ (A_QUAR + 152 <= a < A_QUAR + 156) -> ~ (A_QUAR + 160 <= a < A_QUAR + 192) ->
~ (b <= a < b + 8) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [img_try (img_exact (N0 X))|]. unfold YF2g.WINF in X. clear - X N1 N2 N3. zlia. }
destruct (Z.eq_dec np 0) as [HNP|HNP].
-
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSK0_ok E0 HE0) as SKW.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
iter_tail HS HNP SKW Htp 0%nat 1%nat 2%nat 3%nat
ltac:(img_try (presL HS 0%nat 3%nat BV2 BV32 BV38 DR Usp ltac:(fun Hne Ha => exfalso; img_exact (Hne HNP))))
ltac:(img_try (intros X; exfalso; img_exact (X HNP))) DR R33 R34 R35 R37 Hby.
-
destruct Hlp as (P1 & P2 & P3). destruct (P3 HNP) as (L1 & L2 & L3 & L4).
apply (st_ok_add_region _ _ _ R_LPN) in HS;
[ | img_refl
| img_try (unfold YF2g.R_LPN, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV38;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - L1 L2 LB Ho; numconst; zlia) | img_apply PRQ; [img_exact MQ | img_apply NW0; clear - Ho L1 L2 L3 LB DR Hlo Hhi; numconst; zlia | clear - Ho L1 L2 LB; numconst; zlia | img_apply L4; zlia]] |];
img_apply Forall_nil)
| img_try (unfold YF2g.R_LPN; cbn [YQ0b.all_disjoint ss_mem]; repeat split; unfold YQ0b.extent_disjoint;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2; clear - LB DR L1 L2 L3 Hlo Hhi; numconst; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSKL_ok E0 HE0 HNP) as SKW.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
iter_tail HS HNP SKW Htp 1%nat 2%nat 3%nat 4%nat
ltac:(img_try (presL HS 1%nat 4%nat BV2 BV32 BV38 DR Usp
ltac:(fun Hne Ha => eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV38; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha L1 L2 LB; numconst; zlia)) ])))
ltac:(img_try (intros _; memvo HS 0%nat 0; [img_try (tA) | img_try (tV HNP HNP) | img_try (tR HNP HNP)])) DR R33 R34 R35 R37 Hby.
Qed.
End WK.
End d.
