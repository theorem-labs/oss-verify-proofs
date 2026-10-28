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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFgl.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bs qb nr np lp tby tfi gl : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x331c8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl.
Local Notation XW := (AFgl.XW b nx bs qb nr np lp tby tfi gl).
Local Notation E0 := (AFgl.E0 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation Er := (AFgl.Er regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation E2 := (AFgl.E2 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation E1 := (AFgl.E1 regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqB := (AFgl.EqB regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNX := (AFgl.EqNX regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqBS := (AFgl.EqBS regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqQB := (AFgl.EqQB regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNR := (AFgl.EqNR regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqNP := (AFgl.EqNP regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqLP := (AFgl.EqLP regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqTBY := (AFgl.EqTBY regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqTFI := (AFgl.EqTFI regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation EqGL := (AFgl.EqGL regs0 b nx bs qb nr np lp tby tfi gl).
Local Notation R_STK := AFgl.R_STK.
Local Notation R_QW := AFgl.R_QW.
Local Notation R_QG := AFgl.R_QG.
Local Notation R_B := AFgl.R_B.
Local Notation REG0 := AFgl.REG0.
Local Notation R_LPN := AFgl.R_LPN.
Local Notation FFL := AFgl.FFL.
Local Notation SR0 := AFgl.SR0.
Local Notation SS0 := AFgl.SS0.
Local Notation LYB := (AFgl.LYB W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation derived_ranges := (AFgl.derived_ranges W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation WINF := (AFgl.WINF b).
Local Notation WINA := (AFgl.WINA np lp).
Local Notation WIN := (AFgl.WIN regs0 b np lp).
Local Notation win_sub := AFgl.win_sub.
Local Notation win_sub_sound := (AFgl.win_sub_sound ly regs0).
Local Notation WSK0 := AFgl.WSK0.
Local Notation WSKL := AFgl.WSKL.
Local Notation sk_ok := (AFgl.sk_ok regs0 b np lp).
Local Notation WSK0_ok := (AFgl.WSK0_ok W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation WSKL_ok := (AFgl.WSKL_ok W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation windows_WIN := (AFgl.windows_WIN ly regs0 b np lp).
Local Notation WIN_cases := (AFgl.WIN_cases W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation MEQ := (AFgl.MEQ regs0 mem0 b np lp).
Local Notation MEQ_frame := (AFgl.MEQ_frame ly regs0 mem0 b np lp).
Local Notation MEQ_0 := (AFgl.MEQ_0 regs0 mem0 b np lp).
Local Notation WIN0 := (AFgl.WIN0 regs0 b).
Local Notation WIN0_WIN := (AFgl.WIN0_WIN regs0 b np lp).
Local Notation sk_ok0 := (AFgl.sk_ok0 regs0 b).
Local Notation WSK0_ok0 := (AFgl.WSK0_ok0 W ly regs0 mem0 b nx bs qb nr np lp tby tfi gl FH).
Local Notation MEQ0 := (AFgl.MEQ0 regs0 mem0 b).
Local Notation MEQ0_frame := (AFgl.MEQ0_frame W ly regs0 mem0 b).
Local Notation MEQ0_0 := (AFgl.MEQ0_0 regs0 mem0 b).
Local Notation MEQ0_MEQ := (AFgl.MEQ0_MEQ regs0 mem0 b np lp).
Local Notation SREGS := AFgl.SREGS.
Local Notation GLn := (AFgl.GLn nx gl).
Local Notation TFIn := (AFgl.TFIn b np tfi).
Local Notation at_CONT := (AFgl.at_CONT W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Local Notation at_EXIT := (AFgl.at_EXIT W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Local Notation postL := (AFgl.postL W regs0 mem0 md0 b nx bs qb nr np lp tby tfi gl).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hsp Hsp_al Hpres Hb Hnx Hcnt Hby Hgl Htfi Hlp SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let m1 := eval vm_compute in (ss_mem ss) in idtac "MEM" m1;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
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
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l;
first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 32) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 38) = _ |- _ => rewrite B end; numconst; zlia ].
Ltac tV EGL ETFI := first
[ reflexivity
| cbn [sv_denot]; rewrite ?AFgl.EqB, ?AFgl.EqNX, ?AFgl.EqBS, ?AFgl.EqQB, ?AFgl.EqNR, ?AFgl.EqNP,
?AFgl.EqLP, ?AFgl.EqTBY, ?AFgl.EqTFI, ?AFgl.EqGL; unfold w64; rewrite ?Zbv_add_unsigned;
first [ reflexivity | f_equal; rewrite ?EGL, ?ETFI; zlia
| first [ rewrite (AFgl.Er _ _ _ _ _ _ _ _ _ _ _ 1 1%bv eq_refl) | rewrite (AFgl.Er _ _ _ _ _ _ _ _ _ _ _ 2 2%bv eq_refl)
| rewrite (AFgl.Er _ _ _ _ _ _ _ _ _ _ _ 12 12%bv eq_refl) | rewrite (AFgl.Er _ _ _ _ _ _ _ _ _ _ _ 13 13%bv eq_refl) ];
rewrite ?Z.add_0_r; first [ reflexivity | apply Z_to_bv_bv_unsigned | f_equal; zlia ] ]
| apply denot_by_zev; [ reflexivity | rewrite ?EGL, ?ETFI; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
rewrite ?EGL, ?ETFI; land_lits; numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; zlia ] ].
Ltac tR EGL ETFI := first [ zlia | rewrite ?EGL, ?ETFI; numconst; zlia | apply u64_range
].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_zev HS r EGL ETFI :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | rewrite ?EGL, ?ETFI; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
rewrite ?EGL, ?ETFI; land_lits; numconst; zcanon_simp; repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; zlia ].
Ltac reg_val HS r EGL ETFI := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV EGL ETFI | reg_zev HS r EGL ETFI ].
Ltac sregs HS Htp :=
intros r Hr; cbn [AFgl.SREGS In] in Hr;
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Ltac presL HS iS iB BV2 BV32 BV38 DR Usp tLPH :=
intros a Ha Hh; unfold AFgl.WIN, AFgl.WINF, AFgl.WINA in Ha;
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hne Ha]]];
[ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Hh Usp DR; numconst; zlia) ]
| exfalso; clear - Ha Hh; numconst; zlia | exfalso; clear - Ha Hh; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iB _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ]
| tLPH Hne Ha ].
Ltac fin_CONT HS EGL ETFI Htp iS iW iG iB tPRES tLP :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [assumption|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [reg_lit HS (10%bv : bv 5)|];
split; [let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; reflexivity|];
split; [reg_entry HS (12%bv : bv 5) 12%nat|];
split; [reg_entry HS (13%bv : bv 5) 13%nat|];
split; [reg_val HS (14%bv : bv 5) EGL ETFI|];
split; [reg_val HS (15%bv : bv 5) EGL ETFI|];
split; [reg_val HS (16%bv : bv 5) EGL ETFI|];
split; [reg_val HS (5%bv : bv 5) EGL ETFI|];
split; [reg_entry HS (1%bv : bv 5) 1%nat|];
split; [sregs HS Htp|];
split; [assumption|];
split; [tPRES|];
cbv zeta;
split; [memvo HS iW (A_QUAR + 152); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iW (A_QUAR + 153); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [intros a Ha; eapply (st_ok_chunk_zero (w_H W) E0 _ msx iW _ 2 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]; clear - Ha; numconst; zlia]|];
split; [memvo HS iG (A_QUAR + 160); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 168); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 176); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 184); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iB 0; [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [tLP|];
split; [memvo HS iS 8; [tA | tV EGL ETFI | tR EGL ETFI]|];
memvo HS iS 24; [tA | tV EGL ETFI | tR EGL ETFI]
end.
Ltac fin_EXIT HS EGL ETFI Htp iS iW iG iB tPRES tLP :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [assumption|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [reg_lit HS (10%bv : bv 5)|];
split; [reg_entry HS (11%bv : bv 5) 2%nat|];
split; [reg_entry HS (12%bv : bv 5) 12%nat|];
split; [reg_entry HS (13%bv : bv 5) 13%nat|];
split; [reg_lit HS (1%bv : bv 5)|];
split; [sregs HS Htp|];
split; [assumption|];
split; [tPRES|];
cbv zeta;
split; [intros a Ha;
let C := fresh "C" in
assert (C : a = A_QUAR + 152 \/ a = A_QUAR + 153 \/ A_QUAR + 154 <= a < A_QUAR + 156) by (clear - Ha; zlia);
destruct C as [-> |[-> |C]];
[ let V := fresh "V" in
assert (V : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 1 0) by (memvo HS iW (A_QUAR + 152); [tA | reflexivity | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in V; exact V
| let V := fresh "V" in
assert (V : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 153) 1 0) by (memvo HS iW (A_QUAR + 153); [tA | reflexivity | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in V; exact V
| eapply (st_ok_chunk_zero (w_H W) E0 _ msx iW _ 2 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]; clear - C; numconst; zlia] ]|];
split; [memvo HS iG (A_QUAR + 160); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 168); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 176); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iG (A_QUAR + 184); [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iB 0; [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [tLP|];
split; [memvo HS iS 0; [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iS 8; [tA | tV EGL ETFI | tR EGL ETFI]|];
split; [memvo HS iS 16; [tA | tV EGL ETFI | tR EGL ETFI]|];
memvo HS iS 24; [tA | tV EGL ETFI | tR EGL ETFI]
end.
Ltac iter_tail HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY :=
srr_branch_sh tfibtbl_rtG_ok HS;
[
let Hn := fresh "HNX" in
match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
assert (Hn : nx <> 0) by (clear - Hb0 DR R33; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.eqb_neq in Hb0; exact Hb0); clear Hb0 end;
let EGL := fresh "EGL" in
assert (EGL : GLn = gl) by (unfold AFgl.GLn; destruct (Z.eqb_spec nx 0); [exfalso; zlia | reflexivity]);
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW;
iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL
|
let Hn := fresh "HNX" in
match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
assert (Hn : nx = 0) by (clear - Hb0 DR R33; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.eqb_eq in Hb0; exact Hb0); clear Hb0 end;
let EGL := fresh "EGL" in
assert (EGL : GLn = 0) by (unfold AFgl.GLn; rewrite Hn, Z.eqb_refl; reflexivity);
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW;
iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL ]
with iter_tail2 HS HNP SKW Htp iS iW iG iB tPRES tLP DR R33 R34 R35 R37 HBY EGL :=
srr_branch_sh tfibtbl_rtG_ok HS;
[ first [ exfalso; match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
clear - Hb0 DR R37 HNP; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.eqb_neq in Hb0; exact (Hb0 HNP) end
| match goal with Hb0 : branch_taken _ _ _ = true |- _ => clear Hb0 end;
let ETFI := fresh "ETFI" in
assert (ETFI : TFIn = tfi) by (unfold AFgl.TFIn; destruct (Z.eqb_spec np 0); [exfalso; zlia | reflexivity]);
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW;
iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI ]
| first [ exfalso; match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
clear - Hb0 DR R37 HNP; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.eqb_eq in Hb0; exact (HNP Hb0) end
| match goal with Hb0 : branch_taken _ _ _ = false |- _ => clear Hb0 end;
let ETFI := fresh "ETFI" in
assert (ETFI : TFIn = b) by (unfold AFgl.TFIn; rewrite HNP, Z.eqb_refl; reflexivity);
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW;
iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI ] ]
with iter_tail3 HS SKW Htp iS iW iG iB tPRES tLP DR R34 R35 HBY EGL ETFI :=
srr_branch_sh tfibtbl_rtG_ok HS;
[
match goal with Hb0 : branch_taken _ _ _ = true |- _ =>
assert (qb - bs <= kQuarantineMin) by (clear - Hb0 DR R34 R35 HBY; zbranch Hb0; apply Bool.negb_true_iff in Hb0; apply Z.ltb_ge in Hb0; zlia); clear Hb0 end;
unfold AFgl.postL; destruct (Z.ltb_spec kQuarantineMin (qb - bs)); [exfalso; zlia|];
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfibtbl_rtG_ok HS 0x33434; meq_acc SKW;
fin_EXIT HS EGL ETFI Htp iS iW iG iB tPRES tLP
|
match goal with Hb0 : branch_taken _ _ _ = false |- _ =>
assert (kQuarantineMin < qb - bs) by (clear - Hb0 DR R34 R35 HBY; zbranch Hb0; apply Bool.negb_false_iff in Hb0; apply Z.ltb_lt in Hb0; zlia); clear Hb0 end;
unfold AFgl.postL; destruct (Z.ltb_spec kQuarantineMin (qb - bs)); [|exfalso; zlia];
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfibtbl_rtG_ok HS 0x331c8; meq_acc SKW;
fin_CONT HS EGL ETFI Htp iS iW iG iB tPRES tLP ].
Lemma segL : SRr tfibsegs W cfg0 postL.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = b) by (unfold rho_of; rewrite EqB; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R33 : rho_of E0 33%nat = nx) by (unfold rho_of; rewrite EqNX; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R34 : rho_of E0 34%nat = bs) by (unfold rho_of; rewrite EqBS; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R35 : rho_of E0 35%nat = qb) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R36 : rho_of E0 36%nat = nr) by (unfold rho_of; rewrite EqNR; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R37 : rho_of E0 37%nat = np) by (unfold rho_of; rewrite EqNP; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R38 : rho_of E0 38%nat = lp) by (unfold rho_of; rewrite EqLP; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R39 : rho_of E0 39%nat = tby) by (unfold rho_of; rewrite EqTBY; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R40 : rho_of E0 40%nat = tfi) by (unfold rho_of; rewrite EqTFI; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R41 : rho_of E0 41%nat = gl) by (unfold rho_of; rewrite EqGL; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV32 : bv_unsigned (ew E0 32) = b) by exact R32.
assert (BV38 : bv_unsigned (ew E0 38) = lp) by exact R38.
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HMq Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(zlia)) as [N1 N2].
apply HMq. rewrite unsigned_lit_small by exact N2. exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HMq Hn Ha Hp. apply (apresent_same (w_H W) mem0); [|exact Hp]. apply HMq. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (NW0 : forall a, ~ (sp0 <= a < sp0 + 32) -> ~ (A_QUAR + 152 <= a < A_QUAR + 156) -> ~ (A_QUAR + 160 <= a < A_QUAR + 192) ->
~ (b <= a < b + 8) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [exact (N0 X)|]. unfold AFgl.WINF in X. clear - X N1 N2 N3. zlia. }
destruct (Z.eq_dec np 0) as [HNP|HNP].
-
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSK0_ok E0 HE0) as SKW.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
iter_tail HS HNP SKW Htp 0%nat 1%nat 2%nat 3%nat
ltac:(presL HS 0%nat 3%nat BV2 BV32 BV38 DR Usp ltac:(fun Hne Ha => exfalso; exact (Hne HNP)))
ltac:(intros X; exfalso; exact (X HNP)) DR R33 R34 R35 R37 Hby.
-
destruct Hlp as (P1 & P2 & P3). destruct (P3 HNP) as (L1 & L2 & L3 & L4).
apply (st_ok_add_region _ _ _ R_LPN) in HS;
[ | reflexivity
| unfold AFgl.R_LPN, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV38;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - L1 L2 LB Ho; numconst; zlia) | apply PRQ; [exact MQ | apply NW0; clear - Ho L1 L2 L3 LB DR Hlo Hhi; numconst; zlia | clear - Ho L1 L2 LB; numconst; zlia | apply L4; zlia]] |];
apply Forall_nil
| unfold AFgl.R_LPN; cbn [YP09.all_disjoint ss_mem]; repeat split; unfold YP09.extent_disjoint;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2; clear - LB DR L1 L2 L3 Hlo Hhi; numconst; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSKL_ok E0 HE0 HNP) as SKW.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
iter_tail HS HNP SKW Htp 1%nat 2%nat 3%nat 4%nat
ltac:(presL HS 1%nat 4%nat BV2 BV32 BV38 DR Usp
ltac:(fun Hne Ha => eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV38; clear - Ha; zlia | off_by ltac:(clear - Ha L1 L2 LB; numconst; zlia) ]))
ltac:(intros _; memvo HS 0%nat 0; [tA | tV HNP HNP | tR HNP HNP]) DR R33 R34 R35 R37 Hby.
Qed.
End WK.
End d.
