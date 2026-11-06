(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1d0 X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9 X1rz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X00s X00j
X00k X00l X00h.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X0rr X0ri X0rj X0rk X0rg.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ri OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rg.
Import ListNotations.
Open Scope Z_scope.

Section File2.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Theorem toobig_cpsE :
cpsE bsegs (RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data) (evw 2 msg_too_big) (EXIT fs 2).
Proof using AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
intros T c HR Hk.
destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HD & HLS & Hbig).
pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
pose proof CLX0 as (OUT0 & ERR0 & XE0 & _).
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
replace (evw 2 msg_too_big) with (evw 2 (fp_msg FPtoo_big) ++ evw 1 (so_buf stdout_init))
by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
apply (FPR Σ (FD argvb 67108864) fs (Z_to_bv 64 0x96518) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
(Z_to_bv 64 buf) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_too_big) (Z_to_bv 64 67108864) a3 a4 a5 a6 a7
(Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3) (Z_to_bv 64 67108864) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf)
s8 s9 s10 s11 t3 t4 t5 t6 F fc m FPtoo_big STDERR_FILE lo); try reflexivity; try assumption.
- intros a s Hs. discriminate Hs.
- io_ssp_tac AF_DRV.
- unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
- pois_nil_tac AF.
- intros cf1 Hc1.
destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (v & m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & ERR1 & OUTP1) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
pose proof (OUTP1 stdout_init OUT0) as OUT1.
assert (XE1 : XENV m1).
{ apply (XENV_loc m m1 XE0). intros a Ha. apply PRES1; [right; left; exact (proj1 (XENV_img _ Ha))|].
exact (proj1 (proj2 (proj2 (XENV_img _ Ha)))). }
pose proof (failed_walk2 usp gp (Z_to_bv 64 buf) (Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3) (Z_to_bv 64 67108864)
(Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6
F1 fc1 m1 MI1) as W1.
rewrite (ret_pc_even 0x96518) in Hc1' by lia.
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
intros cf2 Hc2.
destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
apply (EXC Σ (FD argvb 67108864) fs (Z_to_bv 64 0x96544) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 2)
(Z_to_bv 64 buf) (Z_to_bv 64 2) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3)
(Z_to_bv 64 67108864) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1
m1 stdout_init 2 lo); try reflexivity; try assumption.
+ lia.
+ left. reflexivity.
+ unfold call_ok. rewrite EU. split; [exact ST1|]. ul.
+ eapply (io_ssp_pres_fp IO_FP _ _ _ m m1); [| io_ssp_tac AF_DRV| exact (AF_DRV _ _ ART1)| exact PRES1].
intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End File2.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section File2.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Theorem toobig_cpsE :
cpsE asegs (RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data) (evw 2 msg_too_big) (EXIT fs 2).
Proof using AF AF_DRV FPR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
intros T c HR Hk.
destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HD & HLS & Hbig).
pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
pose proof CLX0 as (OUT0 & ERR0 & XE0 & _).
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
replace (evw 2 msg_too_big) with (evw 2 (fp_msg FPtoo_big) ++ evw 1 (so_buf stdout_init))
by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
apply (FPR Σ (FD argvb 67108864) fs (Z_to_bv 64 0x9642c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
(Z_to_bv 64 buf) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_too_big) (Z_to_bv 64 67108864) a3 a4 a5 a6 a7
(Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3) (Z_to_bv 64 67108864) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf)
s8 s9 s10 s11 t3 t4 t5 t6 F fc m FPtoo_big STDERR_FILE lo); try reflexivity; try assumption.
- intros a s Hs. discriminate Hs.
- io_ssp_tac AF_DRV.
- unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
- pois_nil_tac AF.
- intros cf1 Hc1.
destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (v & m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & ERR1 & OUTP1) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
pose proof (OUTP1 stdout_init OUT0) as OUT1.
assert (XE1 : XENV m1).
{ apply (XENV_loc m m1 XE0). intros a Ha. apply PRES1; [right; left; exact (proj1 (XENV_img _ Ha))|].
exact (proj1 (proj2 (proj2 (XENV_img _ Ha)))). }
pose proof (failed_walk2 usp gp (Z_to_bv 64 buf) (Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3) (Z_to_bv 64 67108864)
(Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6
F1 fc1 m1 MI1) as W1.
rewrite (ret_pc_even 0x9642c) in Hc1' by lia.
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
intros cf2 Hc2.
destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
apply (EXC Σ (FD argvb 67108864) fs (Z_to_bv 64 0x96458) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 2)
(Z_to_bv 64 buf) (Z_to_bv 64 2) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 67108864) (Z_to_bv 64 3)
(Z_to_bv 64 67108864) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1
m1 stdout_init 2 lo); try reflexivity; try assumption.
+ lia.
+ left. reflexivity.
+ unfold call_ok. rewrite EU. split; [exact ST1|]. ul.
+ eapply (io_ssp_pres_fp IO_FP _ _ _ m m1); [| io_ssp_tac AF_DRV| exact (AF_DRV _ _ ART1)| exact PRES1].
intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End File2.
