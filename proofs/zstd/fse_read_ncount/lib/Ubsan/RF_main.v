(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B4 RF_main_C RF_main_D.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section Main.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.
Hypothesis TRUN : ptarget_run_stmt.
#[using="MALLOC FREE FPR FWX SWF FWR TOW TRUN"] Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z) ms,
dvalid_sp sp0 argv envp -> SECRET = InitMem.draw_secret draw -> valid_argv argv -> valid_envp envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 ->
P1 sp0 argv envp uid hw draw TID ms ->
implM usegs (ra <- read_all Prog.io raw_malloc raw_free UREAD_STAGE (map bv_unsigned arg1) ;;
match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
(ps_init (reservedZ usegs) ATOP) RQEXIT ms.
Proof.
intros sp0 argv envp uid hw draw arg0 arg1 TID ms VSP HSEC VARGV VENVP EARGV HT HP1.
destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & fc & mm & j8
& -> & FR & BA & HP & ERR & FRM & SJ).
eapply implM_bind.
{ eapply (main_read_all sp0 argv envp uid hw draw arg0 arg1 TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR TOW);
[exact FR| exact BA| exact HP| exact ERR| exact FRM| exact SJ]. }
cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
- apply implM_ret. apply evt_done. exact PB.
- eapply (phaseC sp0 argv envp uid hw draw TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP HT FREE FWR TOW); [exact PB|].
intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
exact (phaseDE sp0 argv envp uid hw draw TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP HT FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
Qed.
#[using="MALLOC FREE FPR FWX SWF FWR TOW TRUN"] Theorem plain_main_proof : pmain_stmt.
Proof.
intros sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM.
destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2]; [| exact (main_usage sp0 argv envp uid hw draw VSP HSEC VARGV VENVP FPR FWX SWF ms AM NE2)].
Local Ltac2 Set LiaHints.tbl := fun () => "0040=5056405920.245056405920.255056405920.265056405920.2800000400800900=S2E2S2E2FS2E2".
destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
eapply implM_mono with (Q := RQEXIT); [| intros code s' ms' H; exact H].
rewrite (main_model_eq argv arg0 arg1 EARGV).
eapply implM_evt.
{ eapply (main_to_P1 sp0 argv envp uid hw draw VSP HSEC VARGV VENVP arg0 arg1); [exact EARGV| exact AM|].
intros TID ms' HT HP1. apply evt_done.
exact (main_from_P1 sp0 argv envp uid hw draw arg0 arg1 TID ms' VSP HSEC VARGV VENVP EARGV HT HP1). }
cbv beta. intros ms' H. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Main.
End CANSEC1.
