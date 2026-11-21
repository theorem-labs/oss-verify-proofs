(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg F_syscalls StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B4 RF_main_C RF_main_D.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import CMonad CMonadX ProgC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require AdapterC DriverC HarnessC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Section Main.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.
  Hypothesis TRUN : ptarget_run_stmt.
  Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z) ms,
    dvalid_sp sp0 argv envp -> SECRET = InitMem.draw_secret draw -> valid_argv argv -> valid_envp envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 sp0 argv envp uid hw draw TID ms ->
    implMC psegs (cmbind (clift (read_all Prog.io raw_malloc raw_free PREAD_STAGE (map bv_unsigned arg1)))
                         (fun ra => match ra with RdExit => cmret 2 | RdDone buf content => main_rest buf content end))
          (ps_init (reservedZ psegs) ATOP) RQEXIT ms.
  Proof.
    intros sp0 argv envp uid hw draw arg0 arg1 TID ms VSP HSEC VARGV VENVP EARGV HT HP1.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & fc & mm & j8
                     & -> & FR & BA & HP & ERR & FRM & SJ).
    eapply implMC_lift_bind.
    { eapply (main_read_all sp0 argv envp uid hw draw arg0 arg1 TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR TOW);
        [exact FR| exact BA| exact HP| exact ERR| exact FRM| exact SJ]. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implMC_ret. apply evt_done. exact PB.
    - eapply (phaseC sp0 argv envp uid hw draw TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP HT FREE FWR TOW); [exact PB|].
      intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
      exact (phaseDE sp0 argv envp uid hw draw TID j8 s4 s5 s6 s7 s8 s9 s10 s11 VSP HT FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
  Qed.

  Theorem plain_main_proof : pmain_stmt.
  Proof.
    intros sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{
        unfold DriverC.main_model. unfold argv_Z at 1. rewrite length_map.
        replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; exact NE2). cbn [negb].
        apply implMC_lift. exact (main_usage sp0 argv envp uid hw draw VSP HSEC VARGV VENVP FPR FWX SWF ms AM NE2). }
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    eapply implMC_mono with (Q := RQEXIT); [| intros code s' ms' H; exact H].
    rewrite (main_model_eq argv arg0 arg1 EARGV).
    eapply implMC_evt.
    { eapply (main_to_P1 sp0 argv envp uid hw draw VSP HSEC VARGV VENVP arg0 arg1); [exact EARGV| exact AM|].
      intros TID ms' HT HP1. apply evt_done.
      exact (main_from_P1 sp0 argv envp uid hw draw arg0 arg1 TID ms' VSP HSEC VARGV VENVP EARGV HT HP1). }
    cbv beta. intros ms' H. exact H.
  Qed.
End Main.
End CANSEC1.
