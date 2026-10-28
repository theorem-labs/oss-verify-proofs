(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Fz_iface Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2 Drv_main_B3 Drv_main_C Drv_main_D.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Drv_sys F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Str_cpy.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Main.
  Variable CS : cli_sig.
  Hypothesis CLI0AT : cli0_at_main CS.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TRUN : rtarget_run_stmt CS.

  (* [comment removed for export] *)
  Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) ms,
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 CS sp0 argv envp uid TID ms ->
    implM usegs (ra <- read_all io raw_malloc raw_free ustage (map bv_unsigned arg1) ;;
                 match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
          (ps_init (reservedZ usegs)) (fun code s' ms' => at_exit ps_so code s' ms') ms.
  Proof.
    intros sp0 argv envp uid arg0 arg1 TID ms VSP CEIL VARGV VENVP EARGV HT HP1.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & mm & pad
                     & -> & FR & BA & HP & ERR & SOF & SE & FL & IFL & SG & CL0 & AX0).
    eapply implM_bind.
    { eapply (main_read_all CS sp0 argv envp uid arg0 arg1 TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR);
        [exact FR| exact BA| exact HP| | | exact SG| ].
      - split; [exact SOF|]. split; [exact SE|]. split; [exact FL|]. split; [split; [exact IFL| exact AX0]| exact CL0].   (* [comment removed for export] *)
      - unfold RATP in ERR. cbv delta [MallocRep.wz] in ERR. unfold errno_addr in ERR. rewrite (unsigned_lit RMallocRep.RATP) in ERR by (unfold RMallocRep.RATP; lia).
        unfold RMallocRep.RERRNO. unfold RMallocRep.RATP in ERR. cbn [Z.add] in ERR. exact ERR.
      - reflexivity. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implM_ret. apply evt_done. exact PB.
    - eapply (phaseC CS sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE FWR); [exact PB|].
      intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
      exact (phaseDE CS sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
  Qed.

  Theorem main_proof : rmain_stmt.
  Proof.
    unfold rmain_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{ unfold main_model. replace (Z.of_nat (length (argv_Z argv)) =? 2) with false by (symmetry; apply Z.eqb_neq; unfold argv_Z; rewrite length_map; exact NE2). cbn [negb].
        exact (main_usage_proof FPR FWX SWF sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS NE2 AM). }
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    rewrite (main_model_eq argv arg0 arg1 EARGV).
    destruct (main_to_P1_proof CS CLI0AT sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS ltac:(rewrite EARGV; reflexivity) AM) as (TID & HT & EV).
    eapply implM_evt; [exact EV|]. cbv beta. intros ms' HP1.
    exact (main_from_P1 sp0 argv envp uid arg0 arg1 TID ms' VSP CEIL VARGV VENVP EARGV HT HP1).
  Qed.
End Main.
End WithCeiling0.
