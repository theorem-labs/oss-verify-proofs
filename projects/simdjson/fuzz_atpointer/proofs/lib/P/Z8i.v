(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1 Zi2.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio Zpb Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Z10m Zcp Layout Exit Startup Z10n Zfm Zfq Zq5 Z8e Z8h Z8g Z8p Z8j Z8k Z8l Z8m Z8n Z8o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Z8q Z9n Z10s.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := Zf2.wz.
Notation pph := Plain.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Z7h.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Main.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TRUN : rtarget_run_stmt.

  Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) ms,
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 sp0 argv envp uid TID ms ->
    implM psegs (ra <- read_all io raw_malloc raw_free pstage (map bv_unsigned arg1) ;;
                 match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
          (ps_init (reservedZ psegs)) (fun code s' ms' => at_exit ps_so code s' ms') ms.
  Proof.
    intros sp0 argv envp uid arg0 arg1 TID ms VSP CEIL VARGV VENVP EARGV HT HP1.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & mm & pad
                     & -> & FR & BA & HP & ERR & SOF & SE & FL & IFL & SG).
    eapply implM_bind.
    { eapply (main_read_all sp0 argv envp uid arg0 arg1 TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR);
        [exact FR| exact BA| exact HP| | | exact SG| ].
      - split; [exact SOF|]. split; [exact SE|]. split; [exact FL| exists (Z_to_bv 8 0); exact IFL].
      - unfold RATP in ERR. cbv delta [Zf2.wz] in ERR. unfold errno_addr in ERR. rewrite (unsigned_lit Zhy.RATP) in ERR by (unfold Zhy.RATP; lia).
        unfold Zhy.RERRNO. unfold Zhy.RATP in ERR. cbn [Z.add] in ERR. exact ERR.
      - reflexivity. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implM_ret. apply evt_done. exact PB.
    - eapply (phaseC sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE FWR); [exact PB|].
      intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
      exact (phaseDE sp0 argv envp uid TID pad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
  Qed.

  Theorem main_proof : rmain_stmt.
  Proof.
    unfold rmain_stmt. intros sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{ unfold main_model. replace (Z.of_nat (length (argv_Z argv)) =? 2) with false by (symmetry; apply Z.eqb_neq; unfold argv_Z; rewrite length_map; exact NE2). cbn [negb].
        exact (main_usage_proof FPR FWX SWF sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS NE2 AM). }
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    rewrite (main_model_eq argv arg0 arg1 EARGV).
    destruct (main_to_P1_proof sp0 argv envp uid ms VSP CEIL VARGV VENVP FITS ltac:(rewrite EARGV; reflexivity) AM) as (TID & HT & EV).
    eapply implM_evt; [exact EV|]. cbv beta. intros ms' HP1.
    exact (main_from_P1 sp0 argv envp uid arg0 arg1 TID ms' VSP CEIL VARGV VENVP EARGV HT HP1).
  Qed.
End Main.
End WithCeiling0.
