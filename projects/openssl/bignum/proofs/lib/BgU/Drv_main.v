(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput and section hypotheses passed by name). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Str_tac Startup_glue InitMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Lib_iface Exit_defs Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2 Drv_main_B3 Drv_main_C Drv_main_D.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Str_cpy.
From OSSVerify.Proofs.openssl.bignum.lib.BgU Require Drv_sys F_memcpy.
From OSSVerify.openssl.bignum.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Section Main.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TRUN : rtarget_run_stmt.

  Lemma main_from_P1 : forall (sp0 : word) (inp : ProcInput) (mbase : word) (arg0 arg1 : list byte) (TID : Z) ms,
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> in_argv inp = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 sp0 inp mbase TID ms ->
    implM bgusegs (ra <- read_all io raw_malloc raw_free bgustage (map bv_unsigned arg1) ;;
                 match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
          (ps_init (reservedZ bgusegs)) (fun code s' ms' => at_exit code s' ms') ms.
  Proof.
    intros sp0 inp mbase arg0 arg1 TID ms VSP CEIL VARGV VENVP EARGV HT HP1.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & mm & pad
                     & -> & FR & BA & HP & ERR & SOF & SE & IFL & SG & OSC & PRI).
    eapply implM_bind.
    { (* A Section lemma keeps only the hypotheses its proof uses, so name the section
         variables positionally and let [first] fill whichever section hypotheses and
         premises survive, in whatever order they arrive (as openssl/bndiv's U/Drv_main.v). *)
      eapply (main_read_all sp0 inp mbase arg0 arg1 TID pad s4 s5 s6 s7 s8 s9 s10 s11);
        first [ exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT
              | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TRUN
              | exact FR | exact BA | exact HP | exact SG
              | (split; [exact SOF|]; split; [exact SE|]; split; [exact IFL|]; split; [exact OSC| exact PRI])
              | (unfold RATP in ERR; cbv delta [MallocRep.wz] in ERR; unfold errno_addr in ERR;
                 rewrite (unsigned_lit RMallocRep.RATP) in ERR by (unfold RMallocRep.RATP; lia);
                 unfold RMallocRep.RERRNO; unfold RMallocRep.RATP in ERR; cbn [Z.add] in ERR; exact ERR)
              | reflexivity ]. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implM_ret. apply evt_done. exact PB.
    - (* the same: no positional section hypotheses, no goal counting *)
      eapply phaseC;
        first [ exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT
              | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TRUN
              | exact PB
              | (intros DATA A cap cw L cfg sc s1 ms1 HC R0; rewrite HC;
                 eapply phaseDE;
                   first [ exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT
                         | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR
                         | exact TRUN | exact R0 ]) ].
  Qed.

  Theorem main_proof : rmain_stmt.
  Proof.
    unfold rmain_stmt. intros sp0 inp mbase ms VSP CEIL VARGV VENVP FITS HSP AM.
    destruct (Z.eq_dec (Z.of_nat (length (in_argv inp))) 2) as [E2|NE2].
    2:{ unfold main_model. replace (Z.of_nat (length (argv_Z (in_argv inp))) =? 2) with false by (symmetry; apply Z.eqb_neq; unfold argv_Z; rewrite length_map; exact NE2). cbn [negb].
        (* [main_usage_proof] is discharged over Section Usage's hypotheses, so do not
           pass them by position. *)
        eapply main_usage_proof;
          first [ exact FPR | exact FWX | exact SWF
                | exact VSP | exact CEIL | exact VARGV | exact VENVP
                | exact FITS | exact HSP | exact NE2 | exact AM ]. }
    pose proof (main_to_P1_proof sp0 inp mbase ms VSP CEIL VARGV VENVP FITS HSP E2 AM) as P1H.
    destruct (in_argv inp) as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV.
    rewrite (main_model_eq inp arg0 arg1 EARGV).
    destruct P1H as (TID & HT & EV).
    eapply implM_evt; [exact EV|]. cbv beta. intros ms' HP1.
    (* [destruct (in_argv inp) ... eqn:EARGV] substitutes the scrutinee for [[arg0; arg1]]
       in [VARGV] too, while [main_from_P1] wants [valid_argv (in_argv inp)]: transport it
       along [EARGV] (as openssl/bndiv's U/Drv_main.v does). *)
    exact (main_from_P1 sp0 inp mbase arg0 arg1 TID ms' VSP CEIL (eq_ind_r valid_argv VARGV EARGV) VENVP EARGV HT HP1).
  Qed.
End Main.
End WithCeiling0.
