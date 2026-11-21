(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import StartupM.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg StdioFiles Startup_A Startup Exit RDriver_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import InitMem RunConst.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Compose.
  Hypothesis STDIO_EXIT : stdio_exit_spec_stmt ps_so set_so_ps.
  Hypothesis MAIN : forall (rc : runConstT) (rl : runLaunchT), @pmain_stmt rc rl.

  Lemma pexit_from_pat_exit : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
    pat_exit code s ms -> implM psegs (Driver.exit_model Prog.io code) s Q ms.
  Proof.
    intros s Q code ms H.
    destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                   s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                   td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
    destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & DSO & LCH & ATX & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO & SP47).
    unfold Prog.io.
    eapply (Exit.exit_spec ps_so set_so_ps STDIO_EXIT s Q);
      [exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact ATX | exact OFL | exact SIN | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO | exact SP47].
  Qed.

  Lemma pmain_exit_from_pat_main : forall (rc : runConstT) (rl : runLaunchT) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) ms
      (Q : Empty_set -> PState -> machine_state -> Prop),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    pat_main sp0 argv envp uid hw draw CAN ms ->
    implM psegs
      (mbind (main_model Prog.io raw_malloc raw_free PREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
             (fun code => exit_model Prog.io code))
      (ps_init (reservedZ psegs) ATOP) Q ms.
  Proof.
    intros rc rl sp0 argv envp uid hw draw ms Q VSP VARGV VENVP HSEC AM.
    eapply (Monad.implM_bind psegs).
    - exact (MAIN rc rl sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM).
    - intros code s' ms'' AE. cbn in AE. apply pexit_from_pat_exit. exact AE.
  Qed.

  Theorem plain_impl_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
      valid_input_either inp ->
      impl psegs (at_node psegs) (Prog.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 psegs p_init_pc p_phdrs en inp).
  Proof.
    intros [sp0 brk mb draw] inp VE VI.
    rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.
    (* the entry's launch
       conjunct LOK and the input's valid_launch feed the start-up and the main statement's launch fact *)
    destruct VE as (VSP & _ & _ & VFIT & LOK).
    pose proof (valid_input_either_launch inp VI) as VLAUNCH.
    destruct VI as (VARGV & VENVP & _).
    unfold ms0. cbn [en_sp en_draw en_mmap_base en_brk].
    unfold Prog.prog, Prog.prog_itree.
    set (rc := run_consts_of (mkEntry sp0 brk mb draw) (pcanary draw) VSP).
    change (entry_atop (mkEntry sp0 brk mb draw)) with (@ATOP rc).
    set (s0 := PState.ps_init (Image.reservedZ psegs) (@ATOP rc)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold Prog.prog_with, Prog.startup.
    change (implM psegs
              (mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))
                     (fun _ => mbind (main_model Prog.io raw_malloc raw_free PREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z (in_argv inp)))
                                     (fun code => exit_model Prog.io code)))
              s0 (fun _ _ _ => True) (init_ms psegs p_init_pc p_phdrs sp0 mb draw inp)).
    (* the launch's constants (RunConst.run_launch_of) *)
    set (rl := run_launch_of inp sp0 mb draw).
    eapply (startup_implM_of psegs s0 _ _
              (@pat_main rl sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw (pcanary draw))).
    - eapply pstartup_spec; eassumption.
    - intros ms' AM.
      assert (VD : @dvalid_sp rc rl sp0 (in_argv inp) (in_envp inp)).
      { split; [exact VSP|]. split; [reflexivity|]. split; [exact VFIT|].
        subst rl. eapply run_launch_ok; eassumption. }
      apply (pmain_exit_from_pat_main rc rl sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw ms' _ VD VARGV VENVP eq_refl AM).
  Qed.
End Compose.
