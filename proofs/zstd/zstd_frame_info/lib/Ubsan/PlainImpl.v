(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StartupM.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg StdioFiles Startup_A Startup Exit RDriver_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Image.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section Compose.
  Hypothesis STDIO_EXIT : stdio_exit_spec_stmt ps_so set_so_ps.
  (* [comment removed for export] *)
  Hypothesis MAIN : forall rc : runConstT, @pmain_stmt rc.

  (* [comment removed for export] *)
  #[using="STDIO_EXIT"] Lemma pexit_from_pat_exit : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
    pat_exit code s ms -> implM usegs (Driver.exit_model Prog.io code) s Q ms.
  Proof.
    intros s Q code ms H.
    destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                   s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                   td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
    destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & LCH & DSO & [reg AX] & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO & SP47).
    unfold Prog.io.
    eapply (Exit.exit_spec ps_so set_so_ps STDIO_EXIT reg s Q);
      [exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AX | exact OFL | exact SIN | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO | exact SP47].
  Qed.

  (* [comment removed for export] *)
  #[using="STDIO_EXIT MAIN"] Lemma pmain_exit_from_pat_main : forall (rc : runConstT) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) ms
      (Q : Empty_set -> PState -> machine_state -> Prop),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    pat_main sp0 argv envp uid hw draw CAN ms ->
    implM usegs
      (mbind (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
             (fun code => exit_model Prog.io code))
      (ps_init (reservedZ usegs) ATOP) Q ms.
  Proof.
    intros rc sp0 argv envp uid hw draw ms Q VSP VARGV VENVP HSEC AM.
    eapply (Monad.implM_bind usegs).
    - exact (MAIN rc sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM).
    - intros code s' ms'' AE. cbn in AE. apply pexit_from_pat_exit. exact AE.
  Qed.

  (* [comment removed for export] *)
  #[using="STDIO_EXIT MAIN"] Theorem plain_impl_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
      valid_input_either inp ->
      impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs u_init_pc u_phdrs en inp).
  Proof.
    intros [sp0 brk mb draw] inp VE VI.
    rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.   (* [comment removed for export] *)
    destruct VE as (VSP & _ & _ & VFIT). destruct VI as (VARGV & VENVP & _).
    destruct inp as [argv envp fs sin uid gid grps net nof sigm hw abt vasz].
    cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap in_fs en_brk] in *.
    unfold ms0. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap].
    unfold Prog.prog, Prog.prog_itree. cbn [in_argv].
    (* [comment removed for export] *)
    set (rc := run_consts_of (mkEntry sp0 brk mb draw) (pcanary draw) VSP).
    change (entry_atop (mkEntry sp0 brk mb draw)) with (@ATOP rc).
    set (s0 := PState.ps_init (Image.reservedZ usegs) (@ATOP rc)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold Prog.prog_with, Prog.startup.
    change (implM usegs
              (mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))
                     (fun _ => mbind (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
                                     (fun code => exit_model Prog.io code)))
              s0 (fun _ _ _ => True) (init_ms usegs u_init_pc u_phdrs sp0 argv envp uid hw draw)).
    eapply (startup_implM_of usegs s0 _ _ (pat_main sp0 argv envp uid hw draw (pcanary draw))).
    - exact (pstartup_spec sp0 argv envp uid hw draw VSP VARGV VENVP).
    - intros ms' AM. apply (pmain_exit_from_pat_main rc sp0 argv envp uid hw draw ms' _ ltac:(split; [exact VSP| split; [reflexivity| exact VFIT]]) VARGV VENVP eq_refl AM).
  Qed.
End Compose.
