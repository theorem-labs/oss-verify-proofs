(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/UbsanImpl.v: module paths and target names for simdjson/fuzz_utf8's ubsan binary; as in that file, ported to LPS 727298f3: the composition also takes the run's launch class, built from the process input, the mmap base and the entry draw (run_launch_of), and proves its launch_ok fact for the driver's stack premise. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import StartupM.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg StdioFiles PStartU RDriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Image.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import PState Monad Stdio Driver ProgP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import InitMem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition pexit_stmt {rc : runConstT} : Prop :=
  forall (code : Z) (s : PState) (ms : machine_state) (Q : Empty_set -> PState -> machine_state -> Prop),
    pat_exitU code s ms -> implM usegs (ProgP.client_exit ;;; Driver.exit_model ProgP.io code) s Q ms.

(* [comment removed for export] *)
Section Compose.
  Hypothesis EXIT : forall rc : runConstT, @pexit_stmt rc.
  (* [comment removed for export] *)
  Hypothesis MAIN : forall (rc : runConstT) (rl : runLaunchT), @pmain_stmt rc rl.

  (* [comment removed for export] *)
  Lemma pmain_exit_from_pat_main : forall (rc : runConstT) (rl : runLaunchT) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) ms
      (Q : Empty_set -> PState -> machine_state -> Prop),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    pat_mainU sp0 argv envp uid hw draw CAN ms ->
    implM usegs (ProgP.main_exit UREAD_STAGE (argv_Z argv)) (ps_init (reservedZ usegs) ATOP) Q ms.
  Proof.
    intros rc rl sp0 argv envp uid hw draw ms Q VSP VARGV VENVP HSEC AM.
    unfold ProgP.main_exit.
    eapply (Monad.implM_bind usegs).
    - exact (MAIN rc rl sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM).
    - intros code s' ms'' AE. cbn in AE. exact (EXIT rc code s' ms'' Q AE).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_impl_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
      valid_input_either inp ->
      impl usegs (at_node usegs) (ProgP.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs u_init_pc u_phdrs en inp).
  Proof.
    intros [sp0 brk mb draw] inp VE VI.
    rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.   (* [comment removed for export] *)
    destruct VE as (VSP & _ & _ & VFIT & LOK).
    pose proof (valid_input_either_launch inp VI) as VLAUNCH.
    destruct VI as (VARGV & VENVP & _).
    unfold ms0. cbn [en_sp en_draw en_mmap_base en_brk].
    unfold ProgP.prog, ProgP.prog_itree.
    (* [comment removed for export] *)
    set (rc := run_consts_of (mkEntry sp0 brk mb draw) (pcanary draw) VSP).
    change (entry_atop (mkEntry sp0 brk mb draw)) with (@ATOP rc).
    set (s0 := PState.ps_init (Image.reservedZ usegs) (@ATOP rc)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold ProgP.prog_with, ProgP.startup.
    change (implM usegs
              (mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))
                     (fun _ => ProgP.main_exit UREAD_STAGE (argv_Z (in_argv inp))))
              s0 (fun _ _ _ => True) (init_ms usegs u_init_pc u_phdrs sp0 mb draw inp)).
    set (rl := run_launch_of inp sp0 mb draw).
    eapply (startup_implM_of usegs s0 _ _
              (@pat_mainU rl sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw (pcanary draw))).
    - eapply pstartup_spec; eassumption.
    - intros ms' AM.
      assert (VD : @dvalid_sp rc rl sp0 (in_argv inp) (in_envp inp)).
      { split; [exact VSP|]. split; [reflexivity|]. split; [exact VFIT|].
        subst rl. eapply run_launch_ok; eassumption. }
      apply (pmain_exit_from_pat_main rc rl sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw ms' _ VD VARGV VENVP eq_refl AM).
  Qed.
End Compose.
