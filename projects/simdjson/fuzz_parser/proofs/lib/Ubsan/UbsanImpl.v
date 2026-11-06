(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import StartupM.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg StdioFiles PStartU RDriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import PState Monad Stdio Driver ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import InitMem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
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
  Hypothesis MAIN : forall rc : runConstT, @pmain_stmt rc.

  (* [comment removed for export] *)
  Lemma pmain_exit_from_pat_main : forall (rc : runConstT) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) ms
      (Q : Empty_set -> PState -> machine_state -> Prop),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    pat_mainU sp0 argv envp uid hw draw CAN ms ->
    implM usegs (ProgP.main_exit UREAD_STAGE (argv_Z argv)) (ps_init (reservedZ usegs) ATOP) Q ms.
  Proof.
    intros rc sp0 argv envp uid hw draw ms Q VSP VARGV VENVP HSEC AM.
    unfold ProgP.main_exit.
    eapply (Monad.implM_bind usegs).
    - exact (MAIN rc sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM).
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
    destruct VE as (VSP & _ & _ & VFIT). destruct VI as (VARGV & VENVP & _).
    destruct inp as [argv envp fs sin uid gid grps net nof sigm hw abt vasz urnd tmp].   (* [comment removed for export] *)
    cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap in_fs en_brk] in *.
    unfold ms0. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap].
    unfold ProgP.prog, ProgP.prog_itree. cbn [in_argv].
    (* [comment removed for export] *)
    set (rc := run_consts_of (mkEntry sp0 brk mb draw) (pcanary draw) VSP).
    change (entry_atop (mkEntry sp0 brk mb draw)) with (@ATOP rc).
    set (s0 := PState.ps_init (Image.reservedZ usegs) (@ATOP rc)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold ProgP.prog_with, ProgP.startup.
    change (implM usegs
              (mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))
                     (fun _ => ProgP.main_exit UREAD_STAGE (argv_Z argv)))
              s0 (fun _ _ _ => True) (init_ms usegs u_init_pc u_phdrs sp0 argv envp uid hw draw)).
    eapply (startup_implM_of usegs s0 _ _ (pat_mainU sp0 argv envp uid hw draw (pcanary draw))).
    - exact (pstartup_spec sp0 argv envp uid hw draw VSP VARGV VENVP).
    - intros ms' AM. apply (pmain_exit_from_pat_main rc sp0 argv envp uid hw draw ms' _ ltac:(split; [exact VSP| split; [reflexivity| exact VFIT]]) VARGV VENVP eq_refl AM).
  Qed.
End Compose.
