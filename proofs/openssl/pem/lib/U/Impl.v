(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Startup Exit F_stdio_exit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import TopLevel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma ps_get_set : forall (s : PState) so, ps_so (set_so_ps so s) = so.
Proof. intros [? ? ? ?] so; reflexivity. Qed.
Lemma ps_set_set : forall (s : PState) so so', set_so_ps so' (set_so_ps so s) = set_so_ps so' s.
Proof. intros [? ? ? ?] so so'; reflexivity. Qed.
Lemma ps_set_get : forall (s : PState), set_so_ps (ps_so s) s = s.
Proof. intros [? ? ? ?]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma exit_impl : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
  at_exit ps_so code s ms -> implM usegs (Driver.exit_model io code) s Q ms.
Proof.
  intros s Q code ms H. unfold io.
  exact (exit_from_at_exit ps_so set_so_ps (stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get) s Q code ms H).
Qed.

Section Compose.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MAIN : forall (CE__ : Ceiling) (RN__ : RunRnd), @rmain_stmt CE__ RN__.

  (* [comment removed for export] *)
  Theorem impl_U_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
      valid_input_w inp ->
      impl usegs (at_node usegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) usegs ustage (in_argv inp))
           (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
  Proof.
    intros [sp0 brk mbase draw] inp VE VI.
    rewrite (valid_entry_sv48 _ _ _ (valid_input_w_va_size _ VI)) in VE.
    destruct VE as (VSP & _ & _ & FITS). destruct VI as (VARGV & VENVP & _). cbn [en_sp en_brk en_draw] in *.
    (* [comment removed for export] *)
    set (RN0 := mkRunRnd draw (in_hwcap inp)).
    (* [comment removed for export] *)
    set (CE0 := ceiling_of_sp (bv_unsigned sp0)).
    assert (CEIL : @ceil_ok CE0 sp0).
    { unfold ceil_ok. subst CE0. destruct VSP as (SPL & SPH & SP16). unfold sp_window_lo, sp_window_hi in *.
      rewrite (ceiling_of_sp_eq (bv_unsigned sp0)) by lia. lia. }
    unfold ms0. cbn [en_sp en_draw]. change draw with (@run_draw RN0). change (in_hwcap inp) with (@run_hw RN0).
    unfold prog.
    set (s0 := ps_init (reservedZ usegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_with. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => at_main sp0 (in_argv inp) (in_envp inp) (in_uid inp) ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => at_main sp0 (in_argv inp) (in_envp inp) (in_uid inp) ms' /\ snd p = s0)).
      + exact (impl_msys_of_enode usegs _ _ _ _ _ (startup_spec (RN__ := RN0) sp0 (in_argv inp) (in_envp inp) (in_uid inp) VSP VARGV VENVP FITS)).
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM usegs
                (Monad.mbind (main_model io raw_malloc raw_free ustage alloc_init run alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind usegs).
      + exact (MAIN CE0 RN0 sp0 (in_argv inp) (in_envp inp) (in_uid inp) ms' VSP CEIL VARGV VENVP FITS AM).
      + intros code s' ms'' AE. cbn in AE. apply exit_impl. exact AE.
  Qed.
End Compose.
