(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Mem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Startup Exit F_stdio_exit Driver_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
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

Lemma exit_impl : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
  at_exit ps_so code s ms -> implM psegs (Driver.exit_model io code) s Q ms.
Proof.
  intros s Q code ms H. unfold io.
  exact (exit_from_at_exit ps_so set_so_ps (stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get) s Q code ms H).
Qed.

Section Compose.
  Hypothesis MAIN : forall (CE__ : Ceiling) (RN__ : RunRnd), @rmain_stmt CE__ RN__.

  Theorem impl_P_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs) en inp ->
      valid_input inp ->
      impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
           (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs en inp).
  Proof.
    intros [sp0 brk mbase draw] inp VE VI.
    (* 727298f3's entry carries the launch conjunct (LOK) beside entry_stack_fits, and the
       start-up reads the launch (VLAUNCH, from valid_input) *)
    pose proof (valid_input_launch inp VI) as VLAUNCH.
    rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ VI)) in VE.
    destruct VE as (VSP & _ & _ & FITS & LOK). destruct VI as (VARGV & VENVP & _).
    cbn [en_sp en_brk en_draw en_mmap_base] in *.
    set (RN0 := run_rnd_of inp sp0 mbase draw).
    set (CE0 := ceiling_of_sp (bv_unsigned sp0)).
    assert (CEIL : @ceil_ok CE0 sp0).
    { unfold ceil_ok. subst CE0. destruct VSP as (SPL & SPH & SP16). unfold sp_window_lo, sp_window_hi in *.
      rewrite (ceiling_of_sp_eq (bv_unsigned sp0)) by lia. lia. }
    unfold ms0. cbn [en_sp en_draw en_mmap_base].
    unfold prog.
    set (s0 := ps_init (reservedZ psegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_with. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => @at_main sp0 (in_argv inp) (in_envp inp) (in_uid inp) RN0 ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => @at_main sp0 (in_argv inp) (in_envp inp) (in_uid inp) RN0 ms' /\ snd p = s0)).
      + exact (impl_msys_of_enode psegs _ _ _ _ _ (startup_spec sp0 brk mbase inp draw VSP VARGV VLAUNCH LOK)).
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM psegs
                (Monad.mbind (main_model io raw_malloc raw_free pstage alloc_init run alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind psegs).
      + (* port727 (geometry (ii)): rmain_stmt takes the launch's geometry; P/Startup's run_launch_ok gives it *)
        exact (MAIN CE0 RN0 sp0 (in_argv inp) (in_envp inp) (in_uid inp) ms' VSP CEIL VARGV VENVP FITS
                 (run_launch_ok sp0 brk mbase inp draw LOK) AM).
      + intros code s' ms'' AE. cbn in AE. apply exit_impl. exact AE.
  Qed.
End Compose.
