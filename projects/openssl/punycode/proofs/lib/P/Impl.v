(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the composition proof takes the new launch conjunct of valid_entry, derives the stack-window floor and the head bound from it, and passes the whole ProcInput and mmap base to at_main, startup_spec and the main statement). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import InitMem Startup Exit F_stdio_exit Driver_iface.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Exit_walk.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib Require Import TopLevel.
From OSSVerify.openssl.punycode.images Require Import Plain.
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
  at_exit ps_so code s ms -> implM psegs (Driver.exit_model io code) s Q ms.
Proof.
  intros s Q code ms H. unfold io.
  exact (exit_from_at_exit ps_so set_so_ps (stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get) s Q code ms H).
Qed.

Section Compose.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MAIN : forall (CE__ : Ceiling) (RN__ : RunRnd), @rmain_stmt CE__ RN__.

  (* [comment removed for export] *)
  Theorem impl_P_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp ->
      valid_input_w inp ->
      impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
           (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 psegs Plain.M.init_pc Plain.M.phdrs en inp).
  Proof.
    intros [sp0 brk mbase draw] inp VE VI.
    rewrite (valid_entry_sv48 _ _ _ (valid_input_w_va_size _ VI)) in VE.
    destruct VE as (VSP & _ & _ & FITS & LAU).
    pose proof (valid_input_w_launch _ VI) as VLN.
    destruct VI as (VARGV & VENVP & _). cbn [en_sp en_brk en_draw en_mmap_base] in *.
    (* The window floor under the launch conjunct ([StoreOk.stack_window_lo_valid]). *)
    assert (WLOK : (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp0 - STK_DEPTH)%Z).
    { pose proof (stack_window_lo_valid inp sp0 brk mbase draw VLN LAU) as W.
      unfold stack_window_reach, stack_max_size, STK_DEPTH in *. lia. }
    pose proof (launch_hsp Sv48 inp mbase sp0 brk draw LAU) as HSP.
    (* [comment removed for export] *)
    set (RN0 := mkRunRnd draw (in_hwcap inp)).
    (* [comment removed for export] *)
    set (CE0 := ceiling_of_sp (bv_unsigned sp0)).
    assert (CEIL : @ceil_ok CE0 sp0).
    { unfold ceil_ok. subst CE0. destruct VSP as (SPL & SPH & SP16). unfold sp_window_lo, sp_window_hi in *.
      rewrite (ceiling_of_sp_eq (bv_unsigned sp0)) by lia. lia. }
    unfold ms0. cbn [en_sp en_draw en_mmap_base]. change draw with (@run_draw RN0) in LAU, WLOK, HSP |- *.
    unfold prog.
    set (s0 := ps_init (reservedZ psegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_with. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
      + (* the Section drops any hypothesis its proof does not use, so let Rocq place them *)
        (* [impl_msys_of_enode]'s conclusion carries [epost (fun p ms' => Q (fst p) ms' /\
           snd p = s)], so a bare [eapply] must solve [?Q (fst p) ms' == at_main sp0 inp
           mbase ms'].  [fst p] is an APPLICATION, not a bound variable, so that is not a
           Miller pattern and the unifier reports the two [impl] terms as unequal even
           though [?Q := fun _ ms' => at_main sp0 inp mbase ms'] solves it.  Give [Q]
           explicitly; nothing else about the step changes. *)
        eapply (impl_msys_of_enode _ _ _ (fun _ ms' => at_main sp0 inp mbase ms') s0).
        (* RULE 25j: `startup_spec` (P/Startup.v:212-214) no longer binds `RN__`, so the
           named argument has nothing to bind to ("Not enough non implicit arguments to
           accept the argument bound to RN__").  The instance
           is determined by the goal, which `change draw with (@run_draw RN0)` at :67 already
           put in `RN0`'s vocabulary. *)
        unshelve eapply startup_spec; first [eassumption | reflexivity].
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM psegs
                (Monad.mbind (main_model io raw_malloc raw_free pstage alloc_init run alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind psegs).
      + exact (MAIN CE0 RN0 sp0 inp mbase ms' VSP CEIL VARGV VENVP FITS HSP AM).
      + intros code s' ms'' AE. cbn in AE. apply exit_impl. exact AE.
  Qed.
End Compose.
