(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the write-certified stack window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import InitMem.
From OSSVerify.Proofs.openssl.pem.lib.U Require Import Startup Exit F_stdio_exit Driver_iface.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import StoreOk.
From OSSVerify.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib Require Import TopLevel.
From OSSVerify.openssl.pem.images Require Import Ubsan.
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
    set (s0 := ps_init (reservedZ usegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_with. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
      + (* the Section drops any hypothesis its proof does not use, so let Rocq place them *)
        (* See P/Impl.v:78-91: print the GOAL, not the unification pair, because both
           sides of that pair are unfolded [fix impl] bodies and the printer drops the
           section-generalised [node]/[segs]/[at_node] arguments that are the only
           remaining candidates. *)
        (* [Q] supplied by hand: the goal's post does not mention [fst p], so
           [?Q (fst p) ms' =?= at_main sp0 inp mbase ms'] is outside the Miller pattern
           fragment and [eapply] cannot invent the constant function.  See
           P/Impl.v:91-106 for the goal the probe printed. *)
        eapply (impl_msys_of_enode usegs NSetTid Decode.dec_set_tid
                         (fun _ ms' => at_main sp0 inp mbase ms') s0).
        (* [RN__] is the FIFTH EXPLICIT argument of [startup_spec], not an implicit one -
           section discharge turns [Context {RN__ : RunRnd}] (U/Startup.v:157) into an
           explicit binder, so [(RN__ := RN0)] cannot place it.  Passed positionally.
           Type printed by a probe build; see P/Impl.v:110-131. *)
        (* [RN__] IS implicit after all, and the two errors together prove it: the named
           form [(RN__ := RN0)] gave "Not enough non implicit arguments", and the bare
           positional form then put RN0 where [valid_sp sp0] was expected - so Coq skips
           it when inserting positionally.  The probe's telescope is still the authority;
           [@] is what makes an application follow it exactly, implicits included. *)
        unshelve eapply (@startup_spec sp0 inp mbase brk RN0);
          first [eassumption | reflexivity].
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM usegs
                (Monad.mbind (main_model io raw_malloc raw_free ustage alloc_init run alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind usegs).
      + exact (MAIN CE0 RN0 sp0 inp mbase ms' VSP CEIL VARGV VENVP FITS HSP AM).
      + intros code s' ms'' AE. cbn in AE. apply exit_impl. exact AE.
  Qed.
End Compose.
