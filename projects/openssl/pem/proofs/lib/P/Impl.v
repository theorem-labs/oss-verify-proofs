(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up facts stated over the launch's ProcInput; the write-certified stack window; the launch premises). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import InitMem Startup Exit F_stdio_exit Driver_iface.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import StoreOk.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Exit_walk.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib Require Import TopLevel.
From OSSVerify.openssl.pem.images Require Import Plain.
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
        (* The build reports an "Unable to unify" here whose two sides are both UNFOLDED
           [fix impl] bodies, and they print structurally identical: same [evt psegs],
           same [at_node psegs], same [msys … s0].  An unfolded fix hides exactly what I
           need, because [ITree.impl] is section-generalised over [node], [segs] and
           [at_node] (Lib/ITree.v:38, :59, :62) and the printer elides those.
           Read first, so the round is not a guess: both files are in the PLAIN node world
           - P/Impl.v:11 and P/Exit_walk.v:11 both import Lib's [ITree Nodes] and NEITHER
           imports [ITreeCfg]/[NodesCfg] - so the node type is not the difference, and
           [impl_msys_of_enode] (P/Exit_walk.v:294) sits OUTSIDE both of that file's
           Sections (:85, :248), so section discharge is not the difference either.
           That leaves the instance arguments the printer drops, which is what this arm
           prints: the GOAL, rather than the unification pair. [fail 100] because the two
           enclosing combinators would otherwise eat a [fail 1] - measured in KStep. *)
        (* THE PROBE ANSWERED IT, AND THE CAUSE IS NONE OF THE THREE I HAD IN MIND.
           The probe build printed the goal:
             impl psegs (at_node psegs) (msys NSetTid Decode.dec_set_tid s0)
                  (epost (fun (p : Z * PState) ms' => at_main sp0 inp mbase ms' /\ p.2 = s0))
                  (init_ms psegs M.init_pc M.phdrs sp0 mbase run_draw inp)
           against the lemma's
             impl segs (at_node segs) (Monad.msys n pl s)
                  (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms
           Every argument unifies first order - segs, n, pl, s, ms - EXCEPT [Q], which
           has to solve [?Q (fst p) ms' =?= at_main sp0 inp mbase ms'].  The goal's post
           DOES NOT MENTION [fst p] at all, so this is outside the Miller pattern
           fragment and [eapply] will not invent the constant function.  It is a
           HIGHER-ORDER UNIFICATION, not a node world, not a section discharge, not an
           instance - and it was invisible in the original "Unable to unify" because
           both sides print the BODY of [impl] with the post already substituted in.
           Supplying [Q] by hand removes the guess; everything else stays inferred. *)
        eapply (impl_msys_of_enode psegs NSetTid Decode.dec_set_tid
                         (fun _ ms' => at_main sp0 inp mbase ms') s0).
        (* THE PROBE PRINTED THE TYPE AND IT ANSWERS THE QUESTION EXACTLY.
           The probe build printed:
             startup_spec : forall (sp0 : word) (inp : ProcInput) (mbase brk0 : word)
                                   (RN__ : RunRnd),
               valid_sp sp0 -> valid_argv (in_argv inp)
               -> entry_stack_fits sp0 (in_argv inp) (in_envp inp)
               -> entry_launch_ok_va Sv48 {| en_sp := sp0; en_brk := brk0;
                                             en_mmap_base := mbase; en_draw := run_draw |} inp
               -> stack_window_lo (in_kernel inp) mbase run_draw <= bv_unsigned sp0 - STK_DEPTH
               -> run_hw = in_hwcap inp
               -> impl psegs (at_node psegs) (enode NSetTid Decode.dec_set_tid) …
           [RN__] IS THE FIFTH EXPLICIT ARGUMENT, not an implicit one.  Section discharge
           turns [Context {RN__ : RunRnd}] (P/Startup.v:158) into an EXPLICIT binder, and
           the named-argument form [(RN__ := RN0)] is only for implicits - hence "Not
           enough non implicit arguments to accept the argument bound to RN__", which
           names the placement and never the list.  Passed positionally instead.
           Two further facts the type gives for free, neither of which the section head
           would have told me: the premises are SIX, not the seven Hypotheses declared,
           because discharge keeps only what the proof uses and [VENVP] dropped out; and
           the post is [epost (fun _ : Z => at_main sp0 inp mbase)], which is why the
           [Q] above had to be the constant function. *)
        (* [RN__] IS implicit after all, and the two errors together prove it: the named
           form [(RN__ := RN0)] gave "Not enough non implicit arguments", and the bare
           positional form then put RN0 where [valid_sp sp0] was expected - so Coq skips
           it when inserting positionally.  The probe's telescope is still the authority;
           [@] is what makes an application follow it exactly, implicits included. *)
        unshelve eapply (@startup_spec sp0 inp mbase brk RN0);
          first [eassumption | reflexivity].
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
