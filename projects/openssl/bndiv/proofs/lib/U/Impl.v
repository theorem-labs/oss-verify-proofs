(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the compose proof takes the stack window floor and launch_hsp from the entry's launch conjunct, calls startup_spec and the main proof over the launch input ProcInput and the mmap base, and imports P.InitMem). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Monad Stdio Driver Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import InitMem.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Startup Exit Exit_defs Driver_iface.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel.
From OSSVerify.openssl.bndiv.images Require Import Ubsan.
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

(* [comment removed for export] *)
Section Compose.
  Context {LM : LibModel}.
  Hypothesis EXITW : forall (CE__ : Ceiling) (RN__ : RunRnd), @exit_from_at_exit_stmt CE__ RN__.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MAIN : forall (CE__ : Ceiling) (RN__ : RunRnd), @rmain_stmt CE__ RN__ LM.

  (* [comment removed for export] *)
  Theorem impl_U_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
      valid_input_either inp ->
      impl usegs (at_node usegs) (@progG (ceiling_of_sp (bv_unsigned (en_sp en))) LM usegs ustage (in_argv inp))
           (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
  Proof.
    intros [sp0 brk mbase draw] inp VE VI.
    rewrite (valid_entry_sv48 _ _ _ (vie_va_size _ VI)) in VE.
    destruct VE as (VSP & _ & _ & FITS & LAU).
    pose proof (vie_launch _ VI) as VLN.
    destruct VI as (VARGV & VENVP & _). cbn [en_sp en_brk en_draw en_mmap_base] in *.
    (* The window floor under the launch conjunct ([InitMem.stack_window_lo_valid]). *)
    assert (WLOK : (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp0 - STK_DEPTH)%Z).
    { pose proof (stack_window_lo_valid inp sp0 brk mbase draw VLN LAU) as W.
      unfold stack_max_size, STK_DEPTH in *. lia. }
    pose proof (launch_hsp Sv48 inp mbase sp0 brk draw LAU) as HSP.
    (* [comment removed for export] *)
    set (RN0 := mkRunRnd draw (in_hwcap inp)).
    (* [comment removed for export] *)
    set (CE0 := ceiling_of_sp (bv_unsigned sp0)).
    assert (CEIL : @ceil_ok CE0 sp0).
    { unfold ceil_ok. subst CE0. destruct VSP as (SPL & SPH & SP16). unfold sp_window_lo, sp_window_hi in *.
      rewrite (ceiling_of_sp_eq (bv_unsigned sp0)) by lia. lia. }
    unfold ms0. cbn [en_sp en_draw en_mmap_base]. change draw with (@run_draw RN0) in LAU, WLOK, HSP |- *.
    unfold progG.
    set (s0 := ps_init (reservedZ usegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_withG. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
      + (* the Section drops any hypothesis its proof does not use, so let Rocq place them *)
        (* [Q] occurs in the lemma's conclusion only as [?Q (fst p)], which is not a
           Miller pattern, so unification cannot invent it: give it by name. *)
        (* [Q] is an EXPLICIT binder of [impl_msys_of_enode] (P|U/Exit.v: forall segs {St A}
           (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms),
           so [(Q := ...)] is rejected -- Rocq's named-argument syntax binds IMPLICITS only,
           which is exactly what "Wrong argument name Q (possible names: St A)" reports: St and
           A are the only implicits.  The diagnosis in the note above is right and the remedy
           was not: give [Q] BY POSITION, fourth after segs, n and pl.  That is what every
           other call site of this lemma in the repository does -- ct, pem, punycode and eight
           simdjson harnesses all write [impl_msys_of_enode <segs> _ _ _ _ _ (startup_spec ...)],
           and this unit was the only [(Q := ...)] anywhere.  The declaration is character-
           identical in 26 units, so nothing about it moved at #38. *)
        eapply (impl_msys_of_enode _ _ _ (fun (_ : Z) ms' => at_main sp0 inp mbase ms')).
        (* [RN__] needs its SLOT REACHED, which is the same lesson as [Q] above seen from the
           other side.  Rocq's named-argument syntax inserts [(x := v)] at x's position and
           fills the slots BEFORE it from the positional arguments given, so with none given
           it reports "Not enough non implicit arguments to accept the argument bound to
           RN__".  [startup_spec] lives in U/Startup.v's [Section Proof], whose binders are
           [sp0 inp mbase brk0] then [Context {RN__ : RunRnd}], and its proof reaches [brk0]:
           it poses [HSP] and [top_le], both of which apply [VLAU], the one hypothesis that
           mentions [brk0].  So the section discharges four binders ahead of [RN__] and they
           are supplied here by name from this proof's own context.  This form is right
           whether or not [RN__] survives discharge as an implicit: four positional arguments
           reach its slot either way. *)
        unshelve eapply (startup_spec sp0 inp mbase brk (RN__ := RN0)); first [eassumption | reflexivity].
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM usegs
                (Monad.mbind (main_model io raw_malloc raw_free ustage alloc_init runG alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io exit_hook code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind usegs).
      + exact (MAIN CE0 RN0 sp0 inp mbase ms' VSP CEIL VARGV VENVP FITS HSP AM).
      + intros code s' ms'' AE. cbn in AE. exact (EXITW CE0 RN0 s' _ code ms'' AE).
  Qed.
End Compose.

(* [comment removed for export] *)
