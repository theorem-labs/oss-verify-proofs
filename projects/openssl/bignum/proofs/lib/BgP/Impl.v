(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput and the init stack window). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Monad Stdio Driver Prog LibProg ProgG.
(* BgP|BgU/Impl.v:47 calls [stack_window_lo_valid], which P/InitMem.v now defines.
   [Require Import] in BgP/Startup.v LOADS P/InitMem for this file but does not IMPORT its
   names here, so the call still read "The variable stack_window_lo_valid was not found in the
   current environment" (BgP/Impl.v:47).  The sibling
   openssl/bndiv P/Impl.v Requires InitMem directly, in this position. *)
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import InitMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Import Startup Exit Exit_defs Driver_iface.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel.
From OSSVerify.openssl.bignum.images Require Import Plain.
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

Section Compose.
  Context {LM : LibModel}.
  Hypothesis EXITW : forall (CE__ : Ceiling) (RN__ : RunRnd), @exit_from_at_exit_stmt CE__ RN__.

  Hypothesis MAIN : forall (CE__ : Ceiling) (RN__ : RunRnd), @rmain_stmt CE__ RN__ LM.

  Theorem impl_P_from_main : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage bgpsegs Plain.M.init_pc Plain.M.phdrs) en inp ->
      valid_input_either inp ->
      impl bgpsegs (at_node bgpsegs) (@progG (ceiling_of_sp (bv_unsigned (en_sp en))) LM bgpsegs bgpstage (in_argv inp))
           (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 bgpsegs Plain.M.init_pc Plain.M.phdrs en inp).
  Proof.
    intros [sp0 brk mbase draw] inp VE VI.
    rewrite (valid_entry_sv48 _ _ _ (vie_va_size _ VI)) in VE.
    destruct VE as (VSP & _ & _ & FITS & LAU).
    pose proof (vie_launch _ VI) as VLN.
    destruct VI as (VARGV & VENVP & _). cbn [en_sp en_brk en_draw en_mmap_base] in *.
    (* The window floor under the launch conjunct ([StoreOk.stack_window_lo_valid]). *)
    assert (WLOK : (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp0 - STK_DEPTH)%Z).
    { pose proof (stack_window_lo_valid inp sp0 brk mbase draw VLN LAU) as W.
      (* [stack_window_reach] does not exist at #38 -- the round's own message offers
         [stack_window_lo] -- and nothing here needs it: the bndiv twin (P/Impl.v:54)
         unfolds exactly [stack_max_size, STK_DEPTH] and gets past this line. *)
      unfold stack_max_size, STK_DEPTH in *. lia. }
    pose proof (launch_hsp Sv48 inp mbase sp0 brk draw LAU) as HSP.

    set (RN0 := mkRunRnd draw (in_hwcap inp)).

    set (CE0 := ceiling_of_sp (bv_unsigned sp0)).
    assert (CEIL : @ceil_ok CE0 sp0).
    { unfold ceil_ok. subst CE0. destruct VSP as (SPL & SPH & SP16). unfold sp_window_lo, sp_window_hi in *.
      rewrite (ceiling_of_sp_eq (bv_unsigned sp0)) by lia. lia. }
    unfold ms0. cbn [en_sp en_draw en_mmap_base]. change draw with (@run_draw RN0) in LAU, WLOK, HSP |- *.
    unfold progG.
    set (s0 := ps_init (reservedZ bgpsegs)).
    eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog_withG. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
    - unfold startup, Monad.mbind.
      eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => at_main sp0 inp mbase ms' /\ snd p = s0)).
      + (* the Section drops any hypothesis its proof does not use, so let Rocq place them *)
        (* [Q] is an EXPLICIT binder of [impl_msys_of_enode] and occurs in the conclusion
           only as [?Q (fst p)], which is not a Miller pattern, so a bare [eapply] cannot
           invent it: give it BY POSITION, fourth after segs, n and pl, as ct, pem,
           punycode, the simdjson harnesses and the bndiv twin all do. *)
        eapply (impl_msys_of_enode _ _ _ (fun (_ : Z) ms' => at_main sp0 inp mbase ms')).
        (* [RN__] is the FIFTH binder of [startup_spec]: BgP/Startup.v's Section Proof
           binds [sp0 inp mbase brk0] then [Context {RN__ : RunRnd}], and the proof reaches
           [brk0] through [HSP]/[WLE]/[WLO_hi], which apply [VLAU] (:168).  Rocq fills the
           slots before a named argument from the positional ones, so four are supplied
           here; with none, it reports "Not enough non implicit arguments to accept the
           argument bound to RN__", which is what the bndiv twin measured. *)
        unshelve eapply (startup_spec sp0 inp mbase brk (RN__ := RN0)); first [eassumption | reflexivity].
      + intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
    - intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
      change (implM bgpsegs
                (Monad.mbind (main_model io raw_malloc raw_free bgpstage alloc_init runG alloc_count (argv_Z (in_argv inp)))
                             (fun code => exit_model io exit_hook code))
                s0 (fun _ _ _ => True) ms').
      eapply (implM_bind bgpsegs).
      + exact (MAIN CE0 RN0 sp0 inp mbase ms' VSP CEIL VARGV VENVP FITS HSP AM).
      + intros code s' ms'' AE. cbn in AE. exact (EXITW CE0 RN0 s' _ code ms'' AE).
  Qed.
End Compose.

