(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RDriver_iface RF_main_A RF_main_B1 RF_main_B4 RF_main_C RF_main_T.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rmain_pre_stmt {HGW : HasGuard} {HCEIL : HasCeiling} : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (ms : machine_state),
    valid_sp sp0 -> alloc_ceiling = LO sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    guard_word = entry_guard rnd -> secret_word = entry_secret rnd ->
    rat_main sp0 argv envp uid hw rnd ms ->
    implM rsegs
      (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free RSV (argv_Z argv))
      (ps_init (reservedZ rsegs) alloc_ceiling)
      (fun ap s' ms' => exists (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word),
                          0 < TID < 4194304 /\ rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s' ms') ms.

Section Main.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis AUXINIT : rauxv_init_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  #[using="MALLOC FREE FPR EXK FWR TOW"] Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z) ms
      (Q : at_parser (ptr:=bptr) -> PState -> machine_state -> Prop),
    valid_sp sp0 -> alloc_ceiling = LO sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 ->
    P1 sp0 argv envp uid hw rnd TID ms ->
    (forall S4 S5 S6 S7 S8 S9 S10 S11 ap s1 ms1, rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s1 ms1 -> Q ap s1 ms1) ->
    implM rsegs (ra <- read_all (io_S ps_so set_so_ps) raw_malloc raw_free RSV (map bv_unsigned arg1) ;;
                 match ra with RdExit => exit_k (io_S ps_so set_so_ps) 2 | RdDone buf content => main_rest buf content end)
          (ps_init (reservedZ rsegs) alloc_ceiling) Q ms.
  Proof.
    intros sp0 argv envp uid hw rnd arg0 arg1 TID ms Q VSP CEIL VARGV VENVP ESF EARGV HT HP1 HQ.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & fc & mm & mpad
                     & -> & FR & BA & HP & CJ & ERR & FRM).
    eapply implM_bind.
    { eapply (main_read_all sp0 argv envp uid hw rnd arg0 arg1 TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV VENVP ESF EARGV HT MALLOC FREE FPR FWR TOW);
        [exact FR| exact BA| exact HP| exact CJ| exact ERR| exact FRM]. }
    cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - eapply implM_evt; [apply evt_done; exact PB| intros msx Hx; exact (EXK _ 2 _ Q msx Hx)].
    - eapply (phaseC sp0 argv envp uid hw rnd TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL HT FREE EXK FWR TOW); [exact PB|].
      intros DATA A cap cw L cfg sc s1 ms1 HC0 R0. rewrite HC0.
      eapply (phaseT sp0 argv envp uid hw rnd arg0 arg1 TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV EARGV HT MALLOC FREE EXK); [first [exact R0 | eapply RUN0_atx; exact R0] ..|].
      intros ap s2 ms2 RP _. exact (HQ _ _ _ _ _ _ _ _ ap s2 ms2 RP).
  Qed.

  #[using="MALLOC FREE AUXINIT FPR EXK FWR TOW"] Theorem rmain_pre_proof : rmain_pre_stmt.
  Proof.
    intros sp0 argv envp uid hw rnd ms VSP CEIL VARGV VENVP ESF GW GS AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2]; [| exact (main_usage sp0 argv envp uid hw rnd VSP CEIL VARGV VENVP ESF GW GS AUXINIT FPR EXK ms _ AM NE2)].
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    rewrite (drv_pre_eq argv arg0 arg1 EARGV).
    eapply implM_evt.
    { eapply (main_to_P1 sp0 argv envp uid hw rnd VSP CEIL VARGV VENVP GW GS AUXINIT arg0 arg1); [exact EARGV| exact AM|].
      intros TID ms' HT HP1. apply evt_done.
      eapply (main_from_P1 sp0 argv envp uid hw rnd arg0 arg1 TID ms'
                (fun ap s' ms' => exists (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word), 0 < TID < 4194304 /\ rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s' ms')
                VSP CEIL VARGV VENVP ESF EARGV HT HP1).
      intros S4 S5 S6 S7 S8 S9 S10 S11 ap s1 ms1 RP. cbv beta. exists TID, S4, S5, S6, S7, S8, S9, S10, S11. split; [exact HT| exact RP]. }
    cbv beta. intros ms' H. exact H.
  Qed.
End Main.
