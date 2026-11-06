(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C RF_mainA_T.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section Main.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FPR : @fprintf_diag_stmt HC ASt.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Hypothesis FWR : @fwrite_diagA_stmt HC ASt.
  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.
  Hypothesis BSR : forall s LB m b, RHEAP_A FI AI s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b).

  #[using="AMS PZ_agree VSP CEIL VARGV ESF AC FPR EXK FWR MCI RDF RDB BSR"] Lemma main_from_P1 : forall (arg0 arg1 : list byte) (TID : Z) msr g
      (Q : at_parser (ptr:=unit) -> ASt -> machine_state -> gst -> Prop),
    argv = [arg0; arg1] -> 0 < TID < 2^31 ->
    P1_A FI AI PZ sp0 argv envp uid hw rnd TID stdout_init msr g ->
    (forall S4 S5 S6 S7 S8 S9 S10 S11 ap so1 ms1 g1, rat_parserA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 ap so1 ms1 g1 -> Q ap so1 ms1 g1) ->
    djM (ra <- read_all ioA amalloc0 afree0 RSVA (map bv_unsigned arg1) ;;
         match ra with RdExit => exit_k ioA 2 | RdDone buf content => main_restA buf content end)
        stdout_init Q msr g.
  Proof.
    intros arg0 arg1 TID msr g Q EARGV HT HP1 HQ.
    destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & mm & mpad & s & st & e
                     & -> & FR & BA & HP & RF & Eg & CJ & ERR & FRM).
    eapply djM_bind.
    { eapply (main_read_all FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd arg0 arg1 TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV ESF EARGV HT AC FPR MCI RDF RDB BSR);
        [exact FR| exact BA| exists s, st; split; [exact HP| split; [exact RF| destruct Eg as (E1 & E2 & E3); split; [exact E1| split; [exact E2| rewrite E3; unfold lb_bytes; cbn; lia]]]]| exact CJ| exact ERR| exact FRM]. }
    cbv beta. intros ra so' ms' g' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - eapply djM_mono; [eapply (djM_of_implM _ _ (fun (_ : at_parser) (_ : ASt) (_ : machine_state) => False)); [exact (EXK TID HT _ 2 _ _ ms' PB)| fdt] |].
      cbv beta. intros r so2 ms2 g2 [F0 _]. destruct F0.
    - eapply (phaseC FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL ESF HT AC EXK FWR); [exact PB|].
      intros DATA A cap cw L cfg sc so1 ms1 g1 HC0 R0. rewrite HC0.
      eapply (phaseT FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd arg0 arg1 TID mpad s4 s5 s6 s7 s8 s9 s10 s11 VSP CEIL VARGV ESF EARGV HT AC MCI BSR); [exact R0|].
      intros ap so2 ms2 g2 RP. exact (HQ _ _ _ _ _ _ _ _ ap so2 ms2 g2 RP).
  Qed.

  Definition QPARSER (ap : at_parser (ptr:=unit)) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word),
      0 < TID < 2^31 /\ (valid_sp sp0 /\ alloc_ceiling = LO sp0 /\ entry_stack_fits sp0 argv envp)
      /\ rat_parserA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 ap so ms g.

  #[using="AMS PZ_agree VSP CEIL VARGV ESF AC FPR EXK FWR MCI RDF RDB BSR"] Theorem main_djM : forall msr g,
    rat_mainA FI AI PZ sp0 argv envp uid hw rnd msr g ->
    djM (drv_preA RSVA (argv_Z argv)) stdout_init QPARSER msr g.
  Proof.
    intros msr g AM.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2]; [| exact (main_usage FI AI PZ PZ_agree sp0 argv envp uid hw rnd VSP CEIL VARGV ESF FPR EXK msr g _ AM NE2)].
    destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
    rewrite (drv_preA_eq argv arg0 arg1 EARGV).
    eapply djM_evt.
    { eapply (main_to_P1 FI AI PZ PZ_agree sp0 argv envp uid hw rnd VSP CEIL ESF arg0 arg1); [exact EARGV| exact AM|].
      intros TID ms' HT HP1. apply evt_done.
      eapply (main_from_P1 arg0 arg1 TID ms' g QPARSER EARGV HT HP1).
      intros S4 S5 S6 S7 S8 S9 S10 S11 ap so1 ms1 g1 RP. exists TID, S4, S5, S6, S7, S8, S9, S10, S11. split; [exact HT|]. split; [split; [exact VSP| split; [exact CEIL| exact ESF]]| exact RP]. }
    cbv beta. intros ms' H. exact H.
  Qed.
End Main.
