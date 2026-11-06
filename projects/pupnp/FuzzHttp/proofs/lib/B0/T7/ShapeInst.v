(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver Prog KNonNull.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim ShapeP0 DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import TSimS RealizeS A0Prog ShapeA0 TopA0 AssembleA0.
Import ListNotations.
Open Scope Z_scope.

Section ShapeInst.
  Variable H_MAIN_A0 : ProcInput -> ExecEntry -> machine_state -> Model -> Prop.
  Variable RS_A : Z.

  Hypothesis hmain_K : forall inp en ms mo, H_MAIN_A0 inp en ms mo -> hmain_model_facts inp mo /\ exists mo', meq mo mo' /\ minv mo' /\ m_halted mo' = None.

  #[using="Type"] Lemma T_A0main_meq : forall rs argv mo mo', meq mo mo' -> t_eq (T_A0main rs argv mo) (T_A0main rs argv mo').
  Proof.
    intros rs argv mo mo' HM. unfold T_A0main. apply tsh_fdtree_cong; [apply fdtree_drv_preA| exact HM|].
    intros [|[ap so]] m1 m2 [_ E]; cbn [KLEAF_A]; [apply t_eq_refl| rewrite E; apply t_eq_refl].
  Qed.

  #[using="hmain_K"] Theorem shape_of_hmain : SHAPE H_MAIN_A0 RS_A.
  Proof.
    intros CP inp spA brkA mbA dA en [ms mo] VI VA VB CEIL HM. unfold at_main in HM. cbn [cfg_ms cfg_model] in *.
    destruct (hmain_K inp en ms mo HM) as [[KF KS KH [t KT]] (mo' & MQ & KM & KH')].
    pose proof (valid_input_va_size _ VI) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in VA. cbn [imgP0] in VA.
    destruct VA as (VSPA & VBRKA & VMBA & ESFA).
    destruct P0_drv_nonnull as (PI & NMAX & HNMAX & PI_mo & PI_soupd & PI_fdupd & PI_perm & PI_weaken & MP & MPX & FP & FPX & PINIT).
    assert (SH : t_incl0 (AssembleP0.T_P0 (in_argv inp) (moP0 brkA mbA spA inp)) (T_A0main RS_A (in_argv inp) mo')
                 /\ t_incl0 (T_A0main RS_A (in_argv inp) mo') (AssembleP0.T_P0 (in_argv inp) (moP0 brkA mbA spA inp))).
    { apply (shape_incl0 (CP:=CP) RS_A PI NMAX HNMAX PI_mo PI_soupd PI_fdupd PI_perm PI_weaken
               (fun k X n s mo Hn H => MP k X n s mo Hn H) (fun k X n s mo Hn H => MPX k X n s mo Hn H) FP FPX 0%nat).
      unfold START, moP0. split; [apply m_tid_init_model|].
      split; [apply minv_init; destruct VSPA as (V1 & V2 & _); split; [exact V1| exact V2]|].
      split; [apply m_halted_init_model|].
      split; [intros t' Ht'; apply (PINIT CP spA brkA mbA inp t' VI VSPA VBRKA VMBA CEIL Ht')|].
      rewrite m_fds_init_model, m_fs_init_model. destruct MQ as [MQ1 MQ2].
      split; [rewrite <- MQ1; symmetry; exact KF|]. split; [rewrite <- MQ2; symmetry; exact KS|].
      split; [exact KM| exact KH']. }
    destruct SH as [S1 S2]. pose proof (T_A0main_meq RS_A (in_argv inp) mo mo' MQ) as TE.
    split.
    - eapply t_incl0_trans; [exact S1|]. apply t_incl0_of_incl. apply t_incl_of_eq. apply t_eq_sym. exact TE.
    - eapply t_incl0_trans; [| exact S2]. apply t_incl0_of_incl. apply t_incl_of_eq. exact TE.
  Qed.
End ShapeInst.
