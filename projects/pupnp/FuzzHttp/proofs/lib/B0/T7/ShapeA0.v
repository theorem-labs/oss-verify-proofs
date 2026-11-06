(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe Stdio Driver Malloc Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim DriverSim DriverModel.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Segs RDriver_kit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ClfIx Require Import PathX.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import TSimS MSimS DriverSimS A0Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).
Local Notation SIM := (stsim nstep nexit nstep nexit) (only parsing).
Local Notation stwfN := (stwf node nstep nexit nsafe) (only parsing).

Lemma stwf_tpaths_post {R} : forall (t : itree node R) mo (Q : R -> Model -> Prop) r mo',
  stwfN t mo Q -> tpaths t mo [] r mo' -> Q r mo'.
Proof.
  induction t as [r0 | n k IH]; intros mo Q r mo' HW HP; cbn in HW, HP.
  - destruct HP as (<- & -> & _). exact HW.
  - destruct HW as (_ & _ & HC). destruct HP as (_ & _ & rsp & mo1 & evs & tr' & ST & HP' & E).
    destruct (HC _ _ _ ST) as [-> HW']. cbn in E. subst tr'. exact (IH rsp mo1 Q r mo' HW' HP').
Qed.

Section ShapeA0.
  Context {CP : HasCeiling}.
  Variable RS_A : Z.

  Variable PI : nat -> list bptr -> PState -> Model -> Prop.
  Variable NMAX : Z.
  Hypothesis HNMAX : 2^26 <= NMAX.
  Hypothesis PI_mo : forall k X s mo, PI k X s mo -> minv mo /\ m_halted mo = None.
  Hypothesis PI_soupd : forall k X s mo so, PI k X s mo -> PI k X (set_so_ps so s) mo.
  Hypothesis PI_fdupd : forall k X s mo mo', PI k X s mo -> (mo' = mo \/ exists f, mo' = with_fds f mo) ->
    minv mo' -> m_halted mo' = None -> PI k X s mo'.
  Hypothesis PI_perm : forall k X Y s mo, Permutation X Y -> PI k X s mo -> PI k Y s mo.
  Hypothesis PI_weaken : forall k X s mo, PI (S k) X s mo -> PI k X s mo.

  Hypothesis MALLOC_P : forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
    stwfN (raw_malloc n s) mo (fun r mo' => exists p s', r = Ok (Some p, s') /\ PI k (p :: X) s' mo' /\ ps_so s' = ps_so s
                                          /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
  Hypothesis MALLOC_PX : forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
    exists p s' mo', tpaths (raw_malloc n s) mo [] (Ok (Some p, s')) mo'.
  Hypothesis FREE_P : forall k X p s mo, PI k (p :: X) s mo ->
    stwfN (raw_free p s) mo (fun r mo' => exists s', r = Ok (tt, s') /\ PI k X s' mo' /\ ps_so s' = ps_so s
                                        /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
  Hypothesis FREE_PX : forall k X p s mo, PI k (p :: X) s mo -> exists s' mo', tpaths (raw_free p s) mo [] (Ok (tt, s')) mo'.

  Definition RI (k : nat) (X : list (bptr * unit)) (sP : PState) (moP : Model) (soA : ASt) (moA : Model) : Prop :=
    PI k (map fst X) sP moP /\ ps_so sP = soA /\ m_fds moP = m_fds moA /\ m_fs moP = m_fs moA /\ minv moA /\ m_halted moA = None.
  Definition RI' (k : nat) (X : list (unit * bptr)) (soA : ASt) (moA : Model) (sP : PState) (moP : Model) : Prop :=
    RI k (map (fun q => (snd q, fst q)) X) sP moP soA moA.

  #[using="Type"] Lemma map_fst_perm {A B} : forall (X Y : list (A * B)), Permutation X Y -> Permutation (map fst X) (map fst Y).
  Proof. intros X Y H. apply Permutation_map. exact H. Qed.

  #[using="PI_mo PI_soupd PI_fdupd PI_perm PI_weaken"] Lemma RI_laws :
    (forall k X sA moA sB moB, RI k X sA moA sB moB -> m_fds moA = m_fds moB /\ m_fs moA = m_fs moB /\ minv moA /\ minv moB /\ m_halted moA = None /\ m_halted moB = None)
    /\ (forall k X sA moA sB moB, RI k X sA moA sB moB -> ps_so sA = aget_so sB)
    /\ (forall k X sA moA sB moB so, RI k X sA moA sB moB -> RI k X (set_so_ps so sA) moA (aset_so so sB) moB)
    /\ (forall k X sA moA sB moB moA' moB', RI k X sA moA sB moB -> fdupd2 moA moA' moB moB' -> minv moA' -> minv moB' -> m_halted moA' = None -> m_halted moB' = None -> RI k X sA moA' sB moB')
    /\ (forall k X Y sA moA sB moB, Permutation X Y -> RI k X sA moA sB moB -> RI k Y sA moA sB moB)
    /\ (forall k X sA moA sB moB, RI (S k) X sA moA sB moB -> RI k X sA moA sB moB).
  Proof.
    split; [| split; [| split; [| split; [| split]]]].
    - intros k X sA moA sB moB (P & _ & EF & ES & MI & HB). destruct (PI_mo _ _ _ _ P) as [MIA HA].
      split; [exact EF| split; [exact ES| split; [exact MIA| split; [exact MI| split; [exact HA| exact HB]]]]].
    - intros k X sA moA sB moB (_ & E & _). exact E.
    - intros k X sA moA sB moB so (P & E & R). split; [apply PI_soupd; exact P|]. split; [destruct sA; reflexivity| exact R].
    - intros k X sA moA sB moB moA' moB' (P & E & EF & ES & MI & HB) U MIA' MIB' HA' HB'. split; [| split; [exact E|]].
      + eapply PI_fdupd; [exact P| | exact MIA'| exact HA']. destruct U as [[-> ->]|(f & -> & ->)]; [left; reflexivity| right; exists f; reflexivity].
      + split; [exact (fdupd2_fds _ _ _ _ EF U)|]. split; [| split; assumption].
        destruct U as [[-> ->]|(f & -> & ->)]; [exact ES| rewrite !m_fs_with_fds; exact ES].
    - intros k X Y sA moA sB moB HP (P & R). split; [eapply PI_perm; [apply map_fst_perm; exact HP| exact P]| exact R].
    - intros k X sA moA sB moB (P & R). split; [apply PI_weaken; exact P| exact R].
  Qed.

  #[using="MALLOC_P"] Lemma malloc_simS_PA : forall k X n, 0 <= n <= NMAX ->
    msimS (RI (S k) X) (raw_malloc n) (amalloc0 n)
          (fun rA rB sA moA sB moB => exists pA pB, rA = Some pA /\ rB = Some pB /\ RI k ((pA, pB) :: X) sA moA sB moB).
  Proof.
    intros k X n Hn. unfold amalloc0. apply msimS_left_ret.
    intros sP moP soA moA (P & E & EF & ES & MI & HB).
    eapply stwf_mono; [exact (MALLOC_P k (map fst X) n sP moP Hn P)|].
    intros [|[r sP']] moP' H; [destruct H as (? & ? & H0 & _); discriminate H0|].
    destruct H as (p & s' & H0 & P' & Eso & EF' & ES'). injection H0 as -> ->. cbn [fst snd].
    exists (Some p), s'. split; [reflexivity|]. exists p, tt. split; [reflexivity|]. split; [reflexivity|].
    split; [exact P'|]. split; [rewrite Eso; exact E|]. rewrite EF', ES'. split; [exact EF| split; [exact ES| split; [exact MI| exact HB]]].
  Qed.

  #[using="FREE_P"] Lemma free_simS_PA : forall k X pA pB, msimS (RI k ((pA, pB) :: X)) (raw_free pA) (afree0 pB) (fun _ _ => RI k X).
  Proof.
    intros k X pA []. unfold afree0. apply msimS_left_ret.
    intros sP moP soA moA (P & E & EF & ES & MI & HB). cbn [map fst] in P.
    eapply stwf_mono; [exact (FREE_P k (map fst X) pA sP moP P)|].
    intros [|[r sP']] moP' H; [destruct H as (? & H0 & _); discriminate H0|].
    destruct H as (s' & H0 & P' & Eso & EF' & ES'). injection H0 as -> ->. cbn [fst snd].
    exists tt, s'. split; [reflexivity|]. split; [exact P'|]. split; [rewrite Eso; exact E|]. rewrite EF', ES'. split; [exact EF| split; [exact ES| split; [exact MI| exact HB]]].
  Qed.

  #[using="NMAX HNMAX PI_mo PI_soupd PI_fdupd PI_perm PI_weaken MALLOC_P FREE_P"] Theorem drv_pre_incl0_PA : forall k X argv sP moP soA moA
      (KA : exc (at_parser (ptr:=bptr) * PState) -> Model -> TSet) (KB : exc (at_parser (ptr:=unit) * ASt) -> Model -> TSet),
    RI (DRV_BUDGET k) X sP moP soA moA ->
    (forall apA sA' moA' apB sB' moB', ap_rel apA apB -> RI k (ap_pairs apA apB ++ X) sA' moA' sB' moB' -> t_incl0 (KA (Ok (apA, sA')) moA') (KB (Ok (apB, sB')) moB')) ->
    (forall moA' moB', t_incl0 (KA Unr moA') (KB Unr moB')) ->
    t_incl0 (tsh (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free P0.RDriver_kit.RSV argv sP) moP KA)
            (tsh (drv_preA RS_A argv soA) moA KB).
  Proof.
    intros k X argv sP moP soA moA KA KB HR HK HU. unfold drv_preA, ioA.
    destruct RI_laws as (L1 & L2 & L3 & L4 & L5 & L6).
    eapply (drv_pre_tshape_incl0 ps_so set_so_ps aget_so aset_so raw_malloc raw_free amalloc0 afree0 P0.RDriver_kit.RSV RS_A RI NMAX HNMAX
              L1 L2 L3 L4 L5 L6 malloc_simS_PA free_simS_PA k X argv sP moP soA moA KA KB HR HK HU).
  Qed.

  #[using="PI_mo PI_soupd PI_fdupd PI_perm PI_weaken"] Lemma RI'_laws :
    (forall k X sA moA sB moB, RI' k X sA moA sB moB -> m_fds moA = m_fds moB /\ m_fs moA = m_fs moB /\ minv moA /\ minv moB /\ m_halted moA = None /\ m_halted moB = None)
    /\ (forall k X sA moA sB moB, RI' k X sA moA sB moB -> aget_so sA = ps_so sB)
    /\ (forall k X sA moA sB moB so, RI' k X sA moA sB moB -> RI' k X (aset_so so sA) moA (set_so_ps so sB) moB)
    /\ (forall k X sA moA sB moB moA' moB', RI' k X sA moA sB moB -> fdupd2 moA moA' moB moB' -> minv moA' -> minv moB' -> m_halted moA' = None -> m_halted moB' = None -> RI' k X sA moA' sB moB')
    /\ (forall k X Y sA moA sB moB, Permutation X Y -> RI' k X sA moA sB moB -> RI' k Y sA moA sB moB)
    /\ (forall k X sA moA sB moB, RI' (S k) X sA moA sB moB -> RI' k X sA moA sB moB).
  Proof.
    destruct RI_laws as (L1 & L2 & L3 & L4 & L5 & L6). unfold RI'.
    split; [| split; [| split; [| split; [| split]]]].
    - intros k X sA moA sB moB H. destruct (L1 _ _ _ _ _ _ H) as (EF & ES & MI1 & MI2 & H1 & H2).
      split; [symmetry; exact EF| split; [symmetry; exact ES| split; [exact MI2| split; [exact MI1| split; [exact H2| exact H1]]]]].
    - intros k X sA moA sB moB H. symmetry. exact (L2 _ _ _ _ _ _ H).
    - intros k X sA moA sB moB so H. apply L3. exact H.
    - intros k X sA moA sB moB moA' moB' H U. intros. eapply L4; eauto. apply fdupd2_sym. exact U.
    - intros k X Y sA moA sB moB HP H. eapply L5; [| exact H]. apply Permutation_map. exact HP.
    - intros k X sA moA sB moB H. apply L6. exact H.
  Qed.

  #[using="MALLOC_P MALLOC_PX"] Lemma malloc_simS_AP : forall k X n, 0 <= n <= NMAX ->
    msimS (RI' (S k) X) (amalloc0 n) (raw_malloc n)
          (fun rA rB sA moA sB moB => exists pA pB, rA = Some pA /\ rB = Some pB /\ RI' k ((pA, pB) :: X) sA moA sB moB).
  Proof.
    intros k X n Hn. unfold amalloc0. apply msimS_right_ret.
    intros soA moA sP moP H. unfold RI' in H. destruct H as (P & E & EF & ES & MI & HB).
    pose proof (MALLOC_P k _ n sP moP Hn P) as W. destruct (MALLOC_PX k _ n sP moP Hn P) as (p & s' & moP' & TP).
    pose proof (stwf_tpaths_post _ _ _ _ _ W TP) as (p0 & s0 & H0 & P' & Eso & EF' & ES'). injection H0 as <- <-.
    eexists _, (Some p), s', moP'. split; [exact W|]. split; [exact TP|].
    exists tt, p. split; [reflexivity|]. split; [reflexivity|]. unfold RI'. cbn [map fst snd].
    split; [exact P'|]. split; [rewrite Eso; exact E|]. rewrite EF', ES'. split; [exact EF| split; [exact ES| split; [exact MI| exact HB]]].
  Qed.

  #[using="FREE_P FREE_PX"] Lemma free_simS_AP : forall k X pA pB, msimS (RI' k ((pA, pB) :: X)) (afree0 pA) (raw_free pB) (fun _ _ => RI' k X).
  Proof.
    intros k X [] pB. unfold afree0. apply msimS_right_ret.
    intros soA moA sP moP H. unfold RI' in H. destruct H as (P & E & EF & ES & MI & HB). cbn [map fst snd] in P.
    pose proof (FREE_P k _ pB sP moP P) as W. destruct (FREE_PX k _ pB sP moP P) as (s' & moP' & TP).
    pose proof (stwf_tpaths_post _ _ _ _ _ W TP) as (s0 & H0 & P' & Eso & EF' & ES'). injection H0 as <-.
    eexists _, tt, s', moP'. split; [exact W|]. split; [exact TP|]. unfold RI'.
    split; [exact P'|]. split; [rewrite Eso; exact E|]. rewrite EF', ES'. split; [exact EF| split; [exact ES| split; [exact MI| exact HB]]].
  Qed.

  #[using="NMAX HNMAX PI_mo PI_soupd PI_fdupd PI_perm PI_weaken MALLOC_P MALLOC_PX FREE_P FREE_PX"] Theorem drv_pre_incl0_AP : forall k X argv sP moP soA moA
      (KA : exc (at_parser (ptr:=unit) * ASt) -> Model -> TSet) (KB : exc (at_parser (ptr:=bptr) * PState) -> Model -> TSet),
    RI' (DRV_BUDGET k) X soA moA sP moP ->
    (forall apA sA' moA' apB sB' moB', ap_rel apA apB -> RI' k (ap_pairs apA apB ++ X) sA' moA' sB' moB' -> t_incl0 (KA (Ok (apA, sA')) moA') (KB (Ok (apB, sB')) moB')) ->
    (forall moA' moB', t_incl0 (KA Unr moA') (KB Unr moB')) ->
    t_incl0 (tsh (drv_preA RS_A argv soA) moA KA)
            (tsh (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free P0.RDriver_kit.RSV argv sP) moP KB).
  Proof.
    intros k X argv sP moP soA moA KA KB HR HK HU. unfold drv_preA, ioA.
    destruct RI'_laws as (L1 & L2 & L3 & L4 & L5 & L6).
    eapply (drv_pre_tshape_incl0 aget_so aset_so ps_so set_so_ps amalloc0 afree0 raw_malloc raw_free RS_A P0.RDriver_kit.RSV RI' NMAX HNMAX
              L1 L2 L3 L4 L5 L6 malloc_simS_AP free_simS_AP k X argv soA moA sP moP KA KB HR HK HU).
  Qed.

  Definition START (k : nat) (moP0 moA : Model) : Prop :=
    m_tid moP0 = None /\ minv moP0 /\ m_halted moP0 = None /\
    (forall t, 0 < t < PID_MAX_ENVELOPE -> PI (DRV_BUDGET k) [] (ps_init (reservedZ P0.Segs.rsegs) alloc_ceiling) (with_tid (Z_to_bv 64 t) moP0)) /\
    m_fds moP0 = m_fds moA /\ m_fs moP0 = m_fs moA /\ minv moA /\ m_halted moA = None.

  #[using="NMAX HNMAX PI_mo PI_soupd PI_fdupd PI_perm PI_weaken MALLOC_P MALLOC_PX FREE_P FREE_PX"] Theorem shape_incl0 : forall k argv moP0 moA,
    START k moP0 moA ->
    t_incl0 (AssembleP0.T_P0 argv moP0) (T_A0main RS_A argv moA)
    /\ t_incl0 (T_A0main RS_A argv moA) (AssembleP0.T_P0 argv moP0).
  Proof.
    intros k argv moP0 moA (TID0 & MIP & HP & PINIT & EF & ES & MIA & HA).
    unfold AssembleP0.T_P0, AssembleP0.prog_pre, T_A0main. unfold enode. rewrite ebind_vis.
    split.
    -
      eapply stsim_tshape.
      + apply ss_left.
        * split; [| intros code mo' EX; exact EX]. intros rsp mo' evs ST. exact (proj1 ST).
        * intros rsp moP1 evs ST. destruct (nstep_dec_set_tid _ _ _ _ MIP ST) as (_ & t & D & Ht & [[E _]|[_ ->]]); [rewrite TID0 in E; discriminate|].
          rewrite D, ebind_ret_ok.
          pose proof (malloc_simS_PA) as MS. pose proof free_simS_PA as FS. destruct RI_laws as (L1 & L2 & L3 & L4 & L5 & L6).
          apply (drv_pre_simS ps_so set_so_ps aget_so aset_so raw_malloc raw_free amalloc0 afree0 P0.RDriver_kit.RSV RS_A RI NMAX HNMAX
                   L1 L2 L3 L4 L5 L6 MS FS k [] (argv_Z argv)).
          split; [apply PINIT; exact Ht|]. split; [reflexivity|]. rewrite m_fds_with_tid, m_fs_with_tid.
          split; [exact EF|]. split; [exact ES|]. split; assumption.
      + intros [|[apA sA']] moA' [|[apB sB']] moB'; cbn [leafQ]; intros HQ; try contradiction; [apply t_incl0_refl|].
        destruct HQ as [(_ & _ & _ & EC & _) (_ & _ & _ & ES' & _)]. cbn [AssembleP0.KLEAF KLEAF_A fst snd]. rewrite EC, ES'. apply t_incl0_refl.
    -
      eapply stsim_tshape.
      + eapply (ss_right nstep nexit nstep nexit _ _ moA _ _ moP0 (eff0 (Z_to_bv 64 1)) (with_tid (Z_to_bv 64 1) moP0)).
        * split; [| intros code mo' EX; exact EX]. intros rsp mo' evs ST. exact (proj1 ST).
        * cbn [nstep]. split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. rewrite TID0.
          split; [rewrite unsigned_lit by lia; unfold PID_MAX_ENVELOPE; lia| reflexivity].
        * assert (D : dec_set_tid (eff0 (Z_to_bv 64 1)) = Some 1).
          { unfold dec_set_tid, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies]. rewrite unsigned_lit by lia. reflexivity. }
          rewrite D, ebind_ret_ok.
          pose proof (malloc_simS_AP) as MS. pose proof free_simS_AP as FS. destruct RI'_laws as (L1 & L2 & L3 & L4 & L5 & L6).
          apply (drv_pre_simS aget_so aset_so ps_so set_so_ps amalloc0 afree0 raw_malloc raw_free RS_A P0.RDriver_kit.RSV RI' NMAX HNMAX
                   L1 L2 L3 L4 L5 L6 MS FS k [] (argv_Z argv)).
          unfold RI', RI. cbn [map]. split; [apply PINIT; unfold PID_MAX_ENVELOPE; lia|]. split; [reflexivity|]. rewrite m_fds_with_tid, m_fs_with_tid.
          split; [exact EF|]. split; [exact ES|]. split; assumption.
      + intros [|[apA sA']] moA' [|[apB sB']] moB'; cbn [leafQ]; intros HQ; try contradiction; [apply t_incl0_refl|].
        destruct HQ as [(_ & _ & _ & EC & _) HRI]. unfold RI', RI in HRI. destruct HRI as (_ & _ & _ & ES' & _).
        cbn [AssembleP0.KLEAF KLEAF_A fst snd]. rewrite EC, ES'. apply t_incl0_refl.
  Qed.
End ShapeA0.
