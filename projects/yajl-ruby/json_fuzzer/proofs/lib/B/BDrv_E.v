(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge ITree Nodes NodesCfg Decode Arr FP InitMem Frame Mem Cells SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ExecA LazyModel NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio SpecT.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model R_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require RDrv_B RDrv_C RDrv_run RDrv_D RDrv_E RDrv_spec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface B_iface5x BDrv_ctx BDrv_A BDrv_B BDrv_C BDrv_run BDrv_D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* [comment removed for export] *)
Lemma open_classify_may : forall path mo ent, open_classify path mo = OcMay ent ->
  ent = FdDir \/ (exists d, ent = FdFile path (Z_to_bv 64 0) /\ fs_lookup (m_fs mo) path = Some d).
Proof.
  intros path mo ent H. unfold open_classify in H.
  destruct (path_max <=? length path)%nat; [discriminate H|].
  destruct path as [|c p]; [discriminate H|].
  destruct (path_is_dirref (c :: p)); [left; inversion H; reflexivity|].
  destruct (fs_lookup (m_fs mo) (c :: p)) as [d|] eqn:E; [| discriminate H].
  right. exists d. inversion H. split; [reflexivity | first [exact E | reflexivity]].
Qed.

Section E.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface bsegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x bsegs ACONSTS D.
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).
  Notation AHEAD := (p_AHEAD D).
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Variables (MO : Model) (FS0 : Fs.Fs).
  Hypothesis MOFS : m_fs MO = FS0.
  Hypothesis MOFD : m_fds MO = dfds_std.

  (* [comment removed for export] *)
  Theorem az_main_usage : forall s ms, AENTRY sp0 argv envp uid hw rnd D MO s ms -> Z.of_nat (length argv) <> 2 ->
    realizes_cfg acfg bsegs (mkCfg ms MO) (TDIE (pieces_usage (map bv_unsigned (hd [] argv))) stdout_init FS0).
  Proof.
    intros s ms AE HARGC. pose proof (main_usage sp0 argv envp uid hw rnd VSP RCSP EFIT VARGV VENVP D DI DIx MO s ms AE HARGC) as U.
    unfold TUSAGE in U. unfold TDIE, TEXIT2. rewrite <- MOFS. exact U.
  Qed.

  (* [comment removed for export] *)
  Section Two.
    Variables (arg0 arg1 : list byte).
    Hypothesis EARGV : argv = [arg0; arg1].

    (* [comment removed for export] *)
    Definition KLOOP (ent : FdEntry) : TSet :=
      match ent with
      | FdDir => TDIE (pieces_read_error (map bv_unsigned arg1)) stdout_init FS0
      | FdFile p _ => match fs_lookup FS0 p with
                      | Some FILE => TFIN FS0 FILE (KDONE FS0 FILE)
                      | None => TDIE [] stdout_init FS0
                      end
      | _ => TDIE [] stdout_init FS0
      end.
    (* [comment removed for export] *)
    Definition ADRV2 : TSet :=
      match open_classify arg1 MO with
      | OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
      | OcMay ent => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent)
      end.

    Lemma KLOOP_nil : forall ent, KLOOP ent [].
    Proof.
      intros ent. unfold KLOOP. destruct ent; try apply TDIE_nil.
      destruct (fs_lookup FS0 _); [| apply TDIE_nil]. apply TFIN_nil. apply KDONE_nil.
    Qed.

    Theorem az_main2 : forall s ms, AENTRY sp0 argv envp uid hw rnd D MO s ms -> realizes_cfg acfg bsegs (mkCfg ms MO) ADRV2.
    Proof.
      intros s ms AE.
      assert (ARGC : argc argv = 2) by (unfold argc; rewrite EARGV; reflexivity).
      eapply (main_to_test sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP D DI MO s ms); [exact AE|].
      intros t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm mo' pad FR BA HK0 FRM SO0 HD0 Efs Efds.
      unfold ADRV2.
      assert (OC' : open_classify arg1 mo' = open_classify arg1 MO) by (unfold open_classify; rewrite Efs; reflexivity).
      rewrite <- OC'.
      apply (az_read_all_head sp0 argv envp uid hw rnd arg0 arg1 pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP VARGV VENVP EARGV D DI DIx FS0 KLOOP s mo'
               t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc mm FR BA HK0 SO0 FRM ltac:(rewrite Efs; exact MOFS) HD0 ltac:(rewrite Efds; exact MOFD) KLOOP_nil).
      intros ent s' mo ms' P1v OC HP1 P1R RI.
      destruct (open_classify_may _ _ _ OC) as [-> | (d & -> & FSL)].
      - (* [comment removed for export] *)
        exact (az_loop_dir sp0 argv envp uid hw rnd arg0 arg1 pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP VARGV VENVP EARGV D DI DIx FS0 P1v HP1 P1R s' mo ms' RI).
      - (* [comment removed for export] *)
        unfold KLOOP. rewrite Efs, MOFS in FSL. rewrite FSL.
        apply (az_loop0 sp0 argv envp uid hw rnd arg0 arg1 pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV D DI DIx FS0 P1v arg1 d
                 (KDONE FS0 d) (KDONE_nil FS0 d)) with (s := s').
        + intros cap s'' mo'' ms'' RB LTC.
          exact (az_after_loop sp0 argv envp uid hw rnd arg0 arg1 pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV D DI DIx FS0 P1v arg1 d cap s'' mo'' ms'' RB LTC).
        + exact RI.
        + destruct RI as (x1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x23 & u3 & u4 & u5 & u6 & F' & fc' & mm' & A & _ & RC & _).
          destruct RC as (junk & H & _ & _ & _ & _ & _ & _ & FS & _). rewrite FS. exact FSL.
    Qed.
  End Two.

End E.

(* [comment removed for export] *)
Definition ADRV (MO : Model) (FS0 : Fs.Fs) (argv : list (list byte)) : TSet :=
  match argv with
  | [_; a1] => ADRV2 MO FS0 a1
  | _ => TDIE (pieces_usage (map bv_unsigned (hd [] argv))) stdout_init FS0
  end.

(* [comment removed for export] *)
Lemma vprintf_pure_twin : forall so ps, vprintf_pure so ps = TrzStdioCfg.vprintf_pure so ps.
Proof. reflexivity. Qed.
Definition oc_twin (c : open_class) : TrzNodesCfg.open_class :=
  match c with OcErrno e => TrzNodesCfg.OcErrno e | OcMay ent => TrzNodesCfg.OcMay ent end.
Lemma open_classify_twin : forall p mo, TrzNodesCfg.open_classify p mo = oc_twin (open_classify p mo).
Proof.
  intros p mo. unfold open_classify, TrzNodesCfg.open_classify.
  destruct (path_max <=? length p)%nat; [reflexivity|]. destruct p as [|c p]; [reflexivity|].
  destruct (path_is_dirref (c :: p)); [reflexivity|]. destruct (fs_lookup (m_fs mo) (c :: p)); reflexivity.
Qed.
Lemma emits_twin : forall n so, BDrv_run.emits n so = RDrv_run.emits n so.
Proof.
  induction n as [|n IH]; intros so; [reflexivity|].
  cbn [BDrv_run.emits RDrv_run.emits]. rewrite <- vprintf_pure_twin. rewrite IH. reflexivity.
Qed.
Lemma KDONE_twin : forall (RC : RunCeiling) fs F, BDrv_D.KDONE fs F = RDrv_D.KDONE fs F.
Proof.
  intros. unfold BDrv_D.KDONE, RDrv_D.KDONE. cbv zeta. rewrite !emits_twin. reflexivity.
Qed.
Lemma ADRV_DRV : forall MO FS0 argv, ADRV MO FS0 argv = RDrv_E.DRV MO FS0 argv.
Proof.
  intros. unfold ADRV, RDrv_E.DRV. destruct argv as [|a0 [|a1 [|a2 l0]]]; try reflexivity.
  (* [comment removed for export] *)
  unfold ADRV2, RDrv_E.DRV2. rewrite open_classify_twin. destruct (open_classify a1 MO) as [e|ent]; cbn [oc_twin]; [reflexivity|].
  apply f_equal2; [reflexivity|].
  unfold KLOOP, RDrv_E.KLOOP. destruct ent; try (lazymatch goal with |- context [fs_lookup] => fail | _ => reflexivity end).
  match goal with |- context [fs_lookup FS0 ?p] => destruct (fs_lookup FS0 p) as [l|]; [| reflexivity] end.
  unfold TFIN, RDrv_C.TFIN. rewrite (KDONE_twin _ FS0 l). unfold TREF, RDrv_C.TREF. reflexivity.
Qed.

Section E2.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface bsegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x bsegs ACONSTS D.
  Variables (MO : Model) (FS0 : Fs.Fs).
  Hypothesis MOFS : m_fs MO = FS0.
  Hypothesis MOFD : m_fds MO = dfds_std.

  Theorem a_main_drv : forall s ms, AENTRY sp0 argv envp uid hw rnd D MO s ms -> realizes_cfg acfg bsegs (mkCfg ms MO) (ADRV MO FS0 argv).
  Proof.
    intros s ms AE. unfold ADRV.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2 | NE2].
    - revert VARGV EFIT AE. destruct argv as [|a0 [|a1 [|a2 l]]]; try (exfalso; cbn in E2; lia). intros VARGV EFIT AE.
      exact (az_main2 sp0 [a0; a1] envp uid hw rnd VSP RCSP EFIT VARGV VENVP D DI DIx MO FS0 MOFS MOFD a0 a1 eq_refl s ms AE).
    - pose proof (az_main_usage sp0 argv envp uid hw rnd VSP RCSP EFIT VARGV VENVP D DI DIx MO FS0 MOFS s ms AE NE2) as U.
      revert U. destruct argv as [|a0 [|a1 [|a2 l]]]; intros U; try exact U. exfalso. cbn in NE2. lia.
  Qed.

  Theorem a_main_spec : forall s ms, AENTRY sp0 argv envp uid hw rnd D MO s ms -> realizes_cfg acfg bsegs (mkCfg ms MO) (spec argv FS0).
  Proof.
    intros s ms AE. eapply rz_conseq_cfg; [apply (a_main_drv s ms AE)|].
    rewrite ADRV_DRV. apply RDrv_spec.DRV_spec; [exact MOFS | exact VARGV].
  Qed.
End E2.
End RC__1.
