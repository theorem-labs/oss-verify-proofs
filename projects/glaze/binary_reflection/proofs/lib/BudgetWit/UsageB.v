(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from DrvS0Dir.v's section ESound of module DrvESound and the argc <> 2 part of section Dies of module DrvS0Glue (die_cert_sound, section Usage), over BudgetWit.Rzb's ShapeRelB.shape_rel and BudgetWit.NodesB, Nodes2B. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput in section Usage: main_entry over inp and the mmap base, the launch premises, the channel reader and the vDSO reservation inclusion at its cs_ok, DrvS0Dir's lemmas at their new arguments). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.RefMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Plan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue.
Require Stdlib.Strings.String Stdlib.Strings.Ascii OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.NodesB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Nodes2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrvESoundB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Nodes2B.DrvNodes2SoundB OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvESound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.RzbAlg OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.ShapeRelB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.NodesB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Nodes2B.DrvNodes2SoundB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section ESound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation AINVe TOP M0 := (AINV_f SWIN_E GE SHP PERM_Ec TOP [] M0 0 0).
#[local] Notation cs_okE TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok U).

Lemma AF_E : forall TOP M0 Lc B C M M' mdl,
  AINVe TOP M0 Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN_E PERM_Ec TOP Lc a /\ M' a <> None) -> AINVe TOP M0 Lc B C M' mdl.
Proof. intros TOP M0. exact (AINV_f_frame SWIN_E GE SHP SHP_frame SHP_zone SHP_disj GE_ro_img GE_img_ceil PERM_Ec TOP [] M0 0 0). Qed.

Section Inst.
Variables (TOP : Z) (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry)) (M0 : word -> option byte).
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable NZBc : list nat.
Hypothesis UINV_nz : forall E j, UINV E -> In j NZBc -> ~ In (Z_to_bv 8 0) (eb E j).

(* [comment removed for export] *)
Variable DIRD : bool.
Hypothesis FDS3d : DIRD = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir.

Lemma XNE_sound : GPS.ext_stmt RSEGS NXD (XNE NZBc DIRD) PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold XNE, DN2.XNe in Hn.
  pose proof (AF_E TOP M0) as AF.
  destruct id as [|id]; [discriminate Hn|].
  destruct id as [|id].
  { exact (plain_OBL_memcpy ADRV NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GDRV eq_refl
             cs cs' E fx R M model T HC Hp Hn Hk). }
  do 3 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (GNB.node_memcpy_blob_sound RSEGS ADRV NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GDRV
             plain_copy_spec cs cs' E fx R M model T HC Hp Hn Hk). }
  do 57 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (node_ioctl_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV FDS1 FDS2 cs cs' E fx R M model T HT HC Hp Hn Hk). }
  do 3 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (node_strnlen_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree NZBc UINV_nz cs cs' E fx R M model T HT HC Hp Hn Hk). }
  destruct id as [|id]; [| discriminate Hn].
  pose proof FDS3d as F3. destruct DIRD; [| discriminate Hn].
  exact (node_read_dir_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV true F3 eq_refl cs cs' E fx R M model T HT HC Hp Hn Hk).
Qed.

Lemma XEE_sound : GPS.emit_stmt RSEGS NXD XEE PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof.
  unfold XEE. pose proof (AF_E TOP M0) as AF.
  exact (XEe_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree (SR_det_of_exact RSEGS SR SRX) SWIN_Ec FDS1 FDS2).
Qed.

Lemma XB0_sound_E : GPS.ext2_stmt RSEGS NXD XB0 PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn. Qed.
Lemma XC0_sound_E : GPS.alt2x_stmt RSEGS NXD XC0 PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 Ta Tb HX Hn. discriminate Hn. Qed.

Theorem drvE_cert_sound : forall (HS : nat -> option acs) (HOLES : nat -> env -> Fs.Fs -> TSet),
  (forall h E E' fs, env_agree NXD E E' -> HOLES h E fs = HOLES h E' fs) ->
  (forall h E fs, HOLES h E fs []) ->
  (forall h E fs, HOLES h E fs = HOLES 0%nat E fs) ->
  GPS.holes_stmt RSEGS HS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV HOLES RZ ->
  forall bf fuel p cs s E fx R M model,
  gplan_ok p = true -> CHKe NZBc DIRD HS bf fuel cs p = COk s ->
  cs_okE TOP FS0 FDS0 M0 UINV E cs fx R M model -> m_fs model = FS0 ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (sd HOLES t_nil E FS0 s).
Proof.
  intros HS HOLES Hag Hnil Hsame HST bf fuel p cs s E fx R M model Hp CERT HC Hfs.
  pose proof (AF_E TOP M0) as AF. rewrite <- Hfs.
  refine (GPS.check_sound RSEGS ITE ITE_ok ADRV NXD LIMIT HS (XNE NZBc DIRD) XEE XB0 XC0 0%nat SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF
            fx_ok UINV UINV_agree HOLES Hag Hnil Hsame
            RZ (sr_step RSEGS SR) (sr_msteps RSEGS SR) (sr_exit RSEGS SR) (sr_conseq RSEGS SR) (RUN_sound_fx RSEGS) plain_in_hull plain_hull_ok
            XNE_sound XEE_sound XB0_sound_E XC0_sound_E HST
            fuel bf None p cs s Hp CERT E fx R M model t_nil HC I eq_refl).
Qed.
End Inst.
End ESound.
End DrvESoundB.
Module DrvS0GlueB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.RefStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3.MhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound.DrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS0Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS1Open OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Nodes2B.DrvNodes2SoundB OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Plan DrvESoundB OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvESound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS0Dir.DrvS0Glue.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.RzbAlg OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.ShapeRelB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.WritevB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefStdioWriteB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.StdioB.RefExitB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.NodesB OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Nodes2B.DrvNodes2SoundB DrvESoundB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section Dies.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation AINVe TOP M0 := (AINV_f SWIN_E GE SHP PERM_Ec TOP [] M0 0 0).
#[local] Notation cs_okE TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok U).
#[local] Notation cs_okW TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINV_f SWIN_T GPLAIN W0 PERM_Tc TOP [] M0 0 0) fx_ok U).
Definition HOLE_0 (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_nil.

(* [comment removed for export] *)
Lemma die_cert_sound : forall TOP M0 FDS0 (a0 p : list byte) (dird : bool) cs pl (L : expr) a b pre j suf E fx R M model,
  fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) -> fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (dird = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir) ->
  ~ In (Z_to_bv 8 0) a0 -> ~ In (Z_to_bv 8 0) p ->
  gplan_ok pl = true -> CHKe NZB dird HS0 BF FUEL cs pl = COk (shS3 L a b pre j suf) ->
  cs_okE TOP (m_fs model) FDS0 M0 (U_D a0 p) E cs fx R M model ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (t_die (map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf) (m_fs model)).
Proof using SRX.
  intros TOP M0 FDS0 a0 p dird cs pl L a b pre j suf E fx R M model F1 F2 F3 N0 N1 Hpl CERT HC.
  eapply (sr_conseq RSEGS SR); [| apply (sd_shS3 HOLE_0 t_nil E (m_fs model) L a b pre j suf)].
  exact (drvE_cert_sound SR SRX TOP (m_fs model) FDS0 M0 F1 F2 (U_D a0 p) (U_D_agree a0 p) NZB (U_D_nz a0 p N0 N1) dird F3
           HS0 HOLE_0 (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun h ch Hh => ltac:(discriminate Hh))
           BF FUEL pl cs _ E fx R M model Hpl CERT HC eq_refl).
Qed.
Lemma nodir : false = true -> fd_lookup fds_std (Z_to_bv 64 3) = Some State.FdDir. Proof using. intros H. discriminate H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
Variable sp0 : word.
Variable inp : ProcInput.
Variables mbase brk : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Variable model : Model.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
#[local] Notation av := (in_argv inp) (only parsing).
#[local] Notation ev := (in_envp inp) (only parsing).
Hypothesis Mh : m_halted model = None.
Hypothesis Ml : m_vm_lazy model = [].
Hypothesis Mm : m_vm_materialized model = [].
Hypothesis Mfd : m_fds model = fds_std.
Hypothesis MC : CEIL_run <= bv_unsigned sp0 - 8388608.
(* [co_rdr]: the launch predicate pins [in_channel_reader], and no model setter writes it. *)
Hypothesis Mrd : m_channel_reader model = true.
Hypothesis MVdso : incl (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) (vm_reserved (m_vmmaps model)).
#[local] Notation E := (EM sp0 inp rdraw tid regs 0 []).
#[local] Notation s0 := (bv_unsigned sp0).

Lemma know_Xu : know_ok RSEGS E mem knXu.
Proof using Hlau Htid Hva Hve Hvl Hvsp ME Mrd RC brk inp mbase mem model rdraw regs sp0 tid.
  pose proof (L0_rng sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as LR. pose proof (CSO_rng sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as SR'. pose proof (bsb_len sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as SRb.
  pose proof (P0_val sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as PV.
  pose proof (uE_STR0 sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0 []) as US. pose proof (uE_L0 sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0 []) as UL.
  pose proof (str_end_le sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0%nat ltac:(pose proof (valid_argv_nonempty av Hva); lia)) as SE. rewrite PV in SE.
  pose proof (BE_le sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as BE. pose proof (BLEN_eq sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as BQ. pose proof (top_le sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME) as TL.
  destruct Hvsp as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
  unfold knXu. apply know_ok_cons.
  { apply kentry_ok_KRange. fold (uE E END0'). unfold END0'. rewrite (uE_add sp0 inp rdraw tid regs 0 []) by (rewrite US, UL; unfold P0; lia). rewrite US, UL.
    unfold HI47, L0v, P0 in *. lia. }
  apply know_ok_cons.
  { cbn [kentry_ok]. unfold elenZ, flat. rewrite !estart_SA. fold (uE E STR0). rewrite !US.
    assert (U8 : bv_unsigned (edenot E (EAlu Instr.ALU_ADD L0 (ELit 8))) = L0v inp + 8).
    { fold (uE E (EAlu Instr.ALU_ADD L0 (ELit 8))). rewrite (uE_add sp0 inp rdraw tid regs 0 []) by (rewrite UL, (uE_litE sp0 inp rdraw tid regs 0 []) by lia; lia).
      rewrite UL, (uE_litE sp0 inp rdraw tid regs 0 []) by lia. lia. }
    rewrite U8. unfold L0v, P0 in *. split; [lia|]. intros i Hi. apply (mem_block sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME). lia. }
  apply know_ok_cons; [apply kn_errno | apply know_ok_nil].
Qed.

Lemma usage_cs_ok : forall argc : kentry,
  kentry_ok RSEGS E mem argc ->
  cs_okE (TOPm sp0) (m_fs model) fds_std mem (U_D (nth 0 av []) (nth 1 av [])) E (tMu argc) fx0 regs mem model.
Proof using MC Mfd Mm Ml Mh Mrd MVdso ME Htid Hvl Hlau Hvsp Hve Hva inp mbase brk.
  intros argc Hargc. pose proof Hvsp as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
  assert (TOP : sptop_den E (a_brk (tMu argc)) = TOPm sp0).
  { change (a_brk (tMu argc)) with SP0. unfold sptop_den. rewrite (uE0 sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0 []). unfold TOPm.
    destruct (Z.eqb_spec (s0 - 48) 0); [lia | reflexivity]. }
  apply cs_ok_intro.
  - exact (regs_M sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0 []).
  - reflexivity.
  - change (kn (tMu argc)) with (argc :: knXu ++ kn tM). apply know_ok_cons; [exact Hargc|]. apply know_ok_app; [exact know_Xu|].
    exact (know_M sp0 inp mbase brk rdraw tid regs mem Hva Hve Hvsp Hvl Hlau Htid ME 0 []).
  - exact Mh. - exact Ml. - exact Mm. - reflexivity. - exact Mfd.
  - change (a_vis (tMu argc)) with (@nil (expr * expr)). cbn [blocks_den bcost bcount map length Z.of_nat fold_right].
    split; [split; [intros b m [] | intros L1 L2 b m b' m' EQ; destruct L1; discriminate EQ]|].
    split; [intros z Hz; right; right; exact (PERM_E_SWIN z Hz)|]. split; [unfold TOPm; lia|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - split; reflexivity.
  - exact fx_ok_fx0.
  - exact (PERM_Ec_den E).
  - exact TOP.
  - change (acs_floor (a_maps (tMu argc))) with (@None expr). cbn [floor_sem]. rewrite TOP. change (a_ylo (tMu argc)) with YLO. unfold TOPm, YLO. lia.
  - exact Mrd.
  - exact MVdso.
Qed.

Theorem usage_sound : length av <> 2%nat ->
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_die (msg_usage (nth 0 av [])) (m_fs model)).
Proof using MC Mfd Mm Ml Mh Mrd MVdso ME Htid Hvl Hlau Hvsp Hve Hva tid rdraw inp mbase brk sp0 SRX RC.
  intros Hne. pose proof (valid_argv_len av Hva) as LA. pose proof (valid_argv_nonempty av Hva) as LA1.
  assert (UA : uE E ARGC = Z.of_nat (length av)) by (unfold uE; cbn; exact (u_argcN inp Hva)).
  assert (N0 : ~ In (Z_to_bv 8 0) (nth 0 av [])) by (apply (valid_argv_str_nz av 0 Hva); lia).
  assert (N1 : ~ In (Z_to_bv 8 0) (nth 1 av [])).
  { destruct (Nat.lt_ge_cases 1 (length av)); [apply (valid_argv_str_nz av 1 Hva); lia | rewrite nth_overflow by lia; intros []]. }
  unfold msg_usage. rewrite <- zUSAGE1_ok, <- zUSAGE2_ok, app_assoc.
  change (nth 0 av []) with (eb E 1) at 1.
  replace (map (Z_to_bv 8) zUSAGE1 ++ eb E 1 ++ map (Z_to_bv 8) zUSAGE2) with (map (Z_to_bv 8) zUSAGE1 ++ eb E 1 ++ map (Z_to_bv 8) zUSAGE2) by reflexivity.
  destruct (Nat.eq_dec (length av) 1) as [H1|H3].
  - change P_MAIN with (pc tMu1).
    rewrite <- app_assoc.
    apply (die_cert_sound (TOPm sp0) mem fds_std (nth 0 av []) (nth 1 av []) false tMu1 planU L0 66 73 zUSAGE1 1 zUSAGE2 E fx0 regs mem model eq_refl eq_refl nodir N0 N1 eq_refl certU1).
    apply usage_cs_ok. apply kentry_ok_KRange. fold (uE E ARGC). rewrite UA. lia.
  - change P_MAIN with (pc tMu3).
    rewrite <- app_assoc.
    apply (die_cert_sound (TOPm sp0) mem fds_std (nth 0 av []) (nth 1 av []) false tMu3 planU L0 66 73 zUSAGE1 1 zUSAGE2 E fx0 regs mem model eq_refl eq_refl nodir N0 N1 eq_refl certU3).
    apply usage_cs_ok. apply kentry_ok_KRange. fold (uE E ARGC). rewrite UA. lia.
Qed.
End Usage.
End Dies.
End DrvS0GlueB.
