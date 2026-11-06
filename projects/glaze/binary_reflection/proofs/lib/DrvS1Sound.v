(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrvGSound.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GSound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).

(* [comment removed for export] *)
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_T (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GDRV b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.

#[local] Notation AINVc TOP M0 := (AINV_f SWIN_T GPLAIN AINVH PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okG TOP FS0 FDS0 M0 UINV := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV).

Lemma AF_G : forall TOP M0 Lc B C M M' mdl,
  AINVc TOP M0 Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN_T PERM_Tc TOP Lc a /\ M' a <> None) -> AINVc TOP M0 Lc B C M' mdl.
Proof. intros TOP M0. exact (AINV_f_frame SWIN_T GPLAIN AINVH AINVH_frame AINVH_zone AINVH_disj drv_G_ro_img drv_G_img_ceil PERM_Tc TOP [] M0 0 0). Qed.

Section Inst.
Variables (TOP : Z) (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry)) (M0 : word -> option byte).
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.

Lemma XNd_sound : GPS.ext_stmt RSEGS NXD XNd PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV RZ.
Proof.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold XNd in Hn.
  pose proof (AF_G TOP M0) as AF.
  destruct id as [|id]; [discriminate Hn|].
  destruct id as [|id].
  { (* [comment removed for export] *)
    exact (plain_OBL_memcpy ADRV NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GPLAIN eq_refl
             cs cs' E fx R M model T HC Hp Hn Hk). }
  do 3 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { (* [comment removed for export] *)
    exact (GNB.node_memcpy_blob_sound RSEGS ADRV NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GPLAIN
             plain_copy_spec cs cs' E fx R M model T HC Hp Hn Hk). }
  do 57 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id]; [| discriminate Hn].
  (* [comment removed for export] *)
  exact (node_ioctl_sound SR NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) AF fx_ok UINV FDS1 FDS2 cs cs' E fx R M model T HT HC Hp Hn Hk).
Qed.

Lemma XEd_sound_G : GPS.emit_stmt RSEGS NXD XEs PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV RZ.
Proof.
  unfold XEs. pose proof (AF_G TOP M0) as AF.
  exact (XEd_sound SR NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) AF fx_ok UINV UINV_agree (SR_det_of_exact SR SRX) SWIN_Tc FDS1 FDS2).
Qed.

Lemma XB0_sound_G : GPS.ext2_stmt RSEGS NXD XB0 PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn. Qed.
Lemma XC0_sound_G : GPS.alt2x_stmt RSEGS NXD XC0 PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 Ta Tb HX Hn. discriminate Hn. Qed.

(* [comment removed for export] *)
Theorem drvG_cert_sound : forall (HS : nat -> option acs) (HOLES : nat -> env -> Fs.Fs -> TSet),
  (forall h E E' fs, env_agree NXD E E' -> HOLES h E fs = HOLES h E' fs) ->
  (forall h E fs, HOLES h E fs []) ->
  (forall h E fs, HOLES h E fs = HOLES 0%nat E fs) ->
  GPS.holes_stmt RSEGS HS PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) fx_ok UINV HOLES RZ ->
  forall bf fuel p cs s E fx R M model,
  gplan_ok p = true -> CHKd HS bf fuel cs p = COk s ->
  cs_okG TOP FS0 FDS0 M0 UINV E cs fx R M model -> m_fs model = FS0 ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (sd HOLES t_nil E FS0 s).
Proof.
  intros HS HOLES Hag Hnil Hsame HST bf fuel p cs s E fx R M model Hp CERT HC Hfs.
  pose proof (AF_G TOP M0) as AF. rewrite <- Hfs.
  refine (GPS.check_sound RSEGS ITD ITD_ok ADRV NXD LIMIT HS XNd XEs XB0 XC0 0%nat SWIN_T PERM_Tc TOP FS0 FDS0 (AINVc TOP M0) AF
            fx_ok UINV UINV_agree HOLES Hag Hnil Hsame
            RZ (sr_step RSEGS SR) (sr_msteps RSEGS SR) (sr_exit RSEGS SR) (sr_conseq RSEGS SR) (RUN_sound_fx RSEGS) plain_in_hull plain_hull_ok
            XNd_sound XEd_sound_G XB0_sound_G XC0_sound_G HST
            fuel bf None p cs s Hp CERT E fx R M model t_nil HC I eq_refl).
Qed.
End Inst.
End GSound.
End DrvGSound.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3.MhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.MhMalloc3.MhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan DrvGSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section S1.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition VM0 (mdl : Model) : Prop :=
  vm_maps (m_vmmaps mdl) = [] /\ vm_noaccess (m_vmmaps mdl) = []
  /\ (vm_brk (m_vmmaps mdl) = vm_start_brk (m_vmmaps mdl)
      /\ bv_unsigned (vm_start_brk (m_vmmaps mdl)) mod 4096 = 0
      /\ IMG_HI <= bv_unsigned (vm_start_brk (m_vmmaps mdl))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mdl)) + 2 ^ 31 + 8192 <= CEIL_run)
  /\ vm_reserved (m_vmmaps mdl) = segments_reserved RSEGS
  /\ page_floor (alloc_top (m_vmmaps mdl)) = CEIL_run
  /\ VMLIM <= vm_limit (m_vmmaps mdl).

(* [comment removed for export] *)
Definition W0 (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop :=
  L = [] /\ img_clear M MLOCK CTX_END /\ img_clear M A_ERRNO (A_ERRNO + 4) /\ VM0 mdl.
Definition X1 (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop := W0 L B C M mdl \/ AINV_R L B C M mdl.

Lemma priv_not_owned : forall i, (MLOCK <= i < CTX_END \/ A_ERRNO <= i < A_ERRNO + 4) ->
  ~ (CEIL_run <= i \/ in_wins SWIN_T i).
Proof.
  intros i Hi [H|H].
  - pose proof drv_G_img_ceil as GC. cbn [g_img_hi GDRV GPLAIN] in GC. unfold MLOCK, CTX_END, CTX, A_ERRNO, TPV in Hi. lia.
  - destruct H as (lo & hi & Hin & Hz). unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
    unfold MLOCK, CTX_END, CTX, A_ERRNO, TPV in Hi.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

Lemma W0_frame : forall L B C M M' mdl,
  W0 L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_T (bv_unsigned a)) /\ M' a <> None) ->
  W0 L B C M' mdl.
Proof.
  intros L B C M M' mdl (-> & HC & HE & HV) FR.
  assert (KEEP : forall i, (MLOCK <= i < CTX_END \/ A_ERRNO <= i < A_ERRNO + 4) -> M (Z_to_bv 64 i) = None -> M' (Z_to_bv 64 i) = None).
  { intros i Hi Hm. destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [rewrite E; exact Hm|]. exfalso.
    destruct (FR _ NE) as [[Hb|Ho] _]; [destruct Hb as (b & n & [] & _)|].
    apply (priv_not_owned i Hi). rewrite u64_lit in Ho by (unfold MLOCK, CTX_END, CTX, A_ERRNO, TPV in Hi; lia). exact Ho. }
  split; [reflexivity|]. split; [|split; [|exact HV]].
  - intros i Hi. apply KEEP; [left; exact Hi | exact (HC i Hi)].
  - intros i Hi. apply KEEP; [right; exact Hi | exact (HE i Hi)].
Qed.
Lemma W0_zone : forall L B C M mdl b m, W0 L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GDRV b m.
Proof. intros L B C M mdl b m (-> & _) []. Qed.
Lemma W0_disj : forall L B C M mdl L1 L2 b m b' m',
  W0 L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. intros L B C M mdl L1 L2 b m b' m' (HL & _) E. rewrite E in HL. destruct L1; discriminate HL. Qed.

Lemma X1_zone : forall L B C M mdl b m, X1 L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GDRV b m.
Proof. intros L B C M mdl b m [H|H]; [exact (W0_zone _ _ _ _ _ _ _ H) | exact (AINV_R_zone_T _ _ _ _ _ _ _ H)]. Qed.
Lemma X1_disj : forall L B C M mdl L1 L2 b m b' m',
  X1 L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. intros L B C M mdl L1 L2 b m b' m' [H|H]; [exact (W0_disj _ _ _ _ _ _ _ _ _ _ _ H) | exact (AINV_R_disj_T _ _ _ _ _ _ _ _ _ _ _ H)]. Qed.
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GPLAIN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).

(* [comment removed for export] *)
Lemma AINV_f_weaken : forall (H H' : list (Z * Z) -> Z -> Z -> mem -> Model -> Prop) TOP M0 Lc B C M mdl,
  (forall L B C M mdl, H L B C M mdl -> H' L B C M mdl) -> AINVc H TOP M0 Lc B C M mdl -> AINVc H' TOP M0 Lc B C M mdl.
Proof. intros H H' TOP M0 Lc B C M mdl W (HA & HP & HT & HZ & HD). split; [exact (W _ _ _ _ _ HA)|]. split; [exact HP|]. split; [exact HT|]. split; [exact HZ | exact HD]. Qed.
Lemma cs_ok_weaken : forall (H H' : list (Z * Z) -> Z -> Z -> mem -> Model -> Prop) TOP FS0 FDS0 M0 U E cs fx R M model,
  (forall L B C M mdl, H L B C M mdl -> H' L B C M mdl) ->
  cs_okI H TOP FS0 FDS0 M0 U E cs fx R M model -> cs_okI H' TOP FS0 FDS0 M0 U E cs fx R M model.
Proof.
  intros H H' TOP FS0 FDS0 M0 U E cs fx R M model W HC.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; try assumption. exact (AINV_f_weaken H H' _ _ _ _ _ _ _ W CA).
Qed.


(* [comment removed for export] *)
Definition fe_cells (M0 : mem) (auxw : Z) (avl : list (Z * Z)) : Prop :=
  cell M0 A_LIBC_AUXV 8 auxw
  /\ (0 <= auxw /\ auxw + 16 * (Z.of_nat (length avl) + 1) <= 2 ^ 63 /\ auxw mod 8 = 0)
  /\ (forall i kv, nth_error avl i = Some kv ->
        cell M0 (auxw + 16 * Z.of_nat i) 8 (fst kv) /\ cell M0 (auxw + 16 * Z.of_nat i + 8) 8 (snd kv) /\ 0 < fst kv < 2 ^ 64 /\ 0 <= snd kv < 2 ^ 64)
  /\ cell M0 (auxw + 16 * Z.of_nat (length avl)) 8 0
  /\ (forall kv, In kv avl -> fst kv = 25 -> snd kv + 24 <= 2 ^ 63 /\ exists bs, length bs = 8%nat /\ rdn RSEGS M0 (Z_to_bv 64 (snd kv + 8)) 8%nat = Some bs)
  /\ cell M0 A_PAGESIZE 8 4096 /\ cell M0 A_NEED_LOCKS 1 0 /\ (exists v, cell M0 A_CANARY 8 v)
  /\ img_clear M0 A_GOT_CANARY (A_GOT_CANARY + 8) /\ img_clear M0 A_TAB_CTZ (A_TAB_CTZ + 32) /\ img_clear M0 A_TAB_SC (A_TAB_MED + 4).

(* [comment removed for export] *)
Lemma zone_img : forall TOP (y : Z),
  (0x10000 <= y < 0x75768 \/ 0xa678c <= y < 0xa6820) ->     (* [comment removed for export] *)
  zone SWIN_T GPLAIN PERM_Tc TOP [] (Z_to_bv 64 y).
Proof.
  intros TOP y Hy. unfold zone. cbn [g_ro_lo g_img_hi g_priv GPLAIN]. rewrite u64_lit by lia.
  split; [|split].
  - right; right. split; [lia|]. intros (lo & hi & Hin & Hz). cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  - intros (lo & hi & Hin & Hz). unfold PERM_Tc, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  - intros (lo & hi & Hin & Hz). unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma zone_top : forall TOP (y : Z), CEIL_run <= TOP -> TOP <= y < 2 ^ 64 ->
  zone SWIN_T GPLAIN PERM_Tc TOP [] (Z_to_bv 64 y).
Proof.
  intros TOP y HT Hy. pose proof drv_G_img_ceil as GC. cbn [g_img_hi GDRV GPLAIN] in GC.
  unfold zone. cbn [g_ro_lo g_img_hi g_priv GPLAIN]. rewrite u64_lit by lia.
  split; [right; left; lia | split].
  - intros (lo & hi & Hin & Hz). unfold PERM_Tc, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  - intros (lo & hi & Hin & Hz). unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma first_env_xfer : forall TOP M0 M mdl B C auxw avl,
  fe_cells M0 auxw avl -> env_above_sp auxw avl TOP ->
  AINVc W0 TOP M0 [] B C M mdl ->
  first_env M mdl auxw avl /\ first_img M.
Proof.
  intros TOP M0 M mdl B C auxw avl (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) [ATOP ARND] (HW & HP & HT & HZ & HD).
  destruct HW as (_ & Wctx & Werr & (V1 & V2 & V3 & V4 & V5 & V6)).
  assert (AGI : forall a k, (0x10000 <= a /\ a + Z.of_nat k <= 0x75768) \/ (0xa678c <= a /\ a + Z.of_nat k <= 0xa6820) ->
                rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS M0 (Z_to_bv 64 a) k).
  { intros a k Ha. apply (MhASlotKA.rdn_agreeZ M0 M a k); [lia | lia |]. intros y Hy. apply HZ. apply zone_img. lia. }
  assert (AGT : forall a k, TOP <= a -> a + Z.of_nat k <= 2 ^ 64 -> rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS M0 (Z_to_bv 64 a) k).
  { intros a k Ha Hk. pose proof ceil_rng. apply (MhASlotKA.rdn_agreeZ M0 M a k); [lia | lia |]. intros y Hy. apply HZ. apply zone_top; lia. }
  assert (CLR : forall lo hi, (0x10000 <= lo /\ hi <= 0x75768) -> img_clear M0 lo hi -> img_clear M lo hi).
  { intros lo hi Hr IC i Hi. rewrite (HZ (Z_to_bv 64 i) (zone_img TOP i ltac:(lia))). exact (IC i Hi). }
  split.
  - constructor.
    + exact Wctx.
    + unfold cell. rewrite (AGI A_LIBC_AUXV 8%nat) by (unfold A_LIBC_AUXV; cbn; lia). exact C1.
    + exact C2.
    + intros i kv Hi. destruct (C3 i kv Hi) as (K1 & K2 & K3 & K4).
      assert (LEN : (i < length avl)%nat) by (apply (proj1 (nth_error_Some avl i)); rewrite Hi; discriminate).
      unfold cell. rewrite !AGT by (cbn; nia). split; [exact K1|]. split; [exact K2|]. split; [exact K3 | exact K4].
    + unfold cell. rewrite AGT by (cbn; nia). exact C4.
    + intros kv Hin H25. destruct (C5 kv Hin H25) as (R1 & bs & Lbs & Rd). split; [exact R1|]. exists bs. split; [exact Lbs|].
      pose proof (ARND kv Hin H25). rewrite AGT by (cbn; lia). exact Rd.
    + unfold cell. rewrite (AGI A_PAGESIZE 8%nat) by (unfold A_PAGESIZE; cbn; lia). exact C6.
    + unfold cell. rewrite (AGI A_NEED_LOCKS 1%nat) by (unfold A_NEED_LOCKS; cbn; lia). exact C7.
    + destruct C8 as (v & C8). exists v. unfold cell. rewrite (AGI A_CANARY 8%nat) by (unfold A_CANARY; cbn; lia). exact C8.
    + split; [exact V1 | exact V2].
    + exact V3.
    + exact V4.
    + exact V5.
    + exact V6.
  - constructor.
    + exact Werr.
    + apply CLR; [unfold A_GOT_CANARY; lia | exact C9].
    + apply CLR; [unfold A_TAB_CTZ; lia | exact C10].
    + apply CLR; [unfold A_TAB_SC, A_TAB_MED; lia | exact C11].
Qed.
End S1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ENT29_tenv : forall {RC : run_ceil} PERMc SPTOPc FS0 FDS0 AINV (U U' : env -> Prop) (E : env) (h T : acs) (w : tbind) fx R M model,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U E h fx R M model ->
  ENT29 h T w = true ->
  U' (tenv E (TH29 h T w)) ->
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV fx_ok U' (tenv E (TH29 h T w)) T fx R M model /\ pc T = pc h.
Proof.
  intros RC PERMc SPTOPc FS0 FDS0 AINV U U' E h T w fx R M model HC H HU'. unfold ENT29 in H. rewrite APC.entails_tw_eq in H.
  apply andb_prop in H as [_ H]. unfold TH29. exact (entails_t_tenv PERMc SPTOPc FS0 FDS0 AINV U U' E h T _ fx R M model HC H HU').
Qed.

Strategy opaque [hM1 hN1 hOPEN tM tMo tAO].

Section M1.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
(* [comment removed for export] *)
Hypothesis HM1 : forall fx : FPState, @MALLOC_FIRST_ALT3 RC fx MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GPLAIN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GPLAIN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD APLAIN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GPLAIN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzE.ce.
Variables (p : Fs.path) (data : list byte) (TOP : Z) (M0 : mem).
(* [comment removed for export] *)
Hypothesis REF_sound : forall M1 len E fx R M model,
  GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model) (FDSr p (len + (2 ^ 26 - len))) (AINVcS TOP M1) fx_ok (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVRb) M model) (t_die msg_refused (m_fs model)).

(* [comment removed for export] *)
Variables (auxw : Z) (avl : list (Z * Z)).
Hypothesis FEC : fe_cells M0 auxw avl.
Hypothesis ENV : env_above_sp auxw avl TOP.

Lemma getr_z5'' : forall (R : bvmap 5 word) (r : bv 5), getr R (Z_to_bv 5 (bv_unsigned r)) = getr R r.
Proof. intros R r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Theorem M1_gen : forall FDS0 (U : env -> Prop) (T0 : acs) (B : Fs.Fs -> TSet),
  fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) -> fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (forall E E', env_agree NXD E E' -> U E -> U E') ->
  ENT29 hN1 T0 [] = true ->
  (forall E, U E -> U (tenv E (TH29 hN1 T0 []))) ->
  forall E fx R M model,
  (forall E' fx' R' M' mdl', env_agree NXD E E' ->
                             GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model) FDS0 (AINVcS TOP M0) fx_ok U (tenv E' (TH29 hN1 T0 [])) T0 fx' R' M' mdl' ->
                             RZ (cfgF RSEGS fx' R' (pc T0) M' mdl') (B (m_fs model))) ->
  cs_okI W0 TOP (m_fs model) FDS0 M0 U E hM1 fx R M model ->
  RZ (cfgF RSEGS fx R (pc hM1) M model) (B (m_fs model)).
Proof.
  intros FDS0 U T0 B F1 F2 U_agree ENT0 HUt E fx R M model HK HC.
  assert (STK : 0 <= MSTK_M <= GlzIface.MSTK) by (unfold MSTK_M, GlzIface.MSTK; lia).
  (* [comment removed for export] *)
  destruct (node_alloc_pre_sound RSEGS NXD PERM_Tc TOP (m_fs model) FDS0 (AINVc W0 TOP M0) fx_ok U GPLAIN BCAP CCAP P_MALLOC_T hM1 hN1 P_AFTER_MALLOC1'
              E fx R M model HC hM1_call_ok hM1_alloc) as [Hpc NPRE].
  pose proof NPRE as (Hh & Hlz & Hmat & HFX & HAF & R1 & Rr & Re & Hn & Hnr & Hsp & Hal & Hspc & Hsptop & R4 & Hstk & HB & HBC).
  pose proof (alloc_pre_of RSEGS SWIN_T GPLAIN fx_ok W0 PERM_Tc TOP [] M0 0 0 MSTK_M STK BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia)
                fx R M model _ _ _ _ _ _ NPRE) as PRE.
  destruct hM1_parts as (E10 & E2 & EVIS & E1).
  rewrite ?E10, ?EVIS in PRE. rewrite ?E10, ?EVIS in HAF. rewrite ?E10 in Hnr.
  rewrite ?uE_lit in PRE by lia. rewrite ?uE_lit in Hnr by lia.
  set (sp := uE E (reg hM1 2)) in *.
  cbn [blocks_den bcost bcount map app Z.add length Z.of_nat] in PRE, HAF.
  (* [comment removed for export] *)
  destruct PRE as (_ & _ & _ & _ & _ & Q1 & Qret & Qev & Q10 & Qnr & Q2 & Qal & Qceil & Q4 & Qstk & QB & QC).
  cbn [g_tp GPLAIN] in Q4.
  assert (MPRE : malloc_pre MSTK_M R M model 0 0 P_AFTER_MALLOC1' 65536 sp).
  { unfold malloc_pre. unfold MH_NMAX, MH_GBUDGET, MhDefs.MBLK, MhDefs.LMAX, TPV.
    split; [exact Hh|]. split; [exact Hlz|]. split; [exact Hmat|].
    split; [rewrite <- (getr_z5'' R 1); exact Q1|]. split; [exact Qret|]. split; [exact Qev|].
    split; [rewrite <- (getr_z5'' R 10); exact Q10|]. split; [lia|].
    split; [rewrite <- (getr_z5'' R 2); exact Q2|]. split; [exact Qal|]. split; [exact Qceil|].
    split; [rewrite <- (getr_z5'' R 4); exact Q4|]. split; [exact Qstk|]. lia. }
  destruct (first_env_xfer TOP M0 M model _ _ auxw avl FEC ENV HAF) as [FE FI].
  assert (ENVsp : env_above_sp auxw avl sp) by (apply (env_above_sp_mono auxw avl TOP); [exact Hsptop | exact ENV]).
  pose proof (HM1 fx R M model P_AFTER_MALLOC1' 65536 sp auxw avl FE FI ENVsp MPRE eq_refl) as KATS.
  rewrite Hpc. unfold cfgF.
  unfold malloc_cfg, A_MALLOC in KATS. unfold P_MALLOC_T, mkstF.
  apply (kats_ok_exact RSEGS SR SRX _ _ _ (B (m_fs model)) KATS).
  - (* [comment removed for export] *)
    intros c' (R' & M' & mdl' & pw & -> & RK & H10 & Hp16 & Hblk & Hdisj & Hdef & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
    (* [comment removed for export] *)
    assert (APOST : alloc_post_ok RSEGS X1 fx_ok GPLAIN MSTK_M fx R M model ([] ++ []) (0 + 0) (0 + 0) 65536 sp fx R' M' mdl' pw).
    { unfold alloc_post_ok.
      split; [exact HFX|]. split; [exact RK|]. split; [rewrite <- (getr_z5'' R' 10); exact H10|]. split; [exact Hp16|].
      split. { destruct Hblk as (Z1 & Z2 & Z3). unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GPLAIN]. unfold HEAPLO in Z1. unfold PTRLO. lia. }
      split; [exact Hdisj|]. split; [exact Hdef|].
      split. { intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed. cbn [g_img_lo g_img_hi g_priv GPLAIN].
               unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in X. pose proof (u64_range a).
               destruct X as [(Y1 & Y2 & Y3)|[X|[X|X]]];
                 [ left; split; [lia|]; split; [lia|]; unfold GPS.in_blocks; unfold MhAInv.in_blocks in Y3; exact Y3
                 | right; left; lia
                 | right; right; exists 0xa6820, 0xa6bd0; split; [cbn; right; right; left; reflexivity | lia]
                 | right; right; exists 0x8647c, 0xa6564; split; [cbn; right; left; reflexivity | lia] ]. }
      split; [exact ST|]. split; [| repeat split; assumption].
      right. unfold mcost, MCNT, GlzIface.MBLK. unfold MhDefs.MBLK in HA'. exact HA'. }
    pose proof (cs_ok_weaken W0 X1 TOP _ _ M0 U E hM1 fx R M model (fun L B C M mdl H => or_introl H) HC) as HC1.
    pose proof (AINV_f_weaken W0 X1 TOP M0 _ _ _ M model (fun L B C M mdl H => or_introl H) HAF) as HAF1.
    pose proof (nalloc_post_ok_of RSEGS SWIN_T GPLAIN fx_ok X1 X1_zone X1_disj drv_G_ro_img drv_G_img_ceil drv_G_priv SWIN_T_img drv_SEGS_out
                  PERM_Tc TOP [] M0 0 0 MSTK_M STK fx R M model [] 0 0 65536 sp fx R' M' mdl' pw HAF1 Hspc Hsptop ltac:(lia) Hstk APOST) as NPOST.
    (* [comment removed for export] *)
    pose proof (node_alloc_ok_sound RSEGS NXD SWIN_T PERM_Tc TOP (m_fs model) FDS0 (AINVc X1 TOP M0) fx_ok U U_agree GPLAIN BCAP CCAP P_MALLOC_T
                  hM1 hN1 P_AFTER_MALLOC1' E fx R M model fx R' M' mdl' pw ltac:(cbn; lia) ltac:(cbn; lia) HC1 hM1_call_ok hM1_alloc) as NAS.
    rewrite E10, EVIS in NAS. change (uE E (reg hM1 2)) with sp in NAS. rewrite uE_lit in NAS by lia.
    cbn [blocks_den bcost bcount map app Z.add length Z.of_nat] in NAS.
    destruct (NAS NPOST) as (E' & [Hag0 Hag] & HC' & Hpc'). clear NAS.
    (* [comment removed for export] *)
    assert (HCS : GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model) FDS0 (AINVcS TOP M0) fx_ok U E' hN1 fx R' M' mdl').
    { destruct HC' as [CR CL CK CHh CZ CF CD CA CU CX CP CT CM CFL].
      constructor; [exact CR | exact CL | exact CK | exact CHh | exact CZ | exact CF | exact CD | | exact CU | exact CX | exact CP | exact CT | exact CM | exact CFL].
      destruct CA as (HA & HP & HT & HZ & HD). split; [| split; [exact HP | split; [exact HT | split; [exact HZ | exact HD]]]].
      destruct HA as [(HL & _)|HA]; [| exact HA]. exfalso. revert HL. vm_compute. discriminate. }
    (* [comment removed for export] *)
    destruct (ENT29_tenv PERM_Tc TOP _ FDS0 _ U U E' hN1 T0 [] fx R' M' mdl' HCS ENT0 (HUt _ (co_uinv HCS))) as [HC2 Hpc2].
    pose proof (HK _ fx R' M' mdl' Hag0 HC2) as HT.
    rewrite Hpc2, Hpc' in HT. unfold cfgF, mkstF in HT. exact HT.
Qed.

(* [comment removed for export] *)
Theorem M1_sound : forall E fx R M model,
  fs_lookup (m_fs model) p = Some data ->
  cs_okI W0 TOP (m_fs model) (FDSr p 0) M0 (U_1 data) E hM1 fx R M model ->
  RZ (cfgF RSEGS fx R (pc hM1) M model) (t_opened data (m_fs model)).
Proof.
  intros E fx R M model Hfs HC.
  refine (M1_gen (FDSr p 0) (U_1 data) tR0 (fun fs => RD data 65536 fs) (fds3_1 _ _) (fds3_2 _ _) (U_1_agree data) entN1 _ E fx R M model _ HC).
  - intros E0 [UF UB]. split; [rewrite (tenv_uE _ _ _ _ (proj1 thN1)); exact UF | rewrite tenv_eb; exact UB].
  - intros E' fx' R' M' mdl' _ HC'. pose proof (co_fs HC') as Hfs'.
    pose proof (R0_sound SR SRX HFR HMB HMA GC_T FZN_sound FZE_sound p data TOP M0 (REF_sound M0) _ fx' R' M' mdl'
                  ltac:(rewrite Hfs'; exact Hfs) ltac:(rewrite Hfs'; exact HC')) as HT.
    rewrite Hfs' in HT. exact HT.
Qed.
End M1.
