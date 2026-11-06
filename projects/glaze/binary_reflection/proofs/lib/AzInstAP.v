(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgePR OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgePR OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section InstAP.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
Hypothesis BT : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.asan_addrs.
Variable Q : AsAinvDefs3.ast -> Prop.
Hypothesis ASCP : AsIfaceNM3.AsIfacePR3.as_contracts_pr ASEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAllocFFam.AsAinvPrist3.AAINV_QX bt Q) (AsAinvDefs3.bt_fs bt).
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDF) + FTOPc <= FMIN.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound ASEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Let G_imglo : g_img_lo GASAN = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt). Proof. rewrite BT. reflexivity. Qed.
Let G_hi : g_img_hi GASAN = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt). Proof. rewrite BT. reflexivity. Qed.

Theorem hprops_asan_pr : hprops SWIN GASAN (AzBridgeH.SHC_bt bt) (AzBridgePR.AINVH_pr bt Q).
Proof. exact (AzBridgePR.hprops_pr bt Q GASAN G_imglo G_hi asan_G_ro_img2 GA_img_al GA_img_shlo GASAN_errno SWIN SWIN_ok). Qed.

(* [comment removed for export] *)
Lemma strlen_entry_asan_pr_j : forall RZg : GPS.rz_t, GPS.RZ_SILENT1 ASEGS RZg ->
  h_strlen_at ASEGS GASAN fx_ok RZg (AzBridgePR.AINVH_pr bt Q) (AsVocab.AsCells.ia_strlen_icpt (AsAinvDefs3.bt_ia bt)) ->
  h_strlen_at ASEGS GASAN fx_ok RZg (AzBridgePR.AINVH_pr bt Q) (g_strlen GASAN).
Proof.
  intros RZg RZg_silent1. rewrite BT. intros H.
  exact (AzThunk.h_strlen_thunk ASEGS SWIN GASAN fx_ok (AzBridgeH.SHC_bt bt) (AzBridgePR.AINVH_pr bt Q) hprops_asan_pr
           GA_img_pg asan_segs_out asan_segs_wx
           RZg RZg_silent1 (g_strlen GASAN) (AsVocab.AsCells.ia_strlen_icpt AsVocab.AsCells.asan_addrs) asan_thunk_strlen_step H).
Qed.



Theorem gcontracts_core_asan_pr_j : forall RZg : GPS.rz_t, (forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T)) -> GPS.RZ_SILENT1 ASEGS RZg ->
  forall (M0 : word -> option byte),
  gcontracts_core ASEGS IT AASAN nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV RZg GASAN.
Proof.
  intros RZg RZg_kc RZg_silent1 M0.
  refine (AzBridgePR.gcontracts_core_pr_j bt Q ASEGS fx_ok ASCP GASAN G_imglo G_hi asan_G_ro_img2 GA_img_al GA_img_shlo GASAN_priv _ _ _ GASAN_errno
            _ _ _ _ _ _ _ _ _ _ _ GA_newh_img asan_segs_out asan_segs_wx asan_segs_wr asan_rom_ok asan_ro_hi
            SWIN SWIN_ok SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 B0_nonneg C0_nonneg
            FTOPc FTOPc_ok AASAN asan_A_img_hi asan_A_img_lo KCAP GKCAP_le IT IT_ok nx0 FS0 UINV UINV_agree
            RZg RZg_kc RZg_silent1 (strlen_entry_asan_pr_j RZg RZg_silent1));
    rewrite BT; try reflexivity.
  intros z Hz. exact Hz.
Qed.

Theorem gcontracts_core_asan_pr_f : forall (M0 : word -> option byte),
  gcontracts_core ASEGS IT AASAN nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV (realizes ASEGS) GASAN.
Proof. exact (gcontracts_core_asan_pr_j (realizes ASEGS) (AsIface3.AsKInst.kclosedD_realizes ASEGS) (GPS.RZ_SILENT1_realizes ASEGS)). Qed.

Section GlueAP.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
Theorem malloc1_glue_asan_pr_j : forall RZg : GPS.rz_t, (forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T)) ->
  forall (M0 : word -> option byte) args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E cs fx R M model ->
  XAg ASEGS nx0 GASAN bcap ccap 12%nat args cs = Some (csa, csb) ->
  64512 < uE E (reg cs 10) ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok ASEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
        (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E' csb fx' R' M' model' ->
      m_fs model' = m_fs model -> RZg (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
  RZg (cfgF ASEGS fx R (pc cs) M model) Tb.
Proof.
  intros RZg RZg_kc M0.
  refine (AzBridgePR.malloc1_glue_pr_j bt Q ASEGS fx_ok ASCP GASAN G_imglo G_hi asan_G_ro_img2 GA_img_al GA_img_shlo GASAN_priv _ _ _ GASAN_errno
            _ _ GA_newh_img SWIN SWIN_ok SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 FTOPc AASAN asan_A_img_hi asan_A_img_lo KCAP GKCAP_le nx0 FS0 UINV UINV_agree
            bcap ccap bcap_ok ccap_ok RZg RZg_kc);
    rewrite BT; try reflexivity.
  intros z Hz. exact Hz.
Qed.

Theorem malloc1_glue_asan_pr_f : forall (M0 : word -> option byte) args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok ASEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E cs fx R M model ->
  XAg ASEGS nx0 GASAN bcap ccap 12%nat args cs = Some (csa, csb) ->
  64512 < uE E (reg cs 10) ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok ASEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
        (AINV_f SWIN GASAN (AzBridgePR.AINVH_pr bt Q) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E' csb fx' R' M' model' ->
      m_fs model' = m_fs model -> realizes ASEGS (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
  realizes ASEGS (cfgF ASEGS fx R (pc cs) M model) Tb.
Proof. intros M0. exact (malloc1_glue_asan_pr_j (realizes ASEGS) (AsIface3.AsKInst.kclosedD_realizes ASEGS) M0). Qed.
End GlueAP.
End InstAP.
