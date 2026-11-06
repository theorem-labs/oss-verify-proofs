(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section InstBN.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
Hypothesis BT : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.both_addrs.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n BSEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
(* [comment removed for export] *)
Hypothesis ASCNM : AsIfaceNM3.as_contracts_nm BSEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvDefs3.AAINV_H bt) (AsAinvDefs3.bt_fs bt).
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
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
Hypothesis IT_ok : itab_sound BSEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Let G_imglo : g_img_lo GBOTH = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt). Proof. rewrite BT. reflexivity. Qed.
Let G_hi : g_img_hi GBOTH = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt). Proof. rewrite BT. reflexivity. Qed.








(* [comment removed for export] *)
Section GlueB.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
(* [comment removed for export] *)
Theorem malloc1_glue_both_j : forall RZg : GPS.rz_t, (forall T, AsIface3.AsK.kclosedD BSEGS (fun c => RZg c T)) ->
  forall (M0 : word -> option byte) args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok BSEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GBOTH (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E cs fx R M model ->
  XAg BSEGS nx0 GBOTH bcap ccap 12%nat args cs = Some (csa, csb) ->
  AzBridgeM2.fresh_site FRESH HID HIDF B0 C0 E cs M model ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok BSEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
        (AINV_f SWIN GBOTH (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E' csb fx' R' M' model' ->
      m_fs model' = m_fs model -> RZg (cfgF BSEGS fx' R' (pc csb) M' model') Tb) ->
  RZg (cfgF BSEGS fx R (pc cs) M model) Tb.
Proof.
  intros RZg RZg_kc M0.
  refine (AzBridgeM2.malloc1_glue_bt_j bt BSEGS fx_ok FRESH ASC GBOTH G_imglo G_hi both_G_ro_img2 GA_img_al GA_img_shlo GBOTH_priv _ _ _ GBOTH_errno
            _ _ GA_newh_img SWIN SWIN_ok SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok
            FTOPc ABOTH both_A_img_hi both_A_img_lo KCAP GKCAP_le nx0 FS0 UINV UINV_agree RZg RZg_kc);
    rewrite BT; try reflexivity.
  intros z Hz. exact Hz.
Qed.

Theorem malloc1_glue_both_f : forall (M0 : word -> option byte) args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok BSEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GBOTH (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E cs fx R M model ->
  XAg BSEGS nx0 GBOTH bcap ccap 12%nat args cs = Some (csa, csb) ->
  AzBridgeM2.fresh_site FRESH HID HIDF B0 C0 E cs M model ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok BSEGS PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
        (AINV_f SWIN GBOTH (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV E' csb fx' R' M' model' ->
      m_fs model' = m_fs model -> realizes BSEGS (cfgF BSEGS fx' R' (pc csb) M' model') Tb) ->
  realizes BSEGS (cfgF BSEGS fx R (pc cs) M model) Tb.
Proof. intros M0. exact (malloc1_glue_both_j (realizes BSEGS) (AsIface3.AsKInst.kclosedD_realizes BSEGS) M0). Qed.
End GlueB.
End InstBN.
