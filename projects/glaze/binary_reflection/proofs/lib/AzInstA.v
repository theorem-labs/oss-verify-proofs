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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopA OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewTopA OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Lemma GA_img_pg : g_img_lo GASAN mod 4096 = 0 /\ g_img_hi GASAN mod 4096 = 0.
Proof. split; reflexivity. Qed.


Section InstA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
Hypothesis BT : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.asan_addrs.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n ASEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
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
Let HPbt := AzBridgeH.hprops_bt bt SWIN GASAN G_imglo G_hi asan_G_ro_img2 GA_img_al GASAN_errno SWIN_ok GA_img_shlo.

(* [comment removed for export] *)
Section GenRZ.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 ASEGS RZg.
Hypothesis RZg_exit : GPS.RZ_EXIT ASEGS RZg.
Hypothesis RZg_conseq : GPS.RZ_CONSEQ RZg.

Lemma strlen_entry_asan_j :
  h_strlen_at ASEGS GASAN fx_ok RZg (AzBridgeH.AINVH_bt bt) (AsVocab.AsCells.ia_strlen_icpt (AsAinvDefs3.bt_ia bt)) ->
  h_strlen_at ASEGS GASAN fx_ok RZg (AzBridgeH.AINVH_bt bt) (g_strlen GASAN).
Proof.
  rewrite BT. intros H.
  exact (AzThunk.h_strlen_thunk ASEGS SWIN GASAN fx_ok (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVH_bt bt) HPbt GA_img_pg asan_segs_out asan_segs_wx
           RZg RZg_silent1 (g_strlen GASAN) (AsVocab.AsCells.ia_strlen_icpt AsVocab.AsCells.asan_addrs) asan_thunk_strlen_step H).
Qed.

Theorem gcontracts_asan_j :
  gcontracts ASEGS IT AASAN nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AzBridgeE3.AINV_bt bt GASAN SWIN PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV RZg GASAN bcap ccap.
Proof.
  refine (AzBridgeE3.gcontracts_bt_j bt ASEGS fx_ok FRESH ASC GASAN G_imglo G_hi asan_G_ro_img2 GA_img_al GA_img_shlo GASAN_priv _ _ _ GASAN_errno
            _ _ _ _ _ _ _ _ _ _ _ _ _ GA_newh_img GA_opnew_kn_wf asan_segs_out asan_segs_wx asan_segs_wr asan_rom_ok asan_ro_hi
            SWIN SWIN_ok SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 B0_nonneg C0_nonneg bcap ccap bcap_ok ccap_ok
            FTOPc FTOPc_ok AASAN asan_A_img_hi asan_A_img_lo KCAP GKCAP_le IT IT_ok nx0 FS0 UINV UINV_agree
            RZg RZg_kc RZg_silent1 strlen_entry_asan_j (opnew_h_asan_j bt FRESH BT ASC RZg RZg_kc RZg_silent1 RZg_exit RZg_conseq));
    rewrite BT; try reflexivity.
  intros z Hz. exact Hz.
Qed.

End GenRZ.



Theorem gcontracts_asan_f :
  gcontracts ASEGS IT AASAN nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AzBridgeE3.AINV_bt bt GASAN SWIN PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV (realizes ASEGS) GASAN bcap ccap.
Proof. exact (gcontracts_asan_j (realizes ASEGS) (AsIface3.AsKInst.kclosedD_realizes ASEGS) (GPS.RZ_SILENT1_realizes ASEGS) (GPS.RZ_EXIT_realizes ASEGS) (GPS.RZ_CONSEQ_realizes ASEGS)). Qed.


End InstA.
