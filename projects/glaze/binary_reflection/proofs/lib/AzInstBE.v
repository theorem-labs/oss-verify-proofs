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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstB OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section SHC.
Context {RC : run_ceil}.
Variable bt : AsAinvDefs3.as_boot.

(* [comment removed for export] *)
Lemma SHC_bt_stack : forall z, SB + GlzConst.RunCeil.CEIL / 8 <= z -> z <= SB + (2 ^ 47 - 1) / 8 -> GPS.in_shc (AzBridgeH.SHC_bt bt) z = true.
Proof.
  intros z H1 H2. unfold GPS.in_shc, AzBridgeH.SHC_bt, AzBridgeH.SHCw, AsVocab.SHC. apply existsb_exists.
  exists (AsVocab.sh_lo GlzConst.RunCeil.CEIL, AsVocab.SB + 2 ^ 44). split; [left; reflexivity|]. cbn [fst snd].
  unfold AsVocab.sh_lo, AsVocab.SB. unfold SB in H1, H2.
  change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in H2.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma SHC_bt_img : forall A : atable,
  img_lo A = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt) -> img_hi A = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) ->
  forall z, SB + img_lo A / 8 <= z -> z <= SB + (img_hi A - 1) / 8 -> GPS.in_shc (AzBridgeH.SHC_bt bt) z = true.
Proof.
  intros A Hlo Hhi z H1 H2. unfold GPS.in_shc, AzBridgeH.SHC_bt, AzBridgeH.SHCw, AsVocab.SHC. apply existsb_exists.
  exists (AsVocab.sh_lo (AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt)),
          AsVocab.sh_hi (AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt)) (AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) - AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt))).
  split; [right; left; reflexivity|]. cbn [fst snd]. rewrite Hlo, Hhi in *.
  unfold AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB. unfold SB in H1, H2.
  replace (AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt) + (AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) - AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt)) + 7)
    with (AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) + 7) by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma SHC_bt_img_both : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.both_addrs ->
  forall A : atable, img_lo A = AsVocab.AsCells.ia_img_lo AsVocab.AsCells.both_addrs -> img_hi A = AsVocab.AsCells.ia_img_hi AsVocab.AsCells.both_addrs ->   (* [comment removed for export] *)
  forall z, SB + img_lo A / 8 <= z -> z <= SB + (img_hi A - 1) / 8 -> GPS.in_shc (AzBridgeH.SHC_bt bt) z = true.
Proof. intros BT A Hlo Hhi. apply SHC_bt_img; rewrite BT; assumption. Qed.
End SHC.

Section GCall.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
Hypothesis BT : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.both_addrs.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n BSEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
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
Hypothesis IT_ok : itab_sound BSEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.


Theorem gcontracts_both_all_f : forall M0 : word -> option byte,
  gcontracts BSEGS IT ABOTH nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF)
    (AINV_f SWIN GBOTH (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0) KCAP FTOPc fx_ok UINV (realizes BSEGS) GBOTH bcap ccap.
Proof.
  intros M0.
  exact (gcontracts_both_f bt BT FRESH ASC SWIN SWIN_ok SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 B0_nonneg C0_nonneg bcap ccap bcap_ok ccap_ok
           FTOPc FTOPc_ok KCAP GKCAP_le IT IT_ok nx0 FS0 UINV UINV_agree).
Qed.
End GCall.
