(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

Section GlueBt.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
#[local] Notation IA := (AsAinvDefs3.bt_ia bt).
Variable SEGS : list Segment.
Variable FXOK : FX -> Prop.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n SEGS FXOK IA (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis G_privs : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> in_wins (g_priv G) z.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.
Hypothesis G_errno : g_errno G = AsVocab.ia_errno IA.
Hypothesis G_errno_img : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Hypothesis G_malloc : g_malloc G = AsVocab.AsCells.ia_malloc IA.
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
Variable FTOPc : Z.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

#[local] Notation AINV_bt := (AzBridgeE3.AINV_bt bt G SWIN PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation AINVN_bt := (AzBridgeE3.AINVN_bt bt G SWIN PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation SHCb := (AzBridgeH.SHC_bt bt).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

(* [comment removed for export] *)
Definition fresh_site (E : env) (cs : acs) (M : word -> option byte) (model : Model) : Prop :=
  exists FF, blocks_den E (a_fake cs) ++ HIDF = map AzBridgeH.wfr FF
             /\ FRESH (blocks_den E (a_vis cs) ++ HID) FF (B0 + bcost E (a_vis cs)) (C0 + bcount (a_vis cs)) (uE E (a_meter cs)) M model (uE E (reg cs 10)).

Let HPb := AzBridgeH.hprops_bt bt SWIN G G_imglo G_hi G_ro_img G_img_al G_errno_img SWIN_ok G_img_shlo.
Let HPNb := fun n => AzBridgeH.hpropsN_bt bt SWIN G G_imglo G_hi G_ro_img G_img_al G_errno_img SWIN_ok G_img_shlo n.
Let ASCL : AsIfaceNM3.as_contracts_n SEGS FXOK IA (AzBridgeH.AAINV_HL bt) FRESH (AsAinvDefs3.bt_fs bt) :=
  AzBridgeE3.ASCL bt SEGS FXOK FRESH ASC G G_hi G_img_al G_img_shlo G_priv G_privs G_errno G_errno_img G_newh_img HIDF.
Let FFc := AzBridgeE3.FF_classes_bt bt G HIDF.
Let SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G :=
  fun lo hi Hin => match SWIN_img lo hi Hin with conj S1 (conj S2 _) => conj (Z.le_trans _ _ _ (Z.le_trans _ _ _ (proj1 G_ro_img) (proj1 (proj2 G_ro_img))) S1) S2 end.
Let G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G :=
  conj (proj1 G_img_al) (conj (proj1 G_ro_img) (Z.le_trans _ _ _ (proj1 (proj2 G_ro_img)) (proj2 (proj2 G_ro_img)))).
Let G_errno_img' : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Proof. pose proof G_ro_img. lia. Qed.

Section GenRZ.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Theorem malloc1_glue_bt_j : forall args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_bt KCAP FTOPc FXOK UINV E cs fx R M model ->
  XAg SEGS nx0 G bcap ccap 12%nat args cs = Some (csa, csb) ->
  fresh_site E cs M model ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_bt KCAP FTOPc FXOK UINV E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
      RZg (cfgF SEGS fx' R' (pc csb) M' model') Tb) ->
  RZg (cfgF SEGS fx R (pc cs) M model) Tb.
Proof.
  intros args cs csa csb E fx R M model Tb HC Hn (FF & HFF & HFR) HTb Kok.
  destruct ASCL as [Wk Mk Mkt Ma Mat Fr Frt Od Ods Sk Frl Mc Amc Ms Ams Mm Amm Sl].
  pose proof (AzBridgeC3.h_malloc1_wj SEGS IA FXOK (AzBridgeH.AAINV_HL bt) FRESH G G_imglo G_hi G_ro_img G_tp G_errno G_privs FFc RZg RZg_kc MSTK_A _ Ma) as H2.
  pose proof (AzBridgeC3.h_malloc1_wj SEGS IA FXOK (AzBridgeH.AAINV_HL bt) FRESH G G_imglo G_hi G_ro_img G_tp G_errno G_privs FFc RZg RZg_kc MSTK_A _ Mat) as H2t.
  rewrite <- G_malloc in H2. rewrite <- G_malloc_thunk in H2t.
  pose proof (AzFrameAlloc.malloc1_nspec_f SEGS SWIN G FXOK SHCb (AzBridgeH.AINVH_bt bt) HPb
                G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZg AzBridgeC3.FPCw PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok
                (AzBridgeC3.FRESHw FRESH) MSTK_A) as NS.
  pose proof (NS (g_malloc G) ltac:(unfold MSTK_A; lia) H2) as NSm.
  pose proof (NS (g_malloc_thunk G) ltac:(unfold MSTK_A; lia) H2t) as NSt.
  refine (AzNodesAlloc3.node_malloc1_glue SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHCb VSHf AINV_bt KCAP FXOK UINV UINV_agree
            RZg G bcap ccap AzBridgeC3.FPCw
            (AzFrameAlloc.If_ifacts SWIN G SHCb G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo (AzBridgeH.AINVH_bt bt) HPb)
            A_img_hi A_img_lo (hp_shc_stack _ _ _ _ HPb) (hp_shc_image _ _ _ _ HPb) SWIN_img' G_img_hull
            (AzFrame.G_img_ceil G G_img_al G_img_shlo) G_errno_img' GKCAP_le AzBridgeC3.fpc_kfpc_w
            (AzFrameAlloc.FRESHf HID HIDF B0 C0 (AzBridgeC3.FRESHw FRESH))
            args cs csa csb E fx R M model Tb NSt NSm HC Hn _ HTb Kok).
  unfold AzFrameAlloc.FRESHf, AzBridgeC3.FRESHw. exists FF. split; [exact HFF | exact HFR].
Qed.
End GenRZ.



End GlueBt.
