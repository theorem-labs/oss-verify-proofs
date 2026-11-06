(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeOp OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeOp OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Definition XE0 : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Definition XB0 : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Definition XA0 : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Section OpInst.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
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
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_stkmal : forall k, 0 <= k <= 3 -> g_stkmal G k = AsVocab.AsCells.ia_stkmal IA k.
Hypothesis G_amemcpy : g_amemcpy G = AsVocab.AsCells.ia_asan_memcpy IA.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Hypothesis SEGS_in_hull_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).          (* [comment removed for export] *)
Variable HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDF) + FTOPc <= FMIN.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis HULL_ok : APS.hull_ok A.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable KC : nat.
Variable FS0 : Fs.Fs.
Variable HS : nat -> option acs.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
(* [comment removed for export] *)
Variable n_e : Z.
Variable nv mv : nat.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Hypothesis HNBF : AzNodesAlloc3.NBF UINV bcap ccap nv mv.
Hypothesis HSIZE : forall E, UINV E -> uE E (EVar nv) = n_e.

#[local] Notation AINVHop := (AzBridgeOp.AINVH_op_bt bt n_e HID).
Definition AINV_op := AINV_f SWIN G AINVHop PERMc SPTOPc HID HIDF M0 B0 C0.
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).
#[local] Notation SHCb := (AzBridgeH.SHC_bt bt).
Let HPop := AzBridgeOp.hprops_op_bt bt SWIN G G_imglo G_hi G_ro_img G_img_al G_errno_img SWIN_ok G_img_shlo n_e HID.

Definition NOKh (n : Z) (L : list (Z * Z)) : Prop := n = n_e /\ L = HID.
Definition NOKn (n : Z) (Lc : list (Z * Z)) : Prop := n = n_e /\ Lc = [].
Lemma NOK_frame : forall n Lc, NOKn n Lc -> NOKh n (Lc ++ HID).
Proof. intros n Lc [-> ->]. split; reflexivity. Qed.
Lemma HNOK : forall E, UINV E -> NOKn (uE E (EVar nv)) [].
Proof. intros E HU. split; [exact (HSIZE E HU) | reflexivity]. Qed.

Lemma SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Proof.
  intros a Ha. apply SEGS_in_hull_out. unfold APS.in_hull in Ha. rewrite A_img_hi, A_img_lo in Ha.
  intros [H1 H2]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in Ha. discriminate Ha.
Qed.
(* [comment removed for export] *)
Lemma ASCL : AsIfaceNM3.as_contracts_n SEGS FXOK IA (AzBridgeH.AAINV_HL bt) FRESH (AsAinvDefs3.bt_fs bt).
Proof.
  apply (AzBridgeH.as_contracts_HL bt G G_hi G_img_shlo SEGS FXOK FRESH); [| | exact ASC].
  - intros z Hz. destruct (G_privs z Hz) as (lo & hi & Hin & Hr). destruct (G_priv lo hi Hin) as [_ P2]. rewrite <- G_hi. lia.
  - rewrite <- G_errno, <- G_hi. exact (proj2 G_errno_img).
Qed.


#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV).

Lemma XE0_sound : forall RZ, GPS.emit_stmt SEGS nx0 XE0 PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV RZ.
Proof. intros RZ id args cs fd ps cs' E fx R M model T _ Hn. discriminate Hn. Qed.
Lemma XA0_sound : forall RZ, GPS.alt2_stmt SEGS nx0 XA0 PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV RZ.
Proof. intros RZ id args cs csa csb E fx R M model Ta Tb _ Hn. discriminate Hn. Qed.
Lemma XT0_sound : forall RZ, GPS.term_stmt SEGS AP.XT0 PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV RZ.
Proof. intros RZ id args cs fd ps code E fx R M model _ Hn. discriminate Hn. Qed.
Lemma XB0_sound : forall RZ, GPS.ext2_stmt SEGS nx0 XB0 PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV RZ.
Proof. intros RZ id args cs csa csb E fx R M model T _ Hn. discriminate Hn. Qed.





Lemma RZ_silent1_rz : GPS.RZ_SILENT1 SEGS (realizes SEGS).
Proof. exact (GPS.RZ_SILENT1_realizes SEGS). Qed.
Lemma RZ_exit_rz : GPS.RZ_EXIT SEGS (realizes SEGS).
Proof. exact (GPS.RZ_EXIT_realizes SEGS). Qed.
Lemma RZ_conseq_rz : GPS.RZ_CONSEQ (realizes SEGS).
Proof. exact (GPS.RZ_CONSEQ_realizes SEGS). Qed.

(* [comment removed for export] *)
Section Live.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
Hypothesis HOLES_same : forall h E fs, HOLES h E fs = HOLES 0%nat E fs.

Definition XNl := AzOpNewH.XN_live SEGS G nx0 nv mv.

(* [comment removed for export] *)
Section GenRZ.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 SEGS RZg.
Hypothesis RZg_exit : GPS.RZ_EXIT SEGS RZg.
Hypothesis RZg_conseq : GPS.RZ_CONSEQ RZg.
Hypothesis HS_sound_j : GPS.holes_stmt SEGS HS PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV HOLES RZg.

Lemma XNl_sound_j : GPS.ext_stmt SEGS nx0 XNl PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV RZg.
Proof.
  destruct ASCL as [Wk0 Mk Mkt Ma Mat Fr Frt Od Ods Sk Frl Mc Amc Ms Ams Mm Amm Sl].
  refine (AzOpNewH.XN_live_sound SEGS SWIN G FXOK SHCb AINVHop HPop G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZg
            AzBridgeC3.FPCw AzBridgeC3.fpc_kfpc_w PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok FTOPc A A_img_hi A_img_lo G_newh_img
            KCAP GKCAP_le nx0 FS0 UINV UINV_agree NOKh NOKn NOK_frame nv mv HNBF HNOK _).
  rewrite G_malloc_thunk.
  exact (AzBridgeC3.h_malloc_live_wj SEGS IA FXOK (AzBridgeH.AAINV_HL bt) G G_imglo G_hi G_ro_img G_tp G_errno G_privs RZg RZg_kc n_e HID _ _ Mkt).
Qed.

Theorem op_check_sound_live_j : forall fuel bfuel lc p cs s,
  gplan_ok p = true ->
  AP.checkA SEGS IT A nx0 LIMIT GPS.ISP0 XNl XE0 XB0 XA0 AP.XT0 HS KC false bfuel fuel lc cs p = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model ->
    GPS.LCOK SEGS nx0 PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV HOLES RZg lc D E (m_fs model) -> D [] ->
    RZg (cfgF SEGS fx R (pc cs) M model) (GPS.sd HOLES D E (m_fs model) s).
Proof.
  intros fuel bfuel lc p cs s Hg Hc E fx R M model D HC HL HD.
  exact (GPS.check_soundA SEGS IT IT_ok A nx0 LIMIT HS XNl XE0 XB0 XA0 AP.XT0 KC SWIN PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc
           (AINV_f_frame SWIN G SHCb AINVHop HPop G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF M0 B0 C0)
           (AINV_f_lazy SWIN G SHCb AINVHop HPop PERMc SPTOPc HID HIDF M0 B0 C0)
           (AzFrameAlloc.If_facts SWIN G SHCb PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo AINVHop HPop)
           FXOK UINV UINV_agree HOLES HOLES_agree HOLES_nil HOLES_same RZg RZg_silent1 RZg_exit RZg_conseq RUN SEGS_in_hull HULL_ok SEGS_wx
           XNl_sound_j (XE0_sound RZg) (XB0_sound RZg) (XA0_sound RZg) (XT0_sound RZg) HS_sound_j
           fuel bfuel lc p cs s Hg Hc E fx R M model D HC HL HD).
Qed.
End GenRZ.

(* [comment removed for export] *)
Hypothesis HS_sound : GPS.holes_stmt SEGS HS PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV HOLES (rrealizes SEGS).



Hypothesis HS_sound_f : GPS.holes_stmt SEGS HS PERMc SPTOPc FS0 SHCb VSHf AINV_op KCAP FTOPc FXOK UINV HOLES (realizes SEGS).


End Live.
End OpInst.
