(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

Section Inst.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable bt : AsAinvDefs3.as_boot.
#[local] Notation IA := (AsAinvDefs3.bt_ia bt).
Variable SEGS : list Segment.
Variable FXOK : FX -> Prop.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n SEGS FXOK IA (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
(* [comment removed for export] *)
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis G_privs : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> in_wins (g_priv G) z.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.
Hypothesis G_errno : g_errno G = AsVocab.ia_errno IA.   (* [comment removed for export] *)
Hypothesis G_errno_img : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
Hypothesis G_malloc : g_malloc G = AsVocab.AsCells.ia_malloc IA.
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_free : g_free G = AsVocab.AsCells.ia_free IA.
Hypothesis G_free_thunk : g_free_thunk G = AsVocab.AsCells.ia_free_thunk IA.
Hypothesis G_opdel : g_opdel G = AsVocab.AsCells.ia_opdel IA.
Hypothesis G_opdel_sized : g_opdel_sized G = AsVocab.AsCells.ia_opdel_sz IA.
Hypothesis G_stkmal : forall k, 0 <= k <= 3 -> g_stkmal G k = AsVocab.AsCells.ia_stkmal IA k.
Hypothesis G_memcpy : g_memcpy G = AsVocab.AsCells.ia_memcpy_icpt IA.
Hypothesis G_amemcpy : g_amemcpy G = AsVocab.AsCells.ia_asan_memcpy IA.
Hypothesis G_memset : g_memset G = AsVocab.AsCells.ia_memset_icpt IA.
Hypothesis G_amemset : g_amemset G = AsVocab.AsCells.ia_asan_memset IA.
Hypothesis G_memmove : g_memmove G = AsVocab.AsCells.ia_memmove_icpt IA.
Hypothesis G_amemmove : g_amemmove G = AsVocab.AsCells.ia_asan_memmove IA.
Hypothesis H_strlen_entry :   (* [comment removed for export] *)
  h_strlen_at SEGS G FXOK (rrealizes SEGS) (AzBridgeH.AINVH_bt bt) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (rrealizes SEGS) (AzBridgeH.AINVH_bt bt) (g_strlen G).
Hypothesis H_strlen_entry_f :   (* [comment removed for export] *)
  h_strlen_at SEGS G FXOK (realizes SEGS) (AzBridgeH.AINVH_bt bt) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (realizes SEGS) (AzBridgeH.AINVH_bt bt) (g_strlen G).
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Hypothesis G_opnew_kn_wf : opnew_kn_wf G = true.   (* [comment removed for export] *)
Hypothesis SEGS_in_hull_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= u x -> u x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.
(* [comment removed for export] *)
Hypothesis OPNEW : h_alloc1_at SEGS G FXOK (rrealizes SEGS) (AzBridgeH.AINVH_bt bt) (AzBridgeC3.FPCw)
                     (hopnew_x SEGS G) MSTK_N (g_opnew G).
Hypothesis OPNEW_f : h_alloc1_at SEGS G FXOK (realizes SEGS) (AzBridgeH.AINVH_bt bt) (AzBridgeC3.FPCw)   (* [comment removed for export] *)
                     (hopnew_x SEGS G) MSTK_N (g_opnew G).
(* [comment removed for export] *)
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
Hypothesis FTOPc_ok : Z.of_nat (length HIDF) + FTOPc <= FMIN.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Definition AINV_bt := AINV_f SWIN G (AzBridgeH.AINVH_bt bt) PERMc SPTOPc HID HIDF M0 B0 C0.
Definition AINVN_bt (n : Z) := AINV_f SWIN G (AzBridgeH.AINVHN_bt bt n) PERMc SPTOPc HID HIDF M0 B0 C0.

(* [comment removed for export] *)
Lemma FF_classes_bt : forall h L FF B C K M mdl f k, AzBridgeH.AAINV_HL bt h L FF B C K M mdl -> In (f, k) FF -> 0 <= k.
Proof.
  intros h L FF B C K M mdl f k [HA _] Hin.
  pose proof (AsVocab.aap_fzone _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt h)) L FF B C K M mdl f k HA Hin) as (X & _). lia.
Qed.

(* [comment removed for export] *)
Lemma ASCL : AsIfaceNM3.as_contracts_n SEGS FXOK IA (AzBridgeH.AAINV_HL bt) FRESH (AsAinvDefs3.bt_fs bt).
Proof.
  apply (AzBridgeH.as_contracts_HL bt G G_hi G_img_shlo SEGS FXOK FRESH); [| | exact ASC].
  - intros z Hz. destruct (G_privs z Hz) as (lo & hi & Hin & Hr). destruct (G_priv lo hi Hin) as [_ P2]. rewrite <- G_hi. lia.
  - rewrite <- G_errno, <- G_hi. exact (proj2 G_errno_img).
Qed.

Lemma SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Proof.
  intros a Ha. apply SEGS_in_hull_out. unfold APS.in_hull in Ha. rewrite A_img_hi, A_img_lo in Ha.
  intros [H1 H2]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in Ha. discriminate Ha.
Qed.


(* [comment removed for export] *)
Section GenRZ.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 SEGS RZg.
Hypothesis H_strlen_entry_j :
  h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVH_bt bt) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVH_bt bt) (g_strlen G).
Hypothesis OPNEW_j : h_alloc1_at SEGS G FXOK RZg (AzBridgeH.AINVH_bt bt) (AzBridgeC3.FPCw) (hopnew_x SEGS G) MSTK_N (g_opnew G).
Theorem gcontracts_bt_j :
  gcontracts SEGS IT A nx0 PERMc SPTOPc FS0 (AzBridgeH.SHC_bt bt) (AzFrame.VSHf HID HIDF) AINV_bt KCAP FTOPc FXOK UINV RZg G bcap ccap.
Proof.
  unfold AINV_bt.
  exact (AzFrameAlloc.gcontracts_f SEGS SWIN G FXOK (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVH_bt bt) (AzBridgeH.AINVHN_bt bt)
           (AzBridgeH.hprops_bt bt SWIN G G_imglo G_hi G_ro_img G_img_al G_errno_img SWIN_ok G_img_shlo)
           G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZg AzBridgeC3.FPCw PERMc SPTOPc HID HIDF M0 B0 C0
           B0_nonneg C0_nonneg bcap ccap bcap_ok ccap_ok FTOPc FTOPc_ok A A_img_hi A_img_lo SEGS_in_hull SEGS_wx SEGS_wr SEGS_in_hull_out ROM_ok
           RO_hi G_newh_img G_opnew_kn_wf KCAP GKCAP_le IT IT_ok nx0 FS0 UINV UINV_agree RZg_silent1 AzBridgeC3.fpc_kfpc_w
           (AzBridgeC3.FRESHw FRESH)
           (AzBridgeC3.hcontracts_core_of_as_j SEGS IA FXOK (AzBridgeH.AAINV_HL bt) FRESH (AsAinvDefs3.bt_fs bt) ASCL G G_imglo G_hi G_ro_img G_tp G_errno G_privs
              G_malloc G_malloc_thunk G_free G_free_thunk G_opdel G_opdel_sized G_stkmal FF_classes_bt RZg RZg_kc)
           (AzBridgeC3.lcontracts_of_as_j SEGS IA FXOK (AzBridgeH.AAINV_HL bt) FRESH (AsAinvDefs3.bt_fs bt) ASCL G G_imglo G_hi G_ro_img G_tp
              SWIN SWIN_ok G_memcpy G_amemcpy G_memset G_amemset G_memmove G_amemmove RZg RZg_kc H_strlen_entry_j)
           OPNEW_j).   (* [comment removed for export] *)
Qed.
End GenRZ.


End Inst.
