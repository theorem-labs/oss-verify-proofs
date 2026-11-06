(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAllocNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAllocNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

Section InstNM.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
#[local] Notation IA := (AsAinvDefs3.bt_ia bt).
Variable SEGS : list Segment.
Variable FXOK : FX -> Prop.
Hypothesis ASCNM : AsIfaceNM3.as_contracts_nm SEGS FXOK IA (AsAinvDefs3.AAINV_H bt) (AsAinvDefs3.bt_fs bt).   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Hypothesis H_strlen_entryN : forall n,
  h_strlen_at SEGS G FXOK (rrealizes SEGS) (AzBridgeH.AINVHW_bt bt n) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (rrealizes SEGS) (AzBridgeH.AINVHW_bt bt n) (g_strlen G).
Hypothesis H_strlen_entryN_f : forall n,   (* [comment removed for export] *)
  h_strlen_at SEGS G FXOK (realizes SEGS) (AzBridgeH.AINVHW_bt bt n) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (realizes SEGS) (AzBridgeH.AINVHW_bt bt n) (g_strlen G).
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Hypothesis SEGS_in_hull_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= u x -> u x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.
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



#[local] Notation HWZ := (AzBridgeH.HW_zone bt).




(* [comment removed for export] *)
Section GenRZ1.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).

End GenRZ1.



(* [comment removed for export] *)
Section GenRZ2.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis H_strlen_entryN_j : forall n,
  h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVHW_bt bt n) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVHW_bt bt n) (g_strlen G).

End GenRZ2.




(* [comment removed for export] *)
Section GenRZ3.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 SEGS RZg.
Hypothesis H_strlen_entryN_j : forall n,
  h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVHW_bt bt n) (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg (AzBridgeH.AINVHW_bt bt n) (g_strlen G).

End GenRZ3.



End InstNM.
