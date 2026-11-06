(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Section HNM.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable RZ : GPS.rz_t.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
Record hcontracts_nm : Prop := HNMC {
  hnm_free : h_free_at SEGS G FXOK RZ AINVH FPC MSTK_A (g_free G);
  hnm_free_thunk : h_free_at SEGS G FXOK RZ AINVH FPC MSTK_A (g_free_thunk G);
  hnm_opdel : h_free_at SEGS G FXOK RZ AINVH FPC MSTK_A (g_opdel G);
  hnm_opdel_sized : h_free_at SEGS G FXOK RZ AINVH FPC MSTK_A (g_opdel_sized G);
  hnm_stkmal : forall k, 0 <= k <= 3 -> h_stkmal SEGS G FXOK RZ AINVH k;
  hnm_fakerel : h_fakerel SEGS G FXOK RZ AINVH
}.
End HNM.

Section FrameAllocNM.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable RZ : GPS.rz_t.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
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
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= u x -> u x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.
Hypothesis HNM : hcontracts_nm SEGS G FXOK RZ AINVH FPC.
Hypothesis LC : lcontracts SEGS SWIN G FXOK RZ AINVH.

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).
(* [comment removed for export] *)
Let If_ifacts := AzFrameAlloc.If_ifacts SWIN G SHC G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0.
Let If_disj := AzFrameAlloc.If_disj SWIN G SHC PERMc SPTOPc HID HIDF M0 B0 C0.
Let If_perm_apart := AzFrameAlloc.If_perm_apart SWIN G SHC G_ro_img G_img_al G_img_shlo SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0.
Let If_perm_mem := AzFrameAlloc.If_perm_mem SWIN G SHC G_ro_img G_img_al G_img_shlo SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0.
Let free_nspec_f := AzFrameAlloc.free_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZ FPC PERMc SPTOPc HID HIDF M0 B0 C0 B0_nonneg C0_nonneg.
Let copy_nspec_f := AzFrameAlloc.copy_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0.
Let fill_nspec_f := AzFrameAlloc.fill_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0.
Let move_nspec_f := AzFrameAlloc.move_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0.
Let strlen_nspec_f := AzFrameAlloc.strlen_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0.
Let stkmal_nspec_f := AzFrameAlloc.stkmal_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0 FTOPc FTOPc_ok.
Let fakerel_nspec_f := AzFrameAlloc.fakerel_nspec_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al SWIN_img RZ PERMc SPTOPc HID HIDF M0 B0 C0.
Let FTOPc_small := AzFrameAlloc.FTOPc_small G G_img_al HIDF FTOPc FTOPc_ok.

Let HI := If_ifacts A A_img_hi A_img_lo AINVH HP.
Let SHC_stack := hp_shc_stack _ _ _ _ HP.
Let SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true := hp_shc_image _ _ _ _ HP.
Let SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G :=
  fun lo hi Hin => match SWIN_img lo hi Hin with conj S1 (conj S2 _) => conj (Z.le_trans _ _ _ (Z.le_trans _ _ _ (proj1 G_ro_img) (proj1 (proj2 G_ro_img))) S1) S2 end.
Let G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G :=
  conj (proj1 G_img_al) (conj (proj1 G_ro_img) (Z.le_trans _ _ _ (proj1 (proj2 G_ro_img)) (proj2 (proj2 G_ro_img)))).
Let G_img_ceil := AzFrame.G_img_ceil G G_img_al G_img_shlo.
Let G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Proof. pose proof (hp_errno _ _ _ _ HP). pose proof G_ro_img. lia. Qed.
Let G_ro_img' : g_ro_lo G <= g_ro_hi G <= g_img_hi G := proj2 G_ro_img.

Theorem gcontracts_core_nm :
  gcontracts_core SEGS IT A nx0 PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ G.
Proof.
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  constructor.
  - (* [comment removed for export] *)
    exact (node_imgload_sound SEGS IT IT_ok nx0 SWIN PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc
             (AINV_f_frame SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HID HIDF M0 B0 C0)
             (AINV_f_lazy SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF M0 B0 C0)
             A I1 SEGS_in_hull SEGS_wx FXOK UINV UINV_agree RZ RZ_silent1 G ROM_ok RO_hi).
  - (* [comment removed for export] *)
    exact (node_free_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hnm_free_thunk _ _ _ _ _ _ HNM))
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hnm_free _ _ _ _ _ _ HNM))).
  - (* [comment removed for export] *)
    exact (node_blkfact_obl SEGS nx0 PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV RZ G
             I7 (If_disj AINVH HP) (If_perm_apart AINVH HP) I4 I6 G_img_hull G_img_ceil).
  - (* [comment removed for export] *)
    exact (node_opdel_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hnm_opdel _ _ _ _ _ _ HNM))).
  - (* [comment removed for export] *)
    exact (node_opdel_sized_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc G_newh_img
             (free_nspec_f MSTK_A _ ltac:(unfold MSTK_A; lia) (hnm_opdel_sized _ _ _ _ _ _ HNM))).
  - (* [comment removed for export] *)
    exact (node_memcpy_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (copy_nspec_f _ (lc_memcpy _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_memset_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (fill_nspec_f _ (lc_memset _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_memmove_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (move_nspec_f _ (lc_memmove _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_strlen_obl SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6 G_ro_img'
             (strlen_nspec_f _ (lc_strlen _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemcpy_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (copy_nspec_f _ (lc_amemcpy _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemset_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (fill_nspec_f _ (lc_amemset _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_amemmove_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             I1 A_img_hi A_img_lo SEGS_in_hull SEGS_wr I2 I3 I4 SHC_stack SHC_image SWIN_img' SEGS_out G_img_ceil G_errno_img G_img_shlo G_img_hull I7 I5 I6
             (If_perm_mem AINVH HP) (move_nspec_f _ (lc_amemmove _ _ _ _ _ _ LC))).
  - (* [comment removed for export] *)
    exact (node_stkmal_all_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img G_newh_img
             (fun k Hk => stkmal_nspec_f k (hnm_stkmal _ _ _ _ _ _ HNM k Hk))).
  - (* [comment removed for export] *)
    exact (node_fakerel_obl SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ RZ_silent1 G
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_errno_img G_newh_img
             (AINV_f_lazy SWIN G SHC AINVH HP PERMc SPTOPc HID HIDF M0 B0 C0) SEGS_in_hull SEGS_wx FTOPc_small IT IT_ok
             (fakerel_nspec_f (hnm_fakerel _ _ _ _ _ _ HNM))).
Qed.
End FrameAllocNM.
