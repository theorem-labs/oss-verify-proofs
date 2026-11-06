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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section OpHooks.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
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
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
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
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable NOK : Z -> list (Z * Z) -> Prop.     (* [comment removed for export] *)
Variable NOKn : Z -> list (Z * Z) -> Prop.    (* [comment removed for export] *)
Hypothesis NOK_frame : forall n Lc, NOKn n Lc -> NOK n (Lc ++ HID).
Variable nv mv : nat.
Hypothesis HNBF : AzNodesAlloc3.NBF UINV bcap ccap nv mv.
Hypothesis HNOK : forall E, UINV E -> NOKn (uE E (EVar nv)) [].
#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

Let HI := AzFrameAlloc.If_ifacts SWIN G SHC G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo AINVH HP.
Let SHC_stack := hp_shc_stack _ _ _ _ HP.
Let SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true := hp_shc_image _ _ _ _ HP.
Let SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G :=
  fun lo hi Hin => match SWIN_img lo hi Hin with conj S1 (conj S2 _) => conj (Z.le_trans _ _ _ (Z.le_trans _ _ _ (proj1 G_ro_img) (proj1 (proj2 G_ro_img))) S1) S2 end.
Let G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G :=
  conj (proj1 G_img_al) (conj (proj1 G_ro_img) (Z.le_trans _ _ _ (proj1 (proj2 G_ro_img)) (proj2 (proj2 G_ro_img)))).
Let G_img_ceil := AzFrame.G_img_ceil G G_img_al G_img_shlo.
Let G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Proof. pose proof (hp_errno _ _ _ _ HP). pose proof G_ro_img. lia. Qed.

(* [comment removed for export] *)
Definition XN_live (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 120%nat => node_alloc_nb SEGS nx0 G MSTK_A (g_malloc_thunk G) nv mv cs
  | _ => None
  end.

Theorem XN_live_sound :
  h_malloc_live_on SEGS NOK G FXOK RZ AINVH FPC MSTK_A (g_malloc_thunk G) ->
  GPS.ext_stmt SEGS nx0 XN_live PERMc SPTOPc FS0 SHC VSHf AINVf KCAP FTOPc FXOK UINV RZ.
Proof.
  intros HML id args.
  destruct (Nat.eq_dec id 120) as [->|Hne].
  - cbn [XN_live].
    exact (node_alloc_nb_live_sound SEGS NOKn A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSHf AINVf KCAP FXOK UINV UINV_agree RZ G bcap ccap FPC
             HI A_img_hi A_img_lo SHC_stack SHC_image SWIN_img' G_img_hull G_img_ceil G_errno_img GKCAP_le FPC_kfpc nv mv HNBF HNOK
             (malloc_nspec_live_f_on SEGS NOK NOKn SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZ FPC
                PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok NOK_frame MSTK_A (g_malloc_thunk G) ltac:(unfold MSTK_A; lia) HML)).
  - intros cs cs' E fx R M model T _ _ _ Hn. exfalso. unfold XN_live in Hn.
    do 121 (destruct id as [|id]; [first [discriminate Hn | exfalso; apply Hne; reflexivity]|]). discriminate Hn.
Qed.
End OpHooks.
