(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HpropsEx.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SEGS : list Segment.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable SHC : list (Z * Z).
Variable I : Type.
(* [comment removed for export] *)
Variable P : I -> list (Z * Z) -> Prop.
Hypothesis P_perm : forall i L L', P i L -> Permutation L L' -> P i L'.
Variable X : I -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable i0 : I.
Hypothesis HPX : forall i, hprops SWIN G SHC (X i).

Definition Xex (L LF : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) : Prop :=
  exists i, P i L /\ X i L LF B C K M mdl.

Theorem hprops_ex : hprops SWIN G SHC Xex.
Proof.
  constructor.
  - intros L LF B C K M M' mdl (i & Pi & H) Hch. exists i. split; [exact Pi|]. exact (hp_frame _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ H Hch).
  - intros L LF B C K M mdl mdl' (i & Pi & H) Hvm. exists i. split; [exact Pi|]. exact (hp_vm _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ H Hvm).
  - intros L LF B C K B' C' K' M mdl (i & Pi & H) HB HC HK. exists i. split; [exact Pi|]. exact (hp_mono _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ _ H HB HC HK).
  - intros L LF B C K M mdl (i & Pi & H).
    destruct (hp_lazy _ _ _ _ (HPX i) _ _ _ _ _ _ _ H) as (AA & A1 & A2 & A3 & A4 & A5).
    exists AA. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    intros mdl' Hm Hs. exists i. split; [exact Pi | exact (A5 mdl' Hm Hs)].
  - intros L LF B C K M mdl (i & Pi & H). exact (hp_facts _ _ _ _ (HPX i) _ _ _ _ _ _ _ H).
  - intros L LF B C K M mdl b m (i & Pi & H). exact (hp_zone _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ H).
  - intros L LF B C K M mdl f m (i & Pi & H). exact (hp_fzone _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ H).
  - intros L LF B C K M mdl L1 L2 b m b' m' (i & Pi & H). exact (hp_disj _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  - intros L LF B C K M mdl F1 F2 f m f' m' (i & Pi & H). exact (hp_fdisj _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  - intros L LF B C K M mdl b m f n (i & Pi & H). exact (hp_bfdisj _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ _ _ H).
  - intros L L' LF LF' B C K M mdl HL HLF (i & Pi & H). exists i. split; [exact (P_perm i L L' Pi HL)|]. exact (hp_perm _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ HL HLF H).
  - exact (hp_shc_stack _ _ _ _ (HPX i0)).
  - exact (hp_shc_image _ _ _ _ (HPX i0)).
  - intros L LF B C K M mdl b n a (i & Pi & H). exact (hp_nolazy _ _ _ _ (HPX i) _ _ _ _ _ _ _ _ _ _ H).
  - exact (hp_errno _ _ _ _ (HPX i0)).
Qed.
End HpropsEx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable bt : AsAinvDefs3.as_boot.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt).
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt).
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_errno : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Hypothesis SWIN_ok : AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) SWIN.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.   (* [comment removed for export] *)
Variable n_e : Z.
Variable L_e : list (Z * Z).

(* [comment removed for export] *)
Definition AINVH_op_bt : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AzBridgeC3.AINVH_op (AzBridgeH.AAINV_HL bt) n_e L_e.

Lemma hprops_h_bt : forall h : option Z,
  hprops SWIN G (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h)).
Proof. intros h. exact (AzBridgeH.hprops_h bt SWIN G G_imglo G_hi G_ro_img G_img_al G_errno SWIN_ok G_img_shlo h). Qed.

Lemma hole_op_perm : forall h L L', AzBridgeC3.hole_op n_e L_e h L -> Permutation L L' -> AzBridgeC3.hole_op n_e L_e h L'.
Proof.
  intros h L L' [->|[-> HP]] HL; [left; reflexivity | right]. split; [reflexivity|].
  exact (Permutation_trans (Permutation_sym HL) HP).
Qed.

Theorem hprops_op_bt : hprops SWIN G (AzBridgeH.SHC_bt bt) AINVH_op_bt.
Proof.
  exact (hprops_ex SWIN G (AzBridgeH.SHC_bt bt) (option Z) (AzBridgeC3.hole_op n_e L_e) hole_op_perm
           (fun h => AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h)) None hprops_h_bt).
Qed.

(* [comment removed for export] *)
Lemma AINVH_op_bt_none : forall L LF B C K M mdl, AzBridgeH.AINVH_bt bt L LF B C K M mdl -> AINVH_op_bt L LF B C K M mdl.
Proof. intros L LF B C K M mdl H. exists None. split; [left; reflexivity | exact H]. Qed.

(* [comment removed for export] *)
Lemma AINVH_op_bt_grown : forall x LF B C K M mdl,
  AINVH_op_bt (x :: L_e) LF B C K M mdl -> AzBridgeH.AINVH_bt bt (x :: L_e) LF B C K M mdl.
Proof.
  intros x LF B C K M mdl (h & [->|[-> HP]] & H); [exact H|].
  exfalso. apply Permutation_length in HP. cbn [length] in HP. lia.
Qed.
End Inst.
