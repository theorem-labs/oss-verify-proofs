(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpWFC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Theorem write_float_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_wf _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GpWFC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpAAf32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWFT GpWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_f32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 136 then Some GpWFT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  let call := PRun [] (PBump BMP (PExt 136 [] (PRun [0x3311c] k))) in
  let fr80 := SA e_sp (- (c_fr cfg) - 80) in
  match m with
  | ML => PFact (img_apart (eadd D1 IXv) 0 (ELit 17)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 17))                         (* [comment removed for export] *)
          (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 17) fr80 (ELit 80)) call))
  | MS => PFact (img_apart (eadd (eaddz GpAA.OBJ 1) IXv) 0 (ELit 17)) (PFact (KDisj (SA (eadd (eaddz GpAA.OBJ 1) IXv) 0) (ELit 17) fr80 (ELit 80)) call)   (* [comment removed for export] *)
  end.

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_f32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAf32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpWDC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Theorem write_double_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_wd _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GpWDC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpWDT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpAAf64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWDT GpWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_f64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some GpWDT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PFact (img_apart (eadd D1 IXv) 0 (ELit 38)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 38))                 (* [comment removed for export] *)
  (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 38) (SA e_sp (- (c_fr cfg) - 128)) (ELit 128))   (* [comment removed for export] *)
  (PRun [] (PBump BMP (PExt 137 [] (PRun [0x33328] k)))))).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_f64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAf64.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpTc32C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Theorem to_chars_u32_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_tc32 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GpTc32C.
Module GpAAi16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 GpTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_i16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GpTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x336f4] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 32767 (armS k) (armS k).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i16_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i16_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAi16.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpI32C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

(* [comment removed for export] *)
Lemma callee_m : forall m p, gplan_ok p = true -> check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) p = COk (SHole 0) ->
  callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (cem m).
Proof.
  intros m p HG CERT.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ p _ HG hshape CERT).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_i32_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof. exact (callee_m ML plan_i32 gplan cert). Qed.
Theorem to_chars40kb_i32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ceS.
Proof. exact (callee_m MS plan_i32S gplanS certS). Qed.
End Contract.
End GpI32C.
Module GpAAi32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32 GpI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_i32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 132 then Some GpI32.ce else if Nat.eqb id 142 then Some GpI32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 132 [VAL; A1; S1; D1; IXv] k | MS => PExt 142 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAi32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpI64C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Theorem to_chars40kb_i64_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_i64 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GpI64C.
Module GpAAi64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64 GpI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_i64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 134 then Some GpI64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 134 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAi64.
Module GpAAi8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 GpTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_i8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GpTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x334fc] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 127 (armS k) (armS k).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i8_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i8_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAi8.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpU32C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Lemma callee_m : forall m, check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) plan_u32 = COk (SHole 0) ->
  callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (cem m).
Proof.
  intros m CERT.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u32 _ gplan hshape CERT).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_u32_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof. exact (callee_m ML cert). Qed.
Theorem to_chars40kb_u32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ceS.
Proof. exact (callee_m MS certS). Qed.
End Contract.
End GpU32C.
Module GpAAu32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32 GpU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_u32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 133 then Some GpU32.ce else if Nat.eqb id 143 then Some GpU32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 133 [VAL; A1; S1; D1; IXv] k | MS => PExt 143 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAu32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpU64C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN 0 0.

Theorem to_chars40kb_u64_callee : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u64 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GpU64C.
Module GpAAu64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64 GpU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpAAT.cfg_u64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 135 then Some GpU64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 135 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAu64.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpW16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpW16C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpW16.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation CHK m B := (check PSEGS (IT B) APLAIN NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (ce m B)) 0%nat BFUEL FUEL16 None).
#[local] Notation CHK1 B := (check PSEGS (IT B) APLAIN NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (ceL1 B)) 0%nat BFUEL FUEL16 None).
Lemma w16u_cert_L1 : CHK1 B16U (tin ML B16U) (PLAN ML B16U) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma w16i_cert_L1 : CHK1 B16I (tin ML B16I) (PLAN ML B16I) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma w16u_cert_S : CHK MS B16U (tin MS B16U) (PLAN MS B16U) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma w16i_cert_S : CHK MS B16I (tin MS B16I) (PLAN MS B16I) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.

Lemma w16_callee : forall m B sh, holes_only sh = true -> CHK m B (tin m B) (PLAN m B) = COk sh -> callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ce m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (ce m B) (IT B) (IT_ok B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ XB _ (PLAN m B) _ (w16_gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (IT B) APLAIN plain_in_hull plain_hull_ok (IT_ok B) NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT0).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma w16_callee1 : forall B sh, holes_only sh = true -> CHK1 B (tin ML B) (PLAN ML B) = COk sh -> callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ceL1 B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (ceL1 B) (IT B) (IT_ok B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ XB _ (PLAN ML B) _ (w16_gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (IT B) APLAIN plain_in_hull plain_hull_ok (IT_ok B) NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT0).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.

Theorem write_u16_u8tag_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ce MS B16U).
Proof. exact (w16_callee MS B16U _ hs0 w16u_cert_S). Qed.
Theorem write_u16_inttag_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ce MS B16I).
Proof. exact (w16_callee MS B16I _ hs0 w16i_cert_S). Qed.
Theorem write_u16_u8tag_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ceL1 B16U).
Proof. exact (w16_callee1 B16U _ hs1 w16u_cert_L1). Qed.
(* [comment removed for export] *)
Theorem write_u16_u8tag_callee_L : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ce ML B16U).
Proof. apply callee_contract_L_of_L1. exact write_u16_u8tag_callee_L1. Qed.
Theorem write_u16_inttag_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ceL1 B16I).
Proof. exact (w16_callee1 B16I _ hs1 w16i_cert_L1). Qed.
(* [comment removed for export] *)
Theorem write_u16_inttag_callee_L : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (ce ML B16I).
Proof. apply callee_contract_L_of_L1. exact write_u16_inttag_callee_L1. Qed.
End Contract.
End GpW16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpWAf32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWFT GpWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_f32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 136 then Some GpWFT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  let call := PRun [] (PBump BMP (PExt 136 [] (PRun [0x34698] k))) in
  let fr80 := SA e_sp (- (c_fr cfg) - 80) in
  match m with
  | ML => PFact (img_apart (eadd D1 IXv) 0 (ELit 17)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 17))
          (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 17) fr80 (ELit 80)) call))
  | MS => PFact (img_apart (eadd (eaddz GpWA.OBJ 1) IXv) 0 (ELit 17)) (PFact (KDisj (SA (eadd (eaddz GpWA.OBJ 1) IXv) 0) (ELit 17) fr80 (ELit 80)) call)
  end.

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_f32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAf32.
Module GpWAf64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWDT GpWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_f64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some GpWDT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PFact (img_apart (eadd D1 IXv) 0 (ELit 38)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 38))                 (* [comment removed for export] *)
  (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 38) (SA e_sp (- (c_fr cfg) - 128)) (ELit 128))   (* [comment removed for export] *)
  (PRun [] (PBump BMP (PExt 137 [] (PRun [0x349ac] k)))))).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_f64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAf64.
Module GpWAi16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 GpTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_i16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GpTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x34f80] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 32767 (armS k) (armS k).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i16_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i16_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAi16.
Module GpWAi32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32 GpI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_i32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 132 then Some GpI32.ce else if Nat.eqb id 142 then Some GpI32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 132 [VAL; A1; S1; D1; IXv] k | MS => PExt 142 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAi32.
Module GpWAi64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64 GpI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_i64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 134 then Some GpI64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 134 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAi64.
Module GpWAi8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 GpTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_i8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GpTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x34c84] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 127 (armS k) (armS k).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i8_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i8_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAi8.
Module GpWAu32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32 GpU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_u32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 133 then Some GpU32.ce else if Nat.eqb id 143 then Some GpU32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 133 [VAL; A1; S1; D1; IXv] k | MS => PExt 143 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u32_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u32_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAu32.
Module GpWAu64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64 GpU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpNum.GpWAT.cfg_u64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 135 then Some GpU64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 135 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u64_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u64_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAu64.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GpWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GpWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GpW16 OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpTc32 GpTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpU32 GpU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpI32 GpI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GpU64 GpU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpI64 GpI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GpWFT GpWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GpWDT GpWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GpW16 GpW16C OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation CHK m B := (check PSEGS (GpNum.GpNumT.IT B) APLAIN GpNum.GpNumT.NXF LIMIT (GpNum.XN B) (B2JCutShare.GlzCallCert.XE0) (GpNum.XB B) XC0 (HSce (GpNum.GpNumT.ce m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check PSEGS (GpNum.GpNumT.IT B) APLAIN GpNum.GpNumT.NXF LIMIT (GpNum.XN1 B) (B2JCutShare.GlzCallCert.XE0) (GpNum.XB B) XC0 (HSce (GpNum.GpNumT.ceL1 B)) 0%nat BFUEL FUELN None).
Lemma numu_cert_S : CHK MS BNU (GpNum.GpNumT.tin MS BNU) (GpNum.PLAN BNU MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma numi_cert_S : CHK MS BNI (GpNum.GpNumT.tin MS BNI) (GpNum.PLAN BNI MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma numu_cert_L1 : CHK1 BNU (GpNum.GpNumT.tin ML BNU) (GpNum.PLANL1 BNU ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma numi_cert_L1 : CHK1 BNI (GpNum.GpNumT.tin ML BNI) (GpNum.PLANL1 BNI ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma num_gplan : forall B m, gplan_ok (GpNum.PLAN B m) = true. Proof. intros B [|]; vm_compute; reflexivity. Qed.
Lemma num_gplan1 : forall B, gplan_ok (GpNum.PLANL1 B ML) = true. Proof. intros B; vm_compute; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.

Lemma CT_ok : forall id ce', GpNum.CT id = Some ce' -> callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce'.
Proof.
  intros id ce' H. unfold GpNum.CT in H.
  destruct (Nat.eqb id 130). { injection H as <-. apply (GpTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 132). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 133). { injection H as <-. apply (GpU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 134). { injection H as <-. apply (GpI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 135). { injection H as <-. apply (GpU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 136). { injection H as <-. apply (GpWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 137). { injection H as <-. apply (GpWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 142). { injection H as <-. apply (GpI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]). }
  destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
  apply (GpU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]).
Qed.

Lemma CT1_ok : forall B id ce', GpNum.CT1 B id = Some ce' -> callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH ce'.
Proof.
  intros B id ce' H. unfold GpNum.CT1 in H.
  destruct (Nat.eqb id 148); [|exact (CT_ok id ce' H)].
  injection H as <-. unfold B16. destruct (is_int B).
  - apply (GpW16C.write_u16_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
  - apply (GpW16C.write_u16_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
Qed.

Lemma CT2_ok : forall B id c, GpNum.CT2 B id = Some c -> callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (c2_merged c).
Proof.
  intros B id c H. unfold GpNum.CT2 in H.
  destruct (Nat.eqb id 138).
  { injection H as <-. change (callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpW16.ce ML (B16 B))). unfold B16. destruct (is_int B).
    - apply (GpW16C.write_u16_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GpW16C.write_u16_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 139); [|discriminate H].
  injection H as <-. change (callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpW16.ce MS (B16 B))). unfold B16. destruct (is_int B).
  - apply (GpW16C.write_u16_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
  - apply (GpW16C.write_u16_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; [(apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
Qed.

Lemma num_callee : forall m B sh, holes_only sh = true -> CHK m B (GpNum.GpNumT.tin m B) (GpNum.PLAN B m) = COk sh ->
  callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ce m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpNum.GpNumT.ce m B) (GpNum.GpNumT.IT B) (GpNum.GpNumT.IT_ok B) LIMIT 0%nat BFUEL FUELN (GpNum.XN B) _ (GpNum.XB B) _ (GpNum.PLAN B m) _ (num_gplan B m) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GpNum.XN.
    apply (XNc_sound PSEGS (GpNum.GpNumT.IT B) APLAIN plain_in_hull plain_hull_ok (GpNum.GpNumT.IT_ok B) GpNum.GpNumT.NXF [] GPLAIN GpNum.GpNumT.BCAP GpNum.GpNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GpNum.CT).
    + intros id ce' H. exact (CT_ok id ce' H).
    + (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GpNum.XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpNum.GpNumT.NXF [] GPLAIN GpNum.GpNumT.BCAP GpNum.GpNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GpNum.CT2 B)).
    + intros id c H. exact (CT2_ok B id c H).
    + (apply OBL2_all; assumption).
Qed.
Lemma num_callee1 : forall B sh, holes_only sh = true -> CHK1 B (GpNum.GpNumT.tin ML B) (GpNum.PLANL1 B ML) = COk sh ->
  callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ceL1 B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpNum.GpNumT.ceL1 B) (GpNum.GpNumT.IT B) (GpNum.GpNumT.IT_ok B) LIMIT 0%nat BFUEL FUELN (GpNum.XN1 B) _ (GpNum.XB B) _ (GpNum.PLANL1 B ML) _ (num_gplan1 B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GpNum.XN1.
    apply (XNc_sound PSEGS (GpNum.GpNumT.IT B) APLAIN plain_in_hull plain_hull_ok (GpNum.GpNumT.IT_ok B) GpNum.GpNumT.NXF [] GPLAIN GpNum.GpNumT.BCAP GpNum.GpNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GpNum.CT1 B)).
    + intros id ce' H. exact (CT1_ok B id ce' H).
    + (apply GC_all; first [assumption | exact (GpNum.GpNumT.IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GpNum.XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpNum.GpNumT.NXF [] GPLAIN GpNum.GpNumT.BCAP GpNum.GpNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GpNum.CT2 B)).
    + intros id c H. exact (CT2_ok B id c H).
    + (apply OBL2_all; assumption).
Qed.

Theorem number_u8tag_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ce MS BNU).
Proof. exact (num_callee MS BNU _ hs0 numu_cert_S). Qed.
Theorem number_inttag_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ce MS BNI).
Proof. exact (num_callee MS BNI _ hs0 numi_cert_S). Qed.
Theorem number_u8tag_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ceL1 BNU).
Proof. exact (num_callee1 BNU _ hs1 numu_cert_L1). Qed.

Theorem number_inttag_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpNum.GpNumT.ceL1 BNI).
Proof. exact (num_callee1 BNI _ hs1 numi_cert_L1). Qed.

End Contract.
