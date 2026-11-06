(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWFC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem write_float_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_wf _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuWFC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuAAf32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT GuWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_f32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 136 then Some GuWFT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  let call := PRun [] (PBump BMP (PExt 136 [] (PRun [0x34edc] k))) in
  let fr80 := SA e_sp (- (c_fr cfg) - 80) in
  match m with
  | ML => PFact (img_apart (eadd D1 IXv) 0 (ELit 17)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 17))                         (* [comment removed for export] *)
          (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 17) fr80 (ELit 80)) call))
  | MS => PFact (img_apart (eadd (eaddz GuAA.OBJ 1) IXv) 0 (ELit 17)) (PFact (KDisj (SA (eadd (eaddz GuAA.OBJ 1) IXv) 0) (ELit 17) fr80 (ELit 80)) call)   (* [comment removed for export] *)
  end.

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_f32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAf32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWDC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem write_double_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_wd _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuWDC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuAAf64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT GuWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_f64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some GuWDT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PFact (img_apart (eadd D1 IXv) 0 (ELit 38)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 38))                 (* [comment removed for export] *)
  (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 38) (SA e_sp (- (c_fr cfg) - 128)) (ELit 128))   (* [comment removed for export] *)
  (PRun [] (PBump BMP (PExt 137 [] (PRun [0x35184] k)))))).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_f64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAf64.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuTc32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem to_chars_u32_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_tc32 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuTc32C.
Module GuAAi16.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_i16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x35690] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 32767 (armS k) (armS k).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i16_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i16_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAi16.
Module GuAAi8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_i8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x353fc] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 127 (armS k) (armS k).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i8_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i8_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAi8.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuTc16C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem to_chars_u16_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_tc16 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuTc16C.
Module GuAAu16.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16 GuTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_u16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 131 then Some GuTc16.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 131 [] (PRun [0x360e0] k))).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u16_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u16_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAu16.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWAf32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT GuWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_f32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 136 then Some GuWFT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  let call := PRun [] (PBump BMP (PExt 136 [] (PRun [0x36964] k))) in
  let fr80 := SA e_sp (- (c_fr cfg) - 80) in
  match m with
  | ML => PFact (img_apart (eadd D1 IXv) 0 (ELit 17)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 17))
          (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 17) fr80 (ELit 80)) call))
  | MS => PFact (img_apart (eadd (eaddz GuWA.OBJ 1) IXv) 0 (ELit 17)) (PFact (KDisj (SA (eadd (eaddz GuWA.OBJ 1) IXv) 0) (ELit 17) fr80 (ELit 80)) call)
  end.

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_f32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAf32.
Module GuWAf64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT GuWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_f64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some GuWDT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PFact (img_apart (eadd D1 IXv) 0 (ELit 38)) (PFact (KRange (eadd D1 IXv) PTRLO (objhi 38))                 (* [comment removed for export] *)
  (PFact (KDisj (SA (eadd D1 IXv) 0) (ELit 38) (SA e_sp (- (c_fr cfg) - 128)) (ELit 128))   (* [comment removed for export] *)
  (PRun [] (PBump BMP (PExt 137 [] (PRun [0x36d58] k)))))).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_f64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAf64.
Module GuWAi16.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_i16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x374e8] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 32767 (armS k) (armS k).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i16_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i16_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAi16.
Module GuWAi8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_i8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] (PRun [0x37114] k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 127 (armS k) (armS k).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i8_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i8_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAi8.
Require LinuxProcessSemantics.Riscv.Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWAu16.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16 GuTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_u16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 131 then Some GuTc16.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 131 [] (PRun [0x38450] k))).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u16_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u16_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAu16.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWNf32.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT GuWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x390f8.  Definition BI : Z := 0x3dcac.
Definition cfg : ncfg := {| n_ninstr := 93; n_K := 4; n_hr := 21; n_wmx := 16; n_vhi := 0; n_join1 := 0xbc; n_ret := 0x13c; n_ixreg := 12; n_rd := 0x3c |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 136 then Some GuWFT.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  let call := PRun [] (PBump BMP (PExt 136 [] k)) in
  let frw := SA e_sp (- 48 - 80) in
  match m with   (* [comment removed for export] *)
  | ML => PFact (img_apart (eadd D1 IX) 0 (ELit 17)) (PFact (KRange (eadd D1 IX) PTRLO (objhi 17)) (PFact (KDisj (SA (eadd D1 IX) 0) (ELit 17) frw (ELit 80)) call))
  | MS => PFact (img_apart (eadd (eaddz GuWN.OBJ 1) IX) 0 (ELit 17)) (PFact (KDisj (SA (eadd (eaddz GuWN.OBJ 1) IX) 0) (ELit 17) frw (ELit 80)) call)
  end.
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-. apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-. apply (GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_f32_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_f32_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_f32_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_f32_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_f32_u8tag_callee_L1. Qed.
Theorem write_number_f32_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_f32_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_f32_inttag_callee_L1. Qed.
End Contract.
End GuWNf32.
Module GuWNf64.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT GuWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x3926c.  Definition BI : Z := 0x3de20.
Definition cfg : ncfg := {| n_ninstr := 105; n_K := 8; n_hr := 38; n_wmx := 36; n_vhi := 0; n_join1 := 0xec; n_ret := 0x16c; n_ixreg := 12; n_rd := 0x3c |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some GuWDT.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PFact (img_apart (eadd D1 IX) 0 (ELit 38)) (PFact (KRange (eadd D1 IX) PTRLO (objhi 38))
  (PFact (KDisj (SA (eadd D1 IX) 0) (ELit 38) (SA e_sp (- 48 - 112)) (ELit 112)) (PRun [] (PBump BMP (PExt 137 [] k))))).
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-. apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-. apply (GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_f64_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_f64_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_f64_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_f64_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_f64_u8tag_callee_L1. Qed.
Theorem write_number_f64_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_f64_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_f64_inttag_callee_L1. Qed.
End Contract.
End GuWNf64.
Module GuWNi16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x39584.  Definition BI : Z := 0x3e138.
Definition cfg : ncfg := {| n_ninstr := 99; n_K := 2; n_hr := 8; n_wmx := 6; n_vhi := 65535; n_join1 := 0xa4; n_ret := 0x154; n_ixreg := 12; n_rd := 0x3c |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] k)).
Definition elem (m : smode) (k : plan) : plan := PCase2 BV 32767 (armS k) (armS k).
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_i16_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_i16_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_i16_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_i16_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_i16_u8tag_callee_L1. Qed.
Theorem write_number_i16_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_i16_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_i16_inttag_callee_L1. Qed.
End Contract.
End GuWNi16.
Module GuWNi8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 GuTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x39410.  Definition BI : Z := 0x3dfc4.
Definition cfg : ncfg := {| n_ninstr := 93; n_K := 1; n_hr := 8; n_wmx := 6; n_vhi := 255; n_join1 := 0x90; n_ret := 0x13c; n_ixreg := 12; n_rd := 0x34 |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 130 then Some GuTc32.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition armS (k : plan) : plan := PRun [] (PBump BMP (PExt 130 [] k)).
Definition elem (m : smode) (k : plan) : plan := PCase2 BV 127 (armS k) (armS k).      (* [comment removed for export] *)
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      apply (GuTc32C.to_chars_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_i8_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_i8_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_i8_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_i8_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_i8_u8tag_callee_L1. Qed.
Theorem write_number_i8_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_i8_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_i8_inttag_callee_L1. Qed.
End Contract.
End GuWNi8.
Module GuWNu16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16 GuTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x39910.  Definition BI : Z := 0x3e4c4.
Definition cfg : ncfg := {| n_ninstr := 87; n_K := 2; n_hr := 8; n_wmx := 5; n_vhi := 65535; n_join1 := 0xa4; n_ret := 0x124; n_ixreg := 12; n_rd := 0x3c |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 131 then Some GuTc16.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 131 [] k)).
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      apply (GuTc16C.to_chars_u16_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_u16_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_u16_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_u16_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_u16_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_u16_u8tag_callee_L1. Qed.
Theorem write_number_u16_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_u16_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_u16_inttag_callee_L1. Qed.
End Contract.
End GuWNu16.
Module GuWNu8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BU : Z := 0x39710.  Definition BI : Z := 0x3e2c4.
Definition cfg : ncfg := {| n_ninstr := 128; n_K := 1; n_hr := 8; n_wmx := 3; n_vhi := 255; n_join1 := 0x90; n_ret := 0x1c8; n_ixreg := 11; n_rd := 0x34 |}.
Definition CT (id : nat) : option gcallee := None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF GUBSAN GuWN.BCAP GuWN.CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q8 : expr := EMd Instr.M_MULHU BV (ELit 0x28f5c28f5c28f5d).           (* [comment removed for export] *)
Definition armA (k : plan) : plan := xl (xl k).                                    (* [comment removed for export] *)
Definition armC (k : plan) : plan := divfactU BV q8 100 (zfact BV q8 100 (xl k)). (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PCase2 BV 9 (armA k) (PCase2 BV 99 (armA k) (armC k)).
Definition PLANt (m : smode) (B : Z) : plan := GuWN.PLAN cfg elem m B.

#[local] Notation CHK m B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ce cfg m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (GuWN.IT cfg B) AUBSAN GuWN.NXF LIMIT (XN B) (B2JCutShare.GlzCallCert.XE0) GuWN.XB XC0 (HSce (GuWN.ceL1 cfg B)) 0%nat BFUEL FUELN None).
Lemma certU_S : CHK MS BU (GuWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (GuWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (GuWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (GuWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma callee_mB : forall m B sh, holes_only sh = true -> CHK m B (GuWN.tin m B) (PLANt m B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ce cfg m B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt m B) _ (gplan m B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Lemma callee_1B : forall B sh, holes_only sh = true -> CHK1 B (GuWN.tin ML B) (PLANt ML B) = COk sh -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWN.ceL1 cfg B) (GuWN.IT cfg B) (GuWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUELN (XN B) _ GuWN.XB _ (PLANt ML B) _ (gplan ML B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWN.IT cfg B) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWN.IT_ok cfg B) GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuWN.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWN.NXF [] GUBSAN GuWN.BCAP GuWN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuWN.CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
Theorem write_number_u8_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BU).
Proof. exact (callee_mB MS BU _ hs0 certU_S). Qed.
Theorem write_number_u8_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg MS BI).
Proof. exact (callee_mB MS BI _ hs0 certI_S). Qed.
Theorem write_number_u8_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BU).
Proof. exact (callee_1B BU _ hs1 certU_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_u8_u8tag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1. exact write_number_u8_u8tag_callee_L1. Qed.
Theorem write_number_u8_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ceL1 cfg BI).
Proof. exact (callee_1B BI _ hs1 certI_L1). Qed.
(* [comment removed for export] *)
Theorem write_number_u8_inttag_callee_L : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1. exact write_number_u8_inttag_callee_L1. Qed.
End Contract.
End GuWNu8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.

Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN GuWNf32 GuWNf64 GuWNi8 GuWNi16 GuWNu8 GuWNu16.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT. Export OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 132 then Some GuI32.ce else if Nat.eqb id 133 then Some GuU32.ce
  else if Nat.eqb id 134 then Some GuI64.ce else if Nat.eqb id 135 then Some GuU64.ce
  else if Nat.eqb id 142 then Some GuI32.ceS else if Nat.eqb id 143 then Some GuU32.ceS else None.
Definition lamB (bu bi : Z) (B : Z) : Z := if is_int B then bi else bu.
Definition CT2 (B : Z) (id : nat) : option gcallee2 :=
  if Nat.eqb id 150 then Some (GuWN.ce2 GuWNf32.cfg ML (lamB GuWNf32.BU GuWNf32.BI B))
  else if Nat.eqb id 151 then Some (GuWN.ce2 GuWNf32.cfg MS (lamB GuWNf32.BU GuWNf32.BI B))
  else if Nat.eqb id 152 then Some (GuWN.ce2 GuWNf64.cfg ML (lamB GuWNf64.BU GuWNf64.BI B))
  else if Nat.eqb id 153 then Some (GuWN.ce2 GuWNf64.cfg MS (lamB GuWNf64.BU GuWNf64.BI B))
  else if Nat.eqb id 154 then Some (GuWN.ce2 GuWNi8.cfg ML (lamB GuWNi8.BU GuWNi8.BI B))
  else if Nat.eqb id 155 then Some (GuWN.ce2 GuWNi8.cfg MS (lamB GuWNi8.BU GuWNi8.BI B))
  else if Nat.eqb id 156 then Some (GuWN.ce2 GuWNi16.cfg ML (lamB GuWNi16.BU GuWNi16.BI B))
  else if Nat.eqb id 157 then Some (GuWN.ce2 GuWNi16.cfg MS (lamB GuWNi16.BU GuWNi16.BI B))
  else if Nat.eqb id 158 then Some (GuWN.ce2 GuWNu8.cfg ML (lamB GuWNu8.BU GuWNu8.BI B))
  else if Nat.eqb id 159 then Some (GuWN.ce2 GuWNu8.cfg MS (lamB GuWNu8.BU GuWNu8.BI B))
  else if Nat.eqb id 160 then Some (GuWN.ce2 GuWNu16.cfg ML (lamB GuWNu16.BU GuWNu16.BI B))
  else if Nat.eqb id 161 then Some (GuWN.ce2 GuWNu16.cfg MS (lamB GuWNu16.BU GuWNu16.BI B))
  else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (IT B) AUBSAN NXF GUBSAN BCAP CCAP CT.
(* [comment removed for export] *)
Definition CT1 (B : Z) (id : nat) : option gcallee :=
  if Nat.eqb id 170 then Some (GuWN.ceL1 GuWNf32.cfg (lamB GuWNf32.BU GuWNf32.BI B))
  else if Nat.eqb id 171 then Some (GuWN.ceL1 GuWNf64.cfg (lamB GuWNf64.BU GuWNf64.BI B))
  else if Nat.eqb id 172 then Some (GuWN.ceL1 GuWNi8.cfg (lamB GuWNi8.BU GuWNi8.BI B))
  else if Nat.eqb id 173 then Some (GuWN.ceL1 GuWNi16.cfg (lamB GuWNi16.BU GuWNi16.BI B))
  else if Nat.eqb id 174 then Some (GuWN.ceL1 GuWNu8.cfg (lamB GuWNu8.BU GuWNu8.BI B))
  else if Nat.eqb id 175 then Some (GuWN.ceL1 GuWNu16.cfg (lamB GuWNu16.BU GuWNu16.BI B))
  else CT id.
Definition XN1 (B : Z) : nat -> list expr -> acs -> option acs := XNc USEGS (IT B) AUBSAN NXF GUBSAN BCAP CCAP (CT1 B).
Definition XB (B : Z) : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP (CT2 B).
Definition FUELN : nat := 4000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CAPB : expr := eaddz (eadd (escale 4 IX) (escale 8 (esub IT0 INLO))) CAPK.
Definition RSZ (m : smode) : list expr := match m with MS => [ELit 0; D; CAPB] | ML => [ELit 1; D; A; S; CAPB] end.
Definition B2 : nat := 130.           (* [comment removed for export] *)
Definition BMP : nat := 170.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exitD (m : smode) (K : Z) (XI a : expr) : plan :=
  let it' := eaddz IT0 K in let cons' := esub it' INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - K))                   (* [comment removed for export] *)
  (PFactLe XI (escale 24 cons') IXHI
  (PFactLe (esub (escale 24 cons') XI) (escale 24 cons') BIG
  (match m with                  (* [comment removed for export] *)
   | ML => PFactLe (capexpr XI it' INLO a) (eaddz (escale 104 cons') CAPK) CAPHI (PHandoffW 1 [(41%nat, ELit K)])
   | MS => PHandoffW 0 [(41%nat, ELit K)]
   end)))).
(* [comment removed for export] *)
Definition pre (k : plan) : plan := PRun [] (PExt 42 [] (PRun [] k)).
Definition ERRX (m : smode) : plan := PRun [] (PHandoffW (hole m) [(41%nat, ELit 0)]).      (* [comment removed for export] *)
Definition EXITERR (m : smode) : plan := pre (ERRX m).                                        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grown (k : plan) : plan :=
  PFact (KDisj (SA (EVar 130) 0) (escale 8 (EVar 131)) (SA e_sp (- FRK)) (ELit (FRK + WSTK)))
  (PFact (KDisj (SA (EVar 130) 0) (escale 8 (EVar 131)) (SA G 0) (ELit 112)) k).
(* [comment removed for export] *)
Definition NSZ (hr : Z) : expr := eaddz (escale 2 IX) (2 * hr).
Definition diamond (m : smode) (hr : Z) (cont : smode -> expr -> expr -> expr -> plan) : plan :=
  match m with
  | ML => PBranch (cont ML D S A)
                  (PRun [] (PBump B2 (PExt2 31 (RSZ ML) (cont ML D (NSZ hr) A) (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))))
  | MS => if Z.leb 23 hr then PBump B2 (PExt2 31 (RSZ MS) (PContraH 0) (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))
          else PBranch (cont MS D D A)
                       (PRun [] (PBump B2 (PExt2 31 (RSZ MS)
                                   (if Z.leb 12 hr then PContraH 0
                                    else PCase2 IX (11 - hr) (cont MS D (NSZ hr) A) PContra)   (* [comment removed for export] *)
                                   (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))))
  end.
(* [comment removed for export] *)
Definition room (m : smode) (hr : Z) (s a : expr) (k : plan) : plan :=
  match m with ML => PFactVia (esub (escale 8 a) IX) (esub s IX) (hr + 1) (2 ^ 40) k | MS => k end.
(* [comment removed for export] *)
Definition bufimg (m : smode) (d : expr) (w : Z) (k : plan) : plan :=
  PFact (img_apart (match m with ML => eadd d IX | MS => eadd (eaddz OBJ 1) IX end) 0 (ELit w)) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JLO : nat := 121.
Definition D1 : expr := EVar 121.  Definition S1 : expr := EVar 122.  Definition A1 : expr := EVar 123.
Definition JRS : nat := 125.        (* [comment removed for export] *)
Definition JNX : nat := 150.
Definition roomJ (m : smode) (hr : Z) : list kentry :=
  match m with MS => [KRange (esub D1 IX) hr (2 ^ 40)] | ML => [KRange (esub S1 IX) hr (2 ^ 37)] end.
Definition csregsJ : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition jhavoc (k : Z) : list nat := 10%nat :: csregsJ.
(* [comment removed for export] *)
Fixpoint ehas (lo hi : nat) (e : expr) : bool :=
  match e with
  | EVar n => (Nat.leb lo n && Nat.ltb n hi)%bool
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ehas lo hi a || ehas lo hi b)%bool
  | EExt _ _ _ a => ehas lo hi a
  | _ => false
  end.
Definition ahas (lo hi : nat) (a : saddr) : bool := ehas lo hi (a_base a).
Definition khas (lo hi : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => ahas lo hi a || ehas lo hi v
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => ahas lo hi a || ehas lo hi n
  | KImg _ _ => false
  | KAlign x _ | KRange x _ _ => ehas lo hi x
  | KDisj a1 n1 a2 n2 => ahas lo hi a1 || ehas lo hi n1 || ahas lo hi a2 || ehas lo hi n2
  end%bool.
(* [comment removed for export] *)
Definition ktp (K : kentry) : bool := match K with KWord a _ _ => expr_eqb (a_base a) TP | _ => false end.
(* [comment removed for export] *)
Inductive jstep : Type := JD (d : dstep) | JB (n : nat).
Definition ITU : itab := IT BNU.  Definition ITI : itab := IT BNI.
Definition XNU := XN BNU.  Definition XNI := XN BNI.  Definition XBU := XB BNU.  Definition XBI := XB BNI.
Fixpoint jpath0 (it : itab) (xn : nat -> list expr -> acs -> option acs) (xb : nat -> list expr -> acs -> option (acs * acs))
         (cs : acs) (l : list jstep) : acs :=
  match l with
  | [] => cs
  | JD d :: r => match dgo USEGS it AUBSAN xn xb BFUEL NXF cs d with Some c => jpath0 it xn xb c r | None => cs end
  | JB n :: r => match APC.node_bump cs n with Some c => jpath0 it xn xb c r | None => cs end
  end.
Definition jpath (B : Z) (cs : acs) (l : list jstep) : acs :=
  if Z.eqb B BNU then jpath0 ITU XNU XBU cs l else jpath0 ITI XNI XBI cs l.
(* [comment removed for export] *)
Definition JSJ (r0 : acs) (k J hr : Z) (m : smode) : acs :=
  mkcsV J (sr_havoc (s_regs (a_ss r0)) (jhavoc k) JRS)
        (roomJ m hr ++ str m IX IT0 121 ++ filter (fun K => negb (khas 34 37 K || ktp K)) (kn r0)) JNX (vis m 121).
(* [comment removed for export] *)
Definition mrgJ (J : Z) : plan := PRun [J] (PMerge 1).
Definition diamondJ (m : smode) (hr J : Z) : plan :=
  match m with
  | ML => PBranch (mrgJ J) (PRun [] (PBump B2 (PExt2 31 (RSZ ML) (mrgJ J) (grown (mrgJ J)))))
  | MS => PBranch (mrgJ J)
                  (PRun [] (PBump B2 (PExt2 31 (RSZ MS)
                              (if Z.leb 12 hr then PContraH 0 else PCase2 IX (11 - hr) (mrgJ J) PContra)
                              (grown (mrgJ J)))))
  end.
(* [comment removed for export] *)
Definition tagsteps (k : Z) : list jstep := (if Z.eqb k 0 then [] else [JD (DHi TAGV (8 * k - 1))]) ++ [JD (DLo TAGV (8 * k + 7))].
Definition pre3 : list jstep := [JD (DRun []); JD (DExt 42 []); JD (DRun [])].
Definition intpre (B stpc K : Z) : list jstep := [JD (DHi REM (K - 1)); JD (DRun [at_ B stpc]); JB 120; JD (DExt 44 [ELit 11]); JD (DRun [])].
Definition armpre (B k : Z) : list jstep :=
  tagsteps k ++ pre3 ++
  match k with
  | 9 => intpre B 0x300 4
  | 10 => intpre B 0x2a4 4
  | 13 => intpre B 0x210 8
  | 14 => intpre B 0x174 8
  | _ => []
  end.
(* [comment removed for export] *)
Definition JR0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  let s := jpath B (tin m B) (armpre B k) in let J := pc s + 4 in (J, set_kn (jpath B s [JD DBrF; JD (DRun [J])]) (kn s)).
  (* [comment removed for export] *)
Definition DARMS : list Z := [9; 10; 13; 14].
Definition JR0_UL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU ML k)) DARMS.
Definition JR0_US : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU MS k)) DARMS.
Definition JR0_IL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI ML k)) DARMS.
Definition JR0_IS : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI MS k)) DARMS.
Definition JR0L (B : Z) (m : smode) : list (Z * (Z * acs)) :=
  if Z.eqb B BNU then match m with ML => JR0_UL | MS => JR0_US end else match m with ML => JR0_IL | MS => JR0_IS end.
Definition jr0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  match find (fun p => Z.eqb (fst p) k) (JR0L B m) with Some (_, x) => x | None => (0, tin m B) end.
(* [comment removed for export] *)
Definition joinJ (B : Z) (m : smode) (k : Z) (hr : Z) (cont : smode -> expr -> expr -> expr -> plan) : plan :=
  (* [comment removed for export] *)
  match m with
  | MS => if Z.leb 23 hr then diamond m hr cont else
      PViaM 1 [(JSJ (snd (jr0 B MS k)) k (fst (jr0 B MS k)) hr MS, cont MS D1 D1 A1); (JSJ (snd (jr0 B MS k)) k (fst (jr0 B MS k)) hr ML, cont ML D1 S1 A1)]
              JLO (diamondJ MS hr (fst (jr0 B MS k)))
  | ML => PViaM 1 [(JSJ (snd (jr0 B ML k)) k (fst (jr0 B ML k)) hr ML, cont ML D1 S1 A1)] JLO (diamondJ ML hr (fst (jr0 B ML k)))
  end.

Section Arms.
Variable B : Z.
Definition o (x : Z) : Z := at_ B x.

(* [comment removed for export] *)
Definition arm_lam (idL : nat) (m : smode) : plan :=
  pre (PBump BMP (PExt2 (match m with ML => idL | MS => Datatypes.S idL end) [ELit (g_tp GUBSAN); ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO]
         (PRun [] (PHandoff 0)) (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).   (* [comment removed for export] *)
Definition HV : expr := EVar 120.
Definition X44 (r : Z) (k : plan) : plan := PExt 44 [ELit r] k.
(* [comment removed for export] *)
Definition int_cont (cid cidS : nat) (K hr : Z) (m : smode) (d s a : expr) : plan :=
  room m hr s a (PRun [] (bufimg m d hr (PBump BMP (PExt (match m with ML => cid | MS => cidS end)
                                         (match m with ML => [HV; a; s; d; IX] | MS => [HV; ELit 0; s; ELit 0; IX] end)
                                         (PRun [] (exitD m K (eadd IX (EVar 194)) a)))))).
Definition arm_int (k : Z) (stpc : Z) (cid cidS : nat) (K hr : Z) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [o stpc] (PBump 120 (X44 11 (PRun [] (joinJ B m k hr (int_cont cid cidS K hr))))))).
(* [comment removed for export] *)
Definition arm_of (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_lam 154 m | 2 => arm_lam 158 m | 5 => arm_lam 156 m | 6 => arm_lam 160 m
  | 8 => arm_lam 150 m | 9 => arm_int 9 0x300 132 142 4 16 m | 10 => arm_int 10 0x2a4 133 143 4 16 m
  | 12 => arm_lam 152 m | 13 => arm_int 13 0x210 134 134 8 24 m | 14 => arm_int 14 0x174 135 135 8 24 m
  | _ => EXITERR m
  end.
Fixpoint classes (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm_of m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm_of m k) (classes m (k + 1) n')
  end.
Definition PLAN (m : smode) : plan := classes m 0 31.
(* [comment removed for export] *)
Definition arm_lamL1 (id1 : nat) (m : smode) : plan :=
  pre (PBump BMP (PExt id1 [ELit (g_tp GUBSAN); ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO] (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).
Definition arm_ofL1 (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_lamL1 172 m | 2 => arm_lamL1 174 m | 5 => arm_lamL1 173 m | 6 => arm_lamL1 175 m
  | 8 => arm_lamL1 170 m | 9 => arm_int 9 0x300 132 142 4 16 m | 10 => arm_int 10 0x2a4 133 143 4 16 m
  | 12 => arm_lamL1 171 m | 13 => arm_int 13 0x210 134 134 8 24 m | 14 => arm_int 14 0x174 135 135 8 24 m
  | _ => EXITERR m
  end.
Fixpoint classesL1 (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm_ofL1 m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm_ofL1 m k) (classesL1 m (k + 1) n')
  end.
Definition PLANL1 (m : smode) : plan := classesL1 m 0 31.   (* [comment removed for export] *)
End Arms.

