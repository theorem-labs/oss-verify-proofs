(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon AzStrResizeT AzStrResizeA.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN (NB : Z) (m : smode) : nat -> list expr -> acs -> option acs := XNc ASEGS IT AASAN (NXF m) GASAN (BCAP NB) CCAP CT0.
Definition planm (NB : Z) (m : smode) : plan := match m with MS => planS | ML => planL NB end.
(* [comment removed for export] *)
Definition N16 : Z := 2^16.  Definition N22 : Z := 2^22.  Definition N26 : Z := 2^26.  Definition N28 : Z := 2^28.
Definition N3G : Z := 3 * 2^30 + 16.  Definition N3H : Z := 3 * 2^30 + 80.  Definition N3X : Z := 13 * 2^28 + 80.
Ltac cert := vm_cast_no_check (@eq_refl cres (COk (SHole 0))).
(* [comment removed for export] *)
Lemma certS16 : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N16 MS) XE0 XB0 (HSce (ce N16 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N16 MS)) (planm N16 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS22 : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N22 MS) XE0 XB0 (HSce (ce N22 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N22 MS)) (planm N22 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS26 : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N26 MS) XE0 XB0 (HSce (ce N26 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N26 MS)) (planm N26 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS28 : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N28 MS) XE0 XB0 (HSce (ce N28 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N28 MS)) (planm N28 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3G : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N3G MS) XE0 XB0 (HSce (ce N3G MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3G MS)) (planm N3G MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3H : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N3H MS) XE0 XB0 (HSce (ce N3H MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3H MS)) (planm N3H MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3X : check ASEGS IT AASAN (NXF MS) LIMIT ISP0 (XN N3X MS) XE0 XB0 (HSce (ce N3X MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3X MS)) (planm N3X MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certL16 : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N16 ML) XE0 XB0 (HSce (ce N16 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N16 ML)) (planm N16 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL22 : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N22 ML) XE0 XB0 (HSce (ce N22 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N22 ML)) (planm N22 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL26 : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N26 ML) XE0 XB0 (HSce (ce N26 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N26 ML)) (planm N26 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL28 : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N28 ML) XE0 XB0 (HSce (ce N28 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N28 ML)) (planm N28 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3G : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N3G ML) XE0 XB0 (HSce (ce N3G ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3G ML)) (planm N3G ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3H : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N3H ML) XE0 XB0 (HSce (ce N3H ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3H ML)) (planm N3H ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3X : check ASEGS IT AASAN (NXF ML) LIMIT ISP0 (XN N3X ML) XE0 XB0 (HSce (ce N3X ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3X ML)) (planm N3X ML) = COk (SHole 0). Proof. cert. Qed.
(* [comment removed for export] *)
Lemma gplan : forall NB m, gplan_ok (planm NB m) = true. Proof. intros NB [|]; reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.

(* [comment removed for export] *)
Lemma contract_of_chk : forall NB m,
  check ASEGS IT AASAN (NXF m) LIMIT ISP0 (XN NB m) XE0 XB0 (HSce (ce NB m)) 0%nat BFUEL FUEL None (ce_tin (ce NB m)) (planm NB m) = COk (SHole 0) ->
  callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (ce NB m).
Proof.
  intros NB m CERT.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            (ce NB m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN NB m) _ (planm NB m) _ (gplan NB m) hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
  refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok (NXF m) [] GASAN (BCAP NB) CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem resizeS_contract : forall NB, In NB CLASSES -> callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (c2_merged (ceS NB)).
Proof.
  intros NB Hin. unfold ceS. change (c2_merged (ce2 NB MS)) with (ce NB MS). cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [ exact (contract_of_chk N16 MS certS16) | exact (contract_of_chk N22 MS certS22) | exact (contract_of_chk N26 MS certS26)
    | exact (contract_of_chk N28 MS certS28) | exact (contract_of_chk N3G MS certS3G) | exact (contract_of_chk N3H MS certS3H) | exact (contract_of_chk N3X MS certS3X) ].
Qed.
Theorem resizeL_contract : forall NB, In NB CLASSES -> callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (c2_merged (ceL NB)).
Proof.
  intros NB Hin. unfold ceL. change (c2_merged (ce2 NB ML)) with (ce NB ML). cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [ exact (contract_of_chk N16 ML certL16) | exact (contract_of_chk N22 ML certL22) | exact (contract_of_chk N26 ML certL26)
    | exact (contract_of_chk N28 ML certL28) | exact (contract_of_chk N3G ML certL3G) | exact (contract_of_chk N3H ML certL3H) | exact (contract_of_chk N3X ML certL3X) ].
Qed.

(* [comment removed for export] *)
Theorem CT2_resize_sound : forall id c, CT2_resize id = Some c ->
  callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (c2_merged c).
Proof.
  intros id c H. destruct (CT2_resize_cases id c H) as (NB & Hin & [-> | ->]).
  - exact (resizeS_contract NB Hin).
  - exact (resizeL_contract NB Hin).
Qed.
End Contract.
