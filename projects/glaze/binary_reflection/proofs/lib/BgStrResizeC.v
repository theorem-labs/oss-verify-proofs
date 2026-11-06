(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgCalleeSub.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.

Lemma callee_contract_more_exits_az : forall SEGS {RC : run_ceil} {SFL : stk_floor} SWIN G FXOK (RZ : GPS.rz_t) SHC KCAP AINVH (c c' : gcallee),
  ce_nxf c' = ce_nxf c -> ce_tin c' = ce_tin c -> ce_bcap c' = ce_bcap c -> ce_ccap c' = ce_ccap c ->
  (forall t, In t (ce_touts c) -> In t (ce_touts c')) ->
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH c -> callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH c'.
Proof.
  intros SEGS RC SFL SWIN G FXOK RZ SHC KCAP AINVH c c' Hn Ht Hb Hc Hsub H.
  unfold callee_contract, callee_contract_when in *.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HF HQ HCS HT Hk.
  rewrite Ht. rewrite Hb in HBc. rewrite Hc in HCc. rewrite Ht in HCS.
  apply (H PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 E fx R M mdl T HB0 HC0 HBc HCc HF HQ HCS HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCS' Hfs.
  apply (Hk tout E' fx' R' M' mdl' (Hsub tout Hin)); [rewrite Hn; exact Hag | exact HCS' | exact Hfs].
Qed.
Lemma callee_contract_L_of_L1_az : forall SEGS {RC : run_ceil} {SFL : stk_floor} SWIN G FXOK (RZ : GPS.rz_t) SHC KCAP AINVH nxf tin tS tL bc cc,
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH (GCE nxf tin [tL; tL] bc cc) ->
  callee_contract SEGS SWIN G FXOK RZ SHC KCAP AINVH (c2_merged (GCE2 nxf tin [tS] [tL] bc cc)).
Proof.
  intros SEGS RC SFL SWIN G FXOK RZ SHC KCAP AINVH nxf tin tS tL bc cc H.
  apply (callee_contract_more_exits_az SEGS SWIN G FXOK RZ SHC KCAP AINVH (GCE nxf tin [tL; tL] bc cc)); try reflexivity; [|exact H].
  intros t Ht. cbn [ce_touts c2_merged c2_touts0 c2_touts1 app] in Ht |- *. right.
  destruct Ht as [<-|Ht]; [left; reflexivity | exact Ht].
Qed.
End BgCalleeSub.
Require Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgStrResizeA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RESIZE_S0 : nat := 100.     (* [comment removed for export] *)
Definition RESIZE_L0 : nat := 110.     (* [comment removed for export] *)
Definition NCLASSES : nat := 7.
Definition class_of (j : nat) : option Z := nth_error CLASSES j.

Definition CT2_resize (id : nat) : option gcallee2 :=
  if Nat.ltb id RESIZE_S0 then None
  else if Nat.ltb id (RESIZE_S0 + NCLASSES) then option_map ceS (class_of (id - RESIZE_S0))
  else if Nat.ltb id RESIZE_L0 then None
  else if Nat.ltb id (RESIZE_L0 + NCLASSES) then option_map ceL (class_of (id - RESIZE_L0))
  else None.

(* [comment removed for export] *)
Definition ct2_or (T1 T2 : nat -> option gcallee2) (id : nat) : option gcallee2 :=
  match T1 id with Some c => Some c | None => T2 id end.


(* [comment removed for export] *)
Definition resize_args_S (s mtr fb : expr) : list expr := [ELit 0; ELit 0; s; mtr; fb].
Definition resize_args_L (d sz A mtr fb : expr) : list expr := [ELit 0; ELit 0; d; sz; A; mtr; fb].

Lemma class_of_in : forall j NB, class_of j = Some NB -> In NB CLASSES.
Proof. intros j NB H. unfold class_of in H. eapply nth_error_In. exact H. Qed.

Lemma CT2_resize_cases : forall id c, CT2_resize id = Some c ->
  exists NB, In NB CLASSES /\ (c = ceS NB \/ c = ceL NB).
Proof.
  intros id c H. unfold CT2_resize in H.
  destruct (Nat.ltb id RESIZE_S0); [discriminate|].
  destruct (Nat.ltb id (RESIZE_S0 + NCLASSES)).
  - destruct (class_of (id - RESIZE_S0)) as [NB|] eqn:E; [|discriminate]. cbn in H. injection H as <-.
    exists NB. split; [eapply class_of_in; exact E | left; reflexivity].
  - destruct (Nat.ltb id RESIZE_L0); [discriminate|]. destruct (Nat.ltb id (RESIZE_L0 + NCLASSES)); [|discriminate].
    destruct (class_of (id - RESIZE_L0)) as [NB|] eqn:E; [|discriminate]. cbn in H. injection H as <-.
    exists NB. split; [eapply class_of_in; exact E | right; reflexivity].
Qed.

Lemma ct2_or_sound : forall (P : gcallee2 -> Prop) (T1 T2 : nat -> option gcallee2),
  (forall id c, T1 id = Some c -> P c) -> (forall id c, T2 id = Some c -> P c) ->
  forall id c, ct2_or T1 T2 id = Some c -> P c.
Proof.
  intros P T1 T2 H1 H2 id c H. unfold ct2_or in H. destruct (T1 id) as [c1|] eqn:E.
  - injection H as <-. exact (H1 id c1 E).
  - exact (H2 id c H).
Qed.

End BgStrResizeA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT BgStrResizeA.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN (NB : Z) (m : smode) : nat -> list expr -> acs -> option acs := XNc BSEGS IT ABOTH (NXF m) GBOTH (BCAP NB) CCAP CT0.
Definition planm (NB : Z) (m : smode) : plan := match m with MS => planS | ML => planL NB end.
(* [comment removed for export] *)
Definition N16 : Z := 2^16.  Definition N22 : Z := 2^22.  Definition N26 : Z := 2^26.  Definition N28 : Z := 2^28.
Definition N3G : Z := 3 * 2^30 + 16.  Definition N3H : Z := 3 * 2^30 + 80.  Definition N3X : Z := 13 * 2^28 + 80.
Ltac cert := vm_cast_no_check (@eq_refl cres (COk (SHole 0))).
(* [comment removed for export] *)
Lemma certS16 : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N16 MS) XE0 XB0 (HSce (ce N16 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N16 MS)) (planm N16 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS22 : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N22 MS) XE0 XB0 (HSce (ce N22 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N22 MS)) (planm N22 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS26 : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N26 MS) XE0 XB0 (HSce (ce N26 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N26 MS)) (planm N26 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS28 : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N28 MS) XE0 XB0 (HSce (ce N28 MS)) 0%nat BFUEL FUEL None (ce_tin (ce N28 MS)) (planm N28 MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3G : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N3G MS) XE0 XB0 (HSce (ce N3G MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3G MS)) (planm N3G MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3H : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N3H MS) XE0 XB0 (HSce (ce N3H MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3H MS)) (planm N3H MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certS3X : check BSEGS IT ABOTH (NXF MS) LIMIT ISP0 (XN N3X MS) XE0 XB0 (HSce (ce N3X MS)) 0%nat BFUEL FUEL None (ce_tin (ce N3X MS)) (planm N3X MS) = COk (SHole 0). Proof. cert. Qed.
Lemma certL16 : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N16 ML) XE0 XB0 (HSce (ce N16 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N16 ML)) (planm N16 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL22 : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N22 ML) XE0 XB0 (HSce (ce N22 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N22 ML)) (planm N22 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL26 : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N26 ML) XE0 XB0 (HSce (ce N26 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N26 ML)) (planm N26 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL28 : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N28 ML) XE0 XB0 (HSce (ce N28 ML)) 0%nat BFUEL FUEL None (ce_tin (ce N28 ML)) (planm N28 ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3G : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N3G ML) XE0 XB0 (HSce (ce N3G ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3G ML)) (planm N3G ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3H : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N3H ML) XE0 XB0 (HSce (ce N3H ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3H ML)) (planm N3H ML) = COk (SHole 0). Proof. cert. Qed.
Lemma certL3X : check BSEGS IT ABOTH (NXF ML) LIMIT ISP0 (XN N3X ML) XE0 XB0 (HSce (ce N3X ML)) 0%nat BFUEL FUEL None (ce_tin (ce N3X ML)) (planm N3X ML) = COk (SHole 0). Proof. cert. Qed.
(* [comment removed for export] *)
Lemma gplan : forall NB m, gplan_ok (planm NB m) = true. Proof. intros NB [|]; reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 BSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT BSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GBOTH SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH bc cc.

(* [comment removed for export] *)
Lemma contract_of_chk : forall NB m,
  check BSEGS IT ABOTH (NXF m) LIMIT ISP0 (XN NB m) XE0 XB0 (HSce (ce NB m)) 0%nat BFUEL FUEL None (ce_tin (ce NB m)) (planm NB m) = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (ce NB m).
Proof.
  intros NB m CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (ce NB m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN NB m) _ (planm NB m) _ (gplan NB m) hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
  refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok (NXF m) [] GBOTH (BCAP NB) CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem resizeS_contract : forall NB, In NB CLASSES -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged (ceS NB)).
Proof.
  intros NB Hin. unfold ceS. change (c2_merged (ce2 NB MS)) with (ce NB MS). cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [ exact (contract_of_chk N16 MS certS16) | exact (contract_of_chk N22 MS certS22) | exact (contract_of_chk N26 MS certS26)
    | exact (contract_of_chk N28 MS certS28) | exact (contract_of_chk N3G MS certS3G) | exact (contract_of_chk N3H MS certS3H) | exact (contract_of_chk N3X MS certS3X) ].
Qed.
Theorem resizeL_contract : forall NB, In NB CLASSES -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged (ceL NB)).
Proof.
  intros NB Hin. unfold ceL. change (c2_merged (ce2 NB ML)) with (ce NB ML). cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [ exact (contract_of_chk N16 ML certL16) | exact (contract_of_chk N22 ML certL22) | exact (contract_of_chk N26 ML certL26)
    | exact (contract_of_chk N28 ML certL28) | exact (contract_of_chk N3G ML certL3G) | exact (contract_of_chk N3H ML certL3H) | exact (contract_of_chk N3X ML certL3X) ].
Qed.

(* [comment removed for export] *)
Theorem CT2_resize_sound : forall id c, CT2_resize id = Some c ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged c).
Proof.
  intros id c H. destruct (CT2_resize_cases id c H) as (NB & Hin & [-> | ->]).
  - exact (resizeS_contract NB Hin).
  - exact (resizeL_contract NB Hin).
Qed.
End Contract.
