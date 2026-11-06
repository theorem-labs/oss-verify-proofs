(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgBJCertX.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BgBJ.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cutS : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUELB None (EPI MS) (EPIK MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cutL : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUELB None (EPI ML) (EPIK ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certE : check BSEGS IT ABOTH NXFE LIMIT ISP0 (BgCommon.XN IT NXFE) XE0 XB0 (HSce ceE) 0%nat BFUEL FUEL None (ce_tin ceE) plan_E = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_bj : gplan_ok plan_bj = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_S : gplan_ok (EPIK MS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_L : gplan_ok (EPIK ML) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_E : gplan_ok plan_E = true. Proof. vm_compute. reflexivity. Qed.
End BgBJCertX.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgBJC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BgBJ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BgBJCert BgBJCertX.

Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs2 : holes_only (SHole 2) = true. Proof. reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUELB None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|[|i]]; [| |destruct i; discriminate H].
  - injection H as <- <-. exists (SHole 0). split; [exact gplan_S|]. split; [reflexivity|]. exact BgBJCertX.cutS.
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_L|]. split; [reflexivity|]. exact BgBJCertX.cutL.
Qed.

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
Notation CC := (callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH).

Lemma CT_sound : forall id c, CT id = Some c -> CC c.
Proof.
  intros id c H. unfold CT in H. destruct (Nat.eqb id 201); [|discriminate H]. injection H as <-.
  exact (BgB2JC.b2jv_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
Lemma CT2_sound : forall id c, CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold CT2 in H.
  destruct (Nat.eqb id 200); [injection H as <-; exact (BgB2JC.b2jv_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  exact (BgStrResizeC.CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c H).
Qed.

Theorem b2j_both_callee : CC ce.
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUELB XN _ XB _ CUTS cuts_ok plan_bj (SHole 2) gplan_bj hs2 BoFZCertE.BgBJCert.top).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNw_sound. apply XNd_sound. apply XNp_sound.
    refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT CT_sound _).
    apply GC_all; first [assumption | exact IT_ok].
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    exact (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).
Qed.

Theorem b2j_both_callee_E : CC ceE.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ceE IT IT_ok LIMIT 0%nat BFUEL FUEL (BgCommon.XN IT NXFE) _ plan_E _ gplan_E hs0 BgBJCertX.certE).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXFE RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End BgBJC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgFA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFATop.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgFA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM2.BgFAPlanDef.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma top : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgFATop.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFAC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgFA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM2.BgFAPlanDef BgFATop OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BgFAcM2.BgFAcM3. Import BgFAcM0.BgFA_A0 BgFAcM0.BgFA_A1 BgFAcM0.BgFA_A2 BgFAcM0.BgFA_A3 BgFAcM0.BgFA_A4 BgFAcM0.BgFA_A5 BgFAcM0.BgFA_A6 BgFAcM0.BgFA_A7 BgFAcM1.BgFA_A8 BgFAcM1.BgFA_A9 BgFAcM1.BgFA_A10 BgFAcM1.BgFA_A11 BgFAcM1.BgFA_A12 BgFAcM1.BgFA_A13 BgFAcM1.BgFA_A14 BgFAcM1.BgFA_A15 BgFAcM2.BgFA_A16 BgFAcM2.BgFA_A17 BgFAcM2.BgFA_A18 BgFAcM2.BgFA_A19 BgFAcM2.BgFA_A20 BgFAcM2.BgFA_A21 BgFAcM2.BgFA_A22 BgFAcM2.BgFA_A23 BgFAcM2.BgFAcM3.BgFA_A24 BgFAcM2.BgFAcM3.BgFA_A25 BgFAcM2.BgFAcM3.BgFA_A26 BgFAcM2.BgFAcM3.BgFA_A27.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt i).
  {
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A0.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A1.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A2.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A3.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A4.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A5.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A6.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM0.BgFA_A7.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A8.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A9.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A10.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A11.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A12.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A13.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A14.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM1.BgFA_A15.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A16.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A17.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A18.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A19.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A20.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A21.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A22.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFA_A23.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFAcM3.BgFA_A24.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFAcM3.BgFA_A25.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFAcM3.BgFA_A26.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgFAcM2.BgFAcM3.BgFA_A27.cut|].
  exfalso. rewrite (proj2 (nth_error_None CUTS _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma top_cert : exists sh, holes_only sh = true /\
  check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk sh.
Proof. eexists. split; [| exact BgFATop.top]. reflexivity. Qed.

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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Theorem fa_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  destruct top_cert as (sh & Hsh & CERT).
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ XB _ CUTS cuts_ok plan_top sh top_gplan Hsh CERT).
  -   intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn.
Qed.
End Contract.
End BgFAC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFMSI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSL.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition S_C : acs := Eval vm_compute in
  snd (dpath BSEGS IT_I ABOTH (XN IT_I NXF) XB0 BFUEL NXF (ce_tin ceI) [DRun []; DExt 50 [ELit 0]; DRun [0xa158c]; DLo KLN 1; DRun [0xa1610]; DBrF; DLo (esub EE IT0) 0; DRun [0xa181c]] 0).
Definition XD : expr := EVar 100.  Definition XER : expr := EVar 101.
Definition shF (a : saddr) : bool :=   (* [comment removed for export] *)
  match a with SA (EAlu ALU_SRL (EVar 43) (ELit 3)) _ => true | _ => false end.
Definition kin0 (K : kentry) : bool := existsb (APC.kentry_eqb K) (kn (ce_tin ceI)).
Definition keepX (K : kentry) : bool :=
  match K with
  | KWord (SA b 0) _ _ => negb (expr_eqb b Q) && negb (expr_eqb b C) && (kin0 K || negb (kentry_vars_lt NXF K))
  | KWord a _ _ => negb (shF a)
  | KRange _ _ _ => kin0 K || negb (kentry_vars_lt NXF K)
  | _ => true
  end.
Definition kn_exitX : list kentry :=
  [KWord (SA Q 0) 8 (eadd IT0 XD); KRange XD 0 10; KRange (esub EE (eadd IT0 XD)) 0 BUFMAX; KWord (SA C 0) 4 XER; KRange XER 0 255].
Definition liveX : list nat := [0; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition regsX : list expr :=
  map (fun i => if existsb (Nat.eqb i) liveX then nth i (s_regs (a_ss S_C)) (ELit 0) else EVar (102 + i)) (seq 0 32).
Definition XT : acs := with_ss S_C (mk_ss 0xa181c regsX (kn_exitX ++ filter keepX (kn S_C)) 140).
Definition kX : plan := PRun [0xa1850] (PExt 51 [] (PRun [] (PHandoffW 0 [(43%nat, XD)]))).
Definition CUTS : list (acs * plan) := [(XT, kX)].

Definition plan_lam : plan :=
  (PRun [] (PExt 50 [ELit 0] (PRun [0xa158c] (PCase2 KLN 1 (PRun [0xa1610] (PBranch (PCase2 (esub EE IT0) 0 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 0)])) (PRun [0xa16fc] (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1708] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 5)]))) (PRun [0xa17a4] (PCaseReg 13 0 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PCaseReg 13 1 (PRun [0xa17b8] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 2)]))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 2)]))) (PRespell 13 (ELit 2) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))) (PRespell 13 (ELit 4) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 3)]))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 3)])))) (PRespell 13 (ELit 6) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))) (PRespell 13 (ELit 8) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 5)]))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 5)])))) (PRespell 13 (ELit 10) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))) (PRespell 13 (ELit 12) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 9)]))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 9)])))) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)]))))))) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 1)])))))))))) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 0)])))) (PRun [0xa181c] (PHandoffW 1 [(100%nat, ELit 0)])))))).

Lemma gplan : gplan_ok plan_lam = true. Proof. vm_compute. reflexivity. Qed.

Lemma hshape1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
Lemma gplanX : gplan_ok kX = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check BSEGS IT_I ABOTH NXF LIMIT ISP0 (XN IT_I NXF) XE0 XB0 (HScut ceI CUTS 0) 0%nat BFUEL FUEL None (ce_tin ceI) plan_lam = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cut_cert : check BSEGS IT_I ABOTH NXF LIMIT ISP0 (XN IT_I NXF) XE0 XB0 (HScut ceI CUTS 1) 0%nat BFUEL FUEL None XT kX = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check BSEGS IT_I ABOTH (ce_nxf ceI) LIMIT ISP0 (XN IT_I NXF) XE0 XB0 (HScut ceI CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H].
  injection H as <- <-. exists (SHole 0). split; [exact gplanX|]. split; [reflexivity|]. exact cut_cert.
Qed.
End BgFMSI.
Module BgFMSD.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSL.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition S_C : acs := Eval vm_compute in
  snd (dpath BSEGS IT_D ABOTH (XN IT_D NXF) XB0 BFUEL NXF (ce_tin ceD) [DRun []; DExt 50 [ELit 0]; DRun [0xa1bd0]; DLo KLN 1; DRun [0xa1c54]; DBrF; DLo (esub EE IT0) 0; DRun [0xa1e94]] 0).
Definition XD : expr := EVar 100.  Definition XER : expr := EVar 101.
Definition shF (a : saddr) : bool :=   (* [comment removed for export] *)
  match a with SA (EAlu ALU_SRL (EVar 43) (ELit 3)) _ => true | _ => false end.
Definition kin0 (K : kentry) : bool := existsb (APC.kentry_eqb K) (kn (ce_tin ceD)).
Definition keepX (K : kentry) : bool :=
  match K with
  | KWord (SA b 0) _ _ => negb (expr_eqb b Q) && negb (expr_eqb b C) && (kin0 K || negb (kentry_vars_lt NXF K))
  | KWord a _ _ => negb (shF a)
  | KRange _ _ _ => kin0 K || negb (kentry_vars_lt NXF K)
  | _ => true
  end.
Definition kn_exitX : list kentry :=
  [KWord (SA Q 0) 8 (eadd IT0 XD); KRange XD 0 10; KRange (esub EE (eadd IT0 XD)) 0 BUFMAX; KWord (SA C 0) 4 XER; KRange XER 0 255].
Definition liveX : list nat := [0; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition regsX : list expr :=
  map (fun i => if existsb (Nat.eqb i) liveX then nth i (s_regs (a_ss S_C)) (ELit 0) else EVar (102 + i)) (seq 0 32).
Definition XT : acs := with_ss S_C (mk_ss 0xa1e94 regsX (kn_exitX ++ filter keepX (kn S_C)) 140).
Definition kX : plan := PRun [0xa1ec8] (PExt 51 [] (PRun [] (PHandoffW 0 [(43%nat, XD)]))).
Definition CUTS : list (acs * plan) := [(XT, kX)].

Definition plan_lam : plan :=
  (PRun [] (PExt 50 [ELit 0] (PRun [0xa1bd0] (PCase2 KLN 1 (PRun [0xa1c54] (PBranch (PCase2 (esub EE IT0) 0 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 0)])) (PRun [0xa1d40] (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1d50] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 9)]))) (PRun [0xa1e1c] (PCaseReg 13 0 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PCaseReg 13 1 (PRun [0xa1e30] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 2)]))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 2)]))) (PRespell 13 (ELit 2) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)]))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)]))) (PRespell 13 (ELit 4) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 3)]))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 3)])))) (PRespell 13 (ELit 6) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 5)])))) (PRespell 13 (ELit 8) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 5)]))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 5)])))) (PRespell 13 (ELit 10) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)]))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 9)])))) (PRespell 13 (ELit 12) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 9)]))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 9)])))) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)]))))))) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 1)])))))))))) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 0)])))) (PRun [0xa1e94] (PHandoffW 1 [(100%nat, ELit 0)])))))).

Lemma gplan : gplan_ok plan_lam = true. Proof. vm_compute. reflexivity. Qed.

Lemma hshape1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
Lemma gplanX : gplan_ok kX = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check BSEGS IT_D ABOTH NXF LIMIT ISP0 (XN IT_D NXF) XE0 XB0 (HScut ceD CUTS 0) 0%nat BFUEL FUEL None (ce_tin ceD) plan_lam = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cut_cert : check BSEGS IT_D ABOTH NXF LIMIT ISP0 (XN IT_D NXF) XE0 XB0 (HScut ceD CUTS 1) 0%nat BFUEL FUEL None XT kX = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check BSEGS IT_D ABOTH (ce_nxf ceD) LIMIT ISP0 (XN IT_D NXF) XE0 XB0 (HScut ceD CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H].
  injection H as <- <-. exists (SHole 0). split; [exact gplanX|]. split; [reflexivity|]. exact cut_cert.
Qed.
End BgFMSD.
Module BgFMSLC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSL.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

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

Section CI.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT_I -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT_I ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.
Theorem lam_i_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ceI.
Proof.
  (* [comment removed for export] *)
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ceI IT_I IT_I_ok LIMIT 0%nat BFUEL FUEL (XN IT_I NXF) _ XB0 _ BgFMSI.CUTS BgFMSI.cuts_ok BgFMSI.plan_lam (SHole 1) BgFMSI.gplan BgFMSI.hshape1 BgFMSI.cert).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT_I IT_I_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_I_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn.
Qed.
End CI.

Section CD.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT_D -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT_D ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.
Theorem lam_d_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ceD.
Proof.
  (* [comment removed for export] *)
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ceD IT_D IT_D_ok LIMIT 0%nat BFUEL FUEL (XN IT_D NXF) _ XB0 _ BgFMSD.CUTS BgFMSD.cuts_ok BgFMSD.plan_lam (SHole 1) BgFMSD.gplan BgFMSD.hshape1 BgFMSD.cert).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT_D IT_D_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_D_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn.
Qed.
End CD.
End Contract.
End BgFMSLC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFMSHCertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSH.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fj_JO : expr := EVar 120.
Definition fj_JN : expr := EVar 121.
Definition fj_steps : list (list dstep) :=
  [ [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRLo 16 1; DRLo 16 0; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRLo 16 1; DRHi 16 0; DHi (esub (esub EE IT0) (ELit 1)) 1; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRHi 16 1; DRLo 16 2; DHi (esub (esub EE IT0) (ELit 1)) 3; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRHi 16 1; DRHi 16 2; DHi (esub (esub EE IT0) (ELit 1)) 7; DRun [0xa2524]; DBrF; DRun [0xa252c]] ].
Definition fj_state (l : list dstep) : acs := snd (dpath BSEGS IT ABOTH (XN MS) (XB MS) BFUEL 44%nat (ce_tin (ce MS)) l 0).
Definition fj_kmem (K : kentry) (k : list kentry) : bool := existsb (APC.kentry_eqb K) k.
Definition fj_kcommon (s0 : acs) (ss : list acs) : list kentry := List.filter (fun K => forallb (fun s => fj_kmem K (kn s)) ss) (kn s0).
Fixpoint fj_regs (rs : list expr) (rss : list (list expr)) (i v : nat) (ov : list (nat * expr)) : list expr :=
  match rs with
  | [] => []
  | r :: rs' =>
      match find (fun p => Nat.eqb (fst p) i) ov with
      | Some (_, e) => e :: fj_regs rs' rss (Datatypes.S i) v ov
      | None =>
          if forallb (fun l => expr_eqb (nth i l (ELit 0)) r) rss then r :: fj_regs rs' rss (Datatypes.S i) v ov
          else EVar v :: fj_regs rs' rss (Datatypes.S i) (Datatypes.S v) ov
      end
  end.
Definition fj_JH : acs := Eval vm_compute in
  match map fj_state fj_steps with
  | s0 :: ss =>
      let regs := fj_regs (s_regs (a_ss s0)) (map (fun s => s_regs (a_ss s)) ss) 0%nat 122%nat [(18%nat, fj_JN); (16%nat, EVar 140)] in
      let kq := List.filter (fun K => match K with KWord (SA b 0) _ _ => negb (expr_eqb b Q) && kentry_vars_lt 44 K
                                                | _ => kentry_vars_lt 44 K end) (fj_kcommon s0 ss) in
      let kj := [KWord (SA Q 0) 8 (eadd IT0 fj_JO); KRange fj_JO 2 9; KRange (esub (esub EE IT0) fj_JO) 0 BUFMAX; KRange fj_JN 0 (2 ^ 48)] in
      with_ss s0 (mk_ss 0xa252c regs (kj ++ kq) 150%nat)
  | [] => ce_tin (ce MS)
  end.

Definition plan_hello : plan :=
  (PCase2 KLN 4 (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])) (PRun [0xa2268] (PBranch (PRun [0xa2274] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])) (PRun [0xa2344] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa2384] (PVia 1 fj_JH 120 (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 2)]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 3)]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 5)])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa2524] (PBranch (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 9)])) (PRun [] (PHandoffW 0 [(44%nat, ELit 9)])))))))) (PBump 150 (PFresh 18 0 None (PRun [0xa2554] (PBranch (PFactLe (EVar 150) (esub (esub EE IT0) (EVar 120)) BUFMAX (PRun [] (PBump 200 (PExt2 102 (resize_args_S (EVar 43) e_mtr e_fb) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 0 [(44%nat, (eadd (EVar 150) (EVar 120))); (47%nat, (EVar 150))]))) (PExt 5 [] (PRun [] (PHandoffW 0 [(44%nat, (eadd (EVar 150) (EVar 120))); (47%nat, (EVar 150))]))))))) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 1 [(44%nat, (eadd (EVar 150) (EVar 120))); (46%nat, EVar 202); (47%nat, EVar 200); (48%nat, (EVar 150)); (49%nat, EVar 201)]))) (PExt 5 [] (PRun [] (PHandoffW 1 [(44%nat, (eadd (EVar 150) (EVar 120))); (46%nat, EVar 202); (47%nat, EVar 200); (48%nat, (EVar 150)); (49%nat, EVar 201)]))))))))))) (PRun [] (PHandoffW 0 [(44%nat, EVar 120)]))))))))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)]))))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)]))))).

Lemma gplan : gplan_ok plan_hello = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check BSEGS IT ABOTH (ce_nxf (ce MS)) LIMIT ISP0 (XN MS) XE0 (XB MS) (HSce (ce MS)) 0%nat BFUEL FUEL None (ce_tin (ce MS)) plan_hello = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgFMSHCertS.
Module BgFMSHCertL.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSH.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fj_JO : expr := EVar 120.
Definition fj_JN : expr := EVar 121.
Definition fj_steps : list (list dstep) :=
  [ [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRLo 16 1; DRLo 16 0; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRLo 16 1; DRHi 16 0; DHi (esub (esub EE IT0) (ELit 1)) 1; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRHi 16 1; DRLo 16 2; DHi (esub (esub EE IT0) (ELit 1)) 3; DRun [0xa252c]];
    [DHi KLN 4; DRun [0xa2268]; DBrF; DRun [0xa2274]; DBrF; DHi (esub EE IT0) 0; DRun [0xa2344]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa2384]; DRHi 16 1; DRHi 16 2; DHi (esub (esub EE IT0) (ELit 1)) 7; DRun [0xa2524]; DBrF; DRun [0xa252c]] ].
Definition fj_state (l : list dstep) : acs := snd (dpath BSEGS IT ABOTH (XN ML) (XB ML) BFUEL 46%nat (ce_tin (ce ML)) l 0).
Definition fj_kmem (K : kentry) (k : list kentry) : bool := existsb (APC.kentry_eqb K) k.
Definition fj_kcommon (s0 : acs) (ss : list acs) : list kentry := List.filter (fun K => forallb (fun s => fj_kmem K (kn s)) ss) (kn s0).
Fixpoint fj_regs (rs : list expr) (rss : list (list expr)) (i v : nat) (ov : list (nat * expr)) : list expr :=
  match rs with
  | [] => []
  | r :: rs' =>
      match find (fun p => Nat.eqb (fst p) i) ov with
      | Some (_, e) => e :: fj_regs rs' rss (Datatypes.S i) v ov
      | None =>
          if forallb (fun l => expr_eqb (nth i l (ELit 0)) r) rss then r :: fj_regs rs' rss (Datatypes.S i) v ov
          else EVar v :: fj_regs rs' rss (Datatypes.S i) (Datatypes.S v) ov
      end
  end.
Definition fj_JH : acs := Eval vm_compute in
  match map fj_state fj_steps with
  | s0 :: ss =>
      let regs := fj_regs (s_regs (a_ss s0)) (map (fun s => s_regs (a_ss s)) ss) 0%nat 122%nat [(18%nat, fj_JN); (16%nat, EVar 140)] in
      let kq := List.filter (fun K => match K with KWord (SA b 0) _ _ => negb (expr_eqb b Q) && kentry_vars_lt 46 K
                                                | _ => kentry_vars_lt 46 K end) (fj_kcommon s0 ss) in
      let kj := [KWord (SA Q 0) 8 (eadd IT0 fj_JO); KRange fj_JO 2 9; KRange (esub (esub EE IT0) fj_JO) 0 BUFMAX; KRange fj_JN 0 (2 ^ 48)] in
      with_ss s0 (mk_ss 0xa252c regs (kj ++ kq) 150%nat)
  | [] => ce_tin (ce ML)
  end.

Definition plan_hello : plan :=
  (PCase2 KLN 4 (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])) (PRun [0xa2268] (PBranch (PRun [0xa2274] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])) (PRun [0xa2344] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa2384] (PVia 1 fj_JH 120 (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 2)]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 3)]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 5)])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa2524] (PBranch (PRun [0xa252c] (PMergeW 1 [(120%nat, ELit 9)])) (PRun [] (PHandoffW 0 [(46%nat, ELit 9)])))))))) (PBump 150 (PFresh 18 0 None (PRun [0xa2554] (PBranch (PFactLe (EVar 150) (esub (esub EE IT0) (EVar 120)) BUFMAX (PRun [] (PBump 200 (PExt2 112 (resize_args_L (EVar 43) (EVar 44) (EVar 45) e_mtr e_fb) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 0 [(46%nat, (eadd (EVar 150) (EVar 120))); (49%nat, EVar 43); (50%nat, (EVar 150)); (51%nat, EVar 45)]))) (PExt 5 [] (PRun [] (PHandoffW 0 [(46%nat, (eadd (EVar 150) (EVar 120))); (49%nat, EVar 43); (50%nat, (EVar 150)); (51%nat, EVar 45)]))))))) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 1 [(46%nat, (eadd (EVar 150) (EVar 120))); (48%nat, EVar 202); (49%nat, EVar 200); (50%nat, (EVar 150)); (51%nat, EVar 201)]))) (PExt 5 [] (PRun [] (PHandoffW 1 [(46%nat, (eadd (EVar 150) (EVar 120))); (48%nat, EVar 202); (49%nat, EVar 200); (50%nat, (EVar 150)); (51%nat, EVar 201)]))))))))))) (PRun [] (PHandoffW 0 [(46%nat, EVar 120)]))))))))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)]))))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)]))))).

Lemma gplan : gplan_ok plan_hello = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check BSEGS IT ABOTH (ce_nxf (ce ML)) LIMIT ISP0 (XN ML) XE0 (XB ML) (HSce (ce ML)) 0%nat BFUEL FUEL None (ce_tin (ce ML)) plan_hello = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgFMSHCertL.
Module BgFMSHC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSH.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

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

Lemma hello_callee_gen : forall (m : smode) (p : plan),
  gplan_ok p = true ->
  check BSEGS IT ABOTH (ce_nxf (ce m)) LIMIT ISP0 (XN m) XE0 (XB m) (HSce (ce m)) 0%nat BFUEL FUEL None (ce_tin (ce m)) p = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (ce m).
Proof.
  intros m p HG CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (ce m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN m) _ (XB m) _ p _ HG hs0 CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound.
    refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok (NXF m) [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok (NXF m) [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem lam_hello_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (ce MS).
Proof. exact (hello_callee_gen MS BgFMSHCertS.plan_hello BgFMSHCertS.gplan BgFMSHCertS.cert). Qed.
Theorem lam_hello_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (ce ML).
Proof. exact (hello_callee_gen ML BgFMSHCertL.plan_hello BgFMSHCertL.gplan BgFMSHCertL.cert). Qed.
End Contract.
End BgFMSHC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSCertL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFMSC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgFMST OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSCertL.BgFMS OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSCertL.BgFMSPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSCertL.BgFMSCertTop OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSCertL.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|[|[|i]]]; [| | |destruct i; discriminate H].
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_L|]. split; [reflexivity|]. exact BgFMSCertL.cutL.
  - injection H as <- <-. exists (SHole 0). split; [exact gplan_X0|]. split; [reflexivity|]. exact BgFMSCertL.cutXS.   (* [comment removed for export] *)
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_X1|]. split; [reflexivity|]. exact BgFMSCertL.cutXL.
Qed.

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

Theorem from_my_struct_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ XB _ CUTS cuts_ok plan_top (SHole 0) gplan_top hs0 BgFMSCertL.BgFMSCertTop.top).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound. apply BgReadCert.BgPw.XNw_sound.   (* [comment removed for export] *)
    refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 100); [injection H as <-; exact (BgFAC.fa_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 101); [injection H as <-; exact (BgFMSLC.lam_i_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 102); [|discriminate H]. injection H as <-.
      exact (BgFMSLC.lam_d_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 _).
    intros id c' H. unfold CT2 in H.
    destruct (Nat.eqb id 103); [injection H as <-; exact (BgFMSHC.lam_hello_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
    destruct (Nat.eqb id 113); [|discriminate H]. injection H as <-.
    exact (BgFMSHC.lam_hello_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
End Contract.
End BgFMSC.
Module BgReadC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgRead OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

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

Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Theorem read_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ XB _ plan_read _ read_gplan hs0 read_cert).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound.
    refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 _).
    intros id c' H. unfold CT2 in H. destruct (Nat.eqb id 101); [|discriminate H]. injection H as <-.
    exact (BgFMSC.from_my_struct_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
End Contract.
End BgReadC.
Module BgReadEC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgRead OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgReadE.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

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

Theorem read_both_callee_E : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH RdE.ceE.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            RdE.ceE IT IT_ok LIMIT 0%nat BFUEL FUEL RdE.XNE _ RdE.plan_readE _ readE_gplan hs0 readE_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold RdE.XNE.
  apply XNp_sound.
  refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok RdE.NXFE [] GBOTH 0 0 fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact IT_ok].
Qed.
End Contract.
End BgReadEC.
Module BgStrCtorC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BgStrCtor.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma cert : check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_ctor = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
Lemma gplan : gplan_ok plan_ctor = true. Proof. vm_compute. reflexivity. Qed.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Theorem str_ctor_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_ctor _ gplan hshape cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End BgStrCtorC.
Require LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgVec.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgVecT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CtorP.
Import Ctor.
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 38%nat); (0x9e684, 50%nat); (0x9e74c, 50%nat); (0x9e830, 41%nat); (0x9e9b0, 34%nat); (0x9ea38, 20%nat);
                                              (0x9ea88, 56%nat); (0x9eb68, 41%nat); (0x9ec0c, 182%nat); (0x9eee4, 30%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition XN : nat -> list expr -> acs -> option acs := XNann NXF GBOTH ANNOT (XNp (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT0)).
Definition HEAD : Z := 0x9ed78.       (* [comment removed for export] *)
Definition BACK : Z := 0x9edc8.       (* [comment removed for export] *)
Definition REL : Z := 0x9ee5c.        (* [comment removed for export] *)
Definition DPATH := dpath BSEGS IT ABOTH XN XB0 BFUEL.
(* [comment removed for export] *)
Definition ST_first : acs :=
  snd (DPATH 0%nat tin [DRun []; DExt 20 []; DRun []; DExt 8 []; DRun []; DExt 8 []; DRun []; DExt 50 [ELit 1]; DExt 47 []; DRun [HEAD]; DRun [HEAD]] 0).
Definition ST_second : acs := snd (DPATH 0%nat ST_first [DRun [BACK]; DBrT; DRun [HEAD]] 0).
Definition F : expr := EVar 82.      (* [comment removed for export] *)
Definition shF : expr := EAlu ALU_SRL F (ELit 3).
(* [comment removed for export] *)
Definition JV : nat := 110.  Definition J : expr := EVar 110.
Definition F_facts : list kentry :=
  [KRange F PTRLO (PTRHI - 128); KRange (eaddz F 128) (PTRLO + 128) PTRHI; KAlign F 128;
   KWr (SA F 0) (ELit 128); KUnk (SA F 0) (ELit 128);
   KUnk (SA shF SB) (ELit 16); KWr (SA shF SB) (ELit 16);
   KDisj (SA shF SB) (ELit 16) (SA (ELit 0) (SB + IMG_LO / 8)) (ELit (IMG_SZ / 8));
   KDisj (SA F 0) (ELit 128) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart F 0 (ELit 128); shmap_apart F 0 (ELit 128);
   KDisj (SA F 0) (ELit 128) (SA P 0) SZ; KDisj (SA F 0) (ELit 128) (SA FIRST 0) SZ; KDisj (SA F 0) (ELit 128) (SA V 0) (ELit 24);
   KWord (SA F 32) 8 (eadd P J)].
Definition kn_loop : list kentry :=
  [ KRange J 0 SZHI; KRange (esub SZ J) 1 SZHI; KWord (SA V 0) 8 P; KWord (SA V 8) 8 P; KWord (SA V 16) 8 (eadd SZ P) ]
  ++ F_facts ++ blkP P SZ ++ kn_fixed ++ stk_facts ++ [KShOk (SA e_sp (- FRS)) (ELit FRS)].
Definition mkcsL (vis : list (expr * expr)) (mtr : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false mtr [(F, ELit 128)] (eaddz e_fb (-1)).
Definition INV_d : acs :=
  let ss := [ST_first; ST_second] in
  let rs := jregs (map (fun s => s_regs (a_ss s)) ss) 0 32 [(10%nat, eadd FIRST J); (20%nat, eadd FIRST J)] 110 111 in
  mkcsL [(P, SZ); (FIRST, SZ)] MTRX HEAD rs (jframe 288 ss 110 ++ kn_loop) (maxvar_regs rs 111).
Definition INV : acs := Eval vm_compute in INV_d.
Definition body : plan := PRun [BACK] (PCase2 (esub SZ J) 1 (PRun [REL] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [HEAD] PNext)).
Definition plan_ctor : plan :=
  PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 8 [] (PRun [] (PExt 50 [ELit 1] (PExt 47 []
    (PRun [HEAD] (PRun [HEAD] (PLoop JV SZ INV [] body (PContraH 0)))))))))))).

End CtorP.

Module PushP.
Import Push.
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 45%nat); (0x9f4b0, 100%nat); (0x9f640, 83%nat); (0x9f78c, 123%nat); (0x9f978, 70%nat);
                                              (0x9e830, 41%nat); (0x9e9b0, 34%nat); (0x9f274, 47%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition XN : nat -> list expr -> acs -> option acs := XNann NXF GBOTH ANNOT (XNp (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT0)).
Definition XNE : nat -> list expr -> acs -> option acs := XNann NXFE GBOTH ANNOT (XNp (XNc BSEGS IT ABOTH NXFE GBOTH BCAPE 1 CT0)).
(* [comment removed for export] *)
Definition tail_push (g : plan -> plan) : plan :=
  PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (g (PExt 22 [] (PRun [] (PHandoff 0)))))))))))).
Definition plan_push : plan :=
  PCase2 SZ 1
    (PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (PRespell 8 (eaddz P2 2) (PExt 22 [] (PRun [] (PHandoff 1)))))))))))))
    (tail_push (fun k => PFact (KRange (eaddz (eadd SZ P2) 1) PTRLO PTRHI) k)).
Definition plan_pushE : plan := PRun [] (PExt 20 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (PHandoff 0))))))).


End PushP.
End BgVec.
Module BgVecCert.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon BgVec.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma ctor_cert : check BSEGS CtorP.IT ABOTH Ctor.NXF LIMIT ISP0 CtorP.XN XE0 XB0 (HSce Ctor.ce) 0%nat BFUEL FUEL None (ce_tin Ctor.ce) CtorP.plan_ctor = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma ctor_gplan : gplan_ok CtorP.plan_ctor = true. Proof. vm_compute. reflexivity. Qed.
Lemma push_cert : check BSEGS PushP.IT ABOTH Push.NXF LIMIT ISP0 PushP.XN XE0 XB0 (HSce Push.ce) 0%nat BFUEL FUEL None (ce_tin Push.ce) PushP.plan_push = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma push_gplan : gplan_ok PushP.plan_push = true. Proof. vm_compute. reflexivity. Qed.
Lemma pushE_cert : check BSEGS PushP.IT ABOTH Push.NXFE LIMIT ISP0 PushP.XNE XE0 XB0 (HSce Push.ceE) 0%nat BFUEL FUEL None (ce_tin Push.ceE) PushP.plan_pushE = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma pushE_gplan : gplan_ok PushP.plan_pushE = true. Proof. vm_compute. reflexivity. Qed.
End BgVecCert.
Module BgVecC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn BgVec BgVecCert.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

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
Hypothesis HANN : h_annot_at BSEGS GBOTH fx_ok AINVH RZ ANNOT.
Notation CC := (callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH).

Theorem vec_ctor_both_callee : CC Ctor.ce.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            Ctor.ce CtorP.IT CtorP.IT_ok LIMIT 0%nat BFUEL FUEL CtorP.XN _ CtorP.plan_ctor _ ctor_gplan hs0 ctor_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold CtorP.XN.
  refine (XNann_sound BSEGS [] GBOTH fx_ok SHC AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            ABOTH both_A_img_hi both_A_img_lo both_in_hull KCAP Ctor.NXF FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound BSEGS CtorP.IT ABOTH both_in_hull both_hull_ok CtorP.IT_ok Ctor.NXF [] GBOTH Ctor.BCAP Ctor.CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact CtorP.IT_ok].
Qed.

(* [comment removed for export] *)
Theorem vec_push_both_callee : CC Push.ce.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            Push.ce PushP.IT PushP.IT_ok LIMIT 0%nat BFUEL FUEL PushP.XN _ PushP.plan_push _ push_gplan hs1 push_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold PushP.XN.
  refine (XNann_sound BSEGS [] GBOTH fx_ok SHC AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            ABOTH both_A_img_hi both_A_img_lo both_in_hull KCAP Push.NXF FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound BSEGS PushP.IT ABOTH both_in_hull both_hull_ok PushP.IT_ok Push.NXF [] GBOTH Push.BCAP Push.CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact PushP.IT_ok].
Qed.
(* [comment removed for export] *)
Theorem vec_push_both_callee_E : CC Push.ceE.
Proof.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            Push.ceE PushP.IT PushP.IT_ok LIMIT 0%nat BFUEL FUEL PushP.XNE _ PushP.plan_pushE _ pushE_gplan hs0 pushE_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold PushP.XNE.
  refine (XNann_sound BSEGS [] GBOTH fx_ok SHC AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            ABOTH both_A_img_hi both_A_img_lo both_in_hull KCAP Push.NXFE FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound BSEGS PushP.IT ABOTH both_in_hull both_hull_ok PushP.IT_ok Push.NXFE [] GBOTH Push.BCAPE 1 fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact PushP.IT_ok].
Qed.
End Contract.
End BgVecC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoFZCertN0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma top : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUELB None (ce_tin ce) plan_top = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cut2 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 3) 0%nat BFUEL FUELB None J2 planJ2 = COk (SHole 4).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 4))). Qed.
Lemma cut5 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 6) 0%nat BFUEL FUELB None J4_0 planJ4 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cut6 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 7) 0%nat BFUEL FUELB None J4_1 planJ4 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_top : gplan_ok plan_top = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_AS : gplan_ok (planA MS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_AL : gplan_ok (planA ML) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J2 : gplan_ok planJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J30 : gplan_ok (planJ3 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J31 : gplan_ok (planJ3 1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J4 : gplan_ok planJ4 = true. Proof. vm_compute. reflexivity. Qed.
End BoFZCertN0.
Module BoFZCertN1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut0 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUELB None A_S (planA MS) = COk (SHole 3).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 3))). Qed.
End BoFZCertN1.
Module BoFZCertN2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut1 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUELB None A_L (planA ML) = COk (SHole 3).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 3))). Qed.
End BoFZCertN2.
Module BoFZCertN3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut3 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 4) 0%nat BFUEL FUELB None J3_0 (planJ3 0) = COk (SHole 6).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 6))). Qed.
End BoFZCertN3.
Module BoFZCertN4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut4 : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 5) 0%nat BFUEL FUELB None J3_1 (planJ3 1) = COk (SHole 7).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 7))). Qed.
End BoFZCertN4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BgNameW OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.BoFZP.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoFZCertE OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error FuzzNP.CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check BSEGS FuzzNP.IT ABOTH (ce_nxf FuzzN.ce) LIMIT ISP0 FuzzNP.XN XE0 FuzzNP.XB (HScut FuzzN.ce FuzzNP.CUTS (Datatypes.S i)) 0%nat BFUEL FuzzNP.FUELB None T k = COk sh.
Proof.
  intros i T k H.
  destruct i as [|[|[|[|[|[|[|i]]]]]]]; [| | | | | | |destruct i; discriminate H]; injection H as <- <-.
  - exists (SHole 3). split; [exact BoFZCertN0.gplan_AS|]. split; [reflexivity|]. exact BoFZCertN1.cut0.
  - exists (SHole 3). split; [exact BoFZCertN0.gplan_AL|]. split; [reflexivity|]. exact BoFZCertN2.cut1.
  - exists (SHole 4). split; [exact BoFZCertN0.gplan_J2|]. split; [reflexivity|]. exact BoFZCertN0.cut2.
  - exists (SHole 6). split; [exact BoFZCertN0.gplan_J30|]. split; [reflexivity|]. exact BoFZCertN3.cut3.
  - exists (SHole 7). split; [exact BoFZCertN0.gplan_J31|]. split; [reflexivity|]. exact BoFZCertN4.cut4.
  - exists (SHole 0). split; [exact BoFZCertN0.gplan_J4|]. split; [reflexivity|]. exact BoFZCertN0.cut5.
  - exists (SHole 0). split; [exact BoFZCertN0.gplan_J4|]. split; [reflexivity|]. exact BoFZCertN0.cut6.
Qed.

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
Hypothesis HANN : h_annot_at BSEGS GBOTH fx_ok AINVH RZ ANNOT.
Hypothesis HSF5 : h_setsh_at BSEGS GBOTH fx_ok AINVH RZ SF5_ENTRY.
Notation CC := (callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH).

Lemma CTN_sound : forall id c, FuzzNP.CT id = Some c -> CC c.
Proof.
  intros id c H. unfold FuzzNP.CT in H.
  destruct (Nat.eqb id 110); [injection H as <-; exact (BgVecC.vec_ctor_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  destruct (Nat.eqb id 111); [injection H as <-; exact (BgStrCtorC.str_ctor_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all BoFZCertE.BgStrCtor.IT BoFZCertE.BgStrCtor.NXF 0 0))|].
  discriminate H.
Qed.
Lemma CT2N_sound : forall id c, FuzzNP.CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold FuzzNP.CT2 in H.
  destruct (Nat.eqb id 112); [injection H as <-; exact (BgReadC.read_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 113); [injection H as <-; exact (BgBJC.b2j_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 114); [injection H as <-; exact (BgVecC.vec_push_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  discriminate H.
Qed.
Lemma CTE_sound : forall id c, FuzzEP.CT id = Some c -> CC c.
Proof.
  intros id c H. unfold FuzzEP.CT in H.
  destruct (Nat.eqb id 111); [injection H as <-; exact (BgStrCtorC.str_ctor_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all BoFZCertE.BgStrCtor.IT BoFZCertE.BgStrCtor.NXF 0 0))|].
  destruct (Nat.eqb id 115); [injection H as <-; exact (BgReadEC.read_both_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 116); [injection H as <-; exact (BgBJC.b2j_both_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 117); [injection H as <-; exact (BgVecC.vec_push_both_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  discriminate H.
Qed.
Lemma CT2E_sound : forall id c, FuzzEP.CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold FuzzEP.CT2 in H.
  destruct (Nat.eqb id 112); [injection H as <-; exact (BgReadC.read_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  discriminate H.
Qed.

(* [comment removed for export] *)
Ltac xn_stack IT IT_ok NXF BCAP CCAP CT CT_sound :=
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa;
  apply BoFZCertE.BgNameW.XNn_sound; [exact HUa|];      (* [comment removed for export] *)
  refine (XNsf5_sound BSEGS [] GBOTH fx_ok SHC AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            ABOTH both_A_img_hi both_A_img_lo KCAP NXF FS0 UINV HUa SF5_ENTRY HSF5 _ _);
  refine (XNann_sound BSEGS [] GBOTH fx_ok SHC AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            ABOTH both_A_img_hi both_A_img_lo both_in_hull KCAP NXF FS0 UINV HUa ANNOT HANN _ _);
  apply XNd_sound; apply XNp_sound;
  refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT CT_sound _);
  apply GC_all; first [assumption | exact IT_ok].
Ltac xb_stack NXF BCAP CCAP CT2 CT2_sound :=
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa;
  exact (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).

Theorem fz_both_callee_N : CC BoDrvHooksA.BoFZ.ceN.
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            FuzzN.ce FuzzNP.IT FuzzNP.IT_ok LIMIT 0%nat BFUEL FuzzNP.FUELB FuzzNP.XN _ FuzzNP.XB _ FuzzNP.CUTS cuts_ok FuzzNP.plan_top (SHole 1)
            BoFZCertN0.gplan_top hs1 BoFZCertN0.top).
  - unfold FuzzNP.XN. xn_stack FuzzNP.IT FuzzNP.IT_ok FuzzN.NXF FuzzN.BCAP FuzzN.CCAP FuzzNP.CT CTN_sound.
  - unfold FuzzNP.XB. xb_stack FuzzN.NXF FuzzN.BCAP FuzzN.CCAP FuzzNP.CT2 CT2N_sound.
Qed.

Theorem fz_both_callee_E : CC BoDrvHooksA.BoFZ.ceE.
Proof.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            FuzzE.ce FuzzEP.IT FuzzEP.IT_ok LIMIT 0%nat BFUEL FuzzEP.FUELB FuzzEP.XN _ FuzzEP.XB _ FuzzEP.planE _ BoFZCertE.gplan_E hs0 BoFZCertE.certE).
  - unfold FuzzEP.XN. xn_stack FuzzEP.IT FuzzEP.IT_ok FuzzN.NXF FuzzE.BCAP FuzzE.CCAP FuzzEP.CT CTE_sound.
  - unfold FuzzEP.XB. xb_stack FuzzN.NXF FuzzE.BCAP FuzzE.CCAP FuzzEP.CT2 CT2E_sound.
Qed.
End Contract.
