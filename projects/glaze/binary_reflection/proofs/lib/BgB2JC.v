(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWFcM2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module BgWF_A16.
Lemma cut : cut_ok 16 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A16.

Module BgWF_A17.
Lemma cut : cut_ok 17 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A17.

Module BgWF_A18.
Lemma cut : cut_ok 18 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A18.

Module BgWF_A19.
Lemma cut : cut_ok 19 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A19.

Module BgWF_A20.
Lemma cut : cut_ok 20 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A20.

Module BgWF_A21.
Lemma cut : cut_ok 21 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A21.

Module BgWF_A22.
Lemma cut : cut_ok 22 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A22.

Module BgWF_A23.
Lemma cut : cut_ok 23 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A23.
End BgWFcM2.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWFC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWF OSSVerify.Proofs.glaze.binary_reflection.lib.BgWF OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM1 BgWFcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFcM4. Import BgWFcM0.BgWF_A0 BgWFcM0.BgWF_A1 BgWFcM0.BgWF_A2 BgWFcM0.BgWF_A3 BgWFcM0.BgWF_A4 BgWFcM0.BgWF_A5 BgWFcM0.BgWF_A6 BgWFcM0.BgWF_A7 BgWFcM1.BgWF_A8 BgWFcM1.BgWF_A9 BgWFcM1.BgWF_A10 BgWFcM1.BgWF_A11 BgWFcM1.BgWF_A12 BgWFcM1.BgWF_A13 BgWFcM1.BgWF_A14 BgWFcM1.BgWF_A15 BgWFcM2.BgWF_A16 BgWFcM2.BgWF_A17 BgWFcM2.BgWF_A18 BgWFcM2.BgWF_A19 BgWFcM2.BgWF_A20 BgWFcM2.BgWF_A21 BgWFcM2.BgWF_A22 BgWFcM2.BgWF_A23 BgWFcM3.BgWF_A24 BgWFcM3.BgWF_A25 BgWFcM3.BgWF_A26 BgWFcM3.BgWF_A27 BgWFcM3.BgWF_A28 BgWFcM3.BgWF_A29 BgWFcM3.BgWF_A30 BgWFcM3.BgWF_A31 BgWFcM4.BgWF_A32 BgWFcM4.BgWF_A33 BgWFcM4.BgWF_A34 BgWFcM4.BgWF_A35 BgWFcM4.BgWF_A36 BgWFcM4.BgWF_A37 BgWFcM4.BgWF_A38.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt i).
  {
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A0.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A1.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A2.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A3.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A4.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A5.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A6.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM0.BgWF_A7.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A8.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A9.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A10.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A11.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A12.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A13.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A14.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM1.BgWF_A15.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A16.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A17.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A18.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A19.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A20.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A21.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A22.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM2.BgWF_A23.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A24.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A25.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A26.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A27.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A28.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A29.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A30.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM3.BgWF_A31.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A32.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A33.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A34.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A35.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A36.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A37.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWFcM4.BgWF_A38.cut|].
  exfalso. rewrite (proj2 (nth_error_None CUTS _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma top_cert : exists sh, holes_only sh = true /\
  check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk sh.
Proof. eexists. split; [| exact BgWF.top]. reflexivity. Qed.

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

Theorem write_float_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
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
End BgWFC.
Require LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAf32CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.BgAAf32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAf32CertL1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAf32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT BgWFC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8.BgAAf32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAf32CertS BgAAf32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_f32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAf32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWD OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDcM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWDC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWD OSSVerify.Proofs.glaze.binary_reflection.lib.BgWD OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDcM1. Import BgWDcM0.BgWD_A0 BgWDcM0.BgWD_A1 BgWDcM0.BgWD_A2 BgWDcM0.BgWD_A3 BgWDcM0.BgWD_A4 BgWDcM0.BgWD_A5 BgWDcM0.BgWD_A6 BgWDcM1.BgWD_A7 BgWDcM1.BgWD_A8 BgWDcM1.BgWD_A9 BgWDcM1.BgWD_A10 BgWDcM1.BgWD_A11 BgWDcM1.BgWD_A12 BgWDcM1.BgWD_A13.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt i).
  {
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A0.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A1.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A2.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A3.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A4.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A5.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM0.BgWD_A6.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A7.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A8.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A9.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A10.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A11.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A12.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact BgWDcM1.BgWD_A13.cut|].
  exfalso. rewrite (proj2 (nth_error_None CUTS _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma top_cert : exists sh, holes_only sh = true /\
  check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk sh.
Proof. eexists. split; [| exact BgWD.top]. reflexivity. Qed.

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

Theorem write_double_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
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
End BgWDC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAf64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAf64CertS.
Module BgAAf64CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAf64CertL1.
Module BgAAf64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT BgWDC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAf64 BgAAf64CertS BgAAf64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_f64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_f64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAf64C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgTc32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Lemma callee_c : 
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_tc32 = COk SHAPE ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  intros CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_tc32 _ gplan hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars_u32_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_c cert). Qed.
End Contract.
End BgTc32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAi16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8.BgAAi16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAi16CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAi16CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_i16_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i16_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAi16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgI32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

(* [comment removed for export] *)
Lemma callee_m : forall m p, gplan_ok p = true ->
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) p = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (cem m).
Proof.
  intros m p HG CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ p _ HG hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_i32_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_m ML plan_i32 gplan cert). Qed.
Theorem to_chars40kb_i32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ceS.
Proof. exact (callee_m MS plan_i32S gplanS certS). Qed.
End Contract.
End BgI32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAi32CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAi32CertS.
Module BgAAi32CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAi32CertL1.
Module BgAAi32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32 BgI32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi32 BgAAi32CertS BgAAi32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_i32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAi32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgI64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Lemma callee_c : 
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_i64 = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  intros CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_i64 _ gplan hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_i64_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_c cert). Qed.
End Contract.
End BgI64C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAi64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAi64CertS.
Module BgAAi64CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAi64CertL1.
Module BgAAi64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64 BgI64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi64 BgAAi64CertS BgAAi64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_i64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAi64C.
Module BgAAi8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAi8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAi8CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAi8CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_i8_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i8_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAi8C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgTc16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc16.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Lemma callee_c : 
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_tc16 = COk SHAPE ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  intros CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_tc16 _ gplan hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars_u16_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_c cert). Qed.
End Contract.
End BgTc16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAu16CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAu16CertS.
Module BgAAu16CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAu16CertL1.
Module BgAAu16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc16 BgTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu16 BgAAu16CertS BgAAu16CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_u16_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u16_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAu16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgU32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Lemma callee_m : forall m,
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) plan_u32 = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (cem m).
Proof.
  intros m CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u32 _ gplan hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_u32_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_m ML cert). Qed.
Theorem to_chars40kb_u32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ceS.
Proof. exact (callee_m MS certS). Qed.
End Contract.
End BgU32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAu32CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAu32CertS.
Module BgAAu32CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAu32CertL1.
Module BgAAu32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32 BgU32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu32 BgAAu32CertS BgAAu32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_u32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAu32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgU64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
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
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound BSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts BSEGS IT ABOTH NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GBOTH 0 0.

Lemma callee_c : 
  check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_u64 = COk (SHole 0) ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof.
  intros CERT.
  refine (contract_of_cert BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u64 _ gplan hshape CERT).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_u64_both_callee : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce.
Proof. exact (callee_c cert). Qed.
End Contract.
End BgU64C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgAAu64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgAA.ce cfg MS) 0 (BgAA.tin cfg MS) (XPLAN_S cfg INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgAAu64CertS.
Module BgAAu64CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgAA.ceL1 cfg) 0 (BgAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgAA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgAAu64CertL1.
Module BgAAu64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64 BgU64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu64 BgAAu64CertS BgAAu64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_u64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAu64C.
Module BgAAu8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgAAu8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAu8CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAu8CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgAAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgAA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgAA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgAA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgAA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgAA.IT cfg) (BgAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgAA.XB _ XN _ BgAA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgAA.IT cfg) ABOTH both_in_hull both_hull_ok (BgAA.IT_ok cfg) BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgAA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgAA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgAA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_aligned_array_u8_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgAA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgAA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u8_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgAA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgAAu8C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgB2Jcerts.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1.BgB2J OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1.BgB2JcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM0.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1.BgB2JcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Lemma CUTS_len : forall w, length (CUTS w) = 127%nat. Proof. destruct w; reflexivity. Qed.
Lemma certs_ML : forall i, cert_stmt ML i.
Proof.
  intro i.
  destruct i as [|i]; [exact b2j_cert_ML_0|].
  destruct i as [|i]; [exact b2j_cert_ML_1|].
  destruct i as [|i]; [exact b2j_cert_ML_2|].
  destruct i as [|i]; [exact b2j_cert_ML_3|].
  destruct i as [|i]; [exact b2j_cert_ML_4|].
  destruct i as [|i]; [exact b2j_cert_ML_5|].
  destruct i as [|i]; [exact b2j_cert_ML_6|].
  destruct i as [|i]; [exact b2j_cert_ML_7|].
  destruct i as [|i]; [exact b2j_cert_ML_8|].
  destruct i as [|i]; [exact b2j_cert_ML_9|].
  destruct i as [|i]; [exact b2j_cert_ML_10|].
  destruct i as [|i]; [exact b2j_cert_ML_11|].
  destruct i as [|i]; [exact b2j_cert_ML_12|].
  destruct i as [|i]; [exact b2j_cert_ML_13|].
  destruct i as [|i]; [exact b2j_cert_ML_14|].
  destruct i as [|i]; [exact b2j_cert_ML_15|].
  destruct i as [|i]; [exact b2j_cert_ML_16|].
  destruct i as [|i]; [exact b2j_cert_ML_17|].
  destruct i as [|i]; [exact b2j_cert_ML_18|].
  destruct i as [|i]; [exact b2j_cert_ML_19|].
  destruct i as [|i]; [exact b2j_cert_ML_20|].
  destruct i as [|i]; [exact b2j_cert_ML_21|].
  destruct i as [|i]; [exact b2j_cert_ML_22|].
  destruct i as [|i]; [exact b2j_cert_ML_23|].
  destruct i as [|i]; [exact b2j_cert_ML_24|].
  destruct i as [|i]; [exact b2j_cert_ML_25|].
  destruct i as [|i]; [exact b2j_cert_ML_26|].
  destruct i as [|i]; [exact b2j_cert_ML_27|].
  destruct i as [|i]; [exact b2j_cert_ML_28|].
  destruct i as [|i]; [exact b2j_cert_ML_29|].
  destruct i as [|i]; [exact b2j_cert_ML_30|].
  destruct i as [|i]; [exact b2j_cert_ML_31|].
  destruct i as [|i]; [exact b2j_cert_ML_32|].
  destruct i as [|i]; [exact b2j_cert_ML_33|].
  destruct i as [|i]; [exact b2j_cert_ML_34|].
  destruct i as [|i]; [exact b2j_cert_ML_35|].
  destruct i as [|i]; [exact b2j_cert_ML_36|].
  destruct i as [|i]; [exact b2j_cert_ML_37|].
  destruct i as [|i]; [exact b2j_cert_ML_38|].
  destruct i as [|i]; [exact b2j_cert_ML_39|].
  destruct i as [|i]; [exact b2j_cert_ML_40|].
  destruct i as [|i]; [exact b2j_cert_ML_41|].
  destruct i as [|i]; [exact b2j_cert_ML_42|].
  destruct i as [|i]; [exact b2j_cert_ML_43|].
  destruct i as [|i]; [exact b2j_cert_ML_44|].
  destruct i as [|i]; [exact b2j_cert_ML_45|].
  destruct i as [|i]; [exact b2j_cert_ML_46|].
  destruct i as [|i]; [exact b2j_cert_ML_47|].
  destruct i as [|i]; [exact b2j_cert_ML_48|].
  destruct i as [|i]; [exact b2j_cert_ML_49|].
  destruct i as [|i]; [exact b2j_cert_ML_50|].
  destruct i as [|i]; [exact b2j_cert_ML_51|].
  destruct i as [|i]; [exact b2j_cert_ML_52|].
  destruct i as [|i]; [exact b2j_cert_ML_53|].
  destruct i as [|i]; [exact b2j_cert_ML_54|].
  destruct i as [|i]; [exact b2j_cert_ML_55|].
  destruct i as [|i]; [exact b2j_cert_ML_56|].
  destruct i as [|i]; [exact b2j_cert_ML_57|].
  destruct i as [|i]; [exact b2j_cert_ML_58|].
  destruct i as [|i]; [exact b2j_cert_ML_59|].
  destruct i as [|i]; [exact b2j_cert_ML_60|].
  destruct i as [|i]; [exact b2j_cert_ML_61|].
  destruct i as [|i]; [exact b2j_cert_ML_62|].
  destruct i as [|i]; [exact b2j_cert_ML_63|].
  destruct i as [|i]; [exact b2j_cert_ML_64|].
  destruct i as [|i]; [exact b2j_cert_ML_65|].
  destruct i as [|i]; [exact b2j_cert_ML_66|].
  destruct i as [|i]; [exact b2j_cert_ML_67|].
  destruct i as [|i]; [exact b2j_cert_ML_68|].
  destruct i as [|i]; [exact b2j_cert_ML_69|].
  destruct i as [|i]; [exact b2j_cert_ML_70|].
  destruct i as [|i]; [exact b2j_cert_ML_71|].
  destruct i as [|i]; [exact b2j_cert_ML_72|].
  destruct i as [|i]; [exact b2j_cert_ML_73|].
  destruct i as [|i]; [exact b2j_cert_ML_74|].
  destruct i as [|i]; [exact b2j_cert_ML_75|].
  destruct i as [|i]; [exact b2j_cert_ML_76|].
  destruct i as [|i]; [exact b2j_cert_ML_77|].
  destruct i as [|i]; [exact b2j_cert_ML_78|].
  destruct i as [|i]; [exact b2j_cert_ML_79|].
  destruct i as [|i]; [exact b2j_cert_ML_80|].
  destruct i as [|i]; [exact b2j_cert_ML_81|].
  destruct i as [|i]; [exact b2j_cert_ML_82|].
  destruct i as [|i]; [exact b2j_cert_ML_83|].
  destruct i as [|i]; [exact b2j_cert_ML_84|].
  destruct i as [|i]; [exact b2j_cert_ML_85|].
  destruct i as [|i]; [exact b2j_cert_ML_86|].
  destruct i as [|i]; [exact b2j_cert_ML_87|].
  destruct i as [|i]; [exact b2j_cert_ML_88|].
  destruct i as [|i]; [exact b2j_cert_ML_89|].
  destruct i as [|i]; [exact b2j_cert_ML_90|].
  destruct i as [|i]; [exact b2j_cert_ML_91|].
  destruct i as [|i]; [exact b2j_cert_ML_92|].
  destruct i as [|i]; [exact b2j_cert_ML_93|].
  destruct i as [|i]; [exact b2j_cert_ML_94|].
  destruct i as [|i]; [exact b2j_cert_ML_95|].
  destruct i as [|i]; [exact b2j_cert_ML_96|].
  destruct i as [|i]; [exact b2j_cert_ML_97|].
  destruct i as [|i]; [exact b2j_cert_ML_98|].
  destruct i as [|i]; [exact b2j_cert_ML_99|].
  destruct i as [|i]; [exact b2j_cert_ML_100|].
  destruct i as [|i]; [exact b2j_cert_ML_101|].
  destruct i as [|i]; [exact b2j_cert_ML_102|].
  destruct i as [|i]; [exact b2j_cert_ML_103|].
  destruct i as [|i]; [exact b2j_cert_ML_104|].
  destruct i as [|i]; [exact b2j_cert_ML_105|].
  destruct i as [|i]; [exact b2j_cert_ML_106|].
  destruct i as [|i]; [exact b2j_cert_ML_107|].
  destruct i as [|i]; [exact b2j_cert_ML_108|].
  destruct i as [|i]; [exact b2j_cert_ML_109|].
  destruct i as [|i]; [exact b2j_cert_ML_110|].
  destruct i as [|i]; [exact b2j_cert_ML_111|].
  destruct i as [|i]; [exact b2j_cert_ML_112|].
  destruct i as [|i]; [exact b2j_cert_ML_113|].
  destruct i as [|i]; [exact b2j_cert_ML_114|].
  destruct i as [|i]; [exact b2j_cert_ML_115|].
  destruct i as [|i]; [exact b2j_cert_ML_116|].
  destruct i as [|i]; [exact b2j_cert_ML_117|].
  destruct i as [|i]; [exact b2j_cert_ML_118|].
  destruct i as [|i]; [exact b2j_cert_ML_119|].
  destruct i as [|i]; [exact b2j_cert_ML_120|].
  destruct i as [|i]; [exact b2j_cert_ML_121|].
  destruct i as [|i]; [exact b2j_cert_ML_122|].
  destruct i as [|i]; [exact b2j_cert_ML_123|].
  destruct i as [|i]; [exact b2j_cert_ML_124|].
  destruct i as [|i]; [exact b2j_cert_ML_125|].
  destruct i as [|i]; [exact b2j_cert_ML_126|].
  unfold cert_stmt. rewrite (proj2 (nth_error_None (CUTS ML) _)); [exact I|]. rewrite CUTS_len. lia.
Qed.
Definition top_ML : top_stmt ML := b2j_top_ML.
(* [comment removed for export] *)
Definition sharedc (c : nat) : bool := match cutT ML c ML with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition lidx (i : nat) : bool := (Nat.leb 8 i && Nat.even i && sharedc (Nat.div2 (i - 8)))%bool.
Lemma certs_MSx : forall i, lidx i = false -> cert_stmt MS i.
Proof.
  intros i H.
  destruct i as [|i]; [exact b2j_cert_MS_0|].
  destruct i as [|i]; [exact b2j_cert_MS_1|].
  destruct i as [|i]; [exact b2j_cert_MS_2|].
  destruct i as [|i]; [exact b2j_cert_MS_3|].
  destruct i as [|i]; [exact b2j_cert_MS_4|].
  destruct i as [|i]; [exact b2j_cert_MS_5|].
  destruct i as [|i]; [exact b2j_cert_MS_6|].
  destruct i as [|i]; [exact b2j_cert_MS_7|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_9|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_11|].
  destruct i as [|i]; [exact b2j_cert_MS_12|].
  destruct i as [|i]; [exact b2j_cert_MS_13|].
  destruct i as [|i]; [exact b2j_cert_MS_14|].
  destruct i as [|i]; [exact b2j_cert_MS_15|].
  destruct i as [|i]; [exact b2j_cert_MS_16|].
  destruct i as [|i]; [exact b2j_cert_MS_17|].
  destruct i as [|i]; [exact b2j_cert_MS_18|].
  destruct i as [|i]; [exact b2j_cert_MS_19|].
  destruct i as [|i]; [exact b2j_cert_MS_20|].
  destruct i as [|i]; [exact b2j_cert_MS_21|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_23|].
  destruct i as [|i]; [exact b2j_cert_MS_24|].
  destruct i as [|i]; [exact b2j_cert_MS_25|].
  destruct i as [|i]; [exact b2j_cert_MS_26|].
  destruct i as [|i]; [exact b2j_cert_MS_27|].
  destruct i as [|i]; [exact b2j_cert_MS_28|].
  destruct i as [|i]; [exact b2j_cert_MS_29|].
  destruct i as [|i]; [exact b2j_cert_MS_30|].
  destruct i as [|i]; [exact b2j_cert_MS_31|].
  destruct i as [|i]; [exact b2j_cert_MS_32|].
  destruct i as [|i]; [exact b2j_cert_MS_33|].
  destruct i as [|i]; [exact b2j_cert_MS_34|].
  destruct i as [|i]; [exact b2j_cert_MS_35|].
  destruct i as [|i]; [exact b2j_cert_MS_36|].
  destruct i as [|i]; [exact b2j_cert_MS_37|].
  destruct i as [|i]; [exact b2j_cert_MS_38|].
  destruct i as [|i]; [exact b2j_cert_MS_39|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_41|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_43|].
  destruct i as [|i]; [exact b2j_cert_MS_44|].
  destruct i as [|i]; [exact b2j_cert_MS_45|].
  destruct i as [|i]; [exact b2j_cert_MS_46|].
  destruct i as [|i]; [exact b2j_cert_MS_47|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_49|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_51|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_53|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_55|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_57|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_59|].
  destruct i as [|i]; [exact b2j_cert_MS_60|].
  destruct i as [|i]; [exact b2j_cert_MS_61|].
  destruct i as [|i]; [exact b2j_cert_MS_62|].
  destruct i as [|i]; [exact b2j_cert_MS_63|].
  destruct i as [|i]; [exact b2j_cert_MS_64|].
  destruct i as [|i]; [exact b2j_cert_MS_65|].
  destruct i as [|i]; [exact b2j_cert_MS_66|].
  destruct i as [|i]; [exact b2j_cert_MS_67|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_69|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_71|].
  destruct i as [|i]; [exact b2j_cert_MS_72|].
  destruct i as [|i]; [exact b2j_cert_MS_73|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_75|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_77|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_79|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_81|].
  destruct i as [|i]; [exact b2j_cert_MS_82|].
  destruct i as [|i]; [exact b2j_cert_MS_83|].
  destruct i as [|i]; [exact b2j_cert_MS_84|].
  destruct i as [|i]; [exact b2j_cert_MS_85|].
  destruct i as [|i]; [exact b2j_cert_MS_86|].
  destruct i as [|i]; [exact b2j_cert_MS_87|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_89|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_91|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_93|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_95|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_97|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_99|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_101|].
  destruct i as [|i]; [discriminate H|].
  destruct i as [|i]; [exact b2j_cert_MS_103|].
  destruct i as [|i]; [exact b2j_cert_MS_104|].
  destruct i as [|i]; [exact b2j_cert_MS_105|].
  destruct i as [|i]; [exact b2j_cert_MS_106|].
  destruct i as [|i]; [exact b2j_cert_MS_107|].
  destruct i as [|i]; [exact b2j_cert_MS_108|].
  destruct i as [|i]; [exact b2j_cert_MS_109|].
  destruct i as [|i]; [exact b2j_cert_MS_110|].
  destruct i as [|i]; [exact b2j_cert_MS_111|].
  destruct i as [|i]; [exact b2j_cert_MS_112|].
  destruct i as [|i]; [exact b2j_cert_MS_113|].
  destruct i as [|i]; [exact b2j_cert_MS_114|].
  destruct i as [|i]; [exact b2j_cert_MS_115|].
  destruct i as [|i]; [exact b2j_cert_MS_116|].
  destruct i as [|i]; [exact b2j_cert_MS_117|].
  destruct i as [|i]; [exact b2j_cert_MS_118|].
  destruct i as [|i]; [exact b2j_cert_MS_119|].
  destruct i as [|i]; [exact b2j_cert_MS_120|].
  destruct i as [|i]; [exact b2j_cert_MS_121|].
  destruct i as [|i]; [exact b2j_cert_MS_122|].
  destruct i as [|i]; [exact b2j_cert_MS_123|].
  destruct i as [|i]; [exact b2j_cert_MS_124|].
  destruct i as [|i]; [exact b2j_cert_MS_125|].
  destruct i as [|i]; [discriminate H|].
  unfold cert_stmt. rewrite (proj2 (nth_error_None (CUTS MS) _)); [exact I|]. rewrite CUTS_len. lia.
Qed.
Definition top_MS : top_stmt MS := b2j_top_MS.

(* [comment removed for export] *)
Lemma cut_entries_len : forall w n c, length (cut_entries w c n) = (2 * n)%nat.
Proof. intros w n. induction n as [|n IH]; intros c; cbn [cut_entries length]; [reflexivity|]. rewrite IH. lia. Qed.
Lemma cut_entries_nth_L : forall w n c j, (j < n)%nat -> nth_error (cut_entries w c n) (2 * j + 1) = Some (cut_entry w (c + j) ML).
Proof.
  intros w n. induction n as [|n IH]; intros c j Hj; [lia|].
  destruct j as [|j]; [cbn [cut_entries nth_error Nat.mul Nat.add]; rewrite Nat.add_0_r; reflexivity|].
  replace (2 * Datatypes.S j + 1)%nat with (Datatypes.S (Datatypes.S (2 * j + 1))) by lia. cbn [cut_entries nth_error].
  rewrite (IH (Datatypes.S c) j) by lia. f_equal. f_equal. lia.
Qed.
Lemma cut_entries_nth_S : forall w n c j, (j < n)%nat -> nth_error (cut_entries w c n) (2 * j) = Some (cut_entry w (c + j) MS).
Proof.
  intros w n. induction n as [|n IH]; intros c j Hj; [lia|].
  destruct j as [|j]; [cbn [cut_entries nth_error Nat.mul Nat.add]; rewrite Nat.add_0_r; reflexivity|].
  replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j))) by lia. cbn [cut_entries nth_error].
  rewrite (IH (Datatypes.S c) j) by lia. f_equal. f_equal. lia.
Qed.
Lemma tags_len : forall w, length (map (fun k => (ATs (Z.of_nat k) w, PRun [] (tagk k w))) (seq 0 7)) = 7%nat.
Proof. intros w. rewrite length_map, length_seq. reflexivity. Qed.
Lemma cut_entry_shared : forall c, sharedc c = true -> cut_entry MS c ML = cut_entry ML c ML.
Proof. intros c H. unfold sharedc in H. unfold cut_entry. destruct (cutT ML c ML); [reflexivity | discriminate H]. Qed.
Lemma cuts_LS : forall i, lidx i = true -> nth_error (CUTS MS) i = nth_error (CUTS ML) i.
Proof.
  intros i H. unfold lidx in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.even_spec in H2. destruct H2 as [q Hq].
  unfold CUTS. rewrite !nth_error_app2 by (rewrite tags_len; lia). rewrite !tags_len.
  replace (i - 7)%nat with (2 * (q - 4) + 1)%nat by lia.
  replace (i - 8)%nat with (2 * (q - 4))%nat in H3 by lia. rewrite Nat.div2_double in H3.
  destruct (Nat.lt_ge_cases (q - 4) NCUT) as [Hlt|Hge].
  - rewrite !cut_entries_nth_L by exact Hlt. cbn [Nat.add]. rewrite (cut_entry_shared _ H3). reflexivity.
  - assert (E1 : nth_error (cut_entries MS 0 NCUT) (2 * (q - 4) + 1) = None) by (apply nth_error_None; rewrite cut_entries_len; lia).
    assert (E2 : nth_error (cut_entries ML 0 NCUT) (2 * (q - 4) + 1) = None) by (apply nth_error_None; rewrite cut_entries_len; lia).
    rewrite E1, E2. reflexivity.
Qed.
Lemma dead_kdead : forall w, kdead (dead (tin w)). Proof. intros w. apply kdeadb_sound. reflexivity. Qed.
Lemma cuts_L_dead : forall j c, (8 <= j)%nat -> lidx j = false -> nth_error (CUTS ML) j = Some c -> kdead (fst c).
Proof.
  intros j c H8 Hl Hn. unfold CUTS in Hn. rewrite nth_error_app2 in Hn by (rewrite tags_len; lia). rewrite tags_len in Hn.
  destruct (Nat.even j) eqn:He.
  - (* [comment removed for export] *)
    apply Nat.even_spec in He. destruct He as [q Hq].
    unfold lidx in Hl. replace (Nat.leb 8 j) with true in Hl by (symmetry; apply Nat.leb_le; lia).
    replace (Nat.even j) with true in Hl by (symmetry; apply Nat.even_spec; exists q; exact Hq). cbn [andb] in Hl.
    replace (j - 8)%nat with (2 * (q - 4))%nat in Hl by lia. rewrite Nat.div2_double in Hl.
    replace (j - 7)%nat with (2 * (q - 4) + 1)%nat in Hn by lia.
    destruct (Nat.lt_ge_cases (q - 4) NCUT) as [Hlt|Hge].
    + rewrite cut_entries_nth_L in Hn by exact Hlt. cbn [Nat.add] in Hn. injection Hn as <-.
      unfold sharedc in Hl. unfold cut_entry. destruct (cutT ML (q - 4) ML); [discriminate Hl|]. apply dead_kdead.
    + rewrite (proj2 (nth_error_None _ _)) in Hn; [discriminate Hn|]. rewrite cut_entries_len. lia.
  - (* [comment removed for export] *)
    assert (Ho : Nat.odd j = true) by (unfold Nat.odd; rewrite He; reflexivity).
    apply Nat.odd_spec in Ho. destruct Ho as [q Hq].
    replace (j - 7)%nat with (2 * (q - 3))%nat in Hn by lia.
    destruct (Nat.lt_ge_cases (q - 3) NCUT) as [Hlt|Hge].
    + rewrite cut_entries_nth_S in Hn by exact Hlt. cbn [Nat.add] in Hn. injection Hn as <-.
      unfold cut_entry. apply dead_kdead.
    + rewrite (proj2 (nth_error_None _ _)) in Hn; [discriminate Hn|]. rewrite cut_entries_len. lia.
Qed.
Lemma touts_ML : ce_touts (ce ML) = [tout ML ML; tout ML ML]. Proof. reflexivity. Qed.
Lemma touts_MS : ce_touts (ce MS) = [tout MS MS; tout MS ML]. Proof. reflexivity. Qed.
Lemma tout_L : tout MS ML = tout ML ML. Proof. reflexivity. Qed.
Lemma hs_LS : forall i, lidx i = true -> hs_sub (HScut (ce ML) (CUTS ML) (Datatypes.S i)) (HScut (ce MS) (CUTS MS) (Datatypes.S i)).
Proof.
  intros i Hi h ch Hh. unfold HScut, NT in Hh |- *. rewrite touts_ML in Hh. rewrite touts_MS.
  change (length [tout ML ML; tout ML ML]) with 2%nat in Hh. change (length [tout MS MS; tout MS ML]) with 2%nat.
  destruct (Nat.ltb h 2) eqn:Hlt.
  - left. exists 1%nat. cbn [Nat.ltb Nat.leb nth_error]. rewrite tout_L. apply Nat.ltb_lt in Hlt.
    destruct h as [|[|h]]; [| |lia]; cbn [nth_error] in Hh; injection Hh as <-; reflexivity.
  - destruct (Nat.leb (Datatypes.S i) (h - 2)) eqn:Hle; [|discriminate Hh]. apply Nat.leb_le in Hle.
    assert (H8 : (8 <= i)%nat).
    { unfold lidx in Hi. apply andb_prop in Hi as [X _]. apply andb_prop in X as [X _]. apply Nat.leb_le in X. exact X. }
    destruct (lidx (h - 2)) eqn:Hl.
    + left. exists h. rewrite Hlt. replace (Nat.leb (Datatypes.S i) (h - 2)) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite (cuts_LS (h - 2) Hl). exact Hh.
    + right. destruct (nth_error (CUTS ML) (h - 2)) as [c|] eqn:Hn; [|discriminate Hh]. injection Hh as <-.
      apply (cuts_L_dead (h - 2) c); [lia | exact Hl | exact Hn].
Qed.
End BgB2Jcerts.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgEscCertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHK m := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HSce (BgEsc.ce m)) 0%nat BFUEL BgEsc.FUEL None).
#[local] Notation CHK1 := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HSce BgEsc.ceL1) 0%nat BFUEL BgEsc.FUEL None).
#[local] Notation CHKc c k := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HScut c BgEsc.CUTS_E k) 0%nat BFUEL BgEsc.FUEL None).
(* [comment removed for export] *)
Lemma esc_cert_S : CHKc (BgEsc.ce MS) 0 (BgEsc.tin MS) (BgEsc.planX MS) = COk (SHole 0).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgEscCertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgEscCertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgEscC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc BgEscCertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgEscCertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs2 : holes_only (SHole 2) = true. Proof. reflexivity. Qed.

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
Lemma esc_callee_cut : forall (c : gcallee) (p : plan) sh,
  ce_nxf c = BgEsc.NXF -> ce_bcap c = BgEsc.BCAP -> ce_ccap c = BgEsc.CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error BgEsc.CUTS_E i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
     (check BSEGS BgEsc.IT ABOTH (ce_nxf c) LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HScut c BgEsc.CUTS_E (Datatypes.S i)) 0%nat BFUEL BgEsc.FUEL None T k = COk sh \/
      exists HS', hs_sub HS' (HScut c BgEsc.CUTS_E (Datatypes.S i)) /\
        check BSEGS BgEsc.IT ABOTH (ce_nxf c) LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB HS' 0%nat BFUEL BgEsc.FUEL None T k = COk sh)) ->
  check BSEGS BgEsc.IT ABOTH (ce_nxf c) LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HScut c BgEsc.CUTS_E 0) 0%nat BFUEL BgEsc.FUEL None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c BgEsc.IT BgEsc.IT_ok LIMIT 0%nat BFUEL BgEsc.FUEL BgEsc.XN QTRUE _ _ BgEsc.XB _ BgEsc.XN _ BgEsc.XB _ BgEsc.CUTS_E HCUTS p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ. unfold BgEsc.XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS BgEsc.IT ABOTH both_in_hull both_hull_ok BgEsc.IT_ok BgEsc.NXF [] GBOTH BgEsc.BCAP BgEsc.CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact BgEsc.IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ. unfold BgEsc.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgEsc.NXF [] GBOTH BgEsc.BCAP BgEsc.CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ. unfold BgEsc.XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS BgEsc.IT ABOTH both_in_hull both_hull_ok BgEsc.IT_ok BgEsc.NXF [] GBOTH BgEsc.BCAP BgEsc.CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact BgEsc.IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa HUQ. unfold BgEsc.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgEsc.NXF [] GBOTH BgEsc.BCAP BgEsc.CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
Lemma esc_hs_L : hs_sub (HScut BgEsc.ceL1 BgEsc.CUTS_E 1) (HScut (BgEsc.ce MS) BgEsc.CUTS_E 1).
Proof.
  intros h ch Hh. left. exists 1%nat. unfold HScut, NT in Hh |- *.
  change (ce_touts BgEsc.ceL1) with [BgEsc.tout ML ML; BgEsc.tout ML ML] in Hh. change (ce_touts (BgEsc.ce MS)) with [BgEsc.tout MS MS; BgEsc.tout MS ML].
  change (length [BgEsc.tout ML ML; BgEsc.tout ML ML]) with 2%nat in Hh. change (length [BgEsc.tout MS MS; BgEsc.tout MS ML]) with 2%nat.
  cbn [Nat.ltb Nat.leb nth_error]. rewrite BgEsc.tout_L.
  destruct h as [|[|h]]; cbn [Nat.ltb Nat.leb nth_error] in Hh; [exact Hh | exact Hh |].
  destruct h as [|h]; cbn [Nat.sub Nat.leb] in Hh; [discriminate Hh|].
  unfold BgEsc.CUTS_E in Hh. cbn [nth_error] in Hh. destruct h; discriminate Hh.
Qed.


Theorem esc_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgEsc.ce MS).
Proof.
  refine (esc_callee_cut (BgEsc.ce MS) (BgEsc.planX MS) _ eq_refl eq_refl eq_refl (esc_gplanX MS) hs0 _ esc_cert_S).
  intros i T k Hn. destruct i as [|i]; [|destruct i; discriminate Hn].
  injection Hn as <- <-. exists (SHole 0). split; [exact BgEsc.esc_gplanC|]. split; [reflexivity|].
  right. exists (HScut BgEsc.ceL1 BgEsc.CUTS_E 1). split; [exact esc_hs_L | exact esc_cut_L].
Qed.

Theorem esc_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH BgEsc.ceL1.
Proof. (refine (esc_callee_cut BgEsc.ceL1 (BgEsc.planX ML) _ eq_refl eq_refl eq_refl (esc_gplanX ML) hs2 _ esc_cert_L1);
  intros i T k Hn; destruct i as [|i]; [|destruct i; discriminate Hn];
  injection Hn as <- <-; exists (SHole 0); split; [exact BgEsc.esc_gplanC|]; split; [reflexivity|]; left; exact esc_cut_L). Qed.
End Contract.
End BgEscC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNf32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT BgWFC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [injection H as <-; exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_f32_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_f32_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_f32_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_f32_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_f32_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_f32_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNf32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNf64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT BgWDC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [injection H as <-; exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_f64_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_f64_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_f64_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_f64_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_f64_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_f64_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNf64C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNi8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [injection H as <-; exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_i8_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_i8_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_i8_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_i8_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_i8_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_i8_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNi8C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNi16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [injection H as <-; exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_i16_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_i16_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_i16_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_i16_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_i16_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_i16_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNi16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNu8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_u8_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_u8_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_u8_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_u8_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_u8_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_u8_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNu8C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWNu16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc16 BgTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Lemma callee_gen : forall (B : Z) (c : gcallee) (p : plan) sh,
  ce_nxf c = BgWN.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  check BSEGS (BgWN.IT cfg B) ABOTH (ce_nxf c) LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce c) 0%nat BFUEL FUEL16 None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros B c p sh HN HB HC HG HSH CERT.
  refine (contract_of_cert_xb BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWN.IT cfg B) (BgWN.IT_ok cfg B) LIMIT 0%nat BFUEL FUEL16 (XN B) _ BgWN.XB _ p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN, BgWN.XNg. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWN.IT cfg B) ABOTH both_in_hull both_hull_ok (BgWN.IT_ok cfg B) BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [injection H as <-; exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      discriminate H.
    + (apply GC_all; first [assumption | exact (BgWN.IT_ok cfg B)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWN.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWN.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem write_number_u16_u8tag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BU).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_u16_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BU).
Proof. exact (callee_gen BU (BgWN.ce cfg MS BU) (PLANt MS BU) _ eq_refl eq_refl eq_refl (gplan MS BU) hs0 certU_S). Qed.
Theorem write_number_u16_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BU).
Proof. exact (callee_gen BU (BgWN.ceL1 cfg BU) (PLANt ML BU) _ eq_refl eq_refl eq_refl (gplan ML BU) hs1 certU_L1). Qed.
Theorem write_number_u16_inttag_both_callee_L : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg ML BI).
Proof. apply callee_contract_L_of_L1_az. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
Theorem write_number_u16_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce cfg MS BI).
Proof. exact (callee_gen BI (BgWN.ce cfg MS BI) (PLANt MS BI) _ eq_refl eq_refl eq_refl (gplan MS BI) hs0 certI_S). Qed.
Theorem write_number_u16_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 cfg BI).
Proof. exact (callee_gen BI (BgWN.ceL1 cfg BI) (PLANt ML BI) _ eq_refl eq_refl eq_refl (gplan ML BI) hs1 certI_L1). Qed.
End Contract.
End BgWNu16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgNumCertUS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma top : top_stmt BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
(* [comment removed for export] *)
End BgNumCertUS.
Module BgNumCertUL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma top : top_stmt BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
(* [comment removed for export] *)
End BgNumCertUL1.
Module BgNumCertIS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma top : top_stmt BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
(* [comment removed for export] *)
End BgNumCertIS.
Module BgNumCertIL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma top : top_stmt BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
(* [comment removed for export] *)
End BgNumCertIL1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgNumcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BgNumcM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgNumC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32 BgU32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32 BgI32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64 BgU64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64 BgI64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf32 BgWNf32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf64 BgWNf64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi8 BgWNi8C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi16 BgWNi16C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu8 BgWNu8C OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu16 BgWNu16C OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum BgNumCertUS OSSVerify.Proofs.glaze.binary_reflection.lib.BgNumcM0 BgNumCertUL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgNumcM1 BgNumCertIS BgNumCertIL1. Import BgNumcM0.BgNumCertUS_A0 BgNumcM0.BgNumCertUS_A1 BgNumcM0.BgNumCertUS_A2 BgNumcM0.BgNumCertUS_A3 BgNumcM0.BgNumCertUS_A4 BgNumcM1.BgNumCertUL1_A0 BgNumcM1.BgNumCertUL1_A1 BgNumcM1.BgNumCertUL1_A2 BgNumcM1.BgNumCertUL1_A3 BgNumcM1.BgNumCertUL1_A4 BgNumcM0.BgNumCertIS_A0 BgNumcM0.BgNumCertIS_A1 BgNumcM0.BgNumCertIS_A2 BgNumcM0.BgNumCertIS_A3 BgNumcM0.BgNumCertIS_A4 BgNumcM1.BgNumCertIL1_A0 BgNumcM1.BgNumCertIL1_A1 BgNumcM1.BgNumCertIL1_A2 BgNumcM1.BgNumCertIL1_A3 BgNumcM1.BgNumCertIL1_A4.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cuts_ok_US : forall i T k, nth_error (CUTS BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU)) i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS (IT BNU) ABOTH (ce_nxf (BgNum.BgNumT.ce MS BNU)) LIMIT ISP0 (BgNum.XN BNU) XE0 (XB BNU) (HScut (BgNum.BgNumT.ce MS BNU) (CUTS BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU)) (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) i).
  { destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertUS_A0.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertUS_A1.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertUS_A2.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertUS_A3.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertUS_A4.cut|].
    exfalso. rewrite (proj2 (nth_error_None (CUTS BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU)) _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma cuts_ok_UL1 : forall i T k, nth_error (CUTS BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU)) i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS (IT BNU) ABOTH (ce_nxf (BgNum.BgNumT.ceL1 BNU)) LIMIT ISP0 (BgNum.XN1 BNU) XE0 (XB BNU) (HScut (BgNum.BgNumT.ceL1 BNU) (CUTS BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU)) (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) i).
  { destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertUL1_A0.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertUL1_A1.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertUL1_A2.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertUL1_A3.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertUL1_A4.cut|].
    exfalso. rewrite (proj2 (nth_error_None (CUTS BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU)) _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma cuts_ok_IS : forall i T k, nth_error (CUTS BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI)) i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS (IT BNI) ABOTH (ce_nxf (BgNum.BgNumT.ce MS BNI)) LIMIT ISP0 (BgNum.XN BNI) XE0 (XB BNI) (HScut (BgNum.BgNumT.ce MS BNI) (CUTS BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI)) (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) i).
  { destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertIS_A0.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertIS_A1.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertIS_A2.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertIS_A3.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM0.BgNumCertIS_A4.cut|].
    exfalso. rewrite (proj2 (nth_error_None (CUTS BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI)) _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma cuts_ok_IL1 : forall i T k, nth_error (CUTS BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI)) i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS (IT BNI) ABOTH (ce_nxf (BgNum.BgNumT.ceL1 BNI)) LIMIT ISP0 (BgNum.XN1 BNI) XE0 (XB BNI) (HScut (BgNum.BgNumT.ceL1 BNI) (CUTS BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI)) (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) i).
  { destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertIL1_A0.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertIL1_A1.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertIL1_A2.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertIL1_A3.cut|].
    destruct i as [|i]; [apply cut_ok_sound; exact BgNumcM1.BgNumCertIL1_A4.cut|].
    exfalso. rewrite (proj2 (nth_error_None (CUTS BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI)) _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
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

Lemma CT_ok : forall id ce', BgNum.CT id = Some ce' -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce'.
Proof.
  intros id ce' H. unfold BgNum.CT in H.
  destruct (Nat.eqb id 132). { injection H as <-. exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)). }
  destruct (Nat.eqb id 133). { injection H as <-. exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)). }
  destruct (Nat.eqb id 134). { injection H as <-. exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)). }
  destruct (Nat.eqb id 135). { injection H as <-. exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)). }
  destruct (Nat.eqb id 142). { injection H as <-. exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)). }
  destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-. exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
Qed.

Lemma WN_f32_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNf32.cfg ML (lamB BgWNf32.BU BgWNf32.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf32C.write_number_f32_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf32C.write_number_f32_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_f32_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNf32.cfg MS (lamB BgWNf32.BU BgWNf32.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf32C.write_number_f32_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf32C.write_number_f32_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_f32_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNf32.cfg (lamB BgWNf32.BU BgWNf32.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf32C.write_number_f32_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf32C.write_number_f32_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_f64_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNf64.cfg ML (lamB BgWNf64.BU BgWNf64.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf64C.write_number_f64_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf64C.write_number_f64_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_f64_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNf64.cfg MS (lamB BgWNf64.BU BgWNf64.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf64C.write_number_f64_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf64C.write_number_f64_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_f64_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNf64.cfg (lamB BgWNf64.BU BgWNf64.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNf64C.write_number_f64_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNf64C.write_number_f64_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i8_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNi8.cfg ML (lamB BgWNi8.BU BgWNi8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi8C.write_number_i8_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi8C.write_number_i8_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i8_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNi8.cfg MS (lamB BgWNi8.BU BgWNi8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi8C.write_number_i8_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi8C.write_number_i8_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i8_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNi8.cfg (lamB BgWNi8.BU BgWNi8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi8C.write_number_i8_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi8C.write_number_i8_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i16_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNi16.cfg ML (lamB BgWNi16.BU BgWNi16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi16C.write_number_i16_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi16C.write_number_i16_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i16_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNi16.cfg MS (lamB BgWNi16.BU BgWNi16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi16C.write_number_i16_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi16C.write_number_i16_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_i16_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNi16.cfg (lamB BgWNi16.BU BgWNi16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNi16C.write_number_i16_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNi16C.write_number_i16_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u8_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNu8.cfg ML (lamB BgWNu8.BU BgWNu8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu8C.write_number_u8_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu8C.write_number_u8_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u8_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNu8.cfg MS (lamB BgWNu8.BU BgWNu8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu8C.write_number_u8_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu8C.write_number_u8_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u8_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNu8.cfg (lamB BgWNu8.BU BgWNu8.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu8C.write_number_u8_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu8C.write_number_u8_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u16_L : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNu16.cfg ML (lamB BgWNu16.BU BgWNu16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu16C.write_number_u16_inttag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu16C.write_number_u16_u8tag_both_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u16_S : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ce BgWNu16.cfg MS (lamB BgWNu16.BU BgWNu16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu16C.write_number_u16_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu16C.write_number_u16_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma WN_u16_L1 : forall B, callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWN.ceL1 BgWNu16.cfg (lamB BgWNu16.BU BgWNu16.BI B)).
Proof. intros B. unfold lamB. destruct (is_int B); [exact (BgWNu16C.write_number_u16_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) | exact (BgWNu16C.write_number_u16_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)]. Qed.
Lemma CT1_ok : forall B id ce', BgNum.CT1 B id = Some ce' -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH ce'.
Proof.
  intros B id ce' H. unfold BgNum.CT1 in H.
  destruct (Nat.eqb id 170). { injection H as <-. exact (WN_f32_L1 B). }
  destruct (Nat.eqb id 171). { injection H as <-. exact (WN_f64_L1 B). }
  destruct (Nat.eqb id 172). { injection H as <-. exact (WN_i8_L1 B). }
  destruct (Nat.eqb id 173). { injection H as <-. exact (WN_i16_L1 B). }
  destruct (Nat.eqb id 174). { injection H as <-. exact (WN_u8_L1 B). }
  destruct (Nat.eqb id 175). { injection H as <-. exact (WN_u16_L1 B). }
  exact (CT_ok id ce' H).
Qed.
Lemma CT2w_ok : forall B id c, BgNum.CT2w B id = Some c -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged c).
Proof.
  intros B id c H. unfold BgNum.CT2w in H.
  destruct (Nat.eqb id 150). { injection H as <-. exact (WN_f32_L B). }
  destruct (Nat.eqb id 151). { injection H as <-. exact (WN_f32_S B). }
  destruct (Nat.eqb id 152). { injection H as <-. exact (WN_f64_L B). }
  destruct (Nat.eqb id 153). { injection H as <-. exact (WN_f64_S B). }
  destruct (Nat.eqb id 154). { injection H as <-. exact (WN_i8_L B). }
  destruct (Nat.eqb id 155). { injection H as <-. exact (WN_i8_S B). }
  destruct (Nat.eqb id 156). { injection H as <-. exact (WN_i16_L B). }
  destruct (Nat.eqb id 157). { injection H as <-. exact (WN_i16_S B). }
  destruct (Nat.eqb id 158). { injection H as <-. exact (WN_u8_L B). }
  destruct (Nat.eqb id 159). { injection H as <-. exact (WN_u8_S B). }
  destruct (Nat.eqb id 160). { injection H as <-. exact (WN_u16_L B). }
  destruct (Nat.eqb id 161). { injection H as <-. exact (WN_u16_S B). }
  discriminate H.
Qed.
Lemma CT2_ok : forall B id c, BgNum.CT2 B id = Some c -> callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged c).
Proof.
  intros B. unfold BgNum.CT2.
  apply (ct2_or_sound (fun c => callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (c2_merged c))).
  - exact (CT2w_ok B).
  - intros id c H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c H).
Qed.
(* [comment removed for export] *)
Lemma XN_ok : forall B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + BCAP <= GBUDGET -> C0 + CCAP <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  GPS.ext_stmt BSEGS NXF (BgNum.XN B) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ.
Proof.
  intros B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgNum.XN.
  apply BgReadCert.BgPw.XNw_sound.
  refine (XNc_sound BSEGS (BgNum.BgNumT.IT B) ABOTH both_in_hull both_hull_ok (BgNum.BgNumT.IT_ok B) BgNum.BgNumT.NXF [] GBOTH BgNum.BgNumT.BCAP BgNum.BgNumT.CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 BgNum.CT _ _).
  - intros id ce' H. exact (CT_ok id ce' H).
  - (apply GC_all; first [assumption | exact (BgNum.BgNumT.IT_ok B)]).
Qed.
Lemma XN1_ok : forall B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + BCAP <= GBUDGET -> C0 + CCAP <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  GPS.ext_stmt BSEGS NXF (BgNum.XN1 B) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ.
Proof.
  intros B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgNum.XN1.
  apply BgReadCert.BgPw.XNw_sound.
  refine (XNc_sound BSEGS (BgNum.BgNumT.IT B) ABOTH both_in_hull both_hull_ok (BgNum.BgNumT.IT_ok B) BgNum.BgNumT.NXF [] GBOTH BgNum.BgNumT.BCAP BgNum.BgNumT.CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 (BgNum.CT1 B) _ _).
  - intros id ce' H. exact (CT1_ok B id ce' H).
  - (apply GC_all; first [assumption | exact (BgNum.BgNumT.IT_ok B)]).
Qed.
Lemma XB_ok : forall B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + BCAP <= GBUDGET -> C0 + CCAP <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  GPS.ext2_stmt BSEGS NXF (BgNum.XB B) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ.
Proof.
  intros B PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgNum.XB.
  refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgNum.BgNumT.NXF [] GBOTH BgNum.BgNumT.BCAP BgNum.BgNumT.CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 (BgNum.CT2 B) _).
  intros id c H. exact (CT2_ok B id c H).
Qed.

Theorem number_u8tag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgNum.BgNumT.ce MS BNU).
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (BgNum.BgNumT.ce MS BNU) (BgNum.BgNumT.IT BNU) (BgNum.BgNumT.IT_ok BNU) LIMIT 0%nat BFUEL FUELN (BgNum.XN BNU) _ (BgNum.XB BNU) _ (CUTS BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU)) cuts_ok_US plan_top (SHole 2) top_gplan eq_refl BgNumCertUS.top).
  - intros; eapply XN_ok; eassumption.
  - intros; eapply XB_ok; eassumption.
Qed.

Theorem number_u8tag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgNum.BgNumT.ceL1 BNU).
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (BgNum.BgNumT.ceL1 BNU) (BgNum.BgNumT.IT BNU) (BgNum.BgNumT.IT_ok BNU) LIMIT 0%nat BFUEL FUELN (BgNum.XN1 BNU) _ (BgNum.XB BNU) _ (CUTS BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU)) cuts_ok_UL1 plan_top (SHole 2) top_gplan eq_refl BgNumCertUL1.top).
  - intros; eapply XN1_ok; eassumption.
  - intros; eapply XB_ok; eassumption.
Qed.
Theorem number_inttag_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgNum.BgNumT.ce MS BNI).
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (BgNum.BgNumT.ce MS BNI) (BgNum.BgNumT.IT BNI) (BgNum.BgNumT.IT_ok BNI) LIMIT 0%nat BFUEL FUELN (BgNum.XN BNI) _ (BgNum.XB BNI) _ (CUTS BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI)) cuts_ok_IS plan_top (SHole 2) top_gplan eq_refl BgNumCertIS.top).
  - intros; eapply XN_ok; eassumption.
  - intros; eapply XB_ok; eassumption.
Qed.

Theorem number_inttag_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgNum.BgNumT.ceL1 BNI).
Proof.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (BgNum.BgNumT.ceL1 BNI) (BgNum.BgNumT.IT BNI) (BgNum.BgNumT.IT_ok BNI) LIMIT 0%nat BFUEL FUELN (BgNum.XN1 BNI) _ (BgNum.XB BNI) _ (CUTS BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI)) cuts_ok_IL1 plan_top (SHole 2) top_gplan eq_refl BgNumCertIL1.top).
  - intros; eapply XN1_ok; eassumption.
  - intros; eapply XB_ok; eassumption.
Qed.
End Contract.
End BgNumC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAf32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWFT BgWFC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8.BgWAf32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAf32CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAf32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 136); [|discriminate H]. injection H as <-.
      exact (BgWFC.write_float_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_f32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAf32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAf64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAf64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAf64CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAf64CertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAf64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT BgWDC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAf64 BgWAf64CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAf64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 137); [|discriminate H]. injection H as <-.
      exact (BgWDC.write_double_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_f64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_f64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAf64C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAi16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAi16CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAi16CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_i16_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i16_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAi16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32CertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAi32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32 BgI32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 132); [injection H as <-; exact (BgI32C.to_chars40kb_i32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      exact (BgI32C.to_chars40kb_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_i32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAi32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAi64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAi64CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi64CertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAi64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64 BgI64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi64 BgWAi64CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      exact (BgI64C.to_chars40kb_i64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_i64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAi64C.
Module BgWAi8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc32 BgTc32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi16.BgWAi8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAi8CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 130); [|discriminate H]. injection H as <-.
      exact (BgTc32C.to_chars_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_i8_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i8_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAi8C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16CertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAu16C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgTc16 BgTc16C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu16CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 131); [|discriminate H]. injection H as <-.
      exact (BgTc16C.to_chars_u16_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_u16_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u16_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAu16C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAu32CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAu32CertS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu32CertL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAu32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32 BgU32C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu32 BgWAu32CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu32CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 133); [injection H as <-; exact (BgU32C.to_chars40kb_u32_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      exact (BgU32C.to_chars40kb_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_u32_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u32_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAu32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgWAu64CertS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg JS0m INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_SX : CHKX (BgWA.ce cfg MS) 0 (BgWA.tin cfg MS) (XPLAN_S cfg JS0m INVm JS1m elem) = COk (SHole 0).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgWAu64CertS.
Module BgWAu64CertL1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End BgWAu64CertL1.
Module BgWAu64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64 BgU64C OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu64 BgWAu64CertS BgWAu64CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      exact (BgU64C.to_chars40kb_u64_both_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_u64_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u64_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAu64C.
Module BgWAu8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAu8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAu8CertS OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAu8CertL1 OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgCalleeSub.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Lemma callee_gen_cut : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS (Datatypes.S i)) 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT.
  refine (contract_of_cert_xb_cut BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ BgWA.XB _ CUTS HCUTS p _ HG HSH CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.
(* [comment removed for export] *)
Lemma callee_gen_cutsh : forall (c : gcallee) (CUTS : list (acs * plan)) (p : plan) sh,
  ce_nxf c = BgWA.NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh', gplan_ok k = true /\ holes_only sh' = true /\
     exists HS', hs_sub HS' (HScut c CUTS (Datatypes.S i)) /\
       check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB HS' 0%nat BFUEL FUELA None T k = COk sh') ->
  check BSEGS (BgWA.IT cfg) ABOTH (ce_nxf c) LIMIT ISP0 XN XE0 BgWA.XB (HScut c CUTS 0) 0%nat BFUEL FUELA None (ce_tin c) p = COk sh ->
  callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH c.
Proof.
  intros c CUTS p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  refine (contract_of_cert_when_cutX BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok (RUN_sound_fx BSEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            c (BgWA.IT cfg) (BgWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ BgWA.XB _ XN _ BgWA.XB _ CUTS _ p sh HG HSH CERT).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold XN. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    apply BgReadCert.BgPw.XNw_sound.
    refine (XNc_sound BSEGS (BgWA.IT cfg) ABOTH both_in_hull both_hull_ok (BgWA.IT_ok cfg) BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (BgWA.IT_ok cfg)]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa _. unfold BgWA.XB. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc.
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok BgWA.NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
  - intros i T k Hn. destruct (HCUTS i T k Hn) as (sh' & H1 & H2 & HS' & H3 & H4). exists sh'. split; [exact H1|]. split; [exact H2|].
    right. exists HS'. split; [exact H3|]. rewrite HN. exact H4.
Qed.
(* [comment removed for export] *)
Lemma xL1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof.
  refine (callee_gen_cut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) (XPLAN_L1 cfg JS0m) _ eq_refl eq_refl eq_refl gplan_XL1 hs1 _ cert_L1X).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.

Theorem write_array_u8_both_callee_S : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ce cfg MS).
Proof.
  refine (callee_gen_cutsh (BgWA.ce cfg MS) (XCUTS cfg INVm JS1m elem) (XPLAN_S cfg JS0m INVm JS1m elem) _ eq_refl eq_refl eq_refl gplan_XS hs0 _ cert_SX).
  intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
  exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|].
  exists (HScut (BgWA.ceL1 cfg) (XCUTS cfg INVm JS1m elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg INVm JS1m elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u8_both_callee_L1 : callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH (BgWA.ceL1 cfg).
Proof. exact xL1. Qed.
End Contract.
End BgWAu8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgCutShare.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1.BgB2J.

Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.


Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Let CERTS_L : forall i, cert_stmt ML i := BgB2Jcerts.certs_ML.
Let TOP_L : top_stmt ML := BgB2Jcerts.top_ML.
Let CERTS_S : forall i, BgB2Jcerts.lidx i = false -> cert_stmt MS i := BgB2Jcerts.certs_MSx.   (* [comment removed for export] *)
Let TOP_S : top_stmt MS := BgB2Jcerts.top_MS.

Notation CC := (callee_contract BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH).
Lemma AA_L1 : forall k, (k < 10)%nat -> CC (BgAA.ceL1 (AAcfg k)).
Proof.
  intros k Hk. do 10 (destruct k as [|k]; [first
    [ exact (BgAAi8C.write_aligned_array_i8_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi16C.write_aligned_array_i16_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi32C.write_aligned_array_i32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi64C.write_aligned_array_i64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu8C.write_aligned_array_u8_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu16C.write_aligned_array_u16_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu32C.write_aligned_array_u32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu64C.write_aligned_array_u64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAf32C.write_aligned_array_f32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAf64C.write_aligned_array_f64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) ]|]).
  lia.
Qed.
Lemma AA_S : forall k, (k < 10)%nat -> CC (c2_merged (BgAA.ce2 (AAcfg k) MS)).
Proof.
  intros k Hk. do 10 (destruct k as [|k]; [first
    [ exact (BgAAi8C.write_aligned_array_i8_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi16C.write_aligned_array_i16_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi32C.write_aligned_array_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAi64C.write_aligned_array_i64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu8C.write_aligned_array_u8_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu16C.write_aligned_array_u16_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu32C.write_aligned_array_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAu64C.write_aligned_array_u64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAf32C.write_aligned_array_f32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgAAf64C.write_aligned_array_f64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) ]|]).
  lia.
Qed.
Lemma WA_L1 : forall k, (k < 10)%nat -> CC (BgWA.ceL1 (WAcfg k)).
Proof.
  intros k Hk. do 10 (destruct k as [|k]; [first
    [ exact (BgWAi8C.write_array_i8_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi16C.write_array_i16_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi32C.write_array_i32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi64C.write_array_i64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu8C.write_array_u8_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu16C.write_array_u16_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu32C.write_array_u32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu64C.write_array_u64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAf32C.write_array_f32_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAf64C.write_array_f64_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) ]|]).
  lia.
Qed.
Lemma WA_S : forall k, (k < 10)%nat -> CC (c2_merged (BgWA.ce2 (WAcfg k) MS)).
Proof.
  intros k Hk. do 10 (destruct k as [|k]; [first
    [ exact (BgWAi8C.write_array_i8_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi16C.write_array_i16_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi32C.write_array_i32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAi64C.write_array_i64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu8C.write_array_u8_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu16C.write_array_u16_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu32C.write_array_u32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAu64C.write_array_u64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAf32C.write_array_f32_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)
    | exact (BgWAf64C.write_array_f64_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all) ]|]).
  lia.
Qed.

Lemma CT0_sound : forall id c, CT0 id = Some c -> CC c.
Proof.
  intros id c H. unfold CT0 in H.
  destruct (Nat.eqb id 203); [injection H as <-; exact (BgEscC.esc_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 223); [injection H as <-; exact (BgNumC.number_u8tag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 233); [injection H as <-; exact (BgNumC.number_inttag_both_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.leb 310 id && Nat.ltb id 320)%bool eqn:HA.
  - injection H as <-. apply andb_prop in HA as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. apply AA_L1. lia.
  - destruct (Nat.leb 330 id && Nat.ltb id 340)%bool eqn:HW; [|discriminate H].
    injection H as <-. apply andb_prop in HW as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. apply WA_L1. lia.
Qed.
Lemma CT2_sound : forall id c, CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold CT2 in H.
  destruct (Nat.eqb id 200); [injection H as <-; exact (BgEscC.esc_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 220); [injection H as <-; exact (BgNumC.number_u8tag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 230); [injection H as <-; exact (BgNumC.number_inttag_both_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.leb 300 id && Nat.ltb id 310)%bool eqn:HA.
  - injection H as <-. apply andb_prop in HA as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. apply AA_S. lia.
  - destruct (Nat.leb 320 id && Nat.ltb id 330)%bool eqn:HW.
    + injection H as <-. apply andb_prop in HW as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. apply WA_S. lia.
    + exact (BgStrResizeC.CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c H).
Qed.

Lemma idepth_lt : forall w, (14 < ce_nxf (ce w))%nat. Proof. intros []; cbv; lia. Qed.
Lemma cuts_ok_of : forall w, (forall i, cert_stmt w i) ->
  forall i T k, nth_error (CUTS w) i = Some (T, k) -> exists sh,
    gplan_ok k = true /\ holes_only sh = true /\
    check BSEGS IT ABOTH (ce_nxf (ce w)) LIMIT ISP0 (XN w) XE0 (XB w) (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUELB None T k = COk sh.
Proof. intros w H i T k Hn. pose proof (H i) as X. unfold cert_stmt in X. rewrite Hn in X. exact X. Qed.

(* [comment removed for export] *)
Lemma XN_L_rec : forall n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap (ce ML) <= GBUDGET -> C0 + ce_ccap (ce ML) <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf (ce ML)) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS 14 E <= n + 1) ->
  callee_contract_upto BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH 14 n (ce ML) ->
  GPS.ext_stmt BSEGS (ce_nxf (ce ML)) (XN ML) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ.
Proof.
  intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn. unfold XN.
  apply XNw_sound. apply XNd_sound. apply XNp_sound.
  refine (XNr_gen_sound BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok RZ RZ_silent1 SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            NXF BCAP CCAP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa 213%nat 14%nat ceL1 _ n _ CCn HUm).
  refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 CT0_sound _).
  apply GC_all; first [assumption | exact IT_ok].
Qed.
Lemma XB_L_rec : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap (ce ML) <= GBUDGET -> C0 + ce_ccap (ce ML) <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree (ce_nxf (ce ML)) E E' -> UINV E -> UINV E') ->
  GPS.ext2_stmt BSEGS (ce_nxf (ce ML)) (XB ML) PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GBOTH AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ.
Proof.
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
  refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).
Qed.

(* [comment removed for export] *)
Theorem b2jv_both_callee_L1 : CC (ce ML).
Proof.
  destruct TOP_L as (s & Hgp & Hho & CERT).
  refine (contract_of_cert_rec_cut_all BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok [] GBOTH fx_ok RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (ce ML) 14 (idepth_lt ML) (RUN_sound_fx BSEGS) LIMIT 0%nat BFUEL FUELB (XN ML) _ (top ML) s Hgp Hho (XB ML) _ (CUTS ML) (cuts_ok_of ML CERTS_L) CERT).
  - exact XN_L_rec.
  - intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn. exact (XB_L_rec PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa).
Qed.

(* [comment removed for export] *)
Lemma CTs_sound : forall id c, CTs id = Some c -> CC c.
Proof.
  intros id c H. unfold CTs in H. destruct (Nat.eqb id 213).
  - injection H as <-. exact b2jv_both_callee_L1.
  - exact (CT0_sound _ _ H).
Qed.
Theorem b2jv_both_callee_S : CC (ce MS).
Proof.
  destruct TOP_S as (s & Hgp & Hho & CERT).
  (* [comment removed for export] *)
  refine (contract_of_cert_rec_cut_allX BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok [] GBOTH fx_ok RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP
            both_G_ro_img2 both_G_img_al both_G_img_shlo both_A_img_hi both_A_img_lo both_segs_wx
            (ce MS) 14 (idepth_lt MS) (RUN_sound_fx BSEGS) LIMIT 0%nat BFUEL FUELB (XN MS) _ (top MS) s Hgp Hho (XB MS) _ (XN ML) _ (XB ML) _ (CUTS MS) _ CERT).
  - intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn. unfold XN.
    apply XNw_sound. apply XNd_sound. apply XNp_sound.
    refine (XNc_sound BSEGS IT ABOTH both_in_hull both_hull_ok IT_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CTs CTs_sound _).
    apply GC_all; first [assumption | exact IT_ok].
  - intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn. unfold XB.
    refine (XBr_gen_sound BSEGS ABOTH both_in_hull both_hull_ok [] GBOTH fx_ok RZ RZ_silent1 SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              NXF BCAP CCAP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa 14%nat 210%nat (ce2 MS) _ n _ CCn HUm).
    refine (XBc_sound0 BSEGS ABOTH both_in_hull both_hull_ok NXF [] GBOTH BCAP CCAP fx_ok SHC KCAP AINVH HP
              both_G_ro_img2 both_G_img_al both_G_img_shlo nil_SWIN_img both_segs_out both_A_img_hi both_A_img_lo both_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).
  - intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn.
    refine (XN_L_rec (2 ^ 64) PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV ltac:(lia) HB0 HC0 HBc HCc HFB HUa _ _).
    + intros E _. unfold DMEAS. pose proof (u64_range (ev E 14)). lia.
    + exact (contract_upto_of_full BSEGS [] GBOTH fx_ok RZ SHC KCAP AINVH 14 (2 ^ 64) (ce ML) b2jv_both_callee_L1).
  - intros n PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV Hn HB0 HC0 HBc HCc HFB HUa HUm CCn.
    exact (XB_L_rec PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa).
  - intros i T k Hn. destruct (BgB2Jcerts.lidx i) eqn:Hl.
    + pose proof (CERTS_L i) as X. unfold cert_stmt in X. rewrite <- (BgB2Jcerts.cuts_LS i Hl), Hn in X.
      destruct X as (sh & H1 & H2 & H3). exists sh. split; [exact H1|]. split; [exact H2|].
      right. exists (HScut (ce ML) (CUTS ML) (Datatypes.S i)). split; [exact (BgB2Jcerts.hs_LS i Hl) | exact H3].
    + pose proof (CERTS_S i Hl) as X. unfold cert_stmt in X. rewrite Hn in X.
      destruct X as (sh & H1 & H2 & H3). exists sh. split; [exact H1|]. split; [exact H2|]. left. exact H3.
Qed.
End Contract.
