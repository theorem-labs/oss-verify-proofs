(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The library of the ubsan target on the ubsan heap instance: the library layout Lay0U satisfies the U layout
   predicate, and the U library contract holds for the input predicate PHI0U. The library functions are proved by
   the walks below where those exist; each function still without a walk is one Section hypothesis. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec HeapIface LibIface LibIfaceFp L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require FrmInv.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmLayoutInst_u5 Pm6LayInst_u5 Pm6FrmInv_u5 PmXubsanStmt.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU HeapInstU HeapClosedU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require PmHeapInst6_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require TopGlueU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopSpecs_u5 TopSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Skel_u5 TopLeaves_u5 SourceDtor_u5 IssCtor_u5 IosbInit_u5 ReaderCtor_u5 IosbDtor_u5 ParserDtor_u5 SbufCtor_u5 EncDtorX_u5 EncCtorX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require OpDel_u5 StrInit_u5 OpNew_u5 StrReserve_u5 VecReserve_u5 VecPush_u5 Memcpy1_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutDemo Require Pm6Memmove_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Pm6Island_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import LibSpecU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require HarnessXWU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require RefBridgeU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmLibSpecsW_u5 PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require TopSpecsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmInteg Require AssemblyFullXWU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLibInstU.
Abbreviation SS := PML.STRTOD_SCR_V.
Abbreviation WD := PMES.WD_SCR_X.
Definition cfgUP : ScfgP := {| SCFG := PmXubsanStmt.PmXubsanStmt.cfgU |}.

Lemma valid_sp_img : forall sp, valid_sp sp -> 0xfe000 <= bv_unsigned sp.
Proof. intros sp (H & _). assert (X : (0xfe000 <=? sp_window_lo) = true) by reflexivity. apply Z.leb_le in X. lia. Qed.

Lemma pm0_layout_L0U : forall sptop, 0xfe000 <= sptop -> PmLayout.pm0_layout (L0U sptop).
Proof.
  intros sptop H. destruct (PmLayoutInst_u5.pm0_layout_L0 sptop H).
  constructor; match goal with Hx : _ |- _ => exact Hx end.
Qed.

Lemma Lay0U_pm : forall sptop, LSU.pm_layout_okxU (L0U sptop) SS WD (TopGlueU.TopGlueU.Lay0U sptop).
Proof.
  intros sptop. unfold LSU.pm_layout_okxU, TopGlueU.TopGlueU.Lay0U, Pm6LayInst_u5.PmLay.
  cbn [ll_heap ll_entry ll_gp ll_stack ll_foot ll_credit ll_rw_lo].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - apply Z.leb_le. vm_compute. reflexivity.
  - split; [reflexivity|]. split; [intros n; reflexivity|]. unfold PML.IMG_RO_HI. lia.
Qed.

Lemma Lay0U_ifaceU : forall PHI sptop,
  @LSU.lib_specxU cfgUP (L0U sptop) (HIU sptop) SS WD PHI (TopGlueU.TopGlueU.Lay0U sptop) ->
  LCU.lib_iface_okU (TopGlueU.TopGlueU.Lay0U sptop) PmXubsanStmt.PmXubsanStmt.cfgU (HIU sptop) PMX.pm_staticsx PHI.
Proof.
  intros PHI sptop LIB. constructor.
  - exact (LIB (Lay0U_pm sptop)).
  - exact (TopGlueU.TopGlueU.pm_statics_init sptop).
  - exact (TopGlueU.TopGlueU.pm_statics_frame sptop).
Qed.

Lemma fp_inv0 : LSU.fp_inv.
Proof.
  intros fx fx' R pc M R' pc' M' H.
  exact (FrmInv.FrmInv.msteps_fp_ok PML.RSEGS Pm6FrmInv_u5.Pm6FrmInv.text_safe fx fx' R _ M _ R' _ M' _ H).
Qed.

Section Inst.
Abbreviation LU sp := (L0U (bv_unsigned sp)).
Abbreviation HU sp := (HIU (bv_unsigned sp)).
#[local] Existing Instance cfgUP.
Section At.
Variable sp : word.
Hypothesis Hsp : valid_sp sp.
Let HIok : heap_iface_ok (LU sp) SCFG (HU sp) := HIU_iface_ok_closed (bv_unsigned sp) PmXubsanStmt.PmXubsanStmt.cfgU eq_refl.
Let LAY : PmLayout.pm0_layout (LU sp) := pm0_layout_L0U (bv_unsigned sp) (valid_sp_img sp Hsp).
Lemma READ : PMXW.read_specxwU (LU sp) (HU sp) SS WD.
Proof.
  pose proof (hiu_malloc_u _ _ _ (HIU_ok_closed (bv_unsigned sp) PmXubsanStmt.PmXubsanStmt.cfgU eq_refl)) as MXU.
  apply (AssemblyFullXWU.ASMFXWU.read_okU (LU sp) (HU sp));
    first [exact HIok | exact LAY | exact fp_inv0 | exact MXU].
Qed.

Lemma ENC_CTOR : PMES.enc_ctor_spec (LU sp) (HU sp).
Proof. exact (EncCtorX_u5.ECX.enc_ctor_ok (LU sp) (HU sp) HIok LAY fp_inv0). Qed.
Lemma SYSCAT : PMS.system_category_spec (LU sp).
Proof. apply Skel_u5.SK.system_category_ok; exact fp_inv0. Qed.
Lemma LOCDTOR : PMS.locale_dtor_spec (LU sp).
Proof. apply TopLeaves_u5.TL.locale_dtor_ok; exact fp_inv0. Qed.
Lemma ISTRDTOR : TPS.istream_dtor_spec (LU sp).
Proof. apply TopLeaves_u5.TL.istream_dtor_ok; exact fp_inv0. Qed.
Lemma OPDELS : PMS.opdel_sized_spec (LU sp) (HU sp).
Proof. apply OpDel_u5.OD.opdel_sized_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma PDTOR : PMS.parser_dtor_spec (LU sp) (HU sp).
Proof. apply ParserDtor_u5.PD.parser_dtor_ok; first [exact HIok | exact LAY | exact fp_inv0 | exact OPDELS]. Qed.
Lemma ENC_DTOR : PMES.enc_dtor_spec (LU sp) (HU sp).
Proof. exact (EncDtorX_u5.EDX.enc_dtor_ok (LU sp) (HU sp) HIok LAY fp_inv0 OPDELS). Qed.
Lemma IOSBDTOR : TPS.iosb_dtor_spec (LU sp).
Proof. eapply IosbDtor_u5.ID.iosb_dtor_ok with (HI := HU sp); first [exact HIok | exact LAY | exact fp_inv0 | exact LOCDTOR]. Qed.
Lemma SDTOR : PMS.source_dtor_spec (LU sp) (HU sp).
Proof.
  apply SourceDtor_u5.SD.source_dtor_ok;
    first [exact HIok | exact LAY | exact fp_inv0 | exact OPDELS | exact LOCDTOR | exact ISTRDTOR | exact IOSBDTOR].
Qed.
Lemma LOCLATER : PMS.locale_ctor_later_spec (LU sp).
Proof. apply Skel_u5.SK.locale_ctor_later_ok; exact fp_inv0. Qed.
Lemma LOCFIRST : PMS.locale_ctor_first_spec (LU sp).
Proof. apply Pm6Island_u5.ISL0.locale_ctor_first_ok; exact fp_inv0. Qed.
Lemma IOSBINIT_LATER : TPS2.iosb_init_later_spec (LU sp).
Proof. apply IosbInit_u5.II.iosb_init_later_ok; first [exact fp_inv0 | exact LOCLATER]. Qed.
Lemma IOSBINIT_FIRST : TPS2.iosb_init_first_spec (LU sp).
Proof. apply IosbInit_u5.II.iosb_init_first_ok; first [exact fp_inv0 | exact LOCFIRST]. Qed.
Lemma STRINIT : PMS.strinit_spec (LU sp) (HU sp).
Proof. apply StrInit_u5.SI.strinit_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma OPNEW : PMS.opnew_spec (LU sp) (HU sp).
Proof. apply OpNew_u5.ON.opnew_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma SBUFCTOR : TPS2.sbuf_ctor_spec (LU sp) (HU sp).
Proof.
  apply SbufCtor_u5.SBC.sbuf_ctor_ok;
    first [exact HIok | exact LAY | exact fp_inv0 | exact LOCLATER | exact OPNEW
          | exact (Pm6Memmove_u5.memmove_copy1 (LU sp) (PmLayout.ly_segs _ LAY))
          | exact (Memcpy1_u5.MC1.memcpy_copy1 (LU sp) (PmLayout.ly_segs _ LAY))].
Qed.
Lemma ISS : PMS.iss_ctor_spec (LU sp) (HU sp).
Proof.
  apply IssCtor_u5.IC.iss_ctor_ok;
    first [exact HIok | exact LAY | exact fp_inv0 | exact IOSBINIT_FIRST | exact IOSBINIT_LATER | exact SBUFCTOR].
Qed.
Lemma STRRSV : PMS.str_reserve_spec (LU sp) (HU sp).
Proof. apply StrReserve_u5.SRV.str_reserve_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma VRSV : PMS.vec_reserve_spec (LU sp) (HU sp).
Proof. apply VecReserve_u5.VR.vec_reserve_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma VPUSH : PMS.vec_push_spec (LU sp) (HU sp).
Proof. apply VecPush_u5.VP.vec_push_ok; first [exact HIok | exact LAY | exact fp_inv0]. Qed.
Lemma RCTOR : PMS.reader_ctor_spec (LU sp) (HU sp).
Proof.
  apply ReaderCtor_u5.RC.reader_ctor_ok;
    first [exact HIok | exact LAY | exact fp_inv0 | exact IOSBINIT_LATER | exact LOCLATER | exact OPNEW | exact STRRSV
          | exact VRSV | exact VPUSH].
Qed.

Lemma FNS : LSU.lib_fnspecsU (LU sp) (HU sp) SS WD.
Proof.
  exact (LSU.LFSU _ _ _ _ STRINIT ISS ENC_CTOR RCTOR SYSCAT READ PDTOR SDTOR
           ENC_DTOR OPDELS LOCDTOR ISTRDTOR IOSBDTOR).
Qed.

Lemma RUN0 : LSU.harness_runU (LU sp) (HU sp) SS WD.
Proof. exact (HarnessXWU.HNXWU.walkU_fns (LU sp) (HU sp) SS WD HIok LAY fp_inv0 FNS RefBridgeU.RefBridgeU.wroom_g0). Qed.
End At.

Theorem lib_iface0U : forall sp, valid_sp sp ->
  LCU.lib_iface_okU (TopGlueU.TopGlueU.Lay0U (bv_unsigned sp)) PmXubsanStmt.PmXubsanStmt.cfgU (HIU (bv_unsigned sp))
    PMX.pm_staticsx PmXubsanStmt.PmXubsanStmt.PHI0U.
Proof.
  intros sp Hsp. apply Lay0U_ifaceU.
  apply (@LSU.lib_specxU_of_run cfgUP (L0U (bv_unsigned sp)) (HIU (bv_unsigned sp)) SS WD).
  - exact (HIU_iface_ok_closed (bv_unsigned sp) PmXubsanStmt.PmXubsanStmt.cfgU eq_refl).
  - exact (pm0_layout_L0U (bv_unsigned sp) (valid_sp_img sp Hsp)).
  - exact (RUN0 sp Hsp).
  - exact PmXubsanStmt.PmXubsanStmt.PHI0U_IND.
Qed.
End Inst.
End PmLibInstU.
