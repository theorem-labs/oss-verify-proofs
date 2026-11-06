(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0120. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0099. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NarWrapFreeR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0095. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0133. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NatLift OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0120.NarDep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0099.NarUkey OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInvFreePure OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInvLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInvLaws4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarWrapKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NarWrapFreeR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarWrapMallocAll OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarWrapFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0095.NarWrapMemI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0133.NarWrapSmallocI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarIfaceLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarIfaceInstFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0133.NarIfaceInstAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceInstSfree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276.NarIfaceLayoutPM OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0133.NarIcptInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0276.NarIcptLawsGap OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarFam.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnACxa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.NTopAsmA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242.PnAOpnewN.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FamTop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable IL : icpt_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x693b00.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x6b4fb8.
Hypothesis Hloff : rn_loff rn = 0x10.
Hypothesis ILY : as0_icpt_layout IL.

#[local] Abbreviation HIk := (art_HIk MAPS0 RESV0 NOACC0 BASE BUDGET rn).

(* [comment removed for export] *)
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_inst : forall D, @NTASMA.inst_ok (MkScfgP scfg) art_L art_C IL (rn_ar rn) (HIk D).
Proof.
  intros D. set (rnD := art_rn_k rn D).
  assert (SM : forall k, In k [0; 1; 2; 3; 4; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIk D) k) by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
  pose proof (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff
                (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Halloc Hwx STATIC Htp) SM) as OKR.
  split; [exact OKR|]. split; [exact (art_icpt_ok scfg IL BUDGET Hwx ILY MAPS0 RESV0 NOACC0 BASE rnD Htp Hkey0 Htsd Hloff)|]. split.
  - apply HAJ.AEXT.
    + exact (art_inst_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
    + exact (@PMACXA.cxa_atexit_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIk D) art_pma_layout OKR (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rnD Htp Hkey0 Htsd Hloff)).
    + exact (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rnD Htp Hkey0 Htsd Hloff).
    + exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
    + exact (art_inst_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
  - exact (art_law_img_gap MAPS0 RESV0 NOACC0 BASE BUDGET rnD).
Qed.

(* [comment removed for export] *)
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_opnew_n : forall D, @PQRAa.opnew_n_spec (MkScfgP scfg) art_L (rn_ar rn) (HIk D).
Proof.
  intros D.
  exact (@PMAOPNW.opnew_n_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIk D) art_pma_layout (art_fam_base MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff D)
           (fun _ => art_fam_mallocN MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff D)).
Qed.

(* [comment removed for export] *)
#[using="Hwx Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_memmove_libc_n : forall D, @PQASA.memmove_libc_n_spec (MkScfgP scfg) art_L (rn_ar rn) (HIk D) IL.
Proof. intros D. exact (art_inst_memmove_libcN scfg IL BUDGET Hwx ILY MAPS0 RESV0 NOACC0 BASE (art_rn_k rn D) Htp Hkey0 Htsd Hloff). Qed.

(* [comment removed for export] *)
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_top : @NTASMA.fam_ok (MkScfgP scfg) art_L art_C IL art_LR (rn_ar rn) HIk.
Proof.
  split; [exact (art_fam_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff)|].
  split; [exact art_fam_inst|exact art_fam_memmove_libc_n].
Qed.
End FamTop.
