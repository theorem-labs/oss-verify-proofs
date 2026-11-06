(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncVisitEndODXA EncVisitEndADXA EncVisitEndOLXA EncVisitEndALXA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVEFA.
Import PMES.
Section VisitEnd.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable CL : Z.
Hypothesis ACC_CBRACE : PMESA.img_aacc HI 0x24b29 1.
Hypothesis ACC_CBRACKET : PMESA.img_aacc HI 0x24b2f 1.
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xasan a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis NEWLINE2_OK : PMESA.new_line2_specA L ar HI PMLA.C_xasan CL 0xba814.
Hypothesis ANNOT_OK : PMES2A.annotate_shrink_ctx_specA L ar HI 0xba5a0.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xasan CL 0xfe144.

Lemma es_cases : forall es : estate, es = [] \/ (exists c0, es = [c0]) \/ (exists c0 c2 r0, es = c0 :: c2 :: r0).
Proof. intros [|c0 [|c2 r0]]; [left; reflexivity | right; left; exists c0; reflexivity | right; right; exists c0, c2, r0; reflexivity]. Qed.

Theorem visit_end_object_ok : PMESA.visit_end_object_specA L ar HI PMLA.C_xasan PMESA.EC_xasan 12800 CL PMESA.PC_VISIT_END_OBJECT_xasan.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g.
  destruct (es_cases (g_es g)) as [Hes|[(c0 & Hes)|(c0 & c2 & r0 & Hes)]].
  - unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (_ & _ & _ & _ & _ & HG & _) Hcont. exfalso. rewrite Hes in HG. exact (HG eq_refl).
  - exact (visit_end_object_last_ok L ar C HI HIok LAY FPM CL ACC_CBRACE FOOTXC NEWLINE2_OK ANNOT_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g c0 Hes).
  - exact (visit_end_object_deep_ok L ar C HI HIok LAY FPM CL ACC_CBRACE FOOTXC NEWLINE2_OK ANNOT_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g c0 c2 r0 Hes).
Qed.

Theorem visit_end_array_ok : PMESA.visit_end_array_specA L ar HI PMLA.C_xasan PMESA.EC_xasan 12800 CL PMESA.PC_VISIT_END_ARRAY_xasan.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g.
  destruct (es_cases (g_es g)) as [Hes|[(c0 & Hes)|(c0 & c2 & r0 & Hes)]].
  - unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (_ & _ & _ & _ & _ & HG & _) Hcont. exfalso. rewrite Hes in HG. exact (HG eq_refl).
  - exact (visit_end_array_last_ok L ar C HI HIok LAY FPM CL ACC_CBRACKET FOOTXC NEWLINE2_OK ANNOT_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g c0 Hes).
  - exact (visit_end_array_deep_ok L ar C HI HIok LAY FPM CL ACC_CBRACKET FOOTXC NEWLINE2_OK ANNOT_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g c0 c2 r0 Hes).
Qed.
End VisitEnd.
End EVEFA.
Print Assumptions EVEFA.visit_end_object_ok.
