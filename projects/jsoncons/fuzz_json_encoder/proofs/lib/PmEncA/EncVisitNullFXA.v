(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncVisitNullRXA EncVisitNullNXA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVNFA.
Import PMES.
Section VisitNull.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ACC_NULL : PMESA.img_aacc HI EVNA.LTXT 4.
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xasan a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Variable CL : Z.
Hypothesis BSCALAR_OK : PMESA.begin_scalar_specA L ar HI PMLA.C_xasan PMESA.EC_xasan CL EVNA.PC_BEGIN_SCALAR.
Hypothesis NULL_OK : PMESA.null_literal_specA L ar HI PMLA.C_xasan EVNA.PC_NULL_LIT.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xasan CL EVNA.PC_APPEND.

Theorem visit_null_ok : PMESA.visit_null_specA L ar HI PMLA.C_xasan PMESA.EC_xasan 12800 CL PMESA.PC_VISIT_NULL_xasan.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  destruct (g_es g) as [|c0 r0] eqn:Hes.
  - apply (visit_null_root_ok L ar C HI HIok LAY FPM ACC_NULL FOOTXC CL NULL_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
  - apply (visit_null_nested_ok L ar C HI HIok LAY FPM ACC_NULL FOOTXC CL BSCALAR_OK NULL_OK APPEND_OK LBo FF LK cr A sp r V S2 kx bx g c0 r0 Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
Qed.
End VisitNull.
End EVNFA.
Print Assumptions EVNFA.visit_null_ok.
