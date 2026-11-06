(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncVisitBoolRXB EncVisitBoolNXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBFA.
Import PMES.
Section VisitBool.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ACC_TRUE : PMESA.img_aacc HI (EVBNA.LTXTf true) 4.
Hypothesis ACC_FALSE : PMESA.img_aacc HI (EVBNA.LTXTf false) 5.
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xboth a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Variable CL : Z.
Hypothesis BSCALAR_OK : PMESA.begin_scalar_specA L ar HI PMLA.C_xboth PMESA.EC_xboth CL EVBNA.PC_BEGIN_SCALAR.
Hypothesis TRUE_OK : PMESA.true_literal_specA L ar HI PMLA.C_xboth EVBNA.PC_TRUE_LIT.
Hypothesis FALSE_OK : PMESA.false_literal_specA L ar HI PMLA.C_xboth EVBNA.PC_FALSE_LIT.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xboth CL EVBNA.PC_APPEND.

Theorem visit_bool_ok : PMESA.visit_bool_specA L ar HI PMLA.C_xboth PMESA.EC_xboth 12800 CL PMESA.PC_VISIT_BOOL_xboth.
Proof.
  intros vb LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  destruct (g_es g) as [|c0 r0] eqn:Hes.
  - apply (visit_bool_root_ok L ar C HI HIok LAY FPM ACC_TRUE ACC_FALSE FOOTXC CL TRUE_OK FALSE_OK APPEND_OK vb LBo FF LK cr A sp r V S2 kx bx g Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
  - apply (visit_bool_nested_ok L ar C HI HIok LAY FPM ACC_TRUE ACC_FALSE FOOTXC CL BSCALAR_OK TRUE_OK FALSE_OK APPEND_OK vb LBo FF LK cr A sp r V S2 kx bx g c0 r0 Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
Qed.
End VisitBool.
End EVBFA.
Print Assumptions EVBFA.visit_bool_ok.
