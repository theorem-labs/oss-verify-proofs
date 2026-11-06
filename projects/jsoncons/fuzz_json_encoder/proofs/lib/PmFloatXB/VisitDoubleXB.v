(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require Import VisitDoubleNTabXB VisitDoubleRTabXB VisitDoubleRXB VisitDoubleNXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVDFA.
Import PMES.
Section VisitDouble.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ACC_NULL : PMESA.img_aacc HI EVDNA.LTXT 4.
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xboth a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Variable IL0 : icpt_layout.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI : Forall (fun r : Z * Z => EVDNA.VBOFF + 8 <= fst r \/ snd r <= EVDNA.VBOFF) (icl_poison IL0).
Hypothesis TPV : hl_tp L = EVDNA.TP.
Hypothesis SM4 : hl_stack_malloc L 4 = EVDNA.PC_SM.
Hypothesis SETSH : aset_shadow_spec L ar SCFG HI EVDNA.PC_SETSH 245 256.
Variable CL : Z.
Hypothesis BSCALAR_OK : PMESA.begin_scalar_specA L ar HI PMLA.C_xboth PMESA.EC_xboth CL EVDNA.PC_BEGIN_SCALAR.
Hypothesis NULL_OK : PMESA.null_literal_specA L ar HI PMLA.C_xboth EVDNA.PC_NULL_LIT.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xboth CL EVDNA.PC_APPEND.
Hypothesis WD_OK : PMESA.write_double_x_specA L ar HI PMLA.C_xboth 12800 CL EVDNA.PC_WD.

Theorem visit_double_ok : PMESA.visit_double_specA L ar HI PMLA.C_xboth PMESA.EC_xboth 12800 CL PMESA.PC_VISIT_DOUBLE_xboth.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  destruct (g_es g) as [|c0 r0] eqn:Hes.
  - apply (visit_double_root_ok L ar C HI HIok LAY FPM ACC_NULL FOOTXC IL0 ISH POI TPV SM4 SETSH CL NULL_OK APPEND_OK WD_OK LBo FF LK cr A sp r V S2 kx bx g Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
  - apply (visit_double_nested_ok L ar C HI HIok LAY FPM ACC_NULL FOOTXC IL0 ISH POI TPV SM4 SETSH CL BSCALAR_OK NULL_OK APPEND_OK WD_OK LBo FF LK cr A sp r V S2 kx bx g c0 r0 Hes fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [rewrite Hes; exact PRE|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
Qed.
End VisitDouble.
End EVDFA.
Print Assumptions EVDFA.visit_double_ok.
