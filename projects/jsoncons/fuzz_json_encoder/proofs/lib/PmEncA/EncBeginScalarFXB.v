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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncBeginScalarXB EncBeginScalarNXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EBFA.
Import PMES.
Section BeginScalar.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ACC_COMMA : PMESA.img_aacc HI EBNA.TXT_COMMA 2.
Variable CL : Z.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xboth CL EBNA.PC_APPEND.
Hypothesis NEWLINE_OK : PMESA.new_line_specA L ar HI PMLA.C_xboth PMESA.EC_xboth CL EBNA.PC_NEW_LINE.

Theorem begin_scalar_ok : PMESA.begin_scalar_specA L ar HI PMLA.C_xboth PMESA.EC_xboth CL PMESA.PC_BEGIN_SCALAR_xboth.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & _ & Hstksh & Hinv & _ & HROOM & Himg & Hcred & Hobjs) Hcont.
  destruct (g_es g) as [|c0 r0] eqn:Hes.
  - apply (begin_scalar_root_ok L ar C HI HIok LAY FPM CL LBo FF LK cr A sp r V S2 kx bx g fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (P1 & P2 & P3 & P4 & P5) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. subst cr'.
    exists g, 0. rewrite Hes. split; [exact P1|]. repeat (split; [first [reflexivity | assumption | lia]|]). exact Hcred.
  - apply (begin_scalar_nested_ok L ar C HI HIok LAY FPM ACC_COMMA CL APPEND_OK NEWLINE_OK LBo FF LK cr A sp r V S2 kx bx g c0 r0 fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs);
      [repeat (split; [first [assumption | rewrite Hes; assumption]|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (g' & d & P) HRP HP Hrt HA Hmo' HLK HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
Qed.
End BeginScalar.
End EBFA.
Print Assumptions EBFA.begin_scalar_ok.
