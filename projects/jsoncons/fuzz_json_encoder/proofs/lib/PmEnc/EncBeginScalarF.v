(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncKit EncBeginScalar EncBeginScalarN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EBF.
Import PMES.
Section BeginScalar.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPEND_OK : str_append_x_spec L HI.
Hypothesis NEWLINE_OK : new_line_spec L HI.

Theorem begin_scalar_ok : begin_scalar_spec L HI.
Proof.
  intros LBo cr sp r V S2 kx g. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & _ & Hinv & _ & Himg & Hcred & Hobjs) Hcont.
  destruct (g_es g) as [|c0 r0] eqn:Hes.
  - apply (EBS.begin_scalar_root_ok L HI HIok LAY FPM LBo cr sp r V S2 kx g fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W HFP (P1 & P2 & P3 & P4 & P5) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. subst cr'.
    exists g, 0. rewrite Hes. split; [exact P1|]. repeat (split; [first [reflexivity | assumption | lia]|]). reflexivity.
  - apply (EBN.begin_scalar_nested_ok L HI HIok LAY FPM APPEND_OK NEWLINE_OK LBo cr sp r V S2 kx g c0 r0 fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W HFP (g' & d & P) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists g', d. rewrite Hes in P. exact P.
Qed.
End BeginScalar.
End EBF.
Print Assumptions EBF.begin_scalar_ok.
