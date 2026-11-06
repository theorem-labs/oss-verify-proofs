(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncVisitEndAD EncVisitEndOD EncVisitEndAL EncVisitEndOL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVEF.
Import PMES.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis NEWLINE2_OK : new_line2_spec L HI.
Hypothesis APPEND_OK : str_append_x_spec L HI.

Lemma es_cases : forall (es : estate), es = [] \/ (exists c0, es = [c0]) \/ (exists c0 c2 r0, es = c0 :: c2 :: r0).
Proof. intros [|c0 [|c2 r0]]; [left; reflexivity | right; left; exists c0; reflexivity | right; right; exists c0, c2, r0; reflexivity]. Qed.

Theorem visit_end_array_ok : visit_end_array_spec L HI WD_SCR_X.
Proof.
  unfold visit_end_array_spec, vtrans, vtrans_gen. intros LBo cr sp r V S2 kx g.
  destruct (es_cases (g_es g)) as [Hes|[(c0 & Hes)|(c0 & c2 & r0 & Hes)]].
  - intros fx R M model K HH Hmo HK Hfp PRE. exfalso. destruct PRE as (_ & _ & _ & _ & G & _). rewrite Hes in G. exact (G eq_refl).
  - exact (EVEAL.visit_end_array_last_ok L HI HIok LAY FPM NEWLINE2_OK APPEND_OK LBo cr sp r V S2 kx g c0 Hes).
  - exact (EVEAD.visit_end_array_deep_ok L HI HIok LAY FPM NEWLINE2_OK APPEND_OK LBo cr sp r V S2 kx g c0 c2 r0 Hes).
Qed.

Theorem visit_end_object_ok : visit_end_object_spec L HI WD_SCR_X.
Proof.
  unfold visit_end_object_spec, vtrans, vtrans_gen. intros LBo cr sp r V S2 kx g.
  destruct (es_cases (g_es g)) as [Hes|[(c0 & Hes)|(c0 & c2 & r0 & Hes)]].
  - intros fx R M model K HH Hmo HK Hfp PRE. exfalso. destruct PRE as (_ & _ & _ & _ & G & _). rewrite Hes in G. exact (G eq_refl).
  - exact (EVEOL.visit_end_object_last_ok L HI HIok LAY FPM NEWLINE2_OK APPEND_OK LBo cr sp r V S2 kx g c0 Hes).
  - exact (EVEOD.visit_end_object_deep_ok L HI HIok LAY FPM NEWLINE2_OK APPEND_OK LBo cr sp r V S2 kx g c0 c2 r0 Hes).
Qed.
Print Assumptions visit_end_object_ok.
End S.
End EVEF.
