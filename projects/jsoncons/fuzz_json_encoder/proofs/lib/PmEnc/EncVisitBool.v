(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncVisitBoolN EncVisitBoolR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBF.
Import PMES.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis BSCALAR_OK : begin_scalar_spec L HI.
Hypothesis TRUE_OK : true_literal_spec L.
Hypothesis FALSE_OK : false_literal_spec L.
Hypothesis APPEND_OK : str_append_x_spec L HI.

Theorem visit_bool_ok : visit_bool_spec L HI WD_SCR_X.
Proof.
  unfold visit_bool_spec, vtrans, vtrans_gen. intros bb LBo cr sp r V S2 kx g.
  assert (Hc : g_es g = [] \/ exists c0 r0, g_es g = c0 :: r0) by (destruct (g_es g) as [|c0 r0]; [left; reflexivity | right; exists c0, r0; reflexivity]).
  destruct Hc as [Hes|(c0 & r0 & Hes)].
  - exact (EVBR.visit_bool_root_ok L HI HIok LAY FPM TRUE_OK FALSE_OK APPEND_OK bb LBo cr sp r V S2 kx g Hes).
  - exact (EVBN.visit_bool_nested_ok L HI HIok LAY FPM BSCALAR_OK TRUE_OK FALSE_OK APPEND_OK bb LBo cr sp r V S2 kx g c0 r0 Hes).
Qed.
End S.
End EVBF.
