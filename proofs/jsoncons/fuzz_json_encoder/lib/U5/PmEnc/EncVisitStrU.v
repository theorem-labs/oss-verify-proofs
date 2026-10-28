(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncVisitStrNU EncVisitStrRU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVStrFU.
Import PMES.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis BSCALAR_OK : begin_scalar_specU L HI.
Hypothesis WSTRING_OK : write_string_specU L HI.

Theorem visit_string_ok : visit_string_specU L HI WD_SCR_X.
Proof.
  unfold visit_string_specU, vtrans_svU. intros tag bs Htag LBo cr sp r V S2 kx bx sv g.
  assert (Hc : g_es g = [] \/ exists c0 r0, g_es g = c0 :: r0) by (destruct (g_es g) as [|c0 r0]; [left; reflexivity | right; exists c0, r0; reflexivity]).
  destruct Hc as [Hes|(c0 & r0 & Hes)].
  - exact (EVStrRU.visit_string_root_ok L HI HIok LAY FPM WSTRING_OK tag sv bs Htag LBo cr sp r V S2 kx bx g Hes).
  - exact (EVStrNU.visit_string_nested_ok L HI HIok LAY FPM BSCALAR_OK WSTRING_OK tag sv bs Htag LBo cr sp r V S2 kx bx g c0 r0 Hes).
Qed.
End S.
End EVStrFU.
