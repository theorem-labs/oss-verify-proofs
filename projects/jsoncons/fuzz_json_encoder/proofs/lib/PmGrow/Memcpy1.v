(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AsanPlanSoundSums HeapIface L5Defs L5Core Pm6Sums Pm6PlanKit PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module MC1.
Definition MEMCPY : Z := 0xba65c.
Section Inst.
Context {SCFG_P : ScfgP}.
Theorem memcpy_copy1 : forall L : heap_layout, hl_segs L = PML.RSEGS -> CH2.copy1_spec L MEMCPY.
Proof. intros L LS. apply CH2.copy1_of_copy_spec. rewrite LS. exact src0_copy_spec_memcpy. Qed.
End Inst.
End MC1.
Print Assumptions MC1.memcpy_copy1.
