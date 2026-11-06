(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AsanPlanSoundSums HeapIface L5Defs L5Core Pm10Sums Pm10PlanKit PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module MC1.
Definition MEMCPY : Z := 0xb5a40.
Section Inst.
Context {SCFG_P : ScfgP}.
Theorem memcpy_copy1 : forall L : heap_layout, hl_segs L = PML.RSEGS -> CH2.copy1_spec L MEMCPY.
Proof. intros L LS. apply CH2.copy1_of_copy_spec. rewrite LS. exact src0_copy_spec_memcpy. Qed.
End Inst.
End MC1.

