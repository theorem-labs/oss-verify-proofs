(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegDiag.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import SegSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2D_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2D_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma p2d_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) P2D P2D_IT 4000 false [] = true.
Proof.
  apply (pcheck_of_chunks SG (fun _ _ => []) (fun _ => false) P2D P2D_IT 4000 false [[D1; D2; D3]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - apply Forall_cons; [exact p2d_c1|]. apply Forall_nil.
Qed.
