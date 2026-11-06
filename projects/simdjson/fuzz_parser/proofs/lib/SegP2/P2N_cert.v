(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegDiag.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2WalkVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPC_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PFFC_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import SegSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2N_c1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2N_c2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Definition P2N_hints : list (list ST.xhint) := [[]; []; []; []; []; []; []; []; []; []; []; []; [ST.XH [(16%nat, EVar 29); (17%nat, EAlu ALU_SUB (EVar 19) (EVar 28))] [] []]; []; [ST.XH [(16%nat, EVar 29); (17%nat, EAlu ALU_SUB (EVar 19) (EVar 28))] [] []]; []].
Lemma p2n_cert : SP.pcheck SG gfp2 (wvc_ok SG 1048512 0x13768) P2N P2N_IT 4000 true P2N_hints = true.
Proof.
  apply (pcheck_of_chunksH SG gfp2 (wvc_ok SG 1048512 0x13768) P2N P2N_IT 4000 true [[(T0, []); (TR1, []); (TR2, []); (RIL, [])]; [(RSL, []); (RFL, []); (REL, [])]; [(RGL, []); (RZL, [])]; [(RPA, [])]; [(RCA, []); (RJA, []); (RCS, [ST.XH [(16%nat, EVar 29); (17%nat, EAlu ALU_SUB (EVar 19) (EVar 28))] [] []]); (RRS, []); (RCP, [ST.XH [(16%nat, EVar 29); (17%nat, EAlu ALU_SUB (EVar 19) (EVar 28))] [] []]); (RRP, [])]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact p2n_c1|]. apply Forall_cons; [exact p2n_c2|]. apply Forall_cons; [exact p2n_c3|]. apply Forall_cons; [exact p2n_c4|]. apply Forall_cons; [exact p2n_c5|]. apply Forall_nil.
Qed.
