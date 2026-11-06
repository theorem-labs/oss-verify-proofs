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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFP_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PFF_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import SegSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c4.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c6.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c7.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_c8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Definition P2_hints : list (list ST.xhint) := [[]; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []].
Lemma p2_cert : SP.pcheck SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true P2_hints = true.
Proof.
  apply (pcheck_of_chunksH SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true [[(T0, []); (CD, []); (CFO, []); (CFO2, []); (CFA, []); (CFA2, []); (HOB, []); (COB, []); (HAB, []); (HAV, []); (CAV, []); (CAV2, []); (CAV3, []); (HAC, []); (CAC, []); (HOC, []); (COC, []); (COC2, []); (HEND, []); (CEND, [])]; [(TAS, [])]; [(HOF, []); (COF1, []); (COF2, []); (COF3, []); (COF4, [])]; [(TOB, [])]; [(TOC, [])]; [(TOS, [])]; [(TRS, [])]; [(NIA, [])]; [(NSA, [])]; [(NFA, []); (NEA, [])]; [(NGA, []); (NZA, [])]; [(NIO, [])]; [(NSO, [])]; [(NFO, []); (NEO, [])]; [(NGO, []); (NZO, [])]; [(NPA, [])]; [(NCA, []); (NJA, [])]; [(NPO, [])]; [(NCO, []); (NJO, [])]; [(CSA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSA, []); (CPA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPA, []); (CSO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSO, []); (CPO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPO, [])]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact p2_c1|]. apply Forall_cons; [exact p2_c2|]. apply Forall_cons; [exact p2_c3|]. apply Forall_cons; [exact p2_c4|]. apply Forall_cons; [exact p2_c5|]. apply Forall_cons; [exact p2_c6|]. apply Forall_cons; [exact p2_c7|]. apply Forall_cons; [exact p2_c8|]. apply Forall_cons; [exact p2_c9|]. apply Forall_cons; [exact p2_c10|]. apply Forall_cons; [exact p2_c11|]. apply Forall_cons; [exact p2_c12|]. apply Forall_cons; [exact p2_c13|]. apply Forall_cons; [exact p2_c14|]. apply Forall_cons; [exact p2_c15|]. apply Forall_cons; [exact p2_c16|]. apply Forall_cons; [exact p2_c17|]. apply Forall_cons; [exact p2_c18|]. apply Forall_cons; [exact p2_c19|]. apply Forall_cons; [exact p2_c20|]. apply Forall_nil.
Qed.
