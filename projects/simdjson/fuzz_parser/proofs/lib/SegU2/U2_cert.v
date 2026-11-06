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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PFFU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import SegSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c4.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c6.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c7.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c8.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c9.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c10.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c11.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c12.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c13.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c14.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c15.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c16.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c17.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c18.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c19.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_c20.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Definition U2_hints : list (list ST.xhint) := [[]; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []; [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]; []].
Lemma u2_cert : SP.pcheck SG gfp2 (SVX.gvc_enrich SVX.bc_enrich (wvc_ok SG 1048512 0x13768)) U2 U2_IT 4000 true U2_hints = true.
Proof.
  apply (pcheck_of_chunksH SG gfp2 (SVX.gvc_enrich SVX.bc_enrich (wvc_ok SG 1048512 0x13768)) U2 U2_IT 4000 true [[(T0, []); (CD, []); (CFO, []); (CFO2, []); (CFA, []); (CFA2, []); (HOB, []); (COB, []); (HAB, []); (HAV, []); (CAV, []); (CAV2, []); (CAV3, []); (HAC, []); (CAC, []); (HOC, []); (COC, []); (COC2, []); (CENDO, []); (CENDA, []); (CIA, [])]; [(TAS, [])]; [(HOF, []); (COF1, []); (COF2, []); (COF3, []); (COF4, [])]; [(TOB, [])]; [(TOC, [])]; [(TOS, [])]; [(TRS, [])]; [(NIA, [])]; [(NSA, [])]; [(NFA, []); (NEA, []); (NEX, [])]; [(NGA, []); (NZA, [])]; [(NIO, [])]; [(NSO, [])]; [(NFO, []); (NEO, []); (NEXO, [])]; [(NGO, []); (NZO, [])]; [(NPA, [])]; [(NCA, []); (NJA, [])]; [(NPO, [])]; [(NCO, []); (NJO, [])]; [(CSA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSA, []); (CPA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPA, []); (CSO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSO, []); (CPO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPO, [])]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact u2_c1|]. apply Forall_cons; [exact u2_c2|]. apply Forall_cons; [exact u2_c3|]. apply Forall_cons; [exact u2_c4|]. apply Forall_cons; [exact u2_c5|]. apply Forall_cons; [exact u2_c6|]. apply Forall_cons; [exact u2_c7|]. apply Forall_cons; [exact u2_c8|]. apply Forall_cons; [exact u2_c9|]. apply Forall_cons; [exact u2_c10|]. apply Forall_cons; [exact u2_c11|]. apply Forall_cons; [exact u2_c12|]. apply Forall_cons; [exact u2_c13|]. apply Forall_cons; [exact u2_c14|]. apply Forall_cons; [exact u2_c15|]. apply Forall_cons; [exact u2_c16|]. apply Forall_cons; [exact u2_c17|]. apply Forall_cons; [exact u2_c18|]. apply Forall_cons; [exact u2_c19|]. apply Forall_cons; [exact u2_c20|]. apply Forall_nil.
Qed.
