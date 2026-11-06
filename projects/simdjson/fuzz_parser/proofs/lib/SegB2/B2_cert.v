(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegDiag.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2WalkVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVC2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import SegSplitH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c4.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c6.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c7.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c8.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c9.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c10.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import B2_c11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Definition B2_hints : list (list ST.xhint) := [[]; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]; []].
Lemma b2_cert : SP.pcheckH SG gfp2 (SVX.gvc_trimp 90 (SVX.gvc_enrich SVX.bc_enrich (wvc_okL SG 1048512 0x236c0))) B2 B2_IT 4000 true B2_hints = true.
Proof.
  apply (pcheckH_of_chunksH SG gfp2 (SVX.gvc_trimp 90 (SVX.gvc_enrich SVX.bc_enrich (wvc_okL SG 1048512 0x236c0))) B2 B2_IT 4000 true [[(T0, []); (CD, []); (CFO, []); (CFO2, []); (CFA, []); (CFA2, []); (HOB, []); (COB, []); (HAB, []); (HAV, [])]; [(CAV, []); (CAV2, []); (CAV3, []); (HAC, []); (CAC, []); (HOC, []); (COC, []); (COC2, []); (CENDO, []); (CENDA, []); (CIA, []); (TAS, [])]; [(HOF, []); (COF1, []); (COF2, []); (COF3, []); (COF4, []); (TOB, [])]; [(TOC, []); (TOS, []); (TRS, [])]; [(NIA, [])]; [(NSA, []); (NFA, []); (NEA, []); (NXM, []); (NXP, []); (NGA, []); (NZA, [])]; [(NIO, [])]; [(NSO, []); (NFO, []); (NEO, []); (NXMO, []); (NXPO, []); (NGO, []); (NZO, [])]; [(NPA, []); (NCA, [])]; [(NPO, [])]; [(NCO, []); (CSA, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]); (RSA, []); (CPA, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]); (RPA, []); (CSO, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]); (RSO, []); (CPO, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-26))) (EVar 29)); (16%nat, EVar 18); (17%nat, EVar 31); (18%nat, EVar 19); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 32)] [] []]); (RPO, [])]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact b2_c1|]. apply Forall_cons; [exact b2_c2|]. apply Forall_cons; [exact b2_c3|]. apply Forall_cons; [exact b2_c4|]. apply Forall_cons; [exact b2_c5|]. apply Forall_cons; [exact b2_c6|]. apply Forall_cons; [exact b2_c7|]. apply Forall_cons; [exact b2_c8|]. apply Forall_cons; [exact b2_c9|]. apply Forall_cons; [exact b2_c10|]. apply Forall_cons; [exact b2_c11|]. apply Forall_nil.
Qed.
