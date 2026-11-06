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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVC2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegDig.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2N Require Import B2N_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma b2n_c1 : forallb (fun th => SP.tm_check SG (SDG.gfpx gfp2) (SVX.gvc_enrich SVX.bc_enrich (SDG.gsplit SG (wvc_okL SG 1048512 0x236c0))) B2N B2N_IT 4000 true (fst th) (snd th)) [(T0, [ST.XH [(19%nat, EVar 36); (20%nat, EVar 39); (21%nat, EVar 42); (22%nat, EVar 43); (23%nat, EAlu ALU_ADD (EVar 18) (EVar 40)); (24%nat, EVar 41); (25%nat, EVar 44); (26%nat, EVar 45)] [] []]); (TR1, [ST.XH [(18%nat, EAlu ALU_ADD (EVar 36) (EVar 46)); (19%nat, EAlu ALU_SUB (EAlu ALU_SUB (EVar 37) (EVar 38)) (EVar 46)); (20%nat, EVar 42); (21%nat, EVar 43); (22%nat, EVar 38)] [] []]); (TR2, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
