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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import P2_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma p2_c17 : forallb (fun th => SP.tm_check SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true (fst th) (snd th)) [(NCA, []); (NJA, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma p2_c18 : forallb (fun th => SP.tm_check SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true (fst th) (snd th)) [(NPO, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma p2_c19 : forallb (fun th => SP.tm_check SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true (fst th) (snd th)) [(NCO, []); (NJO, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma p2_c20 : forallb (fun th => SP.tm_check SG gfp2 (wvc_ok SG 1048512 0x13768) P2 P2_IT 4000 true (fst th) (snd th)) [(CSA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSA, []); (CPA, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPA, []); (CSO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RSO, []); (CPO, [ST.XH [(16%nat, EVar 18); (17%nat, EVar 19)] [] []]); (RPO, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
