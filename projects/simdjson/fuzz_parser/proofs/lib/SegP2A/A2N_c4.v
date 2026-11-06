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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma a2n_c4 : forallb (fun th => SP.tm_check SG gfp2 (wvc_okL SG 1048512 0x23640) A2N A2N_IT 4000 true (fst th) (snd th)) [(RFL, []); (REL, []); (RGL, []); (RZL, []); (RPA, []); (RCA, []); (RJA, []); (RCS, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]); (RRS, []); (RCP, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]); (RRP, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
