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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import SegSplitH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_c1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_c2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_c3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2N_c4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Definition A2N_hints : list (list ST.xhint) := [[ST.XH [(19%nat, EVar 36); (20%nat, EVar 39); (21%nat, EVar 42); (22%nat, EVar 43); (23%nat, EAlu ALU_ADD (EVar 18) (EVar 40)); (24%nat, EVar 41); (25%nat, EVar 44); (26%nat, EVar 45)] [] []]; [ST.XH [(18%nat, EAlu ALU_ADD (EVar 36) (EVar 46)); (19%nat, EAlu ALU_SUB (EAlu ALU_SUB (EVar 37) (EVar 38)) (EVar 46)); (20%nat, EVar 42); (21%nat, EVar 43); (22%nat, EVar 38)] [] []]; []; [ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.XH [(52%nat, ELit 0)] [] []; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.XH [(52%nat, ELit 0)] [] []]; [ST.XH [(52%nat, EAlu ALU_ADD (EVar 52) (ELit 1))] [] []]; []; []; []; []; []; []; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]; []; [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]; []].
Lemma a2n_cert : SP.pcheckH SG gfp2 (wvc_okL SG 1048512 0x23640) A2N A2N_IT 4000 true A2N_hints = true.
Proof.
  apply (pcheckH_of_chunksH SG gfp2 (wvc_okL SG 1048512 0x23640) A2N A2N_IT 4000 true [[(T0, [ST.XH [(19%nat, EVar 36); (20%nat, EVar 39); (21%nat, EVar 42); (22%nat, EVar 43); (23%nat, EAlu ALU_ADD (EVar 18) (EVar 40)); (24%nat, EVar 41); (25%nat, EVar 44); (26%nat, EVar 45)] [] []]); (TR1, [ST.XH [(18%nat, EAlu ALU_ADD (EVar 36) (EVar 46)); (19%nat, EAlu ALU_SUB (EAlu ALU_SUB (EVar 37) (EVar 38)) (EVar 46)); (20%nat, EVar 42); (21%nat, EVar 43); (22%nat, EVar 38)] [] []]); (TR2, [])]; [(RIL, [ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.XH [(52%nat, ELit 0)] [] []; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.xh0; ST.XH [(52%nat, ELit 0)] [] []])]; [(RSL, [ST.XH [(52%nat, EAlu ALU_ADD (EVar 52) (ELit 1))] [] []])]; [(RFL, []); (REL, []); (RGL, []); (RZL, []); (RPA, []); (RCA, []); (RJA, []); (RCS, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]); (RRS, []); (RCP, [ST.XH [(1%nat, EAlu ALU_SUB (EAlu ALU_ADD (EVar 1) (ELit (-24))) (EVar 29)); (16%nat, EVar 36); (17%nat, ELit 0); (18%nat, EAlu ALU_SUB (EVar 19) (EVar 35)); (20%nat, EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (-14))) (EMd M_MUL (ELit 2) (EVar 29))); (21%nat, EVar 37)] [] []]); (RRP, [])]]).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact a2n_c1|]. apply Forall_cons; [exact a2n_c2|]. apply Forall_cons; [exact a2n_c3|]. apply Forall_cons; [exact a2n_c4|]. apply Forall_nil.
Qed.
