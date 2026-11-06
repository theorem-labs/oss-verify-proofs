(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PMA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PDCA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NDCA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWABCF_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma slowabcf_cert : SP.pcheck SG SNG.sng_gfp (fun _ => false) SLOWABCF SLOWABCF_IT 3000 false ([[]; []; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 4)); (19%nat, ELit 63); (20%nat, mul 16 (EVar 21)); (21%nat, add (mul 16 (EVar 21)) (ELit 9))] [] []]; [ST.XH [(16%nat, add (mul 128 (EVar 21)) (ELit 4)); (17%nat, mul 16 (EVar 21)); (18%nat, add (mul 128 (EVar 21)) (ELit 76)); (19%nat, sub (mul 2 (EVar 1)) (add (ELit 14) (mul 2 (EVar 23)))); (20%nat, add (EVar 16) (EAlu ALU_SRL (add (EVar 17) (EVar 26)) (ELit 3))); (21%nat, sub (add (EVar 17) (EVar 26)) (mul 8 (EAlu ALU_SRL (add (EVar 17) (EVar 26)) (ELit 3)))); (22%nat, add (EVar 25) (mul (-1) (EVar 26))); (23%nat, sub (EAlu ALU_SRL (add (add (EVar 17) (EVar 25)) (ELit 55)) (ELit 3)) (EAlu ALU_SRL (add (EVar 17) (EVar 26)) (ELit 3))); (24%nat, ELit 1); (25%nat, add (EVar 16) (EAlu ALU_SRL (add (add (EVar 17) (EVar 25)) (ELit 1)) (ELit 3))); (26%nat, sub (add (add (EVar 17) (EVar 25)) (ELit 1)) (mul 8 (EAlu ALU_SRL (add (add (EVar 17) (EVar 25)) (ELit 1)) (ELit 3)))); (27%nat, add (add (EVar 24) (mul (-1) (EVar 25))) (ELit (-1))); (28%nat, sub (EAlu ALU_SRL (add (add (EVar 17) (EVar 24)) (ELit 55)) (ELit 3)) (EAlu ALU_SRL (add (add (EVar 17) (EVar 25)) (ELit 1)) (ELit 3)))] [] []]; [ST.XH [(16%nat, add (mul 128 (EVar 21)) (ELit 4)); (17%nat, mul 16 (EVar 21))] [] []; ST.XH [(16%nat, add (mul 128 (EVar 21)) (ELit 4)); (17%nat, mul 16 (EVar 21))] [] []]; []; []]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
