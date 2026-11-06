(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_mc.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma a1g_cert : SP.pcheck SG s1_gfp (SG.gvc_list A1G_GV) A1G A1G_IT 4000 true ([[ST.XH [(16%nat, EMd M_MUL (ELit 16) (EVar 1)); (17%nat, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (0x7fff8000 - 1024)))] [] []]]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
