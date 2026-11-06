(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRCB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PMBN_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma pmbn_c1 : forallb (fun th => SP.tm_check SG SNU.snu_gfp (NRCB.nrcb_ok SG) PMBN PMBN_IT 3000 true (fst th) (snd th)) [(T0, []); (ZS8, []); (ZS1, []); (CH, []); (DL, []); (JC, []); (JY, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma pmbn_c2 : forallb (fun th => SP.tm_check SG SNU.snu_gfp (NRCB.nrcb_ok SG) PMBN PMBN_IT 3000 true (fst th) (snd th)) [(SMI, []); (SMIX, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
