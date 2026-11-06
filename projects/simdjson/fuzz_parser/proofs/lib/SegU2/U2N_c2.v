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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegDig.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PFFCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2N_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma u2n_c2 : forallb (fun th => SP.tm_check SG (SDG.gfpx gfp2) (SVX.gvc_enrich SVX.bc_enrich (SDG.gsplit SG (wvc_ok SG 1048512 0x13768))) U2N U2N_IT 4000 true (fst th) (snd th)) [(RSL, []); (RFL, []); (REL, []); (RNX, [])] = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
