(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import LADB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import LMBB_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma lmbb_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) LMBB LMBB_IT 3000 false ([[]; [ST.XH [(19%nat, add (mul 256 (EVar 18)) (ELit 4)); (20%nat, EVar 16); (21%nat, EVar 20); (22%nat, EVar 17); (23%nat, mul 32 (EVar 18))] [] []]; []; []; []; [ST.XH [(19%nat, add (mul 256 (EVar 18)) (ELit 76)); (20%nat, add (mul 256 (EVar 18)) (ELit 4)); (21%nat, EVar 24); (22%nat, mul 32 (EVar 18)); (23%nat, add (mul 32 (EVar 18)) (ELit 9))] [] []]; []; []; [ST.XH [(16%nat, EVar 16); (17%nat, add (mul 256 (EVar 18)) (ELit 76)); (18%nat, EVar 25); (19%nat, EVar 22); (20%nat, EVar 23)] [] []]; []; []; []]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
