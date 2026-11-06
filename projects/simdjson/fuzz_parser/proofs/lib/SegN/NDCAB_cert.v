(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import P5A_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NDCAB_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma ndcab_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) NDCAB NDCAB_IT 3000 false ([[]; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 5)); (19%nat, ELit 62); (20%nat, mul 16 (EVar 21))] [] []]; [ST.XH [(16%nat, add (mul 128 (EVar 21)) (ELit 4)); (17%nat, mul 16 (EVar 21))] [] []]; []; []; []; [ST.XH [(19%nat, add (add (mul 128 (EVar 21)) (ELit 4)) (EVar 26)); (20%nat, add (mul 128 (EVar 21)) (ELit 4)); (21%nat, EVar 25); (22%nat, mul 16 (EVar 21))] [] []]; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 4)); (19%nat, EVar 26); (20%nat, mul 16 (EVar 21))] [] []]; []; []; []; [ST.XH [(19%nat, add (EVar 16) (EVar 26)); (20%nat, EVar 16); (21%nat, EVar 24); (22%nat, EVar 17)] [] []]; [ST.XH [(18%nat, EVar 16); (19%nat, EVar 26); (20%nat, EVar 17)] [] []]; []; []; []; []]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
