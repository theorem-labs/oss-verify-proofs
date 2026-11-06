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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWAB_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWAB_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Lemma slowab_cert : SP.pcheck SG SNG.sng_gfp (SG.gvc_list SLOWAG1_GV) SLOWAB SLOWAB_IT 3000 true ([[]; []; []; []; []; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 80)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 10)); (21%nat, add (mul 16 (EVar 21)) (ELit 11))] [] []]; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 76)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 9)); (21%nat, add (mul 16 (EVar 21)) (ELit 10))] [] []]; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 80)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 10)); (21%nat, add (mul 16 (EVar 21)) (ELit 11))] [] []]; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 76)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 9)); (21%nat, add (mul 16 (EVar 21)) (ELit 10))] [] []]; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 80)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 10)); (21%nat, add (mul 16 (EVar 21)) (ELit 11))] [] []]; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 76)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 9)); (21%nat, add (mul 16 (EVar 21)) (ELit 10))] [] []]; []; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 80)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 10)); (21%nat, add (mul 16 (EVar 21)) (ELit 11))] [] []]; [ST.XH [(18%nat, add (mul 128 (EVar 21)) (ELit 76)); (19%nat, ELit 4); (20%nat, add (mul 16 (EVar 21)) (ELit 9)); (21%nat, add (mul 16 (EVar 21)) (ELit 10))] [] []]; []]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
