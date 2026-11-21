(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt PState Prog
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_PCaps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).


Definition bc (n : Z) : Z := if n =? 24 then 1 else n / 4 - 1.
Definition BC (Y : list (bptr * Z)) : Z := zsum (map (fun b => bc (snd b)) Y).
Definition YW (Y : list (bptr * Z)) : Prop := Forall (fun b => snd b = 24 \/ exists l, 0 <= l /\ snd b = 4 * (l + 1)) Y.
Definition N24 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 24) Y.
Definition N4 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 4) Y.

Lemma LRX_cons p n X c : LRX ((p, n) :: X) c = (if negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c) then 1 else 0) + LRX X c.
Proof. unfold LRX. rewrite zcount_cons. reflexivity. Qed.
Lemma n63X_cons p n X : n63X ((p, n) :: X) = (if MMAP_THRESHOLD <=? n then 1 else 0) + n63X X.
Proof. unfold n63X. rewrite zcount_cons. reflexivity. Qed.






