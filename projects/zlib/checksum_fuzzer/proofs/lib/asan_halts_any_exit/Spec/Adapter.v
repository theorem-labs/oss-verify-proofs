(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Adapter.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable fuzz_one : list Z -> M St Z.
Variable emit : Z -> M St unit.

Definition bad_upd (b rc : Z) : Z := if (rc =? 0) || (rc =? -1) then b else 1.

Lemma bad_upd_01 : forall b rc, 0 <= b <= 1 -> 0 <= bad_upd b rc <= 1.
Proof. intros b rc Hb. unfold bad_upd. destruct ((rc =? 0) || (rc =? -1)); lia. Qed.

Lemma bad_upd_0 : forall b, bad_upd b 0 = b.
Proof. intros b. reflexivity. Qed.

Fixpoint run_calls (n : nat) (payload : list Z) (b : Z) : M St Z :=
  match n with
  | O => mret b
  | S n' => rc' <- fuzz_one payload ;; emit rc' ;;; run_calls n' payload (bad_upd b rc')
  end.

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
  let calls := 1 + Z.land cfg 3 in
  let payload_len := zlength payload in
  a <- (if payload_len =? 0 then mret (Some None)
        else r <- drv_malloc payload_len ;;
             mret (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => mret 2
  | Some owned =>
      b <- run_calls (Z.to_nat calls) payload 0 ;;
      (match owned with Some p => drv_free p | None => mret tt end) ;;;
      mret (if b =? 0 then 0 else 78)
  end.

Definition target_alloc_init (bitmap : Z) : M St unit := mret tt.
Definition target_alloc_count : M St Z := mret 0.

End Adapter.
