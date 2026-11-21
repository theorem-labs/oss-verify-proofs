(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad CMonad Adapter.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section AdapterC.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable fuzz_one : list Z -> MC St Z.
Variable emit : Z -> M St unit.

Definition bad_upd (b rc : Z) : Z := if (rc =? 0) || (rc =? -1) then b else 1.

Lemma bad_upd_01 : forall b rc, 0 <= b <= 1 -> 0 <= bad_upd b rc <= 1.
Proof. intros b rc Hb. unfold bad_upd. destruct ((rc =? 0) || (rc =? -1)); lia. Qed.


Fixpoint run_calls (n : nat) (payload : list Z) (b : Z) : MC St Z :=
  match n with
  | O => cmret b
  | S n' => cmbind (fuzz_one payload) (fun rc' => cmbind (clift (emit rc')) (fun _ => run_calls n' payload (bad_upd b rc')))
  end.

Definition payload_copy (payload : list Z) : M St (option (option ptr)) :=
  let payload_len := zlength payload in
  if payload_len =? 0 then mret (Some None)
  else r <- drv_malloc payload_len ;;
       mret (match r with None => None | Some p => Some (Some p) end).

Definition target_run (cfg : Z) (payload : list Z) : MC St Z :=
  let calls := 1 + Z.land cfg 3 in
  cmbind (clift (payload_copy payload))
         (fun a => match a with
                   | None => cmret 2
                   | Some owned =>
                       cmbind (run_calls (Z.to_nat calls) payload 0)
                              (fun b => cmbind (clift (match owned with Some p => drv_free p | None => mret tt end))
                                               (fun _ => cmret (if b =? 0 then 0 else 78)))
                   end).

End AdapterC.
