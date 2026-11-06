(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetRun.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable emit : Z -> M St unit.
Variable fuzz : list Z -> M St Z.

Definition target_alloc_init (bitmap : Z) : M St unit := mret tt.
Definition target_alloc_count : M St Z := mret 0.

Fixpoint run_calls (n : nat) (payload : list Z) (rc : Z) : M St Z :=
match n with
| O => mret rc
| S n' => rc' <- fuzz payload ;; emit rc' ;;; run_calls n' payload rc'
end.

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
let calls := 1 + Z.land cfg 3 in
let payload_len := zlength payload in
owned <- (if payload_len =? 0 then mret (Some None)
else p <- drv_malloc payload_len ;;
mret (match p with Some q => Some (Some q) | None => None end)) ;;
match owned with
| None => mret 2
| Some owned =>
rc <- run_calls (Z.to_nat calls) payload 0 ;;
(match owned with Some q => drv_free q | None => mret tt end) ;;;
mret (if rc =? 0 then 0 else 1)
end.

End TargetRun.
