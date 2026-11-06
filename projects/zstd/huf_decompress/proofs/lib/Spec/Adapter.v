(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Adapter.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable fuzz_one : list Z -> M St Z.            (* [comment removed for export] *)
Variable emit : Z -> M St unit.                  (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint run_calls (n : nat) (payload : list Z) (rc : Z) : M St Z :=
  match n with
  | O => mret rc
  | S n' => rc' <- fuzz_one payload ;; emit rc' ;;; run_calls n' payload rc'
  end.

(* [comment removed for export] *)
Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
  let calls := 1 + Z.land cfg 3 in
  let payload_len := zlength payload in
  (* [comment removed for export] *)
  a <- (if payload_len =? 0 then mret (Some None)                        (* [comment removed for export] *)
        else r <- drv_malloc payload_len ;;
             mret (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => mret 2                                                        (* [comment removed for export] *)
  | Some owned =>
      rc <- run_calls (Z.to_nat calls) payload 0 ;;
      (match owned with Some p => drv_free p | None => mret tt end) ;;;   (* [comment removed for export] *)
      mret (if rc =? 0 then 0 else 1)
  end.

Definition target_alloc_init (bitmap : Z) : M St unit := mret tt.
Definition target_alloc_count : M St Z := mret 0.

End Adapter.
