(* Port-from: theorem-labs/oss-verify-proofs@8c835db8a5a9 proofs/omx-clap-core/fuzz_state/lib/A/Ox/F80_001.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
From Stdlib Require Import PArray Uint63.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 80 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
