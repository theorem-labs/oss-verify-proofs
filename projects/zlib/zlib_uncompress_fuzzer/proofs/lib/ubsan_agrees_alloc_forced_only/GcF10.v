(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import PArray Uint63.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.GcF09.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 90 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
