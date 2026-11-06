(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Corelib Require Import PrimInt63 PrimArray.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PrimArray.length (PrimArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 72 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
