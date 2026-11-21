(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Ox/F80_003.v for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
Require OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Ox.F80_002.
From Stdlib Require Import PArray Uint63.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 80 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
