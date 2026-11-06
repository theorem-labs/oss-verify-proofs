(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg's asan-ubsan tree lib/B: module paths changed, no other change. *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Ox/F80_002.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Ox.F80_001.
From Stdlib Require Import PArray Uint63.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 80 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
