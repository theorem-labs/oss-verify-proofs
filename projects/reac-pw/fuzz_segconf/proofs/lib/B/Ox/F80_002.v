(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Ox/F80_002.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Ox/F80_002.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Ox/F80_002.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Ox.F80_001.
From Stdlib Require Import PArray Uint63.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 80 0 = 4194303%uint63.
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
