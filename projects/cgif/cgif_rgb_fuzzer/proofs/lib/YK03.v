(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK11 YK0j YK0i YK02 YK0v.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition two_outcomes (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
: (list (list byte) * word) -> Prop :=
fun o => o = (bf, cf) \/ o = (bs, cs).


