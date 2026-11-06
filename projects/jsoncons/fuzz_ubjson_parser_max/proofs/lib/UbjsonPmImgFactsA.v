(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma tgt_ubjson_pm_asan_brk_satisfiable :
image_brk_satisfiable Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
