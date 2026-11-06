(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YD1h.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YG0f.
Open Scope Z_scope.
Definition sliverb (sp : word) (a : word) : bool :=
((SHADOW_OFF + run_ceil (bv_unsigned sp) / 8 <=? bv_unsigned a) && (bv_unsigned a <? SHADOW_OFF + (bv_unsigned sp - 8388608) / 8))%bool.
