(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YD1h.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YD1h.v at origin/ossv/recipes 4b6f0df50aa7 (fuzz_knock's released ASan tree); module paths changed to libdiginet/fuzz_codec. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05 YG0f.
Open Scope Z_scope.
Definition sliverb (sp : word) (a : word) : bool :=
((SHADOW_OFF + run_ceil (bv_unsigned sp) / 8 <=? bv_unsigned a) && (bv_unsigned a <? SHADOW_OFF + (bv_unsigned sp - 8388608) / 8))%bool.
