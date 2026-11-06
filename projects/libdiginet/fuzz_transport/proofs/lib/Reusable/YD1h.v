(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1h.v, with its module paths changed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/YD1h.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YG0f.
Open Scope Z_scope.
Definition sliverb (sp : word) (a : word) : bool :=
((SHADOW_OFF + run_ceil (bv_unsigned sp) / 8 <=? bv_unsigned a) && (bv_unsigned a <? SHADOW_OFF + (bv_unsigned sp - 8388608) / 8))%bool.
