(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlan AsanTailAlist K1HS_s344 K1HS_s345 K1SpinTail344 K1SpinTail345.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition AL_k1 : list (nat * (acs * plan * shape)) := [(344%nat, (HS_s344, PFullTail k1spintail344, SNil)); (345%nat, (HS_s345, PFullTail k1spintail345, SNil))].
