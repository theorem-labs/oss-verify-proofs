(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlan AsanTailAlist BR4HS_s48 BR4HS_s49 BR4SpinTail48 BR4SpinTail49.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition AL_r4 : list (nat * (acs * plan * shape)) := [(48%nat, (HS_s48, PFullTail r4spintail48, SNil)); (49%nat, (HS_s49, PFullTail r4spintail49, SNil))].
