(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlan AsanTailAlist K0HS_e50 K0HS_e51 K0ETail50 K0ETail51.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition AL_k0e : list (nat * (acs * plan * shape)) := [(50%nat, (HS_e50, PFullTail k0etail50, SExit 2)); (51%nat, (HS_e51, PFullTail k0etail51, SExit 2))].
