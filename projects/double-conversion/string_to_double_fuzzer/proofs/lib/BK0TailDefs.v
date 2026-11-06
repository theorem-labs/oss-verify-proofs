(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth AsanTailAlist BK0HS_n65 BK0NullTail65 BK0JS_nulltail65 BK0HS_n67 BK0NullTail67 BK0JS_nulltail67 BK0HS_n85 BK0NullTail85 BK0JS_nulltail85 BK0HS_n87 BK0NullTail87 BK0JS_nulltail87 BK0HS_s44 BK0SpinTail44 BK0HS_s45 BK0SpinTail45.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition nulltail65_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition nulltail67_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition nulltail85_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition nulltail87_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition spintail44_shape : shape := SNil.
Definition spintail45_shape : shape := SNil.
Definition AL_k0 : list (nat * (acs * plan * shape)) := [(44%nat, (HS_s44, PFullTail spintail44, spintail44_shape)); (45%nat, (HS_s45, PFullTail spintail45, spintail45_shape)); (65%nat, (HS_n65, PFullTail (nulltail65 JSraw_nulltail65_10), nulltail65_shape)); (67%nat, (HS_n67, PFullTail (nulltail67 JSraw_nulltail67_10), nulltail67_shape)); (85%nat, (HS_n85, PFullTail (nulltail85 JSraw_nulltail85_10), nulltail85_shape)); (87%nat, (HS_n87, PFullTail (nulltail87 JSraw_nulltail87_10), nulltail87_shape))].
Definition TT_k0 : nat -> option (acs * plan * shape) := tt_of_alist AL_k0.
