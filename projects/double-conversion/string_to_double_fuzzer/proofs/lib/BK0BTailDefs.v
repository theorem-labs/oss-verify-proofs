(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth AsanTailAlist BK0B_HS_n911 BK0B_null911 BK0B_null911_js BK0B_HS_n913 BK0B_null913 BK0B_null913_js.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition nulltail911_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition nulltail913_shape : shape := (SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0))).
Definition AL_k0b : list (nat * (acs * plan * shape)) := [(911%nat, (HS_n911, PFullTail (nulltail911 JSraw_nulltail911_10), nulltail911_shape)); (913%nat, (HS_n913, PFullTail (nulltail913 JSraw_nulltail913_10), nulltail913_shape))].
Definition TT_k0b : nat -> option (acs * plan * shape) := tt_of_alist AL_k0b.
