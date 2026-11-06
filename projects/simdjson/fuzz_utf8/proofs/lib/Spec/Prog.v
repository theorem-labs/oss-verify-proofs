(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.
