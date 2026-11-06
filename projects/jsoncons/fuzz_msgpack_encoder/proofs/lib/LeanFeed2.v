(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
Notation "'LF2CBN(' t ')'" := (t : ltac:(let T := type of t in let T' := eval cbn beta iota in T in exact T')) (at level 0, only parsing).
