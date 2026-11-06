(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition IMGSH_CERT_E : list (Z * list (Z * nat)) := [(189410, [(0, 12089%nat); (4, 12090%nat)]); (189420, [(0, 12109%nat); (4, 12110%nat)])].
