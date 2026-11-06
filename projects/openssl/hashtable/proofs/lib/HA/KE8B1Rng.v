(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Definition ke8b1_ranges : list (Z * nat) := [(1756172, 1%nat); (1768252, 29%nat); (1768428, 9%nat); (1768584, 7%nat); (1843088, 1%nat); (1846480, 77%nat); (1847008, 1%nat); (1847340, 1%nat); (1847400, 11%nat); (1847656, 10%nat); (1856844, 1%nat); (1879692, 13%nat); ( 2044532, 9%nat); (2044624, 43%nat); (2045136, 21%nat); (2045276, 7%nat); (2045456, 9%nat); (2045616, 1%nat); (5360972, 22%nat); (5361092, 19%nat); (5362108, 3%nat); (5362160, 1%nat); (5384244, 1%nat); (5407460, 1%nat); ( 5410988, 3%nat); (5411492, 1%nat); (5411636, 3%nat); (5411752, 10%nat); (5436652, 21%nat); (5436940, 13%nat)].
