(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Ltac lf_concl T := lazymatch T with ?A -> ?B => lf_concl B | _ => T end.
Ltac pfeed_at P t T gred tac :=
  let C := lf_concl T in
  assert (P : C) by (apply t; gred; first [ tac | lazymatch goal with |- ?A => fail 1 "pfeed: cannot prove premise" A end ]).
Ltac pfeed P t tac :=
  let T := type of t in
  let T' := eval cbn beta iota in T in
  pfeed_at P t T' ltac:(cbn beta iota) tac.
