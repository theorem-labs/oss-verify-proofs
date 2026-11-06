(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import ATac.

Ltac clear_other_neg Hi :=
  repeat match goal with H : ~ _ |- _ => tryif constr_eq H Hi then fail else clear H end.
Ltac outside_from_hyps :=
  match goal with
  | Hi : ~ (_ <= ?xo < _)%Z |- ~ (_ <= ?xo2 < _)%Z =>
      clear_other_neg Hi; let R := fresh "R" in intros R; apply Hi; split; lia
  end.
Ltac sub_fp_solve ::=
  unfold sub_fp; cbn [outside]; let xo := fresh "xo" in let Ho := fresh "Ho" in intros xo Ho; destruct_ands Ho;
  repeat split; first [ exact I | assumption | outside_from_hyps | lia ].
