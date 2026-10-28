From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Ltac seqs_land_close :=
  match goal with
  | H : Z.land ?x ?c <> 0 |- _ =>
      first [ change c with (Z.ones 1) in H | change c with (Z.ones 2) in H | change c with (Z.ones 3) in H
            | change c with (Z.ones 4) in H ];
      rewrite Z.land_ones in H by lia;
      match type of H with context [2 ^ ?n] => let v := eval compute in (2 ^ n) in change (2 ^ n) with v in H end;
      exfalso; apply H; clear H; lia
  end.
