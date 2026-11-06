From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition c_space (b : byte) : bool := (bv_unsigned b =? 32) || ((9 <=? bv_unsigned b) && (bv_unsigned b <=? 13)).
Definition c_digit (b : byte) : bool := (48 <=? bv_unsigned b) && (bv_unsigned b <=? 57).

Fixpoint skip_space (s : list byte) : list byte :=
  match s with
  | b :: s' => if c_space b then skip_space s' else s
  | [] => []
  end.
