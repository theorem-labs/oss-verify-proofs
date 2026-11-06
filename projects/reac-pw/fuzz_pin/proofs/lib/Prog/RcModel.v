From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Fixpoint psum (bs : list byte) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => psum bs k' + bv_unsigned (nth k' bs (Z_to_bv 8 0))
  end.

Definition blocksum (bs : list byte) : Z := psum bs 32 mod 256.
