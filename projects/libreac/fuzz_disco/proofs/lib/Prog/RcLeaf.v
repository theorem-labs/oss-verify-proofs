From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel.
Import ListNotations.
Open Scope Z_scope.

Definition bt (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition rsum (rec : list byte) : Z := psum rec 6 mod 128.

Definition hv (b0 b1 : byte) (rec : list byte) : bool :=
  (bv_unsigned b0 =? 4) && (bv_unsigned b1 =? 3) && (rsum rec =? 0).

Definition decl (bs : list byte) : bool :=
  (bt bs 0 =? 1) && (bt bs 1 =? 3) && ((bt bs 4 =? 128) || (bt bs 4 =? 130) || (bt bs 4 =? 132)).

Definition is_in (c : Z) : bool := (c =? 0) || (c =? 2).

Definition is_out (c : Z) : bool := c =? 1.

Fixpoint cnt (f : Z -> bool) (bs : list byte) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => cnt f bs k' + (if f (bt bs (8 + k')) then 1 else 0)
  end.

Definition n_in (bs : list byte) : Z := cnt is_in bs 12.

Definition n_out (bs : list byte) : Z := cnt is_out bs 12.

Definition ports_ok (p q : Z) (bs : list byte) : bool := negb (p =? 0) && negb (q =? 0) && decl bs.
