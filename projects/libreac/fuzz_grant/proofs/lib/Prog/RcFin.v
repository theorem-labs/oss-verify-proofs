From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel.
Import ListNotations.
Open Scope Z_scope.

Definition ubat (row : list byte) (i : nat) : Z := bv_unsigned (nth i row (Z_to_bv 8 0)).

Definition stamp32 (bs : list byte) : list byte :=
  upd_bytes bs 31 [Z_to_bv 8 ((- psum bs 31) mod 256)].

Definition rsum (bs : list byte) (o k : Z) : Z := psum (skipn (Z.to_nat o) bs) (Z.to_nat k).

Definition rstamp (bs : list byte) (o n : Z) : list byte :=
  upd_bytes bs (Z.to_nat (o + n - 1)) [Z_to_bv 8 ((- rsum bs o (n - 1)) mod 128)].

Definition fin (c o n : Z) (bs : list byte) : list byte :=
  if c =? 2 then stamp32 (rstamp bs o n) else if c =? 1 then stamp32 bs else bs.

Definition fin_w (c o n p : Z) : list (Z * Z) :=
  if c =? 2 then [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)]
  else if c =? 1 then [(p + 49, p + 50)] else [].

Definition closes (c o n : Z) (bs : list byte) : Prop :=
  blocksum bs = 0 /\ (c = 2 -> rsum bs o n mod 128 = 0 /\ ubat bs (Z.to_nat (o + n - 1)) < 128).