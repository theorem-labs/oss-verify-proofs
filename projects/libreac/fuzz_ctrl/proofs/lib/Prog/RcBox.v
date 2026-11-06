From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition name_ok (nb : list byte) : Prop :=
  (1 <= length nb <= 16)%nat /\
  (forall i, (S i < length nb)%nat -> bv_unsigned (nth i nb (Z_to_bv 8 0)) <> 0) /\
  (length nb = 16%nat \/ bv_unsigned (nth (pred (length nb)) nb (Z_to_bv 8 0)) = 0).

Fixpoint takenz (bs : list byte) : list byte :=
  match bs with
  | [] => []
  | b :: r => if bv_unsigned b =? 0 then [] else b :: takenz r
  end.

Definition nmf (nb : list byte) : list byte :=
  takenz nb ++ repeat (Z_to_bv 8 0) (16 - length (takenz nb)).

Definition dt1_hdr (n : nat) (a : Z) : list byte := dt1_bytes 3 (Z.of_nat n + 13) a.

Definition dt1_ick (n : nat) (a : Z) (D : list byte) : Z :=
  (- psum (skipn 16 (dt1_hdr n a) ++ D) (n + 4)) mod 128.

Definition dt1_body (n : nat) (a : Z) (D ob : list byte) : list byte :=
  dt1_hdr n a ++ D ++ [Z_to_bv 8 (dt1_ick n a D); Z_to_bv 8 247] ++ firstn (9 - n) (skipn (22 + n) ob).

Definition dt1_out (n : nat) (a : Z) (D ob : list byte) : list byte :=
  dt1_body n a D ob ++ [Z_to_bv 8 ((- psum (dt1_body n a D ob) 31) mod 256)].
