From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Mem.
Import ListNotations.
Open Scope Z_scope.

Definition zb (z : Z) : byte := Z_to_bv 8 z.
Definition fb (B : list byte) (k : nat) : Z := bv_unsigned (nth k B (zb 0)).
Definition fld (B : list byte) (k n : nat) : list byte := firstn n (skipn k B).
Definition fu (B : list byte) (k n : nat) : Z := bytes_le_to_Z (fld B k n).
Definition s32 (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32.
Definition bytes_eqb (a b : list byte) : bool :=
  if list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b) then true else false.
