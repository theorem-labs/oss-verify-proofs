From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse.
Import ListNotations.
Open Scope Z_scope.

Definition cl_eq6 (xs ys : list byte) : bool :=
  forallb (fun i => bv_unsigned (nth i xs cp_z) =? bv_unsigned (nth i ys cp_z)) (seq 0 6).

Definition cl_oui (fr : list byte) : bool :=
  (cp_v fr 6 =? 0x00) && (cp_v fr 7 =? 0x40) && (cp_v fr 8 =? 0xab).

Definition cl_bsum (fr : list byte) : Z := blocksum (skipn 18 fr).

Definition cl_join (fr : list byte) : bool :=
  (cp_v fr 22 =? 0) &&
  (((cp_v fr 34 =? 0x01) && (cp_v fr 35 =? 0x00)) || ((cp_v fr 34 =? 0x03) && (cp_v fr 35 =? 0x02))).

Definition classify (n : Z) (fr us : list byte) : option Z :=
  let k := fst (ctrlparse n fr) in
  if k =? 0 then None
  else if negb (cl_oui fr) then None
  else if cl_eq6 (skipn 6 fr) us then None
  else if negb (k =? 1) && negb (cl_bsum fr =? 0) then None
  else if k =? 5 then (if cl_join fr then Some 1 else None)
  else if cp_bcast fr then (if k =? 1 then Some 0 else None)
  else if negb (cl_eq6 fr us) then None
  else if k =? 7 then Some 3
  else if (k =? 2) && (cp_v fr 19 =? 3) then Some 4
  else if k =? 9 then Some 5
  else Some 2.

Definition cl_r (c : option Z) : Z := match c with Some _ => 0 | None => -1 end.
