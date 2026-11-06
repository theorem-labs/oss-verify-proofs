From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel.
Import ListNotations.
Open Scope Z_scope.

Definition u32 (T : list byte) (k : Z) : Z :=
  tb T k + 256 * tb T (k + 1) + 65536 * tb T (k + 2) + 16777216 * tb T (k + 3).

Definition s32 (T : list byte) (k : Z) : Z := if u32 T k <? 2147483648 then u32 T k else u32 T k - 4294967296.

Definition setb (T : list byte) (k v : Z) : list byte := upd_bytes T (Z.to_nat k) (le1 (Z_to_bv 64 v)).

Definition set4 (T : list byte) (k v : Z) : list byte := upd_bytes T (Z.to_nat k) (le4 (Z_to_bv 64 v)).

Definition nres : Type := (Z * (Z * Z * Z) * list byte)%type.

Definition silent (T : list byte) : nres := (0, (0, 0, 0), T).

Fixpoint first_dirty_from (T : list byte) (i : Z) (n : nat) : option Z :=
  match n with
  | O => None
  | S n' => if tb T (288 + i) =? 0 then first_dirty_from T (i + 1) n' else Some i
  end.

Definition edge_res (T : list byte) (i : Z) : nres :=
  (1, (i / 3, i mod 3, tb T i), set4 (setb T (288 + i) 0) 456 0).

Definition resweep (T : list byte) : nres :=
  if u32 T 452 =? 0 then silent T
  else if tb T 450 =? 0 then silent T
  else
    let T1 := set4 T 456 (u32 T 456 + 1) in
    if u32 T 452 <=? (u32 T 456 + 1) mod 4294967296
    then silent (set4 (set4 (setb (setb (set4 (setb T1 448 1) 456 0) 436 (tb T 449)) 437 (tb T 450)) 440 0) 444 0)
    else silent T1.

Definition carried (T : list byte) (bs o j : Z) : bool :=
  (o =? 0) || ((bs + j / 3 <=? 47) && negb (tb T (144 + 3 * (bs + j / 3) + j mod 3) =? 0)).

Definition emit_res (T1 : list byte) (t c p j total : Z) : nres :=
  let T2 := if j + 1 <? total then set4 T1 444 11 else setb T1 437 0 in
  (1, (c mod 256, p, eff T1 t (c mod 256) p), set4 T2 456 0).

Fixpoint walk (T : list byte) (t bs o total j : Z) (n : nat) : nres :=
  match n with
  | O => silent T
  | S n' =>
      let T1 := set4 T 440 (j + 1) in
      if carried T1 bs o j then emit_res T1 t (bs + j / 3) (j mod 3) j total
      else if j + 1 =? total then resweep (setb T1 437 0)
      else walk T1 t bs o total (j + 1) n'
  end.

Definition after_scan (T : list byte) (t : Z) : nres :=
  if tb T 437 =? 0 then resweep T
  else if 0 <? s32 T 444 then silent (set4 T 444 (s32 T 444 - 1))
  else if 3 * tb T 437 <=? s32 T 440 then resweep (setb T 437 0)
  else walk T t (tb T 436) (tb T 448) (3 * tb T 437) (s32 T 440) (Z.to_nat (3 * tb T 437 - s32 T 440)).

Definition next_model (T : list byte) (t : Z) : nres :=
  if (u32 T 432 =? 0) && (tb T 437 =? 0) then silent T
  else match first_dirty_from T 0 144 with
       | Some i => edge_res T i
       | None => after_scan T t
       end.
