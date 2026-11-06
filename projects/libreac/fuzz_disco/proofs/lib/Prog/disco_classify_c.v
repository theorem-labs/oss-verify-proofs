From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLeaf RcParse CtrlParsed.
Import ListNotations.
Open Scope Z_scope.

Definition gn (G : list byte) : Z := s32 (fu G 256 4).
Definition gmac (G : list byte) (i : nat) : list byte := fld G (32 * i) 6.

Definition gate_ok (G : list byte) : Prop :=
  length G = 264%nat /\ 0 <= gn G <= 8 /\
  forall i j : nat, (i < j)%nat -> Z.of_nat j < gn G -> bytes_eqb (gmac G i) (gmac G j) = false.

Definition sighting_ok (S : list byte) : Prop :=
  length S = 24%nat /\ 0 <= s32 (fu S 8 4) <= 2 /\
  (fb S 12 = 0 \/ (fb S 12 = 1 /\ fb S 13 <= 40 /\ fb S 14 <= 40)).

Definition lock_ok (L : list byte) : Prop :=
  length L = 12%nat /\ (fu L 8 4 = 0 \/ fu L 8 4 = 1).

Definition dkind (F : list byte) (len : Z) : Z := fst (ctrlparse len F).
Definition src (F : list byte) : list byte := fld F 6 6.
Definition tag (F : list byte) : Z := 256 * fb F 34 + fb F 35.
Definition fsum (F : list byte) : Z := blocksum (fld F 18 32).

Definition role (F : list byte) (k : Z) : Z :=
  if k =? 1 then (if cp_bcast F then 0 else 1)
  else if (k =? 2) || (k =? 3) || (k =? 4) || (k =? 6) then 2
  else if (k =? 7) || (k =? 9) then 1
  else if k =? 5 then
    (if (fb F 22 =? 0) && ((tag F =? 256) || (tag F =? 770) || (tag F =? 1280)) then 1 else 2)
  else 0.

Definition slots (F : list byte) : Z :=
  if (fb F 16 =? 207) && (fb F 17 =? 234) && (fb F 22 =? 1) && (fb F 23 =? 3) && (fb F 24 =? 13)
     && (fb F 25 =? 1) && (fb F 26 =? 4)
  then fb F 33 else 0.

Definition sdecl (F : list byte) : option (Z * Z) :=
  let P := fld F 18 20 in
  if decl P && (4 * n_in P <=? 40) && (4 * n_out P <=? 40) then Some (4 * n_in P, 4 * n_out P) else None.

Definition geo (len : Z) : Z :=
  if (52 <=? len) && ((len - 52) mod 36 =? 0) then ((len - 52) / 36) mod 2 ^ 32 else 0.

Definition sight (F : list byte) (len : Z) : list byte :=
  src F ++ [zb 0; zb 0] ++ le4 (Z_to_bv 64 (role F (dkind F len)))
  ++ (match sdecl F with Some (i, o) => [zb 1; zb i; zb o] | None => [zb 0; zb 0; zb 0] end)
  ++ [zb 0; zb (slots F); zb 0; zb 0; zb 0] ++ le4 (Z_to_bv 64 (geo len)).

Definition lm (L : list byte) : list byte := fld L 0 6.
Definition lv (L : list byte) : Z := fu L 8 4.
Definition latch (F L : list byte) : list byte := src F ++ fld L 6 2 ++ le4 (Z_to_bv 64 1).

Definition classify_model (F : list byte) (len : Z) (U : list byte) (L : option (list byte))
    : Z * option (list byte) * option (list byte) :=
  let k := dkind F len in
  if k =? 0 then (-1, None, L)
  else if bytes_eqb (src F) U then (-1, None, L)
  else if negb (k =? 1) && negb (fsum F =? 0) then (-1, None, L)
  else match L with
       | None => (0, Some (sight F len), None)
       | Some Lb =>
           if (k =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F)) then (-1, None, L)
           else (0, Some (sight F len), Some (if negb (k =? 1) && (lv Lb =? 0) then latch F Lb else Lb))
       end.

Definition cm_ret (F : list byte) (len : Z) (U : list byte) (L : option (list byte)) : Z :=
  fst (fst (classify_model F len U L)).
Definition cm_out (F : list byte) (len : Z) (U : list byte) (L : option (list byte)) (O : list byte) : list byte :=
  match snd (fst (classify_model F len U L)) with Some s => s | None => O end.
Definition cm_lock (F : list byte) (len : Z) (U : list byte) (L : option (list byte)) : option (list byte) :=
  snd (classify_model F len U L).
