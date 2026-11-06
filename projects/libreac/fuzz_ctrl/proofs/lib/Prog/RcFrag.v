From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition bat (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

Definition bsl (bs : list byte) (k n : Z) : list byte := firstn (Z.to_nat n) (skipn (Z.to_nat k) bs).

Definition fg_n (g : list byte) : Z := bat g 26.

Definition fg_fr (len : Z) (g : list byte) : bool :=
  (50 <=? len) && (bat g 16 =? 205) && (bat g 17 =? 234) && (bat g 18 =? 4) &&
  ((bat g 19 =? 1) || (bat g 19 =? 2)) && (bat g 22 =? 0) && (bat g 23 =? 2) && (bat g 24 =? 0) &&
  (bat g 25 =? 254) && (1 <=? fg_n g) && (fg_n g <=? 22) && (blocksum (skipn 18 g) =? 0).

Definition fg_hf (st : list byte) : Z := bat st 6.

Definition fg_lf (st : list byte) : Z := bat st 7.

Definition fg_T (st g : list byte) : Z := fg_lf st + fg_n g.

Definition fg_src_eq (st g : list byte) : bool :=
  (bat st 0 =? bat g 6) && (bat st 1 =? bat g 7) && (bat st 2 =? bat g 8) &&
  (bat st 3 =? bat g 9) && (bat st 4 =? bat g 10) && (bat st 5 =? bat g 11).

Definition fg_keep (st g : list byte) : bool :=
  negb (fg_hf st =? 0) && fg_src_eq st g && (fg_T st g <=? 64).

Definition fg_body (g : list byte) : list byte := bsl g 27 (fg_n g).

Definition fg_first (st g : list byte) : list byte :=
  bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)] ++ fg_body g ++ skipn (Z.to_nat (8 + fg_n g)) st.

Definition fg_join (st g : list byte) : list byte :=
  firstn (Z.to_nat (8 + fg_lf st)) st ++ fg_body g ++ skipn (Z.to_nat (8 + fg_T st g)) st.

Definition fg_clear (st : list byte) : list byte := firstn 6 st ++ [Z_to_bv 8 0] ++ skipn 7 st.

Definition fg_close (st g : list byte) : bool :=
  (14 <=? fg_T st g) && (bat (fg_join st g) 8 =? 240) && (bat (fg_join st g) 9 =? 65) &&
  (bat (fg_join st g) 11 =? 0) && (bat (fg_join st g) 12 =? 0) && (bat (fg_join st g) 13 =? 18) &&
  (bat (fg_join st g) 14 =? 18) && (bat (fg_join st g) 15 =? 5) && (bat (fg_join st g) 16 =? 0) &&
  (bat (fg_join st g) (7 + fg_T st g) =? 247) && (recsum (bsl (fg_join st g) 15 (fg_T st g - 8)) =? 0).

Definition fg_addr (st g : list byte) : Z := 256 * bat (fg_join st g) 17 + bat (fg_join st g) 18.

Inductive fg_case : Type := FgRefuse | FgNone | FgFirst | FgDrop | FgJoin | FgClose.

Definition fg_class (f fr pa pp pn len : Z) (st g : list byte) : fg_case :=
  if (f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0) then FgRefuse
  else if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.

Definition fg_ret (c : fg_case) : Z :=
  match c with
  | FgRefuse => -1
  | FgClose => 1
  | _ => 0
  end.

Definition fg_fp (K f pa pp pn S : Z) (c : fg_case) : list (Z * Z) :=
  match c with
  | FgRefuse | FgNone => [(S - K, S)]
  | FgFirst | FgDrop | FgJoin => [(f, f + 72); (S - K, S)]
  | FgClose => [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - K, S)]
  end.

Fixpoint dj_from (a b : Z) (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (c, d) :: l' => (b <= c \/ d <= a) /\ dj_from a b l'
  end.

Fixpoint all_dj (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (a, b) :: l' => dj_from a b l' /\ all_dj l'
  end.
