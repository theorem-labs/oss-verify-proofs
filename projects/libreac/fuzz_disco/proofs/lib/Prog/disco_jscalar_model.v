From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.

Definition jlen (B : list Z) : Z := Z.of_nat (length B).
Definition jbyte (B : list Z) (j : Z) : Z := nth (Z.to_nat j) B 0.

Definition jdigit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition jhexd (c : Z) : bool :=
  jdigit c || ((97 <=? c) && (c <=? 102)) || ((65 <=? c) && (c <=? 70)).
Definition jesc (c : Z) : bool := existsb (Z.eqb c) [34; 92; 47; 98; 102; 110; 114; 116; 117].

Definition jtok : Type := (Z * Z * Z * Z)%type.

Fixpoint jstr (B : list Z) (i j : Z) (fuel : nat) : option jtok :=
  match fuel with
  | O => None
  | S f =>
      if jlen B <=? j then None
      else if jbyte B j =? 34 then Some (j + 1, 1, i + 1, j - i - 1)
      else if jbyte B j <? 32 then None
      else if jbyte B j =? 92 then
        if jlen B <=? j + 1 then None
        else if negb (jesc (jbyte B (j + 1))) then None
        else if jbyte B (j + 1) =? 117 then
          if (jlen B - (j + 1) <=? 4) ||
             negb (jhexd (jbyte B (j + 2)) && jhexd (jbyte B (j + 3)) &&
                   jhexd (jbyte B (j + 4)) && jhexd (jbyte B (j + 5)))
          then None
          else jstr B i (j + 6) f
        else jstr B i (j + 2) f
      else jstr B i (j + 1) f
  end.

Fixpoint jprefix (w r : list Z) : bool :=
  match w, r with
  | [], _ => true
  | a :: w', b :: r' => (a =? b) && jprefix w' r'
  | _ :: _, [] => false
  end.

Definition jlit_words : list (list Z) := [[116; 114; 117; 101]; [102; 97; 108; 115; 101]; [110; 117; 108; 108]].

Fixpoint jlit (B : list Z) (i : Z) (ws : list (list Z)) : option jtok :=
  match ws with
  | [] => None
  | w :: ws' =>
      if (Z.of_nat (length w) <=? jlen B - i) && jprefix w (skipn (Z.to_nat i) B)
      then Some (i + Z.of_nat (length w), 3, i, Z.of_nat (length w))
      else jlit B i ws'
  end.

Fixpoint jdigits (B : list Z) (j : Z) (fuel : nat) : Z :=
  match fuel with
  | O => j
  | S f => if (j <? jlen B) && jdigit (jbyte B j) then jdigits B (j + 1) f else j
  end.

Definition jdig_at (B : list Z) (j : Z) : bool := (j <? jlen B) && jdigit (jbyte B j).

Definition jfrac (B : list Z) (j : Z) : option Z :=
  if (j <? jlen B) && (jbyte B j =? 46) then
    if jdig_at B (j + 1) then Some (jdigits B (j + 1) (length B)) else None
  else Some j.

Definition jexp (B : list Z) (j : Z) : option Z :=
  if (j <? jlen B) && ((jbyte B j =? 101) || (jbyte B j =? 69)) then
    let k := if (j + 1 <? jlen B) && ((jbyte B (j + 1) =? 43) || (jbyte B (j + 1) =? 45)) then j + 2 else j + 1 in
    if jdig_at B k then Some (jdigits B k (length B)) else None
  else Some j.

Definition jnum (B : list Z) (i : Z) : option jtok :=
  let j0 := if jbyte B i =? 45 then i + 1 else i in
  if negb (jdig_at B j0) then None
  else
    let j1 := if jbyte B j0 =? 48 then j0 + 1 else jdigits B j0 (length B) in
    match jfrac B j1 with
    | None => None
    | Some j2 =>
        match jexp B j2 with
        | None => None
        | Some j3 => Some (j3, 2, i, j3 - i)
        end
    end.

Definition jscalar (B : list Z) (i : Z) : option jtok :=
  if jlen B <=? i then None
  else if jbyte B i =? 34 then jstr B i (i + 1) (length B)
  else match jlit B i jlit_words with
       | Some t => Some t
       | None => jnum B i
       end.
