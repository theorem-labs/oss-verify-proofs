From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_text.
Import ListNotations.
Open Scope Z_scope.

Definition jws_char (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 10) || (c =? 13).

Fixpoint json_ws_f (B : list Z) (i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => i
  | S f => if (i <? jlen B) && jws_char (jbyte B i) then json_ws_f B (i + 1) f else i
  end.

Definition json_ws (B : list Z) (i : Z) : Z := json_ws_f B i (length B).

Definition tokv : Type := (Z * Z * Z)%type.

Definition tok_none : tokv := (0, 0, 0).

Definition tv_kind (t : tokv) : Z := fst (fst t).
Definition tv_text (B : list Z) (t : tokv) : list Z :=
  firstn (Z.to_nat (snd t)) (skipn (Z.to_nat (snd (fst t))) B).

Fixpoint lzeqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && lzeqb a' b'
  | _, _ => false
  end.

Definition jtok_is (B : list Z) (v : tokv) (kind : Z) (text : list Z) : bool :=
  (tv_kind v =? kind) && (snd v =? Z.of_nat (length text)) && lzeqb (tv_text B v) text.

Definition keys : list (list Z) := [k_mac; k_role; k_model; k_width; k_owned; k_age_ms].

Fixpoint slot_from (B : list Z) (v : tokv) (ks : list (list Z)) (k : nat) : option nat :=
  match ks with
  | [] => None
  | w :: ks' => if jtok_is B v 1 w then Some k else slot_from B v ks' (S k)
  end.

Definition slot_of (B : list Z) (v : tokv) : option nat := slot_from B v keys 0.

Definition jobj : Type := list tokv.

Definition jobj_empty : jobj := repeat tok_none 6.

Fixpoint set_nth (k : nat) (o : jobj) (t : tokv) : jobj :=
  match o, k with
  | [], _ => []
  | _ :: o', O => t :: o'
  | x :: o', S k' => x :: set_nth k' o' t
  end.

Definition at_byte (B : list Z) (i c : Z) : bool := (i <? jlen B) && (jbyte B i =? c).

Fixpoint json_pairs (B : list Z) (i : Z) (cur : jobj) (fuel : nat) : option (Z * jobj) :=
  match fuel with
  | O => None
  | S f =>
      match jscalar B i with
      | None => None
      | Some (j, kk, ks, kl) =>
          if negb (kk =? 1) then None
          else
            let i1 := json_ws B j in
            if negb (at_byte B i1 58) then None
            else
              let i2 := json_ws B (i1 + 1) in
              match jscalar B i2 with
              | None => None
              | Some (j2, vk, vs, vl) =>
                  let i3 := json_ws B j2 in
                  let cur' :=
                    match slot_of B (kk, ks, kl) with
                    | Some k => if tv_kind (nth k cur tok_none) =? 0 then Some (set_nth k cur (vk, vs, vl)) else None
                    | None => Some cur
                    end in
                  match cur' with
                  | None => None
                  | Some c =>
                      if at_byte B i3 44 then json_pairs B (json_ws B (i3 + 1)) c f
                      else if at_byte B i3 125 then Some (i3 + 1, c)
                      else None
                  end
              end
      end
  end.

Fixpoint json_objs (B : list Z) (i count max : Z) (acc : list jobj) (fuel : nat) : option (Z * list jobj) :=
  match fuel with
  | O => None
  | S f =>
      if negb (at_byte B i 123) then None
      else
        let i1 := json_ws B (i + 1) in
        let r := if at_byte B i1 125 then Some (i1 + 1, jobj_empty) else json_pairs B i1 jobj_empty (length B) in
        match r with
        | None => None
        | Some (i2, cur) =>
            let acc' := if count <? max then acc ++ [cur] else acc in
            let i3 := json_ws B i2 in
            if at_byte B i3 44 then json_objs B (json_ws B (i3 + 1)) (count + 1) max acc' f
            else if at_byte B i3 93 then
              (if json_ws B (i3 + 1) =? jlen B then Some (count + 1, acc') else None)
            else None
        end
  end.

Definition json_read (B : list Z) (max : Z) : option (Z * list jobj) :=
  let i := json_ws B 0 in
  if negb (at_byte B i 91) then None
  else
    let i1 := json_ws B (i + 1) in
    if at_byte B i1 93 then (if json_ws B (i1 + 1) =? jlen B then Some (0, []) else None)
    else json_objs B i1 0 max [] (length B).
