From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.

Record entry : Type := mkE {
  e_mac : list Z;
  e_role : Z;
  e_has_decl : Z;
  e_decl_in : Z;
  e_decl_out : Z;
  e_family : Z;
  e_owned : Z;
  e_last_seen : Z
}.

Definition byte_ok (x : Z) : Prop := 0 <= x <= 255.

Definition entry_wf (e : entry) : Prop :=
  length (e_mac e) = 6%nat /\ Forall byte_ok (e_mac e) /\
  byte_ok (e_has_decl e) /\ byte_ok (e_decl_in e) /\ byte_ok (e_decl_out e) /\ byte_ok (e_family e) /\
  - 2 ^ 31 <= e_role e < 2 ^ 31 /\ - 2 ^ 31 <= e_owned e < 2 ^ 31 /\ 0 <= e_last_seen e < 2 ^ 64.

Definition table_ok (T : list entry) : Prop :=
  (length T <= 8)%nat /\
  Forall (fun e => 0 <= e_role e <= 2) T /\
  NoDup (map e_mac T) /\
  Forall (fun e => (e_has_decl e = 0 \/ (e_has_decl e = 1 /\ e_decl_in e <= 40 /\ e_decl_out e <= 40)) /\
                   (e_owned e = 0 \/ e_owned e = 1)) T.

Definition tok_char (c : Z) : Prop := (97 <= c <= 122) \/ (48 <= c <= 57) \/ c = 45.

Definition tok_ok (tok : Z -> Z -> Z -> option (list Z)) : Prop :=
  forall f a b t, tok f a b = Some t -> (length t <= 11)%nat /\ Forall tok_char t.

Definition hexc (d : Z) : Z := if d <? 10 then 48 + d else 87 + d.
Definition hex2 (x : Z) : list Z := [hexc (x / 16); hexc (x mod 16)].

Fixpoint dec_aux (fuel : nat) (v : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if v =? 0 then acc else dec_aux f (v / 10) ((48 + v mod 10) :: acc)
  end.

Definition dec (v : Z) : list Z := if v =? 0 then [48] else dec_aux 20 v [].

Definition s_box : list Z := [98; 111; 120].
Definition s_master : list Z := [109; 97; 115; 116; 101; 114].
Definition s_unknown : list Z := [117; 110; 107; 110; 111; 119; 110].
Definition s_true : list Z := [116; 114; 117; 101].
Definition s_false : list Z := [102; 97; 108; 115; 101].
Definition s_0x0 : list Z := [48; 120; 48].

Definition k_mac : list Z := [109; 97; 99].
Definition k_role : list Z := [114; 111; 108; 101].
Definition k_model : list Z := [109; 111; 100; 101; 108].
Definition k_width : list Z := [119; 105; 100; 116; 104].
Definition k_owned : list Z := [111; 119; 110; 101; 100].
Definition k_age_ms : list Z := [97; 103; 101; 95; 109; 115].

Definition rolename (r : Z) : list Z :=
  if r =? 1 then s_box else if r =? 2 then s_master else s_unknown.

Definition mac_text (m : list Z) : list Z :=
  hex2 (nth 0 m 0) ++ [58] ++ hex2 (nth 1 m 0) ++ [58] ++ hex2 (nth 2 m 0) ++ [58] ++
  hex2 (nth 3 m 0) ++ [58] ++ hex2 (nth 4 m 0) ++ [58] ++ hex2 (nth 5 m 0).

Definition age_of (now ls : Z) : Z := if ls <? now then (now - ls) / 1000000 else 0.

Definition model_of (tok : Z -> Z -> Z -> option (list Z)) (e : entry) : list Z * list Z :=
  if e_has_decl e =? 0 then (s_unknown, s_0x0)
  else match tok (e_family e) (e_decl_in e) (e_decl_out e) with
       | Some t => (t, dec (e_decl_in e) ++ [120] ++ dec (e_decl_out e))
       | None => (s_unknown, s_0x0)
       end.

Definition owned_text (e : entry) : list Z := if e_owned e =? 0 then s_false else s_true.

Definition key (k : list Z) : list Z := [34] ++ k ++ [34; 58].
Definition qstr (s : list Z) : list Z := [34] ++ s ++ [34].

Definition P1 (i : nat) (e : entry) : list Z :=
  (if Nat.eqb i 0 then [] else [44]) ++ [123] ++ key k_mac ++ qstr (mac_text (e_mac e)).
Definition P2 (e : entry) : list Z := [44] ++ key k_role ++ qstr (rolename (e_role e)).
Definition P3 tok (e : entry) : list Z := [44] ++ key k_model ++ qstr (fst (model_of tok e)).
Definition P4 tok (e : entry) : list Z := [44] ++ key k_width ++ qstr (snd (model_of tok e)).
Definition P5 (e : entry) : list Z := [44] ++ key k_owned ++ owned_text e.
Definition P6 (now : Z) (e : entry) : list Z := [44] ++ key k_age_ms ++ dec (age_of now (e_last_seen e)) ++ [125].

Definition obj_text tok (now : Z) (i : nat) (e : entry) : list Z :=
  P1 i e ++ P2 e ++ P3 tok e ++ P4 tok e ++ P5 e ++ P6 now e.

Fixpoint objs_text tok (now : Z) (i : nat) (T : list entry) : list Z :=
  match T with
  | [] => []
  | e :: T' => obj_text tok now i e ++ objs_text tok now (S i) T'
  end.

Definition table_json_text tok (T : list entry) (now : Z) : list Z :=
  [91] ++ objs_text tok now 0 T ++ [93].
