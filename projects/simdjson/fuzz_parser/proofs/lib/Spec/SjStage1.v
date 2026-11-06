(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition byte_at (data : list Z) (i : Z) : Z := nth (Z.to_nat i) data 0.

(* [comment removed for export] *)
Definition is_space (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 10) || (c =? 13).
Definition is_op (c : Z) : bool := (c =? 44) || (c =? 58) || (c =? 91) || (c =? 93) || (c =? 123) || (c =? 125).
Definition is_ascii_stop (c : Z) : bool := (c <? 32) || (c =? 34) || (c =? 92) || (128 <=? c).
Definition is_cont (c : Z) : bool := Z.land c 192 =? 128.

(* [comment removed for export] *)
Definition utf8_char (data : list Z) (len i : Z) : Z * bool :=
  let b := byte_at data i in let b1 := byte_at data (i+1) in let b2 := byte_at data (i+2) in let b3 := byte_at data (i+3) in
  if Z.land b 64 =? 0 then (i+1, true)
  else if Z.land b 32 =? 0 then
    if (len <? i+1) || negb (is_cont b1) then (i+1, true) else (i+2, b <=? 193)
  else if Z.land b 16 =? 0 then
    if (len <? i+2) || negb (is_cont b1) || negb (is_cont b2) then (i+1, true)
    else (i+3, ((b =? 224) && (b1 <=? 159)) || ((b =? 237) && (160 <=? b1)))
  else
    if (len <? i+3) || negb (is_cont b1) || negb (is_cont b2) || negb (is_cont b3) then (i+1, true)
    else (i+4, ((b =? 240) && (b1 <=? 143)) || ((b =? 244) && (144 <=? b1)) || (245 <=? b)).

(* [comment removed for export] *)
Fixpoint vstring (fuel : nat) (data : list Z) (len i : Z) (err : bool) : option Z * bool :=
  match fuel with
  | O => (None, err)
  | S f =>
    if len <=? i then (None, err)
    else let b := byte_at data i in
      if negb (is_ascii_stop b) then vstring f data len (i+1) err
      else if b =? 34 then (Some i, err)
      else if b =? 92 then vstring f data len (i+2) err
      else if 128 <=? b then let '(i', e) := utf8_char data len i in vstring f data len i' (err || e)
      else vstring f data len (i+1) true          (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint prim_end (fuel : nat) (data : list Z) (len i : Z) : Z :=
  match fuel with
  | O => i
  | S f => let c := byte_at data (i+1) in
      if (i+1 <? len) && negb (is_space c || is_op c) && negb (c =? 30) then prim_end f data len (i+1) else i
  end.

(* [comment removed for export] *)
Fixpoint scan_from (fuel : nat) (data : list Z) (len i : Z) (acc : list Z) (err uncl : bool) : list Z * bool * bool :=
  match fuel with
  | O => (acc, err, uncl)
  | S f =>
    if len <=? i then (acc, err, uncl)
    else let c := byte_at data i in
      if is_space c then scan_from f data len (i+1) acc err uncl
      else if c =? 34 then
        match vstring (S (Z.to_nat len)) data len (i+1) err with
        | (Some j, e) => scan_from f data len (j+1) (i :: acc) e uncl
        | (None, e) => (i :: acc, e, true)
        end
      else if is_op c then scan_from f data len (i+1) (i :: acc) err uncl
      else scan_from f data len (prim_end (Z.to_nat len) data len i + 1) (i :: acc) err uncl
  end.

Definition scan (data : list Z) : bool * list Z :=
  let len := Z.of_nat (length data) in
  let '(acc, err, uncl) := scan_from (S (length data)) data len 0 [] false false in
  (negb (match acc with [] => true | _ => false end) && negb err && negb uncl, rev acc).

(* [comment removed for export] *)
Definition strip_bom (data : list Z) : list Z :=
  match data with
  | a :: b :: c :: r => if (a =? 239) && (b =? 187) && (c =? 191) then r else data
  | _ => data
  end.

Definition is_numstart (c : Z) : bool := (c =? 45) || ((48 <=? c) && (c <=? 57)).

Definition root_number_alloc (data : list Z) : option Z :=
  let d := strip_bom data in
  match scan d with
  | (true, i0 :: _) => if is_numstart (byte_at d i0) then Some (Z.of_nat (length d) - i0 + 64) else None
  | _ => None
  end.

(* [comment removed for export] *)
Example ex_num : root_number_alloc [32; 55] = Some 65. Proof. reflexivity. Qed.                      (* [comment removed for export] *)
Example ex_arr : root_number_alloc [91; 55; 93] = None. Proof. reflexivity. Qed.                      (* [comment removed for export] *)
Example ex_bad_utf8 : root_number_alloc [55; 32; 34; 128; 34] = None. Proof. reflexivity. Qed.       (* [comment removed for export] *)
Example ex_two : root_number_alloc [55; 32; 34; 97; 34] = Some 69. Proof. reflexivity. Qed.          (* [comment removed for export] *)
Example ex_unclosed : root_number_alloc [45; 32; 34; 97] = None. Proof. reflexivity. Qed.            (* [comment removed for export] *)
Example ex_bom : root_number_alloc [239; 187; 191; 49] = Some 65. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma prim_end_ge : forall f data len i, i <= prim_end f data len i.
Proof.
  induction f as [|f IH]; intros data len i; cbn [prim_end]; [lia|].
  destruct (_ && _ && _); [specialize (IH data len (i+1)); lia| lia].
Qed.

Lemma utf8_char_adv : forall data len i i' e, utf8_char data len i = (i', e) -> i + 1 <= i' <= i + 4.
Proof.
  intros data len i i' e H. unfold utf8_char in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H; lia.
Qed.

Lemma vstring_some_bound : forall f data len i err j e, vstring f data len i err = (Some j, e) -> i <= j < len.
Proof.
  induction f as [|f IH]; intros data len i err j e H; cbn [vstring] in H; [discriminate|].
  destruct (len <=? i) eqn:EL; [discriminate|]. apply Z.leb_gt in EL.
  destruct (negb (is_ascii_stop (byte_at data i))); [apply IH in H; lia|].
  destruct (byte_at data i =? 34); [inversion H; subst; lia|].
  destruct (byte_at data i =? 92); [apply IH in H; lia|].
  destruct (128 <=? byte_at data i).
  - destruct (utf8_char data len i) as [i' e'] eqn:EU. apply utf8_char_adv in EU. apply IH in H. lia.
  - apply IH in H. lia.
Qed.

Lemma scan_from_acc_bound : forall f data len i acc err uncl, 0 <= i -> (forall x, In x acc -> 0 <= x < len) ->
  forall x, In x (fst (fst (scan_from f data len i acc err uncl))) -> 0 <= x < len.
Proof.
  induction f as [|f IH]; intros data len i acc err uncl Hi Hacc x Hx; cbn [scan_from] in Hx; [exact (Hacc x Hx)|].
  destruct (len <=? i) eqn:EL; [exact (Hacc x Hx)|]. apply Z.leb_gt in EL.
  assert (Hacc' : forall y, In y (i :: acc) -> 0 <= y < len) by (intros y [<-|Hy]; [lia| exact (Hacc y Hy)]).
  destruct (is_space (byte_at data i)); [eapply IH; [| exact Hacc| exact Hx]; lia|].
  destruct (byte_at data i =? 34).
  - destruct (vstring (S (Z.to_nat len)) data len (i + 1) err) as [[j|] e] eqn:EV.
    + apply vstring_some_bound in EV. eapply IH; [| exact Hacc'| exact Hx]; lia.
    + exact (Hacc' x Hx).
  - destruct (is_op (byte_at data i)); [eapply IH; [| exact Hacc'| exact Hx]; lia|].
    pose proof (prim_end_ge (Z.to_nat len) data len i). eapply IH; [| exact Hacc'| exact Hx]; lia.
Qed.

Lemma scan_idx_bound : forall data x, In x (snd (scan data)) -> 0 <= x < Z.of_nat (length data).
Proof.
  intros data x H. unfold scan in H.
  destruct (scan_from (S (length data)) data (Z.of_nat (length data)) 0 [] false false) as [[acc err] uncl] eqn:E.
  cbn [snd] in H. apply in_rev in H.
  pose proof (scan_from_acc_bound (S (length data)) data (Z.of_nat (length data)) 0 [] false false ltac:(lia) ltac:(intros y [])) as B.
  rewrite E in B. exact (B x H).
Qed.

Lemma strip_bom_length : forall data, (length (strip_bom data) <= length data)%nat.
Proof.
  intros data. unfold strip_bom. destruct data as [|a [|b [|c r]]]; cbn [length]; try lia.
  destruct ((a =? 239) && (b =? 187) && (c =? 191)); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma root_number_alloc_bound : forall data n, root_number_alloc data = Some n -> 64 < n <= Z.of_nat (length data) + 64.
Proof.
  intros data n H. unfold root_number_alloc in H.
  pose proof (strip_bom_length data) as BL.
  destruct (scan (strip_bom data)) as [ok idx] eqn:ES. destruct ok; [|discriminate]. destruct idx as [|i0 r]; [discriminate|].
  destruct (is_numstart (byte_at (strip_bom data) i0)); [|discriminate]. inversion H; subst n.
  assert (Hin : In i0 (snd (scan (strip_bom data)))) by (rewrite ES; left; reflexivity).
  apply scan_idx_bound in Hin. lia.
Qed.
