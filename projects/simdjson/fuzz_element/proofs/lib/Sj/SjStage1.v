(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Export SjS1Out.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition char_table : list Z :=
  [4;4;4;4;4;4;4;4; 4;5;5;4;4;5;4;4; 4;4;4;4;4;4;4;4; 4;4;4;4;4;4;4;4;
   1;0;4;0;0;0;0;0; 0;0;0;0;2;0;0;0; 0;0;0;0;0;0;0;0; 0;0;2;0;0;0;0;0;
   0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;2;4;2;0;0;
   0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;2;0;2;0;0;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8].
Definition tbl (c : Z) : Z := nth (Z.to_nat c) char_table 0.

Definition t_space (c : Z) : bool := negb (Z.land (tbl c) 1 =? 0).
Definition t_op (c : Z) : bool := negb (Z.land (tbl c) 2 =? 0).
Definition t_space_or_op (c : Z) : bool := negb (Z.land (tbl c) 3 =? 0).
Definition t_ascii_stop (c : Z) : bool := negb (Z.land (tbl c) 12 =? 0).

Definition SUCCESS := 0.  Definition UTF8_ERROR := 11.  Definition EMPTY := 13.
Definition UNESCAPED_CHARS := 14.  Definition UNCLOSED_STRING := 15.

Definition is_cont (c : Z) : bool := (128 <=? c) && (c <=? 191).

Section Model.
Variable bs : list Z.
Notation len := (blen bs).
Notation Bi := (B bs).

Fixpoint ws_run (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f => if t_space (Bi i) then (if i + 1 <? len then ws_run f (i + 1) else i + 1) else i
  end.

Fixpoint ascii_run (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f => if t_ascii_stop (Bi i) then i else (if i + 1 <? len then ascii_run f (i + 1) else i + 1)
  end.

Definition utf8_step (i err : Z) : Z * Z :=
  let b := Bi i in
  if Z.land b 64 =? 0 then (i + 1, UTF8_ERROR)
  else if Z.land b 32 =? 0 then
    if negb (is_cont (Bi (i + 1))) then (i + 1, UTF8_ERROR)
    else (i + 2, if b <? 194 then UTF8_ERROR else err)
  else if Z.land b 16 =? 0 then
    if (len <? i + 2) || negb (is_cont (Bi (i + 1))) || negb (is_cont (Bi (i + 2))) then (i + 1, UTF8_ERROR)
    else (i + 3, if ((b =? 224) && (Bi (i + 1) <? 160)) || ((b =? 237) && (159 <? Bi (i + 1))) then UTF8_ERROR else err)
  else
    if (len <? i + 3) || negb (is_cont (Bi (i + 1))) || negb (is_cont (Bi (i + 2))) || negb (is_cont (Bi (i + 3)))
    then (i + 1, UTF8_ERROR)
    else (i + 4, if ((b =? 240) && (Bi (i + 1) <? 144)) || ((b =? 244) && (143 <? Bi (i + 1))) || (244 <? b)
                 then UTF8_ERROR else err).

Definition str_token (i err : Z) : Z * Z :=
  let b := Bi i in
  if b =? 92 then (i + 2, err)
  else if 128 <=? b then utf8_step i err
  else (i + 1, if b <? 32 then UNESCAPED_CHARS else err).

Fixpoint str_loop (fuel : nat) (i err : Z) : Z * Z * bool :=
  match fuel with
  | O => (i, err, true)
  | S f =>
      if i <? len then
        let i1 := ascii_run (length bs) i in
        if len <=? i1 then (i1, err, true)
        else if Bi i1 =? 34 then (i1, err, false)
        else let '(i2, err2) := str_token i1 err in str_loop f i2 err2
      else (i, err, true)
  end.

Fixpoint prim_run (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f => if (i + 1 <? len) && negb (t_space_or_op (Bi (i + 1))) && negb (Bi (i + 1) =? 30)
           then prim_run f (i + 1) else i
  end.

Record s1st : Type := mkS1 { s_idx : Z; s_err : Z; s_unclosed : bool; s_out : list Z }.

Definition scan_token (i : Z) (st : s1st) : s1st :=
  let c := Bi i in
  if c =? 34 then
    let '(i', err', u) := str_loop (length bs) (i + 1) (s_err st) in
    mkS1 (i' + 1) err' (s_unclosed st || u) (s_out st ++ [i])
  else if t_op c then mkS1 (i + 1) (s_err st) (s_unclosed st) (s_out st ++ [i])
  else mkS1 (prim_run (length bs) i + 1) (s_err st) (s_unclosed st) (s_out st ++ [i]).

Fixpoint scan_loop (fuel : nat) (st : s1st) : s1st :=
  match fuel with
  | O => st
  | S f =>
      if s_idx st <? len then
        let i := ws_run (length bs) (s_idx st) in
        if len <=? i then mkS1 i (s_err st) (s_unclosed st) (s_out st)
        else scan_loop f (scan_token i st)
      else st
  end.

Definition s1_init : s1st := mkS1 0 SUCCESS false [].

Definition s1_code (st : s1st) : Z :=
  if (length (s_out st) =? 0)%nat then EMPTY
  else if s_unclosed st then UNCLOSED_STRING else s_err st.

Definition stage1_st : s1st := scan_loop (S (length bs)) s1_init.
Definition stage1 : Z * list Z := (s1_code stage1_st, s_out stage1_st).

Definition stage1_code : Z := fst stage1.
Definition stage1_idx0 : Z := hd 0 (snd stage1).

Lemma ws_run_S : forall f i, ws_run (S f) i =
  if t_space (Bi i) then (if i + 1 <? len then ws_run f (i + 1) else i + 1) else i.
Proof. reflexivity. Qed.
Lemma ascii_run_S : forall f i, ascii_run (S f) i =
  if t_ascii_stop (Bi i) then i else (if i + 1 <? len then ascii_run f (i + 1) else i + 1).
Proof. reflexivity. Qed.
Lemma prim_run_S : forall f i, prim_run (S f) i =
  if (i + 1 <? len) && negb (t_space_or_op (Bi (i + 1))) && negb (Bi (i + 1) =? 30)
  then prim_run f (i + 1) else i.
Proof. reflexivity. Qed.
Lemma str_loop_S : forall f i err, str_loop (S f) i err =
  if i <? len then
    let i1 := ascii_run (length bs) i in
    if len <=? i1 then (i1, err, true)
    else if Bi i1 =? 34 then (i1, err, false)
    else let '(i2, err2) := str_token i1 err in str_loop f i2 err2
  else (i, err, true).
Proof. reflexivity. Qed.
Lemma scan_loop_S : forall f st, scan_loop (S f) st =
  if s_idx st <? len then
    let i := ws_run (length bs) (s_idx st) in
    if len <=? i then mkS1 i (s_err st) (s_unclosed st) (s_out st)
    else scan_loop f (scan_token i st)
  else st.
Proof. reflexivity. Qed.

Lemma ws_run_bounds : forall f i, i < len -> i <= ws_run f i <= len.
Proof.
  induction f as [|f IH]; intros i H; cbn [ws_run]; [lia|].
  destruct (t_space (Bi i)); [|lia].
  destruct (Z.ltb_spec (i + 1) len); [|lia].
  specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

Lemma ascii_run_bounds : forall f i, i < len -> i <= ascii_run f i <= len.
Proof.
  induction f as [|f IH]; intros i H; cbn [ascii_run]; [lia|].
  destruct (t_ascii_stop (Bi i)); [lia|].
  destruct (Z.ltb_spec (i + 1) len); [|lia].
  specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

Lemma prim_run_bounds : forall f i, i < len -> i <= prim_run f i < len.
Proof.
  induction f as [|f IH]; intros i H; cbn [prim_run]; [lia|].
  destruct (Z.ltb_spec (i + 1) len); cbn [andb]; [|lia].
  destruct (negb (t_space_or_op (Bi (i + 1))) && negb (Bi (i + 1) =? 30)); [|lia].
  specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

Lemma utf8_step_bounds : forall i err, i < fst (utf8_step i err) <= i + 4.
Proof.
  intros i err. unfold utf8_step.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst]; lia.
Qed.

Lemma str_token_bounds : forall i err, i < fst (str_token i err) <= i + 4.
Proof.
  intros i err. unfold str_token.
  destruct (Bi i =? 92); [cbn [fst]; lia|].
  destruct (128 <=? Bi i); [apply utf8_step_bounds| cbn [fst]; lia].
Qed.

Lemma str_loop_done : forall f i err, len <= i -> str_loop f i err = (i, err, true).
Proof.
  intros [|f] i err H; cbn [str_loop]; [reflexivity|].
  destruct (Z.ltb_spec i len); [lia|reflexivity].
Qed.

Lemma str_loop_bounds : forall f i err i' err' u, str_loop f i err = (i', err', u) -> i <= i' <= Z.max i (len + 3).
Proof.
  induction f as [|f IH]; intros i err i' err' u H; cbn [str_loop] in H.
  - inversion H; subst. lia.
  - destruct (Z.ltb_spec i len) as [L|L]; [|inversion H; subst; lia].
    pose proof (ascii_run_bounds (length bs) i L) as AB.
    cbv zeta in H.
    destruct (Z.leb_spec len (ascii_run (length bs) i)); [inversion H; subst; lia|].
    destruct (Bi (ascii_run (length bs) i) =? 34); [inversion H; subst; lia|].
    pose proof (str_token_bounds (ascii_run (length bs) i) err) as TB.
    destruct (str_token (ascii_run (length bs) i) err) as [i2 err2]. cbn [fst] in TB.
    specialize (IH _ _ _ _ _ H). lia.
Qed.

Lemma scan_loop_done : forall f st, len <= s_idx st -> scan_loop f st = st.
Proof.
  intros [|f] st H; cbn [scan_loop]; [reflexivity|].
  destruct (Z.ltb_spec (s_idx st) len); [lia|reflexivity].
Qed.

Definition err_ok (e : Z) : Prop := e = SUCCESS \/ e = UTF8_ERROR \/ e = UNESCAPED_CHARS.

Lemma err_ok_range : forall e, err_ok e -> 0 <= e < 64.
Proof. unfold err_ok, SUCCESS, UTF8_ERROR, UNESCAPED_CHARS. intros e H. lia. Qed.

Lemma utf8_step_err : forall i err, err_ok err -> err_ok (snd (utf8_step i err)).
Proof.
  intros i err H. unfold utf8_step.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd]; unfold err_ok; auto.
Qed.

Lemma str_token_err : forall i err, err_ok err -> err_ok (snd (str_token i err)).
Proof.
  intros i err H. unfold str_token.
  destruct (Bi i =? 92); [exact H|].
  destruct (128 <=? Bi i); [apply utf8_step_err; exact H|].
  cbn [snd]. destruct (Bi i <? 32); [unfold err_ok; auto| exact H].
Qed.

Lemma str_loop_err : forall f i err i' err' u, str_loop f i err = (i', err', u) -> err_ok err -> err_ok err'.
Proof.
  induction f as [|f IH]; intros i err i' err' u H HE; cbn [str_loop] in H.
  - inversion H; subst. exact HE.
  - destruct (i <? len); [|inversion H; subst; exact HE].
    cbv zeta in H.
    destruct (len <=? ascii_run (length bs) i); [inversion H; subst; exact HE|].
    destruct (Bi (ascii_run (length bs) i) =? 34); [inversion H; subst; exact HE|].
    pose proof (str_token_err (ascii_run (length bs) i) err HE) as TE.
    destruct (str_token (ascii_run (length bs) i) err) as [i2 err2]. cbn [snd] in TE.
    exact (IH _ _ _ _ _ H TE).
Qed.

Lemma prim_run_end : forall f i, len <= i + 1 -> prim_run f i = i.
Proof.
  intros [|f] i H; cbn [prim_run]; [reflexivity|].
  destruct (Z.ltb_spec (i + 1) len); [lia|reflexivity].
Qed.

Lemma prim_run_unfold : forall f i, (0 < f)%nat -> prim_run f i =
  if (i + 1 <? len) && negb (t_space_or_op (Bi (i + 1))) && negb (Bi (i + 1) =? 30)
  then prim_run (pred f) (i + 1) else i.
Proof. intros [|f] i H; [lia|reflexivity]. Qed.

End Model.
