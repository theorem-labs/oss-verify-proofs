(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition nz (v : Z) : bool := negb (v =? 0).

Record shfile := mkSh {
  sh_buf : list Z;
  sh_rpos : Z;
  sh_cnt0 : Z;
  sh_n : Z;
  sh_stdio : bool;
  sh_shlim_neg : bool
}.

Definition sh_getc (f : shfile) : Z * shfile :=
  if negb (sh_stdio f) then
    (znth (sh_buf f) (sh_rpos f),
     mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))
  else if negb (sh_rpos f =? sh_n f) then
    (znth (sh_buf f) (sh_rpos f),
     mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))
  else
    (-1, mkSh (sh_buf f) (sh_rpos f) (sh_cnt0 f) (sh_n f) (sh_stdio f) true).

Definition sh_unget (f : shfile) : shfile :=
  if negb (sh_shlim_neg f)
  then mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)
  else f.

Definition sh_lim0 (f : shfile) : shfile :=
  mkSh (sh_buf f) (sh_rpos f) (sh_rpos f) (sh_n f) (sh_stdio f) false.

Definition sh_cnt (f : shfile) : Z := sh_rpos f - sh_cnt0 f.

Definition setrpos (f : shfile) (r : Z) : shfile :=
  mkSh (sh_buf f) r (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).

Definition m_isspace (c : Z) : bool := (c =? 32) || (u32 (c - 9) <? 5).

Definition digval (c : Z) : Z :=
  if (48 <=? c) && (c <=? 57) then c - 48
  else if (65 <=? c) && (c <=? 90) then c - 55
  else if (97 <=? c) && (c <=? 122) then c - 87
  else 255.

Fixpoint is_ws_loop (fuel : nat) (f : shfile) : option (Z * shfile) :=
  match fuel with
  | O => None
  | S fu => let '(c, f1) := sh_getc f in if m_isspace c then is_ws_loop fu f1 else Some (c, f1)
  end.

Fixpoint is_dig_loop (fuel : nat) (base c : Z) (f : shfile) : option (Z * shfile) :=
  match fuel with
  | O => None
  | S fu => if digval c <? base then let '(c1, f1) := sh_getc f in is_dig_loop fu base c1 f1 else Some (c, f)
  end.

Definition is_digits (fuel : nat) (base c : Z) (f : shfile) : option shfile :=
  match is_dig_loop fuel base c f with Some (_, f1) => Some (sh_unget f1) | None => None end.

Definition intscan (fuel : nat) (base pok : Z) (f : shfile) : option shfile :=
  match is_ws_loop fuel f with
  | None => None
  | Some (c, f) =>
    let '(c, f) := (if (c =? 43) || (c =? 45) then sh_getc f else (c, f)) in
    if (base =? 16) && (c =? 48) then
      let '(c, f) := sh_getc f in
      if Z.lor c 32 =? 120 then
        let '(c, f) := sh_getc f in
        if 16 <=? digval c then Some (if nz pok then sh_unget (sh_unget f) else sh_lim0 (sh_unget f))
        else is_digits fuel 16 c f
      else is_digits fuel 16 c f
    else if base <=? digval c then Some (sh_lim0 (sh_unget f))
    else is_digits fuel base c f
  end.

Inductive sdir := SD | SW | SL (c : Z).
Definition FMT_VERSION : list sdir := [SD; SW; SL 46; SW; SD].
Definition FMT_STATUSLINE : list sdir := [SD; SW; SL 46; SW; SD; SW; SD].

Inductive vres := VOk (f : shfile) | VInput | VMatch | VFuel.

Definition vf_W (fuel : nat) (f : shfile) : vres :=
  match is_ws_loop fuel (sh_lim0 f) with Some (_, f1) => VOk (sh_unget f1) | None => VFuel end.

Definition vf_L (ch : Z) (f : shfile) : vres :=
  let '(c, f1) := sh_getc (sh_lim0 f) in
  if c =? ch then VOk f1 else if c <? 0 then VInput else VMatch.

Definition vf_D (fuel : nat) (f : shfile) : vres :=
  match vf_W fuel f with
  | VOk f2 =>
    let '(c, f4) := sh_getc (sh_lim0 f2) in
    if c <? 0 then VInput else
    match intscan fuel 10 0 (sh_unget f4) with
    | Some f6 => if sh_cnt f6 =? 0 then VMatch else VOk f6
    | None => VFuel
    end
  | r => r
  end.

Fixpoint vfs (fuel : nat) (fmt : list sdir) (f : shfile) (matches : Z) : option Z :=
  match fmt with
  | [] => Some matches
  | d :: fmt' =>
    let r := match d with SW => vf_W fuel f | SL ch => vf_L ch f | SD => vf_D fuel f end in
    match r with
    | VOk f' => vfs fuel fmt' f' (match d with SD => matches + 1 | _ => matches end)
    | VInput => Some (if matches =? 0 then -1 else matches)
    | VMatch => Some matches
    | VFuel => None
    end
  end.

Definition ssf0 (txt : list Z) (p : Z) : shfile := mkSh txt 0 0 p true false.

Definition stf0 (txt : list Z) : shfile := mkSh txt 0 0 0 false false.

Definition sscanf_model (fmt : list sdir) (txt : list Z) (p : Z) : option Z :=
  vfs (S (length txt)) fmt (ssf0 txt p) 0.

Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).
Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Fixpoint cstr (bs : list Z) : list Z :=
  match bs with [] => [] | c :: bs' => if c =? 0 then [] else c :: cstr bs' end.
Fixpoint drop_while (f : Z -> bool) (l : list Z) : list Z :=
  match l with [] => [] | c :: l' => if f c then drop_while f l' else l end.
Fixpoint take_while_len (f : Z -> bool) (l : list Z) : nat :=
  match l with [] => 0%nat | c :: l' => if f c then S (take_while_len f l') else 0%nat end.
Fixpoint scan_count (fmt : list sdir) (inp : list Z) (acc : Z) : Z :=
  match fmt with
  | [] => acc
  | SW :: fmt' => scan_count fmt' (drop_while is_space inp) acc
  | SL c :: fmt' => match inp with c' :: inp' => if c' =? c then scan_count fmt' inp' acc else acc | [] => acc end
  | SD :: fmt' =>
      let i1 := drop_while is_space inp in
      let i2 := match i1 with c :: r => if (c =? 43) || (c =? 45) then r else i1 | [] => i1 end in
      let nd := take_while_len is_digit i2 in
      if Nat.eqb nd 0 then acc else scan_count fmt' (skipn nd i2) (acc + 1)
  end.

Ltac getc_cases f :=
  unfold sh_getc; destruct (sh_stdio f) eqn:?ST; cbn [negb];
  [destruct (Z.eqb_spec (sh_rpos f) (sh_n f)); cbn [negb]|].

Lemma sh_getc_buf : forall f, sh_buf (snd (sh_getc f)) = sh_buf f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. intros f. getc_cases f; cbn; congruence. Qed.
Lemma sh_getc_cnt0 : forall f, sh_cnt0 (snd (sh_getc f)) = sh_cnt0 f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_n : forall f, sh_n (snd (sh_getc f)) = sh_n f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_rpos : forall f, sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1.
Proof. intros f. getc_cases f; cbn; lia. Qed.
Lemma sh_getc_neg : forall f, sh_stdio f = false -> sh_shlim_neg (snd (sh_getc f)) = sh_shlim_neg f.
Proof. intros f H. unfold sh_getc. rewrite H. reflexivity. Qed.
Lemma sh_getc_char : forall f,
  (fst (sh_getc f) = -1 /\ sh_rpos (snd (sh_getc f)) = sh_rpos f /\ sh_stdio f = true /\ sh_rpos f = sh_n f
   /\ sh_shlim_neg (snd (sh_getc f)) = true)
  \/ (fst (sh_getc f) = znth (sh_buf f) (sh_rpos f) /\ sh_rpos (snd (sh_getc f)) = sh_rpos f + 1
      /\ (sh_stdio f = true -> sh_rpos f <> sh_n f) /\ sh_shlim_neg (snd (sh_getc f)) = sh_shlim_neg f).
Proof. intros f. getc_cases f; cbn; [left|right|right]; repeat split; auto; try congruence. Qed.
Lemma sh_getc_nonstdio : forall f, sh_stdio f = false ->
  sh_getc f = (znth (sh_buf f) (sh_rpos f), setrpos f (sh_rpos f + 1)).
Proof. intros f H. unfold sh_getc, setrpos. rewrite H. reflexivity. Qed.

Lemma sh_unget_rpos : forall f, sh_rpos f - 1 <= sh_rpos (sh_unget f) <= sh_rpos f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); cbn; lia. Qed.
Lemma sh_unget_rpos_eq : forall f, sh_shlim_neg f = false -> sh_rpos (sh_unget f) = sh_rpos f - 1.
Proof. intros f H. unfold sh_unget. rewrite H. reflexivity. Qed.
Lemma sh_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
Proof. intros f H. unfold sh_unget. rewrite H. reflexivity. Qed.
Lemma sh_unget_buf : forall f, sh_buf (sh_unget f) = sh_buf f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_stdio : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_cnt0 : forall f, sh_cnt0 (sh_unget f) = sh_cnt0 f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_n : forall f, sh_n (sh_unget f) = sh_n f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_neg : forall f, sh_shlim_neg (sh_unget f) = sh_shlim_neg f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f) eqn:E; cbn; congruence. Qed.

Lemma znth_ge : forall l i, zlength l <= i -> znth l i = 0.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [reflexivity|].
  apply nth_overflow. lia.
Qed.
Lemma znth_app_l : forall l1 l2 i, 0 <= i < zlength l1 -> znth (l1 ++ l2) i = znth l1 i.
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
  apply app_nth1. lia.
Qed.
Lemma znth_app_r : forall l1 l2 i, zlength l1 <= i -> znth (l1 ++ l2) i = znth l2 (i - zlength l1).
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Z.ltb_spec0 (i - Z.of_nat (length l1)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_In : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
  apply nth_In. lia.
Qed.

Lemma digval_range : forall c, 0 <= digval c <= 35 \/ digval c = 255.
Proof.
  intros c. unfold digval.
  destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 65 c); destruct (Z.leb_spec0 c 90); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 97 c); destruct (Z.leb_spec0 c 122); cbn [andb]; lia.
Qed.
Lemma digval_lt10 : forall c, digval c < 10 <-> 48 <= c <= 57.
Proof.
  intros c. unfold digval.
  destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 65 c); destruct (Z.leb_spec0 c 90); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 97 c); destruct (Z.leb_spec0 c 122); cbn [andb]; lia.
Qed.
Lemma digval_lt16 : forall c, digval c < 16 <-> (48 <= c <= 57 \/ 65 <= c <= 70 \/ 97 <= c <= 102).
Proof.
  intros c. unfold digval.
  destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 65 c); destruct (Z.leb_spec0 c 90); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 97 c); destruct (Z.leb_spec0 c 122); cbn [andb]; lia.
Qed.
Lemma digval_nondigit_stop : forall c, c = 0 \/ c = -1 -> digval c = 255.
Proof. intros c [-> | ->]; reflexivity. Qed.
Lemma m_isspace_iff : forall c, -2^31 < c < 2^31 -> m_isspace c = true <-> (c = 32 \/ 9 <= c <= 13).
Proof.
  intros c Hc. unfold m_isspace, u32. rewrite Bool.orb_true_iff, Z.eqb_eq, Z.ltb_lt.
  split; intros H; Z.div_mod_to_equations; lia.
Qed.
