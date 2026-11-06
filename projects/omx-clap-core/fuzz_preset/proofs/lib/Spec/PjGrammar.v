From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Open Scope Z_scope.

Definition MAXD : nat := 32.

Definition ws (b : Z) : bool := (b =? 32) || (b =? 9) || (b =? 10) || (b =? 13).

Fixpoint skip (x : list Z) : list Z :=
  match x with
  | [] => []
  | b :: r => if ws b then skip r else x
  end.

Definition digit (b : Z) : bool := (48 <=? b) && (b <=? 57).

Definition numch (b : Z) : bool :=
  digit b || (b =? 46) || (b =? 101) || (b =? 69) || (b =? 43) || (b =? 45).

Definition hexval (b : Z) : option Z :=
  if (48 <=? b) && (b <=? 57) then Some (b - 48)
  else if (97 <=? b) && (b <=? 102) then Some (b - 87)
  else if (65 <=? b) && (b <=? 70) then Some (b - 55)
  else None.

Definition hex4 (x : list Z) : option Z :=
  match x with
  | h0 :: h1 :: h2 :: h3 :: _ =>
    match hexval h0, hexval h1, hexval h2, hexval h3 with
    | Some v0, Some v1, Some v2, Some v3 => Some (4096 * v0 + 256 * v1 + 16 * v2 + v3)
    | _, _, _, _ => None
    end
  | _ => None
  end.

Definition utf8 (cp : Z) : list Z :=
  if cp <? 128 then [cp]
  else if cp <? 2048 then [192 + cp / 64; 128 + cp mod 64]
  else if cp <? 65536 then [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64]
  else [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64].

Fixpoint scan (x : list Z) : option nat :=
  match x with
  | [] => None
  | b :: r =>
    if b =? 34 then Some 0%nat
    else if b =? 92 then
      match r with
      | [] => None
      | _ :: r2 => option_map (fun q => S (S q)) (scan r2)
      end
    else option_map S (scan r)
  end.

Definition escape (e : Z) : option Z :=
  if e =? 34 then Some 34
  else if e =? 92 then Some 92
  else if e =? 47 then Some 47
  else if e =? 98 then Some 8
  else if e =? 102 then Some 12
  else if e =? 110 then Some 10
  else if e =? 114 then Some 13
  else if e =? 116 then Some 9
  else None.

Definition low (z : list Z) : option Z :=
  match z with
  | b1 :: b2 :: r =>
    if (b1 =? 92) && (b2 =? 117) then
      match hex4 r with
      | Some lo => if (56320 <=? lo) && (lo <=? 57343) then Some lo else None
      | None => None
      end
    else None
  | _ => None
  end.

Definition pair_cp (hi lo : Z) : Z := 65536 + (hi - 55296) * 1024 + (lo - 56320).

Definition emit (bs : list Z) (d : option (list Z * list Z)) : option (list Z * list Z) :=
  match d with
  | Some (s, r) => Some (bs ++ s, r)
  | None => None
  end.

Fixpoint decode (x : list Z) : option (list Z * list Z) :=
  match x with
  | [] => None
  | b :: r =>
    if b =? 34 then Some ([], r)
    else if b <? 32 then None
    else if negb (b =? 92) then emit [b] (decode r)
    else
      match r with
      | [] => None
      | e :: r2 =>
        if e =? 117 then
          match r2 with
          | _ :: _ :: _ :: _ :: r3 =>
            match hex4 r2 with
            | None => None
            | Some cp =>
              if cp =? 0 then None
              else if (55296 <=? cp) && (cp <? 56320) then
                match r3 with
                | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
                  match low r3 with
                  | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
                  | None => None
                  end
                | _ => None
                end
              else if (56320 <=? cp) && (cp <? 57344) then None
              else emit (utf8 cp) (decode r3)
            end
          | _ => None
          end
        else
          match escape e with
          | Some c => emit [c] (decode r2)
          | None => None
          end
      end
  end.

Fixpoint span (p : Z -> bool) (x : list Z) : list Z * list Z :=
  match x with
  | [] => ([], [])
  | b :: r => if p b then let (a, z) := span p r in (b :: a, z) else ([], x)
  end.

Fixpoint prefixb (w x : list Z) : bool :=
  match w, x with
  | [], _ => true
  | a :: w', b :: x' => (a =? b) && prefixb w' x'
  | _ :: _, [] => false
  end.

Definition finite (bits : Z) : bool := negb (Z.land (Z.shiftr bits 52) 2047 =? 2047).

Inductive ev : Type :=
| EAlloc (n : nat)
| EGrow (m n : nat)
| EFail (n : nat)
| EFree (n : nat).

Definition is_call (e : ev) : bool :=
  match e with
  | EFree _ => false
  | _ => true
  end.

Fixpoint calls (t : list ev) : nat :=
  match t with
  | [] => 0%nat
  | e :: r => if is_call e then S (calls r) else calls r
  end.

Definition held_ev (e : ev) : Z :=
  match e with
  | EAlloc n => Z.of_nat n
  | EGrow m n => Z.of_nat n - Z.of_nat m
  | EFail _ => 0
  | EFree n => - Z.of_nat n
  end.

Fixpoint held (t : list ev) : Z :=
  match t with
  | [] => 0
  | e :: r => held_ev e + held r
  end.

Definition M (A : Type) : Type := list bool -> option A * list ev * list bool.

Definition jret {A : Type} (a : A) : M A := fun ok => (Some a, [], ok).

Definition jrefuse {A : Type} : M A := fun ok => (None, [], ok).

Definition jbind {A B : Type} (m : M A) (k : A -> M B) : M B :=
  fun ok =>
    match m ok with
    | (Some a, t, ok1) => match k a ok1 with (r, t', ok2) => (r, t ++ t', ok2) end
    | (None, t, ok1) => (None, t, ok1)
    end.

Definition take (ok : list bool) : bool * list bool :=
  match ok with
  | [] => (true, [])
  | b :: r => (b, r)
  end.

Definition jalloc (n : nat) : M unit :=
  fun ok => let (b, ok1) := take ok in
    if b then (Some tt, [EAlloc n], ok1) else (None, [EFail n], ok1).

Definition jrealloc (m n : nat) : M unit :=
  fun ok => let (b, ok1) := take ok in
    if b then (Some tt, [EGrow m n], ok1) else (None, [EFail n], ok1).

Definition jfree (n : nat) : M unit := fun ok => (Some tt, [EFree n], ok).

Definition jr_string (x : list Z) : M (list Z * list Z) :=
  match scan x with
  | None => jrefuse
  | Some q =>
    jbind (jalloc (S q)) (fun _ =>
      match decode x with
      | Some sr => jret sr
      | None => jbind (jfree (S q)) (fun _ => jrefuse)
      end)
  end.

Definition w_true : list Z := [116; 114; 117; 101].
Definition w_false : list Z := [102; 97; 108; 115; 101].
Definition w_null : list Z := [110; 117; 108; 108].

Definition lit (w : list Z) (v : jv) (x : list Z) : M (jv * list Z) :=
  if prefixb w x then jret (v, skipn (length w) x) else jrefuse.

Definition grow (o : bool) (n cap : nat) : M nat :=
  if Nat.ltb n cap then jret cap
  else
    let cap' := if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat in
    jbind (jrealloc (56 * cap) (56 * cap')) (fun _ =>
      if o then jbind (jrealloc (8 * cap) (8 * cap')) (fun _ => jret cap') else jret cap').

Definition closer (o : bool) : Z := if o then 125 else 93.

Definition mk (o : bool) (acc : list (list Z * jv)) : jv :=
  if o then JObj acc else JArr (map snd acc).

Definition sblock (z : list Z) : nat :=
  match scan z with
  | Some q => S q
  | None => 0%nat
  end.

Definition jr_name (o : bool) (y : list Z) : M (list Z * list Z) :=
  if o then
    match skip y with
    | b :: z =>
      if b =? 34 then
        jbind (jr_string z) (fun '(name, r) =>
          match skip r with
          | c :: r1 => if c =? 58 then jret (name, r1) else jbind (jfree (sblock z)) (fun _ => jrefuse)
          | [] => jbind (jfree (sblock z)) (fun _ => jrefuse)
          end)
      else jrefuse
    | [] => jrefuse
    end
  else jret ([], y).

Definition jr_cont
  (loop : nat -> bool -> nat -> nat -> list (list Z * jv) -> list Z -> M (jv * list Z))
  (d : nat) (o : bool) (x : list Z) : M (jv * list Z) :=
  if Nat.ltb MAXD (S d) then jrefuse
  else
    let y := skip (tl x) in
    match y with
    | c :: r => if c =? closer o then jret (mk o [], r) else loop (S d) o 0%nat 0%nat [] y
    | [] => loop (S d) o 0%nat 0%nat [] y
    end.

Section Reader.

Variable strtod_model : list Z -> Z * Z.

Definition whole (txt : list Z) : bool :=
  (fst (strtod_model txt) =? Z.of_nat (length txt)) && finite (snd (strtod_model txt)).

Definition jr_number (x : list Z) : M (jv * list Z) :=
  let j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end in
  match skipn j x with
  | [] => jrefuse
  | c :: z =>
    if negb (digit c) then jrefuse
    else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then jrefuse
    else
      let (a, r) := span numch z in
      let txt := firstn j x ++ c :: a in
      jbind (jalloc (S (length txt))) (fun _ =>
        if whole txt then jret (JNum txt (snd (strtod_model txt)), r) else jrefuse)
  end.

Fixpoint jrv (fuel d : nat) (x : list Z) {struct fuel} : M (jv * list Z) :=
  match fuel with
  | O => jrefuse
  | S f =>
    match skip x with
    | [] => jrefuse
    | b :: y =>
      if b =? 123 then jr_cont (jrl f) d true (b :: y)
      else if b =? 91 then jr_cont (jrl f) d false (b :: y)
      else if b =? 34 then jbind (jr_string y) (fun '(s, r) => jret (JStr s, r))
      else if b =? 116 then lit w_true JTrue (b :: y)
      else if b =? 102 then lit w_false JFalse (b :: y)
      else if b =? 110 then lit w_null JNull (b :: y)
      else jr_number (b :: y)
    end
  end
with jrl (fuel d : nat) (o : bool) (n cap : nat) (acc : list (list Z * jv)) (y : list Z)
  {struct fuel} : M (jv * list Z) :=
  match fuel with
  | O => jrefuse
  | S f =>
    jbind (grow o n cap) (fun cap1 =>
    jbind (jr_name o y) (fun '(name, y1) =>
    jbind (jrv f d y1) (fun '(v, r) =>
    match skip r with
    | c :: r1 =>
      if c =? 44 then jrl f d o (S n) cap1 ((name, v) :: acc) r1
      else if c =? closer o then jret (mk o (rev ((name, v) :: acc)), r1)
      else jrefuse
    | [] => jrefuse
    end)))
  end.

Definition jr_value (d : nat) (x : list Z) : M (jv * list Z) := jrv (S (2 * length x)) d x.

Definition jr_items (d : nat) (o : bool) (x : list Z) : M (jv * list Z) :=
  jr_cont (jrl (2 * length x + 2)) d o x.

Definition jr_run (x : list Z) (ok : list bool) : option jv * list ev :=
  match jr_value 0 x ok with
  | (Some (t, r), tr, _) => (match skip r with [] => Some t | _ :: _ => None end, tr)
  | (None, tr, _) => (None, tr)
  end.

Definition json_read (x : list Z) : option jv := fst (jr_run x []).

Definition ncalls (x : list Z) : nat := calls (snd (jr_run x [])).


Ltac zb := repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ || _)%bool = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  end.

Lemma some_inj : forall (A : Type) (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H. auto. Qed.

Lemma pair_inj : forall (A B : Type) (a a' : A) (b b' : B), (a, b) = (a', b') -> a = a' /\ b = b'.
Proof. intros A B a a' b b' H. injection H. auto. Qed.

Ltac sinj H := apply some_inj in H; apply pair_inj in H; let H1 := fresh in let H2 := fresh in destruct H as [H1 H2].

Lemma skip_len : forall x, (length (skip x) <= length x)%nat.
Proof.
  induction x as [|b r IH]; simpl; [lia|].
  destruct (ws b); simpl; lia.
Qed.

Lemma scan_quote : forall x q, scan x = Some q -> (q < length x)%nat /\ nth q x 0 = 34.
Proof.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn q H.
  destruct x as [|b r]; [discriminate|]. cbn [scan] in H.
  destruct (b =? 34) eqn:E34.
  - inversion H; subst. zb. subst b. simpl. split; [lia|reflexivity].
  - destruct (b =? 92) eqn:E92.
    + destruct r as [|e r2]; [discriminate|].
      destruct (scan r2) as [q2|] eqn:Es; [|discriminate]. simpl in H. injection H as <-.
      simpl in Hn.
      destruct (IH (length r2) ltac:(lia) r2 eq_refl q2 Es) as [H1 H2].
      simpl. split; [lia|exact H2].
    + destruct (scan r) as [q1|] eqn:Es; [|discriminate]. simpl in H. injection H as <-.
      simpl in Hn.
      destruct (IH (length r) ltac:(lia) r eq_refl q1 Es) as [H1 H2].
      simpl. split; [lia|exact H2].
Qed.

Lemma scan_ndq : forall b r, b <> 34 -> b <> 92 -> scan (b :: r) = option_map S (scan r).
Proof.
  intros b r H1 H2. cbn [scan].
  destruct (b =? 34) eqn:E1; zb; [contradiction|].
  destruct (b =? 92) eqn:E2; zb; [contradiction|]. reflexivity.
Qed.

Lemma scan_bs : forall e r, scan (92 :: e :: r) = option_map (fun q => S (S q)) (scan r).
Proof. reflexivity. Qed.

Lemma hexval_some : forall b v, hexval b = Some v -> b <> 34 /\ b <> 92 /\ 0 <= v < 16.
Proof.
  intros b v H. unfold hexval in H.
  destruct ((48 <=? b) && (b <=? 57)) eqn:E1; [inversion H; subst; zb; lia|].
  destruct ((97 <=? b) && (b <=? 102)) eqn:E2; [inversion H; subst; zb; lia|].
  destruct ((65 <=? b) && (b <=? 70)) eqn:E3; [inversion H; subst; zb; lia|].
  discriminate.
Qed.

Lemma hex4_some : forall z v, hex4 z = Some v ->
  exists a b c d r, z = a :: b :: c :: d :: r /\
    a <> 34 /\ a <> 92 /\ b <> 34 /\ b <> 92 /\ c <> 34 /\ c <> 92 /\ d <> 34 /\ d <> 92 /\
    0 <= v < 65536.
Proof.
  intros z v H. destruct z as [|a [|b [|c [|d r]]]]; try discriminate.
  unfold hex4 in H.
  destruct (hexval a) as [va|] eqn:Ha; [|discriminate].
  destruct (hexval b) as [vb|] eqn:Hb; [|discriminate].
  destruct (hexval c) as [vc|] eqn:Hc; [|discriminate].
  destruct (hexval d) as [vd|] eqn:Hd; [|discriminate].
  change (Some (4096 * va + 256 * vb + 16 * vc + vd) = Some v) in H. apply some_inj in H.
  apply hexval_some in Ha, Hb, Hc, Hd.
  exists a, b, c, d, r. split; [reflexivity|lia].
Qed.

Lemma hex4_quote : forall z k, (k < 4)%nat -> nth k z 0 = 34 -> hex4 z = None.
Proof.
  intros z k Hk H. destruct z as [|a [|b [|c [|d r]]]]; try reflexivity.
  unfold hex4.
  destruct k as [|[|[|[|k]]]]; simpl in H; subst; [| | | |lia];
  repeat match goal with |- context [hexval ?v] => is_var v; destruct (hexval v) end;
  reflexivity.
Qed.

Lemma low_some : forall z lo, low z = Some lo ->
  exists m0 m1 m2 m3 r, z = 92 :: 117 :: m0 :: m1 :: m2 :: m3 :: r /\
    m0 <> 34 /\ m0 <> 92 /\ m1 <> 34 /\ m1 <> 92 /\ m2 <> 34 /\ m2 <> 92 /\ m3 <> 34 /\ m3 <> 92 /\
    56320 <= lo <= 57343.
Proof.
  intros z lo H. destruct z as [|b1 [|b2 r]]; try discriminate.
  unfold low in H.
  destruct ((b1 =? 92) && (b2 =? 117)) eqn:E; [|discriminate]. zb. subst.
  destruct (hex4 r) as [v|] eqn:Hx; [|discriminate].
  destruct ((56320 <=? v) && (v <=? 57343)) eqn:E2; [|discriminate].
  inversion H; subst. zb.
  destruct (hex4_some r lo Hx) as (a & b & c & d & r' & -> & Hn).
  exists a, b, c, d, r'. split; [reflexivity|lia].
Qed.

Lemma low_quote : forall z k, (k < 6)%nat -> nth k z 0 = 34 -> low z = None.
Proof.
  intros z k Hk H. destruct z as [|b1 [|b2 r]]; try reflexivity.
  unfold low.
  destruct k as [|[|k]].
  - simpl in H; subst. reflexivity.
  - simpl in H; subst. destruct (b1 =? 92); reflexivity.
  - simpl in H. rewrite (hex4_quote r k ltac:(lia) H).
    destruct ((b1 =? 92) && (b2 =? 117)); reflexivity.
Qed.

Lemma hex4_cons4 : forall a b c d r, hex4 (a :: b :: c :: d :: r) = hex4 [a; b; c; d].
Proof. reflexivity. Qed.

Lemma low_cons6 : forall a b c d e f r, low (a :: b :: c :: d :: e :: f :: r) = low [a; b; c; d; e; f].
Proof. reflexivity. Qed.

Definition zbyte (b : Z) : Prop := 0 < b < 256.

Lemma pair_cp_range : forall hi lo, 55296 <= hi /\ hi < 56320 -> 56320 <= lo <= 57343 -> 0 < pair_cp hi lo <= 1114111.
Proof. intros hi lo H1 H2. unfold pair_cp. lia. Qed.

Lemma utf8_bytes : forall cp, 0 < cp <= 1114111 -> Forall zbyte (utf8 cp).
Proof.
  intros cp H. unfold utf8, zbyte.
  destruct (cp <? 128) eqn:E1; zb; [repeat constructor; lia|].
  destruct (cp <? 2048) eqn:E2; zb.
  { repeat constructor; Z.div_mod_to_equations; lia. }
  destruct (cp <? 65536) eqn:E3; zb.
  { repeat constructor; Z.div_mod_to_equations; lia. }
  repeat constructor; Z.div_mod_to_equations; lia.
Qed.

Lemma utf8_len : forall cp, (length (utf8 cp) <= (if Z.ltb cp 65536 then 3 else 4))%nat.
Proof.
  intros cp. unfold utf8.
  destruct (cp <? 128) eqn:E1; zb; [destruct (cp <? 65536); simpl; lia|].
  destruct (cp <? 2048) eqn:E2; zb; [destruct (cp <? 65536); simpl; lia|].
  destruct (cp <? 65536) eqn:E3; simpl; lia.
Qed.

Lemma escape_some : forall e c, escape e = Some c -> zbyte c.
Proof.
  intros e c H. unfold escape, zbyte in *.
  repeat match type of H with
  | context [if ?t then _ else _] => destruct t
  end; inversion H; subst; lia.
Qed.

Lemma Forall_zbyte_no0 : forall s, Forall zbyte s -> ~ In 0 s.
Proof.
  intros s H Hin. rewrite Forall_forall in H. apply H in Hin. unfold zbyte in Hin. lia.
Qed.

Definition zbyte0 (b : Z) : Prop := 0 <= b < 256.

Lemma decode_stop : forall x s r, decode x = Some (s, r) ->
  exists q, scan x = Some q /\ r = skipn (S q) x /\ (length s <= q)%nat /\
    (Forall zbyte0 x -> Forall zbyte s) /\ Forall (fun b => b <> 0) s.
Proof.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn s r H.
  destruct x as [|b r0]; [discriminate|]. cbn [decode] in H.
  destruct (b =? 34) eqn:E34.
  - sinj H. subst s r. exists 0%nat. cbn [scan]. rewrite E34.
    split; [reflexivity|]. split; [reflexivity|]. split; [simpl; lia|].
    split; [intros _; constructor|constructor].
  - destruct (b <? 32) eqn:E32; [discriminate|].
    destruct (negb (b =? 92)) eqn:E92.
    + destruct (decode r0) as [[s1 r1]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
      simpl in Hn. destruct (IH (length r0) ltac:(lia) r0 eq_refl s1 r1 Hd) as (q1 & Hs & Hr & Hl & Hb & Hz).
      zb. exists (S q1). rewrite scan_ndq by lia. rewrite Hs.
      split; [reflexivity|]. split; [exact Hr|]. split; [simpl; lia|].
      split.
      * intros Hx. inversion Hx; subst. constructor; [unfold zbyte, zbyte0 in *; lia|auto].
      * constructor; [lia|exact Hz].
    + zb. subst b.
      destruct r0 as [|e r2]; [discriminate|].
      destruct (e =? 117) eqn:Eu.
      * zb. subst e.
        destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; try discriminate.
        destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hx; [|discriminate].
        destruct (hex4_some _ _ Hx) as (a0 & a1 & a2 & a3 & r' & Heq & N0 & N0' & N1 & N1' & N2 & N2' & N3 & N3' & Hcp).
        inversion Heq; subst a0 a1 a2 a3 r'. clear Heq.
        destruct (cp =? 0) eqn:Ec0; [discriminate|]. zb.
        destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Ehi.
        -- zb. destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; try discriminate.
           destruct (low (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4)) as [lo|] eqn:Hl; [|discriminate].
           destruct (low_some _ _ Hl) as (n0 & n1 & n2 & n3 & r'' & Heq & M0 & M0' & M1 & M1' & M2 & M2' & M3 & M3' & Hlo).
           inversion Heq; subst b1 b2 n0 n1 n2 n3 r''. clear Heq.
           destruct (decode r4) as [[s4 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
           simpl in Hn.
           destruct (IH (length r4) ltac:(lia) r4 eq_refl s4 r5 Hd) as (q4 & Hs & Hr & Hlen & Hb & Hz).
           exists (12 + q4)%nat.
           rewrite scan_bs. rewrite !scan_ndq by assumption. rewrite scan_bs. rewrite !scan_ndq by assumption.
           rewrite Hs. split; [reflexivity|]. split; [exact Hr|].
           pose proof (utf8_len (pair_cp cp lo)) as HL.
           pose proof (utf8_bytes (pair_cp cp lo) (pair_cp_range cp lo ltac:(split; assumption) Hlo)) as HB.
           split; [rewrite length_app; destruct (_ <? 65536); simpl in HL; lia|].
           split.
           ++ intros HX. apply Forall_app. split; [exact HB|].
              apply Hb. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end; auto.
           ++ apply Forall_app. split; [|exact Hz].
              eapply Forall_impl; [|exact HB]. unfold zbyte. intros; lia.
        -- destruct ((56320 <=? cp) && (cp <? 57344)) eqn:Elo; [discriminate|].
           destruct (decode r3) as [[s3 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
           simpl in Hn.
           destruct (IH (length r3) ltac:(lia) r3 eq_refl s3 r5 Hd) as (q3 & Hs & Hr & Hlen & Hb & Hz).
           exists (6 + q3)%nat.
           rewrite scan_bs. rewrite !scan_ndq by assumption.
           rewrite Hs. split; [reflexivity|]. split; [exact Hr|].
           pose proof (utf8_len cp) as HL.
           pose proof (utf8_bytes cp ltac:(lia)) as HB.
           assert (Hc : (cp <? 65536) = true) by (apply Z.ltb_lt; lia).
           rewrite Hc in HL.
           split; [rewrite length_app; lia|].
           split.
           ++ intros HX. apply Forall_app. split; [exact HB|].
              apply Hb. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end; auto.
           ++ apply Forall_app. split; [|exact Hz].
              eapply Forall_impl; [|exact HB]. unfold zbyte. intros; lia.
      * destruct (escape e) as [c|] eqn:He; [|discriminate].
        destruct (decode r2) as [[s2 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
        simpl in Hn.
        destruct (IH (length r2) ltac:(lia) r2 eq_refl s2 r5 Hd) as (q2 & Hs & Hr & Hlen & Hb & Hz).
        pose proof (escape_some e c He) as Hc.
        exists (S (S q2)). rewrite scan_bs, Hs.
        split; [reflexivity|]. split; [exact Hr|]. split; [simpl; lia|].
        split.
        -- intros HX. constructor; [exact Hc|].
           apply Hb. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end; auto.
        -- constructor; [unfold zbyte in Hc; lia|exact Hz].
Qed.

Lemma nth_firstn_app : forall (l y : list Z) k m, (k < m)%nat -> (m <= length l)%nat ->
  nth k (firstn m l ++ y) 0 = nth k l 0.
Proof.
  intros l y k m H1 H2. rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite nth_firstn. destruct (Nat.ltb k m) eqn:E; zb; [reflexivity|lia].
Qed.

Lemma emit_local : forall bs (d : option (list Z * list Z)) y,
  emit bs (option_map (fun p => (fst p, y)) d) = option_map (fun p => (fst p, y)) (emit bs d).
Proof. intros bs [[s r]|] y; reflexivity. Qed.

Lemma decode_local : forall x q y, scan x = Some q ->
  decode (firstn (S q) x ++ y) = option_map (fun p => (fst p, y)) (decode x).
Proof.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn q y H.
  destruct x as [|b r0]; [discriminate|].
  pose proof (scan_quote _ _ H) as [Hq Hnth].
  cbn [scan] in H.
  destruct (b =? 34) eqn:E34.
  - injection H as <-. change (firstn 1 (b :: r0) ++ y) with (b :: y). cbn [decode]. rewrite E34. reflexivity.
  - destruct (b =? 92) eqn:E92.
    + zb. subst b.
      destruct r0 as [|e r2]; [discriminate|].
      destruct (scan r2) as [q2|] eqn:Es; [|discriminate]. simpl in H. inversion H; subst q. clear H.
      pose proof (scan_quote _ _ Es) as [Hq2 Hn2].
      simpl in Hn.
      change (firstn (S (S (S q2))) (92 :: e :: r2) ++ y) with (92 :: e :: (firstn (S q2) r2 ++ y)).
      cbn [decode]. try change (92 =? 34) with false. try change (92 <? 32) with false. try change (negb (92 =? 92)) with false. cbv beta iota.
      destruct (e =? 117) eqn:Eu.
      * destruct (Nat.ltb q2 4) eqn:E4; zb.
        -- assert (Hw : nth q2 (firstn (S q2) r2 ++ y) 0 = 34) by (rewrite nth_firstn_app by lia; exact Hn2).
           remember (firstn (S q2) r2 ++ y) as w eqn:Ew.
           assert (L : forall (z : list Z), nth q2 z 0 = 34 ->
             match z with
             | _ :: _ :: _ :: _ :: r3 =>
               match hex4 z with
               | None => None
               | Some cp =>
                 if cp =? 0 then None
                 else if (55296 <=? cp) && (cp <? 56320) then
                   match r3 with
                   | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
                     match low r3 with
                     | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
                     | None => None
                     end
                   | _ => None
                   end
                 else if (56320 <=? cp) && (cp <? 57344) then None
                 else emit (utf8 cp) (decode r3)
               end
             | _ => None
             end = None).
           { intros z Hz. destruct z as [|a1 [|a2 [|a3 [|a4 z']]]]; try reflexivity.
             rewrite (hex4_quote _ q2 E4 Hz). reflexivity. }
           rewrite (L w Hw), (L r2 Hn2). reflexivity.
        -- destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; simpl in Hq2; try lia.
           destruct q2 as [|[|[|[|q3]]]]; try lia.
           change (firstn (S (S (S (S (S q3))))) (h0 :: h1 :: h2 :: h3 :: r3) ++ y)
             with (h0 :: h1 :: h2 :: h3 :: (firstn (S q3) r3 ++ y)).
           rewrite (hex4_cons4 h0 h1 h2 h3 r3), (hex4_cons4 h0 h1 h2 h3 (firstn (S q3) r3 ++ y)).
           destruct (hex4 [h0; h1; h2; h3]) as [cp|] eqn:Hx; [|reflexivity].
           destruct (hex4_some _ _ Hx) as (a0 & a1 & a2 & a3 & r' & Heq & N0 & N0' & N1 & N1' & N2 & N2' & N3 & N3' & Hcp).
           inversion Heq; subst a0 a1 a2 a3 r'. clear Heq.
           rewrite !scan_ndq in Es by assumption.
           destruct (scan r3) as [q3'|] eqn:Es3; [|discriminate]. simpl in Es. inversion Es; subst q3'. clear Es.
           pose proof (scan_quote _ _ Es3) as [Hq3 Hn3].
           destruct (cp =? 0); [reflexivity|].
           destruct ((55296 <=? cp) && (cp <? 56320)).
           ++ destruct (Nat.ltb q3 6) eqn:E6; zb.
              ** assert (Hw : nth q3 (firstn (S q3) r3 ++ y) 0 = 34) by (rewrite nth_firstn_app by lia; exact Hn3).
                 remember (firstn (S q3) r3 ++ y) as w eqn:Ew.
                 assert (L : forall (z : list Z), nth q3 z 0 = 34 ->
                   match z with
                   | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
                     match low z with
                     | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
                     | None => None
                     end
                   | _ => None
                   end = None).
                 { intros z Hz. destruct z as [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 z']]]]]]; try reflexivity.
                   rewrite (low_quote _ q3 E6 Hz). reflexivity. }
                 rewrite (L w Hw), (L r3 Hn3). reflexivity.
              ** destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; simpl in Hq3; try lia.
                 destruct q3 as [|[|[|[|[|[|q4]]]]]]; try lia.
                 change (firstn (S (S (S (S (S (S (S q4))))))) (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4) ++ y)
                   with (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: (firstn (S q4) r4 ++ y)).
                 rewrite (low_cons6 b1 b2 m0 m1 m2 m3 r4), (low_cons6 b1 b2 m0 m1 m2 m3 (firstn (S q4) r4 ++ y)).
                 destruct (low [b1; b2; m0; m1; m2; m3]) as [lo|] eqn:Hl; [|reflexivity].
                 destruct (low_some _ _ Hl) as (n0 & n1 & n2 & n3 & r'' & Heq & M0 & M0' & M1 & M1' & M2 & M2' & M3 & M3' & Hlo).
                 inversion Heq; subst b1 b2 n0 n1 n2 n3 r''. clear Heq.
                 rewrite scan_bs in Es3. rewrite !scan_ndq in Es3 by assumption.
                 destruct (scan r4) as [q4'|] eqn:Es4; [|discriminate]. simpl in Es3. inversion Es3; subst q4'.
                 simpl in Hn.
                 rewrite (IH (length r4) ltac:(lia) r4 eq_refl q4 y Es4).
                 apply emit_local.
           ++ destruct ((56320 <=? cp) && (cp <? 57344)); [reflexivity|].
              simpl in Hn.
              rewrite (IH (length r3) ltac:(lia) r3 eq_refl q3 y Es3).
              apply emit_local.
      * destruct (escape e) as [c|]; [|reflexivity].
        rewrite (IH (length r2) ltac:(lia) r2 eq_refl q2 y Es).
        apply emit_local.
    + destruct (scan r0) as [q1|] eqn:Es; [|discriminate]. simpl in H. inversion H; subst q. clear H.
      simpl in Hn.
      change (firstn (S (S q1)) (b :: r0) ++ y) with (b :: (firstn (S q1) r0 ++ y)).
      cbn [decode]. rewrite E34, E92. simpl negb.
      destruct (b <? 32); [reflexivity|].
      rewrite (IH (length r0) ltac:(lia) r0 eq_refl q1 y Es).
      apply emit_local.
Qed.

Theorem G1_4 : forall x s r, decode x = Some (s, r) ->
  exists q, scan x = Some q /\ r = skipn (S q) x /\ (length s <= q)%nat /\ ~ In 0 s.
Proof.
  intros x s r H. destruct (decode_stop x s r H) as (q & H1 & H2 & H3 & _ & H5).
  exists q. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros Hin. rewrite Forall_forall in H5. exact (H5 0 Hin eq_refl).
Qed.

Theorem G1_4_local : forall x q y, scan x = Some q ->
  decode (firstn (S q) x ++ y) = option_map (fun p => (fst p, y)) (decode x).
Proof. exact decode_local. Qed.

Theorem G1_4_bytes : forall x s r, Forall (fun b => 0 <= b < 256) x -> decode x = Some (s, r) ->
  Forall (fun b => 0 < b < 256) s.
Proof.
  intros x s r Hx H. destruct (decode_stop x s r H) as (q & _ & _ & _ & H4 & _). exact (H4 Hx).
Qed.

Lemma calls_app : forall a b, calls (a ++ b) = (calls a + calls b)%nat.
Proof. induction a as [|e r IH]; intros b; simpl; [reflexivity|]. destruct (is_call e); rewrite IH; reflexivity. Qed.

Lemma held_app : forall a b, held (a ++ b) = held a + held b.
Proof. induction a as [|e r IH]; intros b; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Definition ok_upto (ok : list bool) (k : nat) : Prop := forall i, (i < k)%nat -> nth i ok true = true.

Definition esize (e : ev) : nat :=
  match e with
  | EAlloc n => n
  | EGrow _ n => n
  | EFail n => n
  | EFree n => n
  end.

Definition agrees {A : Type} (m : M A) : Prop :=
  forall ok,
    (ok_upto ok (calls (snd (fst (m [])))) ->
       m ok = (fst (fst (m [])), snd (fst (m [])), skipn (calls (snd (fst (m [])))) ok)) /\
    (forall j, (j < calls (snd (fst (m []))))%nat -> nth j ok true = false -> ok_upto ok j ->
       exists P E rest, m ok = (None, P ++ [EFail (esize E)], skipn (S j) ok) /\
         snd (fst (m [])) = P ++ E :: rest /\ calls P = j /\ is_call E = true).

Lemma ok_upto_nil : forall k, ok_upto [] k.
Proof. intros k i _. destruct i; reflexivity. Qed.

Lemma ok_upto_le : forall ok k j, ok_upto ok k -> (j <= k)%nat -> ok_upto ok j.
Proof. intros ok k j H Hj i Hi. apply H. lia. Qed.

Lemma nth_skipn_b : forall (ok : list bool) a i, nth i (skipn a ok) true = nth (a + i) ok true.
Proof.
  induction ok as [|b r IH]; intros a i.
  - rewrite skipn_nil. assert (N : forall k, nth k (@nil bool) true = true) by (intros [|k]; reflexivity).
    rewrite !N. reflexivity.
  - destruct a as [|a]; [reflexivity|]. simpl. apply IH.
Qed.

Lemma skipn_skipn_b : forall (ok : list bool) a b, skipn a (skipn b ok) = skipn (b + a) ok.
Proof.
  induction ok as [|x r IH]; intros a b.
  - rewrite !skipn_nil. reflexivity.
  - destruct b as [|b]; [reflexivity|]. simpl. apply IH.
Qed.

Lemma ok_upto_skipn : forall ok a b, ok_upto ok (a + b) -> ok_upto (skipn a ok) b.
Proof. intros ok a b H i Hi. rewrite nth_skipn_b. apply H. lia. Qed.

Lemma ok_upto_dec : forall ok k, ok_upto ok k \/ exists j, (j < k)%nat /\ nth j ok true = false /\ ok_upto ok j.
Proof.
  intros ok k. induction k as [|k IH].
  - left. intros i Hi. lia.
  - destruct IH as [H|(j & Hj & Hf & Hu)].
    + destruct (nth k ok true) eqn:E.
      * left. intros i Hi. destruct (Nat.eq_dec i k) as [->|Hne]; [exact E|apply H; lia].
      * right. exists k. auto.
    + right. exists j. split; [lia|auto].
Qed.

Lemma agrees_nil : forall A (m : M A), agrees m -> m [] = (fst (fst (m [])), snd (fst (m [])), []).
Proof.
  intros A m H. pose proof (proj1 (H []) (ok_upto_nil _)) as E. rewrite skipn_nil in E. exact E.
Qed.

Lemma agrees_some : forall A (m : M A) ok a t ok', agrees m -> m ok = (Some a, t, ok') ->
  m [] = (Some a, t, []) /\ ok' = skipn (calls t) ok.
Proof.
  intros A m ok a t ok' H E.
  destruct (ok_upto_dec ok (calls (snd (fst (m []))))) as [Hu|(j & Hj & Hf & Hu)].
  - pose proof (proj1 (H ok) Hu) as E2. rewrite E in E2.
    pose proof (agrees_nil A m H) as N. rewrite N.
    injection E2 as E3 E4 E5. rewrite <- E3, <- E4. split; [reflexivity|]. rewrite E4. exact E5.
  - destruct (proj2 (H ok) j Hj Hf Hu) as (P & e & rest & E2 & _). rewrite E in E2. discriminate.
Qed.

Lemma agrees_ret : forall A (a : A), agrees (jret a).
Proof.
  intros A a ok. simpl. split.
  - intros _. reflexivity.
  - intros j Hj. lia.
Qed.

Lemma agrees_refuse : forall A, agrees (@jrefuse A).
Proof.
  intros A ok. simpl. split.
  - intros _. reflexivity.
  - intros j Hj. lia.
Qed.

Lemma agrees_free : forall n, agrees (jfree n).
Proof.
  intros n ok. simpl. split.
  - intros _. reflexivity.
  - intros j Hj. lia.
Qed.

Lemma agrees_alloc : forall n, agrees (jalloc n).
Proof.
  intros n ok. simpl. split.
  - intros Hu. destruct ok as [|b r]; [reflexivity|].
    pose proof (Hu 0%nat ltac:(lia)) as Hb. simpl in Hb. subst b. reflexivity.
  - intros j Hj Hf _. assert (j = 0%nat) by lia. subst j.
    destruct ok as [|b r]; [discriminate|]. simpl in Hf. subst b.
    exists [], (EAlloc n), []. simpl. auto.
Qed.

Lemma agrees_realloc : forall m n, agrees (jrealloc m n).
Proof.
  intros m n ok. simpl. split.
  - intros Hu. destruct ok as [|b r]; [reflexivity|].
    pose proof (Hu 0%nat ltac:(lia)) as Hb. simpl in Hb. subst b. reflexivity.
  - intros j Hj Hf _. assert (j = 0%nat) by lia. subst j.
    destruct ok as [|b r]; [discriminate|]. simpl in Hf. subst b.
    exists [], (EGrow m n), []. simpl. auto.
Qed.

Lemma agrees_bind : forall A B (m : M A) (k : A -> M B),
  agrees m -> (forall a, agrees (k a)) -> agrees (jbind m k).
Proof.
  intros A B m k Hm Hk ok.
  pose proof (agrees_nil A m Hm) as N0.
  destruct (m []) as [[r0 t0] o0] eqn:E0. simpl in N0. injection N0 as Ho0. subst o0.
  pose proof (Hm ok) as [H1 H2]. rewrite E0 in H1, H2. cbn [fst snd] in H1, H2.
  unfold jbind. rewrite E0.
  destruct r0 as [a|].
  - pose proof (agrees_nil B (k a) (Hk a)) as N1.
    destruct (k a []) as [[r1 t1] o1] eqn:E1. simpl in N1. injection N1 as Ho1. subst o1.
    simpl. rewrite calls_app. split.
    + intros Hu.
      assert (Hu0 : ok_upto ok (calls t0)) by (eapply ok_upto_le; [exact Hu|lia]).
      rewrite (H1 Hu0). cbv beta iota.
      pose proof (proj1 (Hk a (skipn (calls t0) ok))) as K1. rewrite E1 in K1. cbn [fst snd] in K1.
      rewrite (K1 (ok_upto_skipn _ _ _ Hu)). rewrite skipn_skipn_b. reflexivity.
    + intros j Hj Hf Hu.
      destruct (Nat.ltb j (calls t0)) eqn:Ej.
      * apply Nat.ltb_lt in Ej.
        destruct (H2 j Ej Hf Hu) as (P & e & rest & Em & Et & Hc & Hic).
        rewrite Em. cbv beta iota. exists P, e, (rest ++ t1). split; [reflexivity|].
        split; [rewrite Et, <- app_assoc; reflexivity|]. auto.
      * apply Nat.ltb_ge in Ej.
        rewrite (H1 (ok_upto_le _ _ _ Hu Ej)). cbv beta iota.
        pose proof (proj2 (Hk a (skipn (calls t0) ok)) (j - calls t0)%nat) as K2.
        rewrite E1 in K2. cbn [fst snd] in K2.
        destruct K2 as (P & e & rest & Ek & Et & Hc & Hic).
        { lia. }
        { rewrite nth_skipn_b. replace (calls t0 + (j - calls t0))%nat with j by lia. exact Hf. }
        { apply ok_upto_skipn. replace (calls t0 + (j - calls t0))%nat with j by lia. exact Hu. }
        rewrite Ek. cbv beta iota. exists (t0 ++ P), e, rest.
        split.
        { rewrite skipn_skipn_b, <- app_assoc. replace (calls t0 + S (j - calls t0))%nat with (S j) by lia.
          reflexivity. }
        split; [rewrite Et, <- app_assoc; reflexivity|].
        split; [rewrite calls_app; lia|exact Hic].
  - simpl. split.
    + intros Hu. rewrite (H1 Hu). reflexivity.
    + intros j Hj Hf Hu. destruct (H2 j Hj Hf Hu) as (P & e & rest & Em & Et & Hc & Hic).
      rewrite Em. cbv beta iota. exists P, e, rest. auto.
Qed.

Definition pos_ev (e : ev) : nat :=
  match e with
  | EAlloc n => n
  | EGrow m n => (n - m)%nat
  | EFail _ => 0%nat
  | EFree _ => 0%nat
  end.

Fixpoint pos (t : list ev) : nat :=
  match t with
  | [] => 0%nat
  | e :: r => (pos_ev e + pos r)%nat
  end.

Lemma pos_app : forall a b, pos (a ++ b) = (pos a + pos b)%nat.
Proof. induction a as [|e r IH]; intros b; cbn [pos app]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma held_le_pos : forall t, held t <= Z.of_nat (pos t).
Proof.
  induction t as [|e r IH]; cbn [held pos]; [lia|].
  destruct e; cbn [held_ev pos_ev]; lia.
Qed.

Lemma pos_prefix : forall p r, (pos p <= pos (p ++ r))%nat.
Proof. intros p r. rewrite pos_app. lia. Qed.

Lemma skipn_len_le : forall (j : nat) (x : list Z), (length (skipn j x) <= length x)%nat.
Proof. intros j x. rewrite length_skipn. lia. Qed.

Lemma span_app : forall p z a r, span p z = (a, r) -> z = a ++ r.
Proof.
  intros p z. induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- <-. reflexivity.
  - destruct (p b).
    + destruct (span p z) as [a1 r1] eqn:E. injection H as <- <-. rewrite (IH a1 r1 eq_refl). reflexivity.
    + injection H as <- <-. reflexivity.
Qed.

Lemma prefixb_app : forall w x, prefixb w x = true -> (length w + length (skipn (length w) x) = length x)%nat.
Proof.
  induction w as [|a w IH]; intros x H; [reflexivity|].
  destruct x as [|b x]; [discriminate|]. cbn [prefixb] in H. zb.
  cbn [length skipn]. specialize (IH x H0). lia.
Qed.

Definition wgt (o : bool) : nat := if o then 64%nat else 56%nat.
Definition slack (o : bool) : nat := if o then 672%nat else 224%nat.
Definition inv (n cap : nat) : Prop := (n <= cap /\ cap <= Nat.max 8 (2 * n) /\ (cap = 0 -> n = 0) /\ (cap = 0 \/ 8 <= cap))%nat.

Lemma grow_spec : forall o n cap ok, inv n cap ->
  match grow o n cap ok with
  | (Some cap1, t, _) =>
    inv (S n) cap1 /\ (n < cap1)%nat /\ (cap1 <= Nat.max 8 (2 * n))%nat /\ (cap <= cap1)%nat /\
    (calls t <= if o then 2 else 1)%nat /\ (pos t + wgt o * cap = wgt o * cap1)%nat
  | (None, t, _) =>
    (calls t <= if o then 2 else 1)%nat /\ (pos t + wgt o * cap <= wgt o * Nat.max 8 (2 * n))%nat
  end.
Proof.
  intros o n cap ok [H1 [H2 [H3 H4]]]. unfold grow.
  destruct (Nat.ltb n cap) eqn:E; zb.
  - unfold jret, inv. cbn [calls pos]. lia.
  - assert (n = cap) by lia. subst n.
    assert (Hc : (if Nat.eqb cap 0 then 8 else 2 * cap)%nat = Nat.max 8 (2 * cap) /\ (cap < Nat.max 8 (2 * cap))%nat).
    { destruct (Nat.eqb cap 0) eqn:E0; zb; [subst cap; simpl; lia|]. lia. }
    destruct Hc as [Hc1 Hc2].
    unfold jbind, jrealloc, take. cbv zeta. rewrite Hc1.
    destruct ok as [|b1 ok]; [|destruct b1]; cbv beta iota.
    + destruct o; cbv beta iota; unfold jret, inv, wgt; cbn [calls pos pos_ev is_call app]; lia.
    + destruct o; cbv beta iota; [destruct ok as [|b2 ok]; [|destruct b2]; cbv beta iota|];
        unfold jret, inv, wgt; cbn [calls pos pos_ev is_call app]; lia.
    + destruct o; unfold wgt; cbn [calls pos pos_ev is_call app]; lia.
Qed.

Lemma jr_string_spec : forall z ok,
  match jr_string z ok with
  | (Some (s, r), t, _) => exists q, scan z = Some q /\ decode z = Some (s, r) /\ t = [EAlloc (S q)] /\
      (length r + S q = length z)%nat
  | (None, t, _) => (calls t <= 1)%nat /\ (calls t <= length z)%nat /\ (pos t <= length z)%nat
  end.
Proof.
  intros z ok. unfold jr_string.
  destruct (scan z) as [q|] eqn:Es.
  - pose proof (scan_quote z q Es) as [Hq _].
    unfold jbind, jalloc, take.
    destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
    + destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
      * exists q. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
        rewrite Hr, length_skipn. lia.
      * unfold jfree, jrefuse. cbn [calls pos pos_ev is_call app]. lia.
    + destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
      * exists q. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        destruct (decode_stop z s r Ed) as (q' & Es' & Hr & _). rewrite Es in Es'. injection Es' as <-.
        rewrite Hr, length_skipn. lia.
      * unfold jfree, jrefuse. cbn [calls pos pos_ev is_call app]. lia.
    + cbn [calls pos pos_ev is_call]. lia.
  - unfold jrefuse. cbn [calls pos]. lia.
Qed.

Lemma jr_name_spec : forall o y ok,
  match jr_name o y ok with
  | (Some (nm, y1), t, _) =>
    if o then exists q, t = [EAlloc (S q)] /\ (length y1 + q + 3 <= length y)%nat
    else t = [] /\ y1 = y
  | (None, t, _) => (calls t <= 1)%nat /\ (calls t <= length y)%nat /\ (pos t <= length y)%nat
  end.
Proof.
  intros o y ok. unfold jr_name. destruct o.
  - destruct (skip y) as [|b z] eqn:Ey.
    + unfold jrefuse. cbn [calls pos]. lia.
    + pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
      destruct (b =? 34) eqn:Eb.
      * unfold jbind at 1.
        pose proof (jr_string_spec z ok) as Hs.
        destruct (jr_string z ok) as [[[[nm r]|] t] ok1] eqn:Ej.
        -- destruct Hs as (q & Hsc & Hd & -> & Hl). cbv beta iota.
           assert (Hb : sblock z = S q) by (unfold sblock; rewrite Hsc; reflexivity).
           destruct (skip r) as [|c r1] eqn:Er.
           ++ unfold jbind, jfree, jrefuse. rewrite Hb. cbn [calls pos pos_ev is_call app]. lia.
           ++ pose proof (skip_len r) as Hr. rewrite Er in Hr. cbn [length] in Hr.
              destruct (c =? 58).
              ** unfold jret. cbn [app]. exists q. split; [reflexivity|]. lia.
              ** unfold jbind, jfree, jrefuse. rewrite Hb. cbn [calls pos pos_ev is_call app]. lia.
        -- destruct Hs as (H1 & H2 & H3). cbn [app]. lia.
      * unfold jrefuse. cbn [calls pos]. lia.
  - unfold jret. split; reflexivity.
Qed.

Lemma lit_spec : forall w v x ok, w <> [] ->
  match lit w v x ok with
  | (Some (u, r), t, _) => t = [] /\ (length r < length x)%nat
  | (None, t, _) => t = []
  end.
Proof.
  intros w v x ok Hw. unfold lit.
  destruct (prefixb w x) eqn:E.
  - unfold jret. split; [reflexivity|]. pose proof (prefixb_app w x E).
    destruct w; [contradiction|]. cbn [length] in *. lia.
  - reflexivity.
Qed.

Lemma jr_number_spec : forall x ok, x <> [] ->
  match jr_number x ok with
  | (Some (u, r), t, _) => exists k, t = [EAlloc (S k)] /\ (1 <= k)%nat /\ (k + length r = length x)%nat
  | (None, t, _) => (calls t <= 1)%nat /\ (pos t <= S (length x))%nat
  end.
Proof.
  intros x ok Hx. unfold jr_number.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end).
  assert (Hj : (j <= length x)%nat).
  { unfold j. destruct x as [|b x']; [contradiction|]. destruct (b =? 45); cbn [length]; lia. }
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez.
  - unfold jrefuse. cbn [calls pos]. lia.
  - destruct (negb (digit c)).
    + unfold jrefuse. cbn [calls pos]. lia.
    + destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end).
      * unfold jrefuse. cbn [calls pos]. lia.
      * destruct (span numch z) as [a r] eqn:Es.
        pose proof (span_app _ _ _ _ Es) as Hz.
        assert (Ht : (length (firstn j x ++ c :: a) + length r = length x)%nat).
        { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk.
          rewrite Hz, length_app in Hsk. lia. }
        assert (Ht1 : (1 <= length (firstn j x ++ c :: a))%nat) by (rewrite length_app; cbn [length]; lia).
        unfold jbind, jalloc, take.
        destruct ok as [|b ok]; [|destruct b]; cbv beta iota.
        -- destruct (whole (firstn j x ++ c :: a)); unfold jret, jrefuse; cbn [app].
           ++ exists (length (firstn j x ++ c :: a)). split; [reflexivity|]. lia.
           ++ cbn [calls pos pos_ev is_call]. lia.
        -- destruct (whole (firstn j x ++ c :: a)); unfold jret, jrefuse; cbn [app].
           ++ exists (length (firstn j x ++ c :: a)). split; [reflexivity|]. lia.
           ++ cbn [calls pos pos_ev is_call]. lia.
        -- cbn [calls pos pos_ev is_call]. lia.
Qed.

Definition vspec (x : list Z) (d : nat) (res : option (jv * list Z) * list ev * list bool) : Prop :=
  (calls (snd (fst res)) <= 2 * length x)%nat /\
  (pos (snd (fst res)) <= 224 * length x + 512 * (MAXD - d))%nat /\
  (forall v r, fst (fst res) = Some (v, r) ->
     (length r < length x)%nat /\
     (calls (snd (fst res)) + 2 * length r <= 2 * length x)%nat /\
     (pos (snd (fst res)) + 224 * length r <= 224 * length x)%nat).

Definition lspec (o : bool) (n cap : nat) (y : list Z) (d : nat)
  (res : option (jv * list Z) * list ev * list bool) : Prop :=
  (calls (snd (fst res)) <= 2 * length y + 2)%nat /\
  (wgt o * cap + pos (snd (fst res)) <= 224 * length y + slack o * n + 736 + 512 * (MAXD - d))%nat /\
  (forall v r, fst (fst res) = Some (v, r) ->
     (length r < length y)%nat /\
     (calls (snd (fst res)) + 2 * length r <= 2 * length y + 2)%nat /\
     (wgt o * cap + pos (snd (fst res)) + 224 * length r <= 224 * length y + slack o * n + 224)%nat).

Lemma vspec_mono : forall x x' d res, (length x' <= length x)%nat -> vspec x' d res -> vspec x d res.
Proof.
  intros x x' d res Hl (H1 & H2 & H3). split; [lia|]. split; [lia|].
  intros v r Hr. destruct (H3 v r Hr) as (A & B & C). lia.
Qed.

Lemma vspec_refuse : forall x d ok, vspec x d (None, [], ok).
Proof. intros x d ok. unfold vspec. cbn [fst snd calls pos]. split; [lia|]. split; [lia|]. intros v r H; discriminate. Qed.

Lemma jr_cont_spec : forall loop d o b y ok,
  (forall o' n cap acc y' ok', inv n cap -> lspec o' n cap y' (S d) (loop (S d) o' n cap acc y' ok')) ->
  vspec (b :: y) d (jr_cont loop d o (b :: y) ok).
Proof.
  intros loop d o b y ok HL. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; zb.
  - apply vspec_refuse.
  - cbn [tl]. pose proof (skip_len y) as Hy.
    assert (Hloop : vspec (b :: y) d (loop (S d) o 0%nat 0%nat [] (skip y) ok)).
    { assert (Hi : inv 0 0) by (unfold inv; lia).
      destruct (HL o 0%nat 0%nat [] (skip y) ok Hi) as (A & B & C).
      unfold vspec, MAXD in *. cbn [length]. split; [lia|]. split; [lia|].
      intros v r Hr. destruct (C v r Hr) as (C1 & C2 & C3). lia. }
    destruct (skip y) as [|c r] eqn:Ey; [exact Hloop|].
    destruct (c =? closer o); [|exact Hloop].
    unfold jret, vspec. cbn [fst snd calls pos length] in *. split; [lia|]. split; [lia|].
    intros v r' Hr. injection Hr as _ <-. lia.
Qed.

Lemma vspec_lit : forall w v x d ok, w <> [] -> vspec x d (lit w v x ok).
Proof.
  intros w v x d ok Hw. pose proof (lit_spec w v x ok Hw) as H.
  destruct (lit w v x ok) as [[[[u r]|] t] ok'].
  - destruct H as [-> Hr]. unfold vspec. cbn [fst snd calls pos].
    split; [lia|]. split; [lia|]. intros v' r' E. injection E as _ <-. lia.
  - subst t. apply vspec_refuse.
Qed.

Lemma vspec_number : forall x d ok, x <> [] -> vspec x d (jr_number x ok).
Proof.
  intros x d ok Hx. pose proof (jr_number_spec x ok Hx) as H.
  assert (Hl : (1 <= length x)%nat) by (destruct x; [contradiction|cbn [length]; lia]).
  destruct (jr_number x ok) as [[[[u r]|] t] ok'].
  - destruct H as (k & -> & Hk & Hkr). unfold vspec. cbn [fst snd calls pos pos_ev is_call].
    split; [lia|]. split; [lia|]. intros v' r' E. injection E as _ <-. lia.
  - destruct H as [H1 H2]. unfold vspec. cbn [fst snd].
    split; [lia|]. split; [lia|]. intros v' r' E. discriminate.
Qed.

Lemma jr_name_ok : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  (calls tn = if o then 1 else 0)%nat /\ (length y1 + pos tn + (if o then 2 else 0) <= length y)%nat /\
  (o = false -> pos tn = 0%nat /\ length y1 = length y).
Proof.
  intros o y ok nm y1 tn ok2 E. pose proof (jr_name_spec o y ok) as H. rewrite E in H.
  destruct o.
  - destruct H as (q & -> & Hq). cbn [calls pos pos_ev is_call]. split; [reflexivity|]. split; [lia|].
    intros; discriminate.
  - destruct H as [-> ->]. cbn [calls pos]. split; [reflexivity|]. split; [lia|]. auto.
Qed.

Ltac dstr := repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  end.

Lemma spec_fuel : forall f,
  (forall d x ok, vspec x d (jrv f d x ok)) /\
  (forall d o n cap acc y ok, inv n cap -> lspec o n cap y d (jrl f d o n cap acc y ok)).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok. apply vspec_refuse.
    + intros d o n cap acc y ok Hi. cbn [jrl]. unfold jrefuse, lspec. cbn [fst snd calls pos].
      unfold inv in Hi. destruct o; unfold wgt, slack; split; try lia; split; try lia; intros v r E; discriminate.
  - split.
    + intros d x ok. cbn [jrv].
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; [apply vspec_refuse|].
      apply (vspec_mono x (b :: y)); [exact Hsx|].
      destruct (b =? 123); [apply jr_cont_spec; intros; apply IHl; assumption|].
      destruct (b =? 91); [apply jr_cont_spec; intros; apply IHl; assumption|].
      destruct (b =? 34).
      * unfold jbind. pose proof (jr_string_spec y ok) as Hs.
        destruct (jr_string y ok) as [[[[s r]|] t] ok1] eqn:Ej.
        -- destruct Hs as (q & _ & _ & -> & Hl). unfold jret. cbn [app]. unfold vspec.
           cbn [fst snd calls pos pos_ev is_call length].
           split; [lia|]. split; [lia|]. intros v r' Hr. injection Hr as _ <-. lia.
        -- destruct Hs as (H1 & H2 & H3). unfold vspec. cbn [fst snd length].
           split; [lia|]. split; [lia|]. intros v r' Hr. discriminate.
      * destruct (b =? 116); [apply vspec_lit; discriminate|].
        destruct (b =? 102); [apply vspec_lit; discriminate|].
        destruct (b =? 110); [apply vspec_lit; discriminate|].
        apply vspec_number. discriminate.
    + intros d o n cap acc y ok Hi. cbn [jrl]. unfold jbind at 1. cbv beta.
      pose proof (grow_spec o n cap ok Hi) as Hg.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1] eqn:Eg.
      2: { unfold lspec, inv in *. cbn [fst snd]. dstr.
           destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
           split; try lia; split; try lia; intros v r Hr; discriminate. }
      destruct Hg as (G1 & G2 & G3 & G4 & G5 & G6).
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (jr_name_spec o y ok1) as Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En.
      2: { destruct Hn as (N1 & N2 & N3). unfold lspec, inv in *. cbn [fst snd]. dstr.
           rewrite calls_app, pos_app.
           destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
           split; try lia; split; try lia; intros v r Hr; discriminate. }
      destruct (jr_name_ok o y ok1 nm y1 tn ok2 En) as (N1 & N2 & N3). clear Hn.
      cbv beta iota. unfold jbind at 1. cbv beta.
      pose proof (IHv d y1 ok2) as Hv.
      destruct (jrv f d y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev;
        unfold vspec in Hv; cbn [fst snd] in Hv; destruct Hv as (V1 & V2 & V3).
      2: { unfold lspec, inv in *. cbn [fst snd]. dstr.
           rewrite !calls_app, !pos_app.
           destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
           split; try lia; split; try lia; intros v r Hr; discriminate. }
      destruct (V3 v r eq_refl) as (V4 & V5 & V6). clear V3.
      cbv beta iota.
      pose proof (skip_len r) as Hsr.
      destruct (skip r) as [|c r1] eqn:Er.
      { unfold jrefuse, lspec, inv in *. cbn [fst snd]. dstr.
        rewrite !calls_app, !pos_app. cbn [calls pos app].
        destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
        split; try lia; split; try lia; intros v' r' Hr; discriminate. }
      cbn [length] in Hsr.
      destruct (c =? 44).
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 G1) as Hl.
        destruct (jrl f d o (S n) cap1 ((nm, v) :: acc) r1 ok3) as [[res t'] ok4] eqn:El.
        cbv beta iota.
        unfold lspec, inv in *. cbn [fst snd] in *. dstr.
        rewrite !calls_app, !pos_app.
        destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
        split; try lia; split; try lia;
        intros v' r' Hr; match goal with H : forall v r, res = Some (v, r) -> _ |- _ =>
          destruct (H v' r' Hr) as (L4 & L5 & L6) end; lia. }
      destruct (c =? closer o).
      { unfold jret, lspec, inv in *. cbn [fst snd]. dstr.
        rewrite !calls_app, !pos_app. cbn [calls pos app].
        destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
        split; try lia; split; try lia; intros v' r' Hr; injection Hr as _ <-; lia. }
      { unfold jrefuse, lspec, inv in *. cbn [fst snd]. dstr.
        rewrite !calls_app, !pos_app. cbn [calls pos app].
        destruct o; cbv iota in *; unfold wgt, slack, MAXD in *;
        split; try lia; split; try lia; intros v' r' Hr; discriminate. }
Qed.

Ltac ag := repeat (cbv beta iota zeta; match goal with
  | |- agrees (jbind _ _) => apply agrees_bind
  | |- forall p : (_ * _), _ => intros [? ?]
  | |- forall _, _ => intros ?
  | |- agrees (jret _) => apply agrees_ret
  | |- agrees jrefuse => apply agrees_refuse
  | |- agrees (jalloc _) => apply agrees_alloc
  | |- agrees (jrealloc _ _) => apply agrees_realloc
  | |- agrees (jfree _) => apply agrees_free
  | |- agrees (jr_cont _ _ _ _) => unfold jr_cont
  | H : forall d x, agrees (jrv _ d x) |- agrees (jrv _ _ _) => apply H
  | H : forall d o n cap acc y, agrees (jrl _ d o n cap acc y) |- agrees (jrl _ _ _ _ _ _ _) => apply H
  | H : forall z, agrees (jr_string z) |- agrees (jr_string _) => apply H
  | |- agrees (match ?t with _ => _ end) => destruct t
  end).

Lemma agrees_jr_string : forall z, agrees (jr_string z).
Proof. intros z. unfold jr_string. ag. Qed.

Lemma agrees_grow : forall o n cap, agrees (grow o n cap).
Proof. intros o n cap. unfold grow. ag. Qed.

Lemma agrees_jr_name : forall o y, agrees (jr_name o y).
Proof. pose proof agrees_jr_string. intros o y. unfold jr_name. ag. Qed.

Lemma agrees_lit : forall w v x, agrees (lit w v x).
Proof. intros w v x. unfold lit. ag. Qed.

Lemma agrees_jr_number : forall x, agrees (jr_number x).
Proof. intros x. unfold jr_number. ag. Qed.

Lemma agrees_fuel : forall f,
  (forall d x, agrees (jrv f d x)) /\ (forall d o n cap acc y, agrees (jrl f d o n cap acc y)).
Proof.
  pose proof agrees_jr_string.
  induction f as [|f [IHv IHl]].
  - split; intros; apply agrees_refuse.
  - split.
    + intros d x. cbn [jrv]. ag; first [apply agrees_lit | apply agrees_jr_number].
    + intros d o n cap acc y. cbn [jrl]. ag; first [apply agrees_grow | apply agrees_jr_name].
Qed.

Lemma fuel_mono : forall f,
  (forall d x f' ok, (2 * length x + 1 <= f)%nat -> (f <= f')%nat -> jrv f' d x ok = jrv f d x ok) /\
  (forall d o n cap acc y f' ok, (2 * length y + 2 <= f)%nat -> (f <= f')%nat ->
     jrl f' d o n cap acc y ok = jrl f d o n cap acc y ok).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; lia.
  - split.
    + intros d x f' ok H1 H2. destruct f' as [|f']; [lia|]. cbn [jrv].
      pose proof (skip_len x) as Hs.
      destruct (skip x) as [|b y] eqn:Ex; [reflexivity|].
      cbn [length] in Hs.
      assert (Hc : forall o, jr_cont (jrl f') d o (b :: y) ok = jr_cont (jrl f) d o (b :: y) ok).
      { intros o. unfold jr_cont. cbn [tl]. destruct (Nat.ltb MAXD (S d)); [reflexivity|].
        pose proof (skip_len y) as Hy.
        destruct (skip y) as [|c r] eqn:Ey.
        - apply IHl; cbn [length]; lia.
        - destruct (c =? closer o); [reflexivity|]. apply IHl; lia. }
      destruct (b =? 123); [apply Hc|].
      destruct (b =? 91); [apply Hc|].
      reflexivity.
    + intros d o n cap acc y f' ok H1 H2. destruct f' as [|f']; [lia|]. cbn [jrl].
      unfold jbind.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1]; [|reflexivity]. cbv beta iota.
      pose proof (jr_name_spec o y ok1) as Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En; [|reflexivity]. cbv beta iota.
      assert (Hy1 : (length y1 <= length y)%nat) by (destruct o; cbv iota in Hn; dstr; subst; lia).
      rewrite (IHv d y1 f' ok2) by lia.
      pose proof (proj1 (spec_fuel f) d y1 ok2) as Hv.
      destruct (jrv f d y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev; [|reflexivity]. cbv beta iota.
      unfold vspec in Hv. cbn [fst snd] in Hv. destruct Hv as (_ & _ & Hv).
      destruct (Hv v r eq_refl) as (Hr & _ & _).
      pose proof (skip_len r) as Hsr.
      destruct (skip r) as [|c r1] eqn:Er; [reflexivity|]. cbn [length] in Hsr.
      destruct (c =? 44); [|reflexivity].
      rewrite (IHl d o (S n) cap1 ((nm, v) :: acc) r1 f' ok3) by lia.
      reflexivity.
Qed.

Lemma jr_value_fuel : forall f d x ok, (2 * length x + 1 <= f)%nat -> jrv f d x ok = jr_value d x ok.
Proof.
  intros f d x ok H. unfold jr_value.
  apply (proj1 (fuel_mono (S (2 * length x)))); lia.
Qed.

Lemma jr_items_fuel : forall f d o x ok, (2 * length x + 2 <= f)%nat ->
  jr_cont (jrl f) d o x ok = jr_items d o x ok.
Proof.
  intros f d o x ok H. unfold jr_items, jr_cont.
  destruct (Nat.ltb MAXD (S d)); [reflexivity|].
  pose proof (skip_len (tl x)) as Hs.
  assert (Ht : (length (tl x) <= length x)%nat) by (destruct x; cbn [tl length]; lia).
  destruct (skip (tl x)) as [|c r] eqn:Ey.
  - apply (proj2 (fuel_mono (2 * length x + 2))); cbn [length]; lia.
  - destruct (c =? closer o); [reflexivity|].
    apply (proj2 (fuel_mono (2 * length x + 2))); lia.
Qed.

Lemma agrees_jr_value : forall d x, agrees (jr_value d x).
Proof. intros d x. apply (proj1 (agrees_fuel _)). Qed.

Lemma agrees_jr_items : forall d o x, agrees (jr_items d o x).
Proof.
  intros d o x. pose proof (proj2 (agrees_fuel (2 * length x + 2))) as H.
  pose proof agrees_jr_string.
  unfold jr_items. ag.
Qed.

Lemma vspec_jr_value : forall d x ok, vspec x d (jr_value d x ok).
Proof. intros d x ok. apply (proj1 (spec_fuel _)). Qed.

Lemma jr_value_rest : forall d x ok t r tr ok', jr_value d x ok = (Some (t, r), tr, ok') ->
  (length r < length x)%nat.
Proof.
  intros d x ok t r tr ok' E. pose proof (vspec_jr_value d x ok) as H. rewrite E in H.
  unfold vspec in H. cbn [fst snd] in H. destruct H as (_ & _ & H). apply (H t r eq_refl).
Qed.

Definition post (res : option (jv * list Z)) : option jv :=
  match res with
  | Some (t, r) => match skip r with [] => Some t | _ :: _ => None end
  | None => None
  end.

Lemma jr_run_eq : forall x ok,
  jr_run x ok = (post (fst (fst (jr_value 0 x ok))), snd (fst (jr_value 0 x ok))).
Proof.
  intros x ok. unfold jr_run.
  destruct (jr_value 0 x ok) as [[[[t r]|] tr] ok']; reflexivity.
Qed.

Theorem G7_1 : forall x ok, (forall i, (i < ncalls x)%nat -> nth i ok true = true) ->
  jr_run x ok = (json_read x, snd (jr_run x [])).
Proof.
  intros x ok Hu. unfold json_read, ncalls in *. rewrite !jr_run_eq in *. cbn [fst snd] in *.
  rewrite (proj1 (agrees_jr_value 0 x ok) Hu). reflexivity.
Qed.

Theorem G7_1_calls : forall x ok, (forall i, (i < ncalls x)%nat -> nth i ok true = true) ->
  calls (snd (jr_run x ok)) = ncalls x.
Proof. intros x ok Hu. rewrite (G7_1 x ok Hu). reflexivity. Qed.

Theorem G7_2 : forall x ok j, (j < ncalls x)%nat -> nth j ok true = false ->
  (forall i, (i < j)%nat -> nth i ok true = true) ->
  fst (jr_run x ok) = None /\ calls (snd (jr_run x ok)) = S j.
Proof.
  intros x ok j Hj Hf Hu. unfold ncalls in *. rewrite !jr_run_eq in *. cbn [fst snd] in *.
  destruct (proj2 (agrees_jr_value 0 x ok) j Hj Hf Hu) as (P & e & rest & E & _ & Hc & Hic).
  rewrite E. cbn [fst snd post]. split; [reflexivity|].
  rewrite calls_app. cbn [calls is_call]. lia.
Qed.

Theorem G7_3 : forall x ok j, (j < ncalls x)%nat -> nth j ok true = false ->
  (forall i, (i < j)%nat -> nth i ok true = true) ->
  exists P E rest, snd (jr_run x ok) = P ++ [EFail (esize E)] /\
    snd (jr_run x []) = P ++ E :: rest /\ calls P = j /\ is_call E = true.
Proof.
  intros x ok j Hj Hf Hu. unfold ncalls in *. rewrite !jr_run_eq in *. cbn [fst snd] in *.
  destruct (proj2 (agrees_jr_value 0 x ok) j Hj Hf Hu) as (P & e & rest & E & Ht & Hc & Hic).
  exists P, e, rest. rewrite E. cbn [fst snd]. auto.
Qed.

Theorem G7_4 : forall x ok, (calls (snd (jr_run x ok)) <= 2 * length x + 2)%nat.
Proof.
  intros x ok. rewrite jr_run_eq. cbn [snd].
  pose proof (vspec_jr_value 0 x ok) as H. unfold vspec in H. destruct H as (H & _). lia.
Qed.

Theorem G10_1 : forall d x ok t r tr ok', jr_value d x ok = (Some (t, r), tr, ok') ->
  held tr <= 224 * (Z.of_nat (length x) - Z.of_nat (length r)).
Proof.
  intros d x ok t r tr ok' E. pose proof (vspec_jr_value d x ok) as H. rewrite E in H.
  unfold vspec in H. cbn [fst snd] in H. destruct H as (_ & _ & H).
  destruct (H t r eq_refl) as (_ & _ & H3). pose proof (held_le_pos tr). lia.
Qed.

Theorem G10_2 : forall d x ok p rest, snd (fst (jr_value d x ok)) = p ++ rest ->
  held p <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (MAXD - d).
Proof.
  intros d x ok p rest E. pose proof (vspec_jr_value d x ok) as H.
  unfold vspec in H. destruct H as (_ & H & _). rewrite E in H.
  pose proof (held_le_pos p). pose proof (pos_prefix p rest). lia.
Qed.

Theorem G10 : forall x ok p rest, snd (jr_run x ok) = p ++ rest ->
  held p <= 224 * Z.of_nat (length x) + 16384.
Proof.
  intros x ok p rest E. rewrite jr_run_eq in E. cbn [snd] in E.
  pose proof (G10_2 0 x ok p rest E) as H. unfold MAXD in H. cbn [Nat.sub] in H. lia.
Qed.

Theorem G10_bound : forall n, 0 <= n -> 224 * n + 16384 <= 256 * n + 20480.
Proof. intros n H. lia. Qed.

Theorem G8 : forall x y, x = y -> json_read x = json_read y /\ ncalls x = ncalls y.
Proof. intros x y ->. split; reflexivity. Qed.


Lemma vspec_jr_items : forall d o b y ok, vspec (b :: y) d (jr_items d o (b :: y) ok).
Proof.
  intros d o b y ok. unfold jr_items. apply jr_cont_spec.
  intros o' n cap acc y' ok' Hi. apply (proj2 (spec_fuel _)). exact Hi.
Qed.

Theorem G7_4_items : forall d o b y ok, (calls (snd (fst (jr_items d o (b :: y) ok))) <= 2 * length (b :: y))%nat.
Proof. intros d o b y ok. exact (proj1 (vspec_jr_items d o b y ok)). Qed.

Theorem G10_1_items : forall d o b y ok t r tr ok', jr_items d o (b :: y) ok = (Some (t, r), tr, ok') ->
  held tr <= 224 * (Z.of_nat (length (b :: y)) - Z.of_nat (length r)).
Proof.
  intros d o b y ok t r tr ok' E. pose proof (vspec_jr_items d o b y ok) as H. rewrite E in H.
  unfold vspec in H. cbn [fst snd] in H. destruct H as (_ & _ & H).
  destruct (H t r eq_refl) as (_ & _ & H3). pose proof (held_le_pos tr). lia.
Qed.

Theorem G10_2_items : forall d o b y ok p rest, snd (fst (jr_items d o (b :: y) ok)) = p ++ rest ->
  held p <= 224 * Z.of_nat (length (b :: y)) + 512 * Z.of_nat (MAXD - d).
Proof.
  intros d o b y ok p rest E. pose proof (vspec_jr_items d o b y ok) as H.
  unfold vspec in H. destruct H as (_ & H & _). rewrite E in H.
  pose proof (held_le_pos p). pose proof (pos_prefix p rest). lia.
Qed.

Theorem jr_items_rest : forall d o b y ok t r tr ok', jr_items d o (b :: y) ok = (Some (t, r), tr, ok') ->
  (length r < length (b :: y))%nat.
Proof.
  intros d o b y ok t r tr ok' E. pose proof (vspec_jr_items d o b y ok) as H. rewrite E in H.
  unfold vspec in H. cbn [fst snd] in H. destruct H as (_ & _ & H). apply (H t r eq_refl).
Qed.

Lemma jbind_some : forall A B (m : M A) (k : A -> M B) ok b t ok', jbind m k ok = (Some b, t, ok') ->
  exists a t1 ok1 t2, m ok = (Some a, t1, ok1) /\ k a ok1 = (Some b, t2, ok') /\ t = t1 ++ t2.
Proof.
  intros A B m k ok b t ok' H. unfold jbind in H.
  destruct (m ok) as [[[a|] t1] ok1]; cbv beta iota in H; [|discriminate].
  destruct (k a ok1) as [[r t2] o2] eqn:E. cbv beta iota in H. injection H as Hr Ht Ho. subst.
  exists a, t1, ok1, t2. auto.
Qed.

Lemma lit_depth : forall w v x ok t r tr ok', (v = JTrue \/ v = JFalse \/ v = JNull) ->
  lit w v x ok = (Some (t, r), tr, ok') -> depth t = 0%nat.
Proof.
  intros w v x ok t r tr ok' Hv H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _. destruct Hv as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma number_depth : forall x ok t r tr ok', jr_number x ok = (Some (t, r), tr, ok') -> depth t = 0%nat.
Proof.
  intros x ok t r tr ok' H. unfold jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r']. cbv beta iota in H.
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _).
  destruct (whole _); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _. reflexivity.
Qed.

Lemma mk_depth : forall o L k, Forall (fun m => (depth (snd m) <= k)%nat) L -> (depth (mk o L) <= S k)%nat.
Proof.
  intros o L k H. destruct o; unfold mk; cbn [depth]; apply le_n_S.
  - apply list_max_le, Forall_map. eapply Forall_impl; [|exact H]. intros [nm v] Hv. exact Hv.
  - rewrite map_map. apply list_max_le, Forall_map. exact H.
Qed.

Lemma cont_depth : forall loop d o x ok t r tr ok',
  (forall o' n cap acc y ok1 t1 r1 tr1 ok2, Forall (fun m => (depth (snd m) <= MAXD - S d)%nat) acc ->
     loop (S d) o' n cap acc y ok1 = (Some (t1, r1), tr1, ok2) -> (depth t1 <= S (MAXD - S d))%nat) ->
  jr_cont loop d o x ok = (Some (t, r), tr, ok') -> (depth t <= MAXD - d)%nat.
Proof.
  intros loop d o x ok t r tr ok' HL H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  apply Nat.ltb_ge in Ed. cbv zeta in H.
  assert (HL' : forall y, loop (S d) o 0%nat 0%nat [] y ok = (Some (t, r), tr, ok') -> (depth t <= MAXD - d)%nat).
  { intros y Hy. pose proof (HL o 0%nat 0%nat [] y ok t r tr ok' (Forall_nil _) Hy). lia. }
  destruct (skip (tl x)) as [|c r0]; cbv beta iota in H; [exact (HL' _ H)|].
  destruct (c =? closer o); cbv beta iota in H; [|exact (HL' _ H)].
  unfold jret in H. injection H as <- _ _ _.
  pose proof (mk_depth o [] 0%nat (Forall_nil _)). lia.
Qed.

Lemma depth_fuel : forall f,
  (forall d x ok t r tr ok', jrv f d x ok = (Some (t, r), tr, ok') -> (depth t <= MAXD - d)%nat) /\
  (forall d o n cap acc y ok t r tr ok', Forall (fun m => (depth (snd m) <= MAXD - d)%nat) acc ->
     jrl f d o n cap acc y ok = (Some (t, r), tr, ok') -> (depth t <= S (MAXD - d))%nat).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H.
      { apply (cont_depth _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 91); cbv beta iota in H.
      { apply (cont_depth _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & _ & H & _). cbv beta iota in H.
        unfold jret in H. injection H as <- _ _ _. cbn [depth]. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { rewrite (lit_depth _ _ _ _ _ _ _ _ (or_introl eq_refl) H). lia. }
      destruct (b =? 102); cbv beta iota in H.
      { rewrite (lit_depth _ _ _ _ _ _ _ _ (or_intror (or_introl eq_refl)) H). lia. }
      destruct (b =? 110); cbv beta iota in H.
      { rewrite (lit_depth _ _ _ _ _ _ _ _ (or_intror (or_intror eq_refl)) H). lia. }
      rewrite (number_depth _ _ _ _ _ _ H). lia.
    + intros d o n cap acc y ok t r tr ok' Hacc H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & _ & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (IHv d y1 ok2 v r0 tv ok3 Ev) as Dv.
      assert (Hacc' : Forall (fun m => (depth (snd m) <= MAXD - d)%nat) ((nm, v) :: acc))
        by (constructor; [exact Dv|exact Hacc]).
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (c =? 44); cbv beta iota in H.
      { exact (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' Hacc' H). }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as <- _ _ _.
      apply mk_depth. apply Forall_app. split; [apply Forall_rev; exact Hacc|constructor; [exact Dv|constructor]].
Qed.

Theorem jr_value_depth : forall d x ok t r tr ok', jr_value d x ok = (Some (t, r), tr, ok') ->
  (depth t <= MAXD - d)%nat.
Proof. intros d x ok t r tr ok' H. exact (proj1 (depth_fuel _) d x ok t r tr ok' H). Qed.

Theorem jr_items_depth : forall d o x ok t r tr ok', jr_items d o x ok = (Some (t, r), tr, ok') ->
  (depth t <= MAXD - d)%nat.
Proof.
  intros d o x ok t r tr ok' H. unfold jr_items in H.
  apply (cont_depth _ _ _ _ _ _ _ _ _
    (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => proj2 (depth_fuel _) (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H).
Qed.

Theorem json_read_depth : forall x t, json_read x = Some t -> (depth t <= MAXD)%nat.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  pose proof (jr_value_depth 0 x [] t' r tr ok' E). lia.
Qed.

Ltac efin := cbn [In snd fst app] in *;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : False |- _ => destruct H
  end; subst; cbn [esize]; lia.

Lemma in_jbind : forall (A B : Type) (m : M A) (k : A -> M B) (ok : list bool) (e : ev),
  In e (snd (fst (jbind m k ok))) ->
  In e (snd (fst (m ok))) \/
  (exists a, fst (fst (m ok)) = Some a /\ In e (snd (fst (k a (snd (m ok)))))).
Proof.
  intros A B m k ok e H. unfold jbind in H.
  destruct (m ok) as [[o t] ok1] eqn:Em.
  destruct o as [a|].
  - destruct (k a ok1) as [[o2 t2] ok2] eqn:Ek. cbn [snd fst] in H |- *.
    apply in_app_or in H. destruct H as [H|H].
    + left. exact H.
    + right. exists a. split; [reflexivity|]. rewrite Ek. cbn [snd fst]. exact H.
  - cbn [snd fst] in H |- *. left. exact H.
Qed.

Lemma lit_no_ev : forall w v x ok e, In e (snd (fst (lit w v x ok))) -> False.
Proof.
  intros w v x ok e H. unfold lit in H.
  destruct (prefixb w x); [unfold jret in H | unfold jrefuse in H];
    cbn [snd fst In] in H; exact H.
Qed.

Lemma jrealloc_esize : forall m m' ok e, In e (snd (fst (jrealloc m m' ok))) -> esize e = m'.
Proof.
  intros m m' ok e Hin. unfold jrealloc, take in Hin.
  destruct ok as [| b ok]; [|destruct b]; cbn [snd fst In] in Hin;
    destruct Hin as [He|[]]; subst e; reflexivity.
Qed.

Lemma grow_esize : forall o n cap ok e, inv n cap ->
  In e (snd (fst (grow o n cap ok))) -> (esize e <= 112 * n + 448)%nat.
Proof.
  intros o n cap ok e [H1 [H2 [H3 H4]]] Hin. unfold grow in Hin.
  destruct (Nat.ltb n cap) eqn:E.
  - unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin.
  - apply Nat.ltb_ge in E. assert (Hnc : n = cap) by lia. subst n.
    assert (Hcb : ((if Nat.eqb cap 0 then 8 else 2 * cap) <= 8 + 2 * cap)%nat)
      by (destruct (Nat.eqb cap 0); lia).
    cbv zeta in Hin.
    apply in_jbind in Hin. destruct Hin as [Hin | (u1 & _ & Hin)].
    + apply jrealloc_esize in Hin. rewrite Hin. lia.
    + cbv beta in Hin. destruct o; cbv beta iota in Hin.
      * apply in_jbind in Hin. destruct Hin as [Hin | (u2 & _ & Hin)].
        -- apply jrealloc_esize in Hin. rewrite Hin. lia.
        -- cbv beta in Hin; unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin.
      * unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin.
Qed.

Lemma jr_string_esize : forall z ok e, In e (snd (fst (jr_string z ok))) -> (esize e <= length z)%nat.
Proof.
  intros z ok e Hin. unfold jr_string in Hin.
  destruct (scan z) as [q|] eqn:Es; [ | unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin ].
  pose proof (scan_quote z q Es) as [Hq _].
  unfold jbind, jalloc, take, jret, jrefuse, jfree in Hin.
  destruct ok as [|b ok]; [|destruct b]; destruct (decode z) as [[s r]|] eqn:Ed;
    cbv beta iota in Hin; efin.
Qed.

Lemma jr_name_esize : forall o y ok e, In e (snd (fst (jr_name o y ok))) -> (esize e <= length y)%nat.
Proof.
  intros o y ok e Hin. unfold jr_name in Hin. destruct o.
  2: { unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin. }
  destruct (skip y) as [|b z] eqn:Ey; [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  destruct (b =? 34) eqn:Eb; [ | unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin ].
  cbv iota in Hin. apply in_jbind in Hin. destruct Hin as [Hin | ((nm & r) & _ & Hin)].
  - apply jr_string_esize in Hin. lia.
  - cbv beta iota in Hin. destruct (skip r) as [|c r1] eqn:Er.
    + apply in_jbind in Hin. destruct Hin as [Hin | (u & _ & Hin)].
      * unfold jfree in Hin. cbn [snd fst In] in Hin. destruct Hin as [He|[]]. subst e.
        cbn [esize]. unfold sblock. destruct (scan z) as [q|] eqn:Esc.
        -- pose proof (scan_quote z q Esc) as [Hq _]. lia.
        -- lia.
      * unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin.
    + destruct (c =? 58).
      * unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin.
      * apply in_jbind in Hin. destruct Hin as [Hin | (u & _ & Hin)].
        -- unfold jfree in Hin. cbn [snd fst In] in Hin. destruct Hin as [He|[]]. subst e.
           cbn [esize]. unfold sblock. destruct (scan z) as [q|] eqn:Esc.
           ++ pose proof (scan_quote z q Esc) as [Hq _]. lia.
           ++ lia.
        -- unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin.
Qed.

Lemma jr_number_esize : forall x ok e, In e (snd (fst (jr_number x ok))) -> (esize e <= length x + 1)%nat.
Proof.
  intros x ok e Hin. unfold jr_number in Hin.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) in *.
  assert (Hj : (j <= length x)%nat).
  { unfold j. destruct x as [|b0 x']; [cbn; lia|]. destruct (b0 =? 45); cbn [length]; lia. }
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez;
    [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
  destruct (negb (digit c));
    [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end);
    [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
  destruct (span numch z) as [a r] eqn:Es.
  pose proof (span_app _ _ _ _ Es) as Hza.
  assert (Htxt : (length (firstn j x ++ c :: a) <= length x)%nat).
  { rewrite length_app, length_firstn.
    cbn [length] in Hsk. rewrite Hza, length_app in Hsk.
    assert (Hmin : Nat.min j (length x) = j) by (apply Nat.min_l; exact Hj).
    rewrite Hmin. cbn [length]. lia. }
  unfold jbind, jalloc, take, jret, jrefuse in Hin.
  destruct ok as [|b ok]; [|destruct b];
    destruct (whole (firstn j x ++ c :: a)); cbv beta iota in Hin; efin.
Qed.

Definition esz_v (x : list Z) (res : option (jv * list Z) * list ev * list bool) : Prop :=
  forall e, In e (snd (fst res)) -> (esize e <= 56 * length x + 448)%nat.

Definition esz_l (n : nat) (y : list Z) (res : option (jv * list Z) * list ev * list bool) : Prop :=
  forall e, In e (snd (fst res)) -> (esize e <= 56 * (2 * n + length y) + 448)%nat.

Lemma esz_cont : forall loop d o b y ok,
  (forall o' n cap acc y' ok', inv n cap -> esz_l n y' (loop (S d) o' n cap acc y' ok')) ->
  esz_v (b :: y) (jr_cont loop d o (b :: y) ok).
Proof.
  intros loop d o b y ok HL e Hin. unfold jr_cont in Hin.
  destruct (Nat.ltb MAXD (S d));
    [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
  cbn [tl] in Hin. cbv zeta in Hin.
  pose proof (skip_len y) as Hsy.
  assert (Hi0 : inv 0 0) by (unfold inv; lia).
  pose proof (HL o 0%nat 0%nat [] (skip y) ok Hi0) as Hloop. unfold esz_l in Hloop.
  assert (Hcov : forall e', In e' (snd (fst (loop (S d) o 0%nat 0%nat [] (skip y) ok))) ->
                 (esize e' <= 56 * length (b :: y) + 448)%nat).
  { intros e' He'. apply Hloop in He'. cbn [length]. lia. }
  destruct (skip y) as [|c r] eqn:Ey.
  - apply Hcov. exact Hin.
  - destruct (c =? closer o).
    + unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin.
    + apply Hcov. exact Hin.
Qed.

Lemma bound_fuel : forall f,
  (forall d x ok, esz_v x (jrv f d x ok)) /\
  (forall d o n cap acc y ok, inv n cap -> esz_l n y (jrl f d o n cap acc y ok)).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok e Hin. cbn [jrv] in Hin. unfold jrefuse in Hin. cbn [snd fst In] in Hin. destruct Hin.
    + intros d o n cap acc y ok Hi e Hin. cbn [jrl] in Hin. unfold jrefuse in Hin.
      cbn [snd fst In] in Hin. destruct Hin.
  - split.
    + intros d x ok e Hin. cbn [jrv] in Hin.
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex;
        [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
      assert (Hby : (length (b :: y) <= length x)%nat) by exact Hsx.
      destruct (b =? 123) eqn:E1.
      { cbv iota in Hin.
        assert (He := esz_cont (jrl f) d true b y ok
          (fun o' n cap acc y' ok' Hi => IHl (S d) o' n cap acc y' ok' Hi) e Hin). lia. }
      destruct (b =? 91) eqn:E2.
      { cbv iota in Hin.
        assert (He := esz_cont (jrl f) d false b y ok
          (fun o' n cap acc y' ok' Hi => IHl (S d) o' n cap acc y' ok' Hi) e Hin). lia. }
      destruct (b =? 34) eqn:E3.
      { cbv iota in Hin. apply in_jbind in Hin. destruct Hin as [Hin | ((s & r) & _ & Hin)].
        - apply jr_string_esize in Hin. cbn [length] in Hby. lia.
        - cbv beta iota in Hin. unfold jret in Hin. cbn [snd fst In] in Hin. destruct Hin. }
      destruct (b =? 116) eqn:E4.
      { cbv iota in Hin. exfalso. exact (lit_no_ev _ _ _ _ _ Hin). }
      destruct (b =? 102) eqn:E5.
      { cbv iota in Hin. exfalso. exact (lit_no_ev _ _ _ _ _ Hin). }
      destruct (b =? 110) eqn:E6.
      { cbv iota in Hin. exfalso. exact (lit_no_ev _ _ _ _ _ Hin). }
      cbv iota in Hin. apply jr_number_esize in Hin. cbn [length] in Hby. lia.
    + intros d o n cap acc y ok Hi e Hin. cbn [jrl] in Hin.
      apply in_jbind in Hin. destruct Hin as [Hin | (cp & Hcp & Hin)].
      { apply (grow_esize _ _ _ _ _ Hi) in Hin. lia. }
      pose proof (grow_spec o n cap ok Hi) as Hg.
      destruct (grow o n cap ok) as [[[cap1|] tg] og] eqn:Eg; cbn [fst snd] in Hcp, Hin;
        [ | discriminate Hcp ].
      injection Hcp as Hcc. subst cap1.
      destruct Hg as (G1 & G2 & G3 & G4 & G5 & G6).
      cbv beta in Hin.
      apply in_jbind in Hin. destruct Hin as [Hin | ((nmw & y1w) & Hnm & Hin)].
      { apply jr_name_esize in Hin. lia. }
      destruct (jr_name o y og) as [[[[nm0 y1']|] tn] on] eqn:En; cbn [fst snd] in Hnm, Hin;
        [ | discriminate Hnm ].
      injection Hnm as <- <-.
      pose proof (jr_name_ok o y og nm0 y1' tn on En) as (NC & NL & _).
      assert (Hyle : (length y1' <= length y)%nat) by (destruct o; lia).
      cbv beta iota in Hin.
      apply in_jbind in Hin. destruct Hin as [Hin | ((v0 & r0) & Hvr & Hin)].
      { assert (HB : (esize e <= 56 * length y1' + 448)%nat) by (apply (IHv d y1' on); exact Hin). lia. }
      destruct (jrv f d y1' on) as [[[[v0' r0']|] tv] ov] eqn:Ev; cbn [fst snd] in Hvr, Hin;
        [ | discriminate Hvr ].
      injection Hvr as <- <-.
      pose proof (proj1 (spec_fuel f) d y1' on) as Hv. unfold vspec in Hv.
      rewrite Ev in Hv. cbn [fst snd] in Hv. destruct Hv as (_ & _ & Hv3).
      destruct (Hv3 v0' r0' eq_refl) as (Hrlt & _ & _).
      cbv beta iota in Hin.
      pose proof (skip_len r0') as Hsr.
      destruct (skip r0') as [|c r1] eqn:Er;
        [ unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin | ].
      cbn [length] in Hsr.
      destruct (c =? 44).
      { assert (HB : (esize e <= 56 * (2 * S n + length r1) + 448)%nat)
          by (apply (IHl d o (S n) cp ((nm0, v0') :: acc) r1 ov G1); exact Hin). lia. }
      destruct (c =? closer o).
      { unfold jret in Hin; cbn [snd fst In] in Hin; destruct Hin. }
      { unfold jrefuse in Hin; cbn [snd fst In] in Hin; destruct Hin. }
Qed.

Lemma esz_jr_value : forall d x ok e, In e (snd (fst (jr_value d x ok))) ->
  (esize e <= 56 * length x + 448)%nat.
Proof. intros d x ok e H. apply (proj1 (bound_fuel (S (2 * length x))) d x ok); exact H. Qed.

Theorem jr_esize_bound : forall x ok e, In e (snd (jr_run x ok)) ->
  (esize e <= 56 * length x + 448)%nat.
Proof.
  intros x ok e H. rewrite jr_run_eq in H. cbn [snd] in H.
  apply (esz_jr_value 0 x ok); exact H.
Qed.

End Reader.
