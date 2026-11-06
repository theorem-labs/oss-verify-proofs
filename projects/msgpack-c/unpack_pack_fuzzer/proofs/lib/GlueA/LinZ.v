(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import MainExport.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module LinZ.

Definition lin : Type := (Z * list (nat * Z))%type.

Fixpoint lsum (V : nat -> Z) (l : list (nat * Z)) : Z :=
  match l with [] => 0 | nc :: r => snd nc * V (fst nc) + lsum V r end.
Definition leval (V : nat -> Z) (p : lin) : Z := fst p + lsum V (snd p).

Fixpoint ladd1 (n : nat) (c : Z) (l : list (nat * Z)) : list (nat * Z) :=
  match l with
  | [] => if c =? 0 then [] else [(n, c)]
  | md :: r =>
      if (n <? fst md)%nat then (if c =? 0 then l else (n, c) :: l)
      else if (n =? fst md)%nat then (if c + snd md =? 0 then r else (n, c + snd md) :: r)
      else md :: ladd1 n c r
  end.

Lemma lsum_ladd1 : forall V n c l, lsum V (ladd1 n c l) = c * V n + lsum V l.
Proof.
  intros V n c l. induction l as [|[m d] r IH]; cbn [ladd1 fst snd].
  - destruct (Z.eqb_spec c 0); cbn [lsum fst snd]; subst; lia.
  - destruct (Nat.ltb_spec n m).
    + destruct (Z.eqb_spec c 0); cbn [lsum fst snd]; subst; lia.
    + destruct (Nat.eqb_spec n m).
      * subst m. destruct (Z.eqb_spec (c + d) 0); cbn [lsum fst snd]; nia.
      * cbn [lsum fst snd]. rewrite IH. lia.
Qed.

Definition lmerge (a b : list (nat * Z)) : list (nat * Z) := fold_right (fun nc acc => ladd1 (fst nc) (snd nc) acc) b a.
Lemma lsum_lmerge : forall V a b, lsum V (lmerge a b) = lsum V a + lsum V b.
Proof. intros V a b. induction a as [|[n c] r IH]; cbn [lmerge fold_right lsum fst snd]; [lia|]. fold (lmerge r b). rewrite lsum_ladd1, IH. lia. Qed.

Definition ladd (p q : lin) : lin := (fst p + fst q, lmerge (snd p) (snd q)).
Lemma leval_ladd : forall V p q, leval V (ladd p q) = leval V p + leval V q.
Proof. intros V p q. unfold leval, ladd. cbn [fst snd]. rewrite lsum_lmerge. lia. Qed.

Definition lscale (k : Z) (p : lin) : lin :=
  if k =? 0 then (0, []) else (k * fst p, map (fun nc => (fst nc, k * snd nc)) (snd p)).
Lemma lsum_scale : forall V k l, lsum V (map (fun nc => (fst nc, k * snd nc)) l) = k * lsum V l.
Proof. intros V k l. induction l as [|[n c] r IH]; cbn [map lsum fst snd]; [lia| rewrite IH; lia]. Qed.
Lemma leval_lscale : forall V k p, leval V (lscale k p) = k * leval V p.
Proof.
  intros V k p. unfold lscale. destruct (Z.eqb_spec k 0); unfold leval; cbn [fst snd lsum].
  - subst. lia.
  - rewrite lsum_scale. lia.
Qed.

Definition lconst (z : Z) : lin := (z, []).
Lemma leval_lconst : forall V z, leval V (lconst z) = z. Proof. intros. unfold leval, lconst. cbn. lia. Qed.
Definition lvar (n : nat) : lin := (0, [(n, 1)]).
Lemma leval_lvar : forall V n, leval V (lvar n) = V n. Proof. intros. unfold leval, lvar. cbn. lia. Qed.

Fixpoint kv_get (kv : list (nat * Z)) (n : nat) : option Z :=
  match kv with [] => None | nz :: r => if (n =? fst nz)%nat then Some (snd nz) else kv_get r n end.
Definition kv_ok (V : nat -> Z) (kv : list (nat * Z)) : Prop := Forall (fun nz => V (fst nz) = snd nz) kv.
Lemma kv_get_sound : forall V kv n z, kv_ok V kv -> kv_get kv n = Some z -> V n = z.
Proof.
  intros V kv n z H. induction H as [|[m y] r Hm Hr IH]; cbn [kv_get fst snd]; [discriminate|].
  destruct (Nat.eqb_spec n m); [intros [= <-]; subst; exact Hm| exact IH].
Qed.

Definition is_const (p : lin) : option Z := match snd p with [] => Some (fst p) | _ => None end.
Lemma is_const_sound : forall V p c, is_const p = Some c -> leval V p = c.
Proof. intros V [c0 l] c H. unfold is_const in H. cbn in H. destruct l; [injection H as <-; unfold leval; cbn; lia| discriminate]. Qed.

Fixpoint lin_of (kv : list (nat * Z)) (e : zexp) : option lin :=
  match e with
  | ZLit z => Some (lconst z)
  | ZV n => match kv_get kv n with Some z => Some (lconst z) | None => Some (lvar n) end
  | ZAdd a b => match lin_of kv a, lin_of kv b with Some p, Some q => Some (ladd p q) | _, _ => None end
  | ZMul a b =>
      match lin_of kv a, lin_of kv b with
      | Some p, Some q =>
          match is_const p, is_const q with
          | Some c, _ => Some (lscale c q)
          | None, Some d => Some (lscale d p)
          | None, None => None
          end
      | _, _ => None
      end
  | ZAnd a b =>
      match lin_of kv a, lin_of kv b with
      | Some p, Some q => match is_const p, is_const q with Some c, Some d => Some (lconst (Z.land c d)) | _, _ => None end
      | _, _ => None
      end
  | ZLtu a b =>
      match lin_of kv a, lin_of kv b with
      | Some p, Some q => match is_const p, is_const q with
                          | Some c, Some d => Some (lconst (Z.b2z (c mod two64 <? d mod two64))) | _, _ => None end
      | _, _ => None
      end
  end.

Lemma lin_of_sound : forall V kv, kv_ok V kv -> forall e p, lin_of kv e = Some p -> zv V e = leval V p.
Proof.
  intros V kv HK. induction e as [z|n|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa b IHb]; intros p H; cbn [lin_of] in H.
  - injection H as <-. rewrite leval_lconst. reflexivity.
  - destruct (kv_get kv n) as [z|] eqn:G; injection H as <-; cbn [zv].
    + rewrite leval_lconst. exact (kv_get_sound V kv n z HK G).
    + rewrite leval_lvar. reflexivity.
  - destruct (lin_of kv a) as [pa|]; [|discriminate]. destruct (lin_of kv b) as [pb|]; [|discriminate].
    injection H as <-. cbn [zv]. rewrite leval_ladd, (IHa pa eq_refl), (IHb pb eq_refl). reflexivity.
  - destruct (lin_of kv a) as [pa|]; [|discriminate]. destruct (lin_of kv b) as [pb|]; [|discriminate].
    cbn [zv]. rewrite (IHa pa eq_refl), (IHb pb eq_refl).
    destruct (is_const pa) as [c|] eqn:Ca.
    + injection H as <-. rewrite leval_lscale, (is_const_sound V pa c Ca). reflexivity.
    + destruct (is_const pb) as [d|] eqn:Cb; [|discriminate]. injection H as <-.
      rewrite leval_lscale, (is_const_sound V pb d Cb). lia.
  - destruct (lin_of kv a) as [pa|]; [|discriminate]. destruct (lin_of kv b) as [pb|]; [|discriminate].
    destruct (is_const pa) as [c|] eqn:Ca; [|discriminate]. destruct (is_const pb) as [d|] eqn:Cb; [|discriminate].
    injection H as <-. cbn [zv]. rewrite (IHa pa eq_refl), (IHb pb eq_refl), (is_const_sound V pa c Ca), (is_const_sound V pb d Cb), leval_lconst. reflexivity.
  - destruct (lin_of kv a) as [pa|]; [|discriminate]. destruct (lin_of kv b) as [pb|]; [|discriminate].
    destruct (is_const pa) as [c|] eqn:Ca; [|discriminate]. destruct (is_const pb) as [d|] eqn:Cb; [|discriminate].
    injection H as <-. cbn [zv]. rewrite (IHa pa eq_refl), (IHb pb eq_refl), (is_const_sound V pa c Ca), (is_const_sound V pb d Cb), leval_lconst. reflexivity.
Qed.

Fixpoint coefs_eqb (a b : list (nat * Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (fst x =? fst y)%nat && (snd x =? snd y) && coefs_eqb a' b'
  | _, _ => false
  end.
Lemma coefs_eqb_eq : forall a b, coefs_eqb a b = true -> a = b.
Proof.
  induction a as [|[n c] a IH]; intros [|[m d] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. exact (IH b H3).
Qed.

Definition ldiff (p q : lin) : option Z := if coefs_eqb (snd p) (snd q) then Some (fst p - fst q) else None.
Lemma ldiff_sound : forall V p q d, ldiff p q = Some d -> leval V p = leval V q + d.
Proof.
  intros V [c l] [c' l'] d H. unfold ldiff in H. cbn [fst snd] in H. destruct (coefs_eqb l l') eqn:Ec; [|discriminate].
  injection H as <-. apply coefs_eqb_eq in Ec. subst l'. unfold leval. cbn [fst snd]. lia.
Qed.

Definition lin_eqb (p q : lin) : bool := match ldiff p q with Some d => d =? 0 | None => false end.
Lemma lin_eqb_sound : forall V p q, lin_eqb p q = true -> leval V p = leval V q.
Proof. intros V p q H. unfold lin_eqb in H. destruct (ldiff p q) as [d|] eqn:D; [|discriminate]. apply Z.eqb_eq in H. subst d. rewrite (ldiff_sound V p q 0 D). lia. Qed.

Definition lin_eqb64 (p q : lin) : bool := match ldiff p q with Some d => d mod two64 =? 0 | None => false end.
Lemma lin_eqb64_sound : forall V p q, lin_eqb64 p q = true -> (leval V p) mod two64 = (leval V q) mod two64.
Proof.
  intros V p q H. unfold lin_eqb64 in H. destruct (ldiff p q) as [d|] eqn:D; [|discriminate]. apply Z.eqb_eq in H.
  rewrite (ldiff_sound V p q d D). unfold two64 in *. rewrite Z.add_mod by lia. rewrite H, Z.add_0_r. apply Z.mod_mod. lia.
Qed.

End LinZ.
