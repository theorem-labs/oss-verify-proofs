(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia String.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

Definition Zsdecimal (n : Z) : list Z := if n <? 0 then 45 :: Zdecimal (- n) else Zdecimal n.

Definition norm8 (l : list Z) : list Z := map (fun b => b mod 256) l.

Lemma norm8_length : forall l, zlength (norm8 l) = zlength l.
Proof. intros. unfold norm8, zlength. rewrite length_map. reflexivity. Qed.
Lemma norm8_bytes : forall l, Forall (fun b => 0 <= b < 256) (norm8 l).
Proof. intros l. unfold norm8. apply Forall_map. apply Forall_forall. intros b _. apply Z.mod_pos_bound. lia. Qed.
Lemma norm8_id : forall l, Forall (fun b => 0 <= b < 256) l -> norm8 l = l.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hb Hl]; subst.
  cbn. rewrite Z.mod_small by lia. f_equal. apply IH. exact Hl.
Qed.

Fixpoint zstore (buf : list Z) (o : Z) (bs : list Z) : list Z :=
  match bs with
  | [] => buf
  | b :: bs' => zstore (zupd buf o b) (o + 1) bs'
  end.
Lemma zstore_length : forall bs buf o, zlength (zstore buf o bs) = zlength buf.
Proof. induction bs as [|b bs IH]; intros; cbn; [reflexivity|]. rewrite IH. apply zlength_zupd. Qed.

Fixpoint zlist_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zlist_eqb a' b'
  | _, _ => false
  end.
Lemma zlist_eqb_eq : forall a b, zlist_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try reflexivity; try discriminate.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. congruence.
  - inversion H; subst. apply andb_true_iff. split; [apply Z.eqb_refl| apply IH; reflexivity].
Qed.

Local Open Scope string_scope.
Definition N_deflateInit : list Z := str "deflateInit".
Definition N_deflate1 : list Z := str "deflate small 1".
Definition N_deflate2 : list Z := str "deflate small 2".
Definition N_deflateEnd : list Z := str "deflateEnd".
Definition N_inflateInit : list Z := str "inflateInit".
Definition N_inflate : list Z := str "inflate".
Definition N_inflateEnd : list Z := str "inflateEnd".
Definition msg_err (what : list Z) (rc : Z) : list Z := what ++ str " error: " ++ Zsdecimal rc ++ [10].
Definition MSG_BAD_INFLATE : list Z := str "bad inflate" ++ [10].
Local Close Scope string_scope.

Section Harness.
Variable za : zapi.

Definition ZD_FUEL (d : list Z) (cl : Z) : nat := Z.to_nat (2 * (zlength d + cl) + 16).

Definition ZI_FUEL (size cl : Z) : nat := Z.to_nat (size + cl + 16).

Definition DSA : Type := (DS za * Z)%type.

Definition d_call (d : list Z) (dsa : DSA) (flush : Z) : DSA * list Z * Z :=
  let '(ds', ai', _, bs, rc) := d_deflate za d (fst dsa) (if flush =? Z_NO_FLUSH then 1 else snd dsa) 1 flush in
  ((ds', ai'), bs, rc).

Definition i_call (comprc : list Z) (is : IS za) (ok : bool) : IS za * list Z * Z :=
  let '(is', _, _, bs, rc) := i_inflate za comprc is 1 1 ok in (is', bs, rc).

Definition d_step_ok (d : list Z) (cl : Z) (ds : DS za) (dsa' : DSA) (bs : list Z) : bool :=
  (0 <=? snd dsa') && (snd dsa' <=? 1) && (0 <=? d_total_in za (fst dsa')) && (d_total_in za (fst dsa') + snd dsa' <=? zlength d)
  && (d_total_out za (fst dsa') =? d_total_out za ds + zlength bs) && (d_total_out za (fst dsa') <=? cl).

Fixpoint dloop1 (fuel : nat) (d : list Z) (cl : Z) (dsa : DSA) (out : list Z) : option (DSA * list Z) :=
  match fuel with
  | O => None
  | S f =>
      if negb (d_total_in za (fst dsa) =? zlength d) && (d_total_out za (fst dsa) <? cl) then
        let '(dsa', bs, rc) := d_call d dsa Z_NO_FLUSH in
        if d_step_ok d cl (fst dsa) dsa' bs then
          if rc =? Z_OK then dloop1 f d cl dsa' (zstore out (d_total_out za (fst dsa)) bs) else None
        else None
      else Some (dsa, out)
  end.

Fixpoint dloop2 (fuel : nat) (d : list Z) (cl : Z) (dsa : DSA) (out : list Z) : option (DSA * list Z) :=
  match fuel with
  | O => None
  | S f =>
      let '(dsa', bs, rc) := d_call d dsa Z_FINISH in
      if d_step_ok d cl (fst dsa) dsa' bs then
        let out' := zstore out (d_total_out za (fst dsa)) bs in
        if rc =? Z_STREAM_END then Some (dsa', out')
        else if rc =? Z_OK then dloop2 f d cl dsa' out'
        else None
      else None
  end.

Definition test_deflate_pure (d : list Z) (cl : Z) : option (list Z) :=

  match dloop1 (ZD_FUEL d cl) d cl (d_init za, 0) (zrepeat 0 cl) with
  | None => None
  | Some (dsa1, out1) =>
      match dloop2 (ZD_FUEL d cl) d cl dsa1 out1 with
      | None => None
      | Some (dsa2, out2) => if d_end za (fst dsa2) =? Z_OK then Some out2 else None
      end
  end.

Inductive ires : Type :=
| IRdone (is : IS za) (uc : list Z)
| IRerr (rc : Z)
| IRstuck.

Definition i_out_ok (size : Z) (is : IS za) (bs : list Z) : bool := i_total_out za is + zlength bs <=? size.
Definition i_next_ok (size cl : Z) (is' : IS za) : bool :=
  (0 <=? i_total_in za is') && (i_total_in za is' <=? cl) && (0 <=? i_total_out za is') && (i_total_out za is' <=? size).

Fixpoint iloop_pure (fuel : nat) (comprc : list Z) (size cl : Z) (is : IS za) (uc : list Z) : ires :=
  match fuel with
  | O => IRstuck
  | S f =>
      if (i_total_out za is <? size) && (i_total_in za is <? cl) then
        let '(is', bs, rc) := i_call comprc is true in
        if i_out_ok size is bs then
          let uc' := zstore uc (i_total_out za is) bs in
          if rc =? Z_STREAM_END then IRdone is' uc'
          else if rc =? Z_OK then (if i_next_ok size cl is' then iloop_pure f comprc size cl is' uc' else IRstuck)
          else IRerr rc
        else IRstuck
      else IRdone is uc
  end.

Definition test_inflate_stderr (d8 comprc : list Z) (size cl : Z) : list Z :=
  match iloop_pure (ZI_FUEL size cl) (norm8 comprc) size cl (i_init za) (zrepeat 0 size) with
  | IRerr rc => msg_err N_inflate rc
  | IRdone is uc => if i_end za is =? Z_OK then (if zlist_eqb (norm8 uc) d8 then [] else MSG_BAD_INFLATE) else []
  | IRstuck => []
  end.

Definition harness_stderr (d : list Z) : list Z :=
  let size := zlength d in
  if (size <? 1) || (ZH_MAX <? size) then []
  else
    let d8 := norm8 d in
    let cl := z_bound za size in
    match test_deflate_pure d8 cl with
    | None => []
    | Some comprc => test_inflate_stderr d8 comprc size cl
    end.

Definition ZB_MAX : Z := 2 * ZH_MAX.

Record zapi_ok : Prop := mkZapiOk {

  zo_dinit : d_total_in za (d_init za) = 0 /\ d_total_out za (d_init za) = 0;
  zo_iinit : i_total_in za (i_init za) = 0 /\ i_total_out za (i_init za) = 0;

  zo_bound : forall n, 1 <= n <= ZH_MAX -> 0 < z_bound za n <= ZB_MAX;
  zo_sizes : Forall (fun n => 0 < n <= ZH_MAX)
                    [z_dstate za; z_dwin za; z_dprev za; z_dhead za; z_dpend za; z_isize za; z_wsize za];

  zo_deflate : forall d, 1 <= zlength d <= ZH_MAX -> Forall (fun b => 0 <= b < 256) d ->
    test_deflate_pure d (z_bound za (zlength d)) <> None;

  zo_inflate : forall size comprc, 1 <= size <= ZH_MAX ->
    zlength comprc = z_bound za size -> Forall (fun b => 0 <= b < 256) comprc ->
    match iloop_pure (ZI_FUEL size (z_bound za size)) comprc size (z_bound za size) (i_init za) (zrepeat 0 size) with
    | IRstuck => False
    | IRdone is _ => i_end za is = Z_OK
    | IRerr _ => True
    end;

  zo_nomem : forall comprc is, i_wants_window za comprc is = true ->
    snd (i_call comprc is false) = Z_MEM_ERROR;
  zo_nomem_bs : forall comprc is, i_wants_window za comprc is = true ->
    snd (fst (i_call comprc is false)) = snd (fst (i_call comprc is true));

  zo_irc : forall comprc is ok, - 2^31 <= snd (i_call comprc is ok) < 2^31
}.

End Harness.

Arguments IRdone {za}.
Arguments IRerr {za}.
Arguments IRstuck {za}.
