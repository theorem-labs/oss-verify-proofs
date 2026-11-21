
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base ZBitsIn Inflate Inflate14.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma inf_iter14_add : forall k1 k2 c q q1,
  inf_iter14 k1 c q = Some q1 ->
  inf_iter14 (k1 + k2) c q = inf_iter14 k2 c q1.
Proof.
  induction k1 as [|k1 IH]; intros k2 c q q1 H.
  - cbn in H. injection H as <-. reflexivity.
  - replace (S k1 + k2)%nat with (S (k1 + k2))%nat by lia.
    cbn [inf_iter14] in H |- *.
    destruct (inf_step14 c q) as [q'| | | |]; try discriminate.
    now apply IH.
Qed.

Lemma inf_loop14_after_iter : forall k c q q1 n r,
  inf_iter14 k c q = Some q1 ->
  inf_loop14 n c q1 = Some r ->
  inf_loop14 (k + n) c q = Some r.
Proof.
  induction k as [|k IH]; intros c q q1 n r HI HL.
  - cbn in HI. injection HI as <-. exact HL.
  - replace (S k + n)%nat with (S (k + n))%nat by lia.
    cbn [inf_iter14] in HI. cbn [inf_loop14].
    destruct (inf_step14 c q) as [q'| | | |]; try discriminate.
    now apply (IH c q' q1).
Qed.

Lemma inf_iter14_one : forall c q q',
  inf_step14 c q = InfCont q' -> inf_iter14 1 c q = Some q'.
Proof. intros c q q' H. cbn [inf_iter14]. now rewrite H. Qed.

Lemma inf_loop14_one_exit : forall c q r,
  inf_step14 c q = r ->
  (match r with InfCont _ => False | _ => True end) ->
  inf_loop14 1 c q = Some r.
Proof.
  intros c q r H HX. cbn [inf_loop14]. rewrite H.
  destruct r; try reflexivity. contradiction.
Qed.

Lemma inf_iter14_alias_S : forall c a b k r,
  inf_step14 c a = inf_step14 c b ->
  inf_iter14 (S k) c b = Some r ->
  inf_iter14 (S k) c a = Some r.
Proof.
  intros c a b k r HE H. cbn [inf_iter14] in *. now rewrite HE.
Qed.

Lemma inf_loop14_alias_S : forall c a b n r,
  inf_step14 c a = inf_step14 c b ->
  inf_loop14 (S n) c b = Some r ->
  inf_loop14 (S n) c a = Some r.
Proof.
  intros c a b n r HE H. cbn [inf_loop14] in *. now rewrite HE.
Qed.
