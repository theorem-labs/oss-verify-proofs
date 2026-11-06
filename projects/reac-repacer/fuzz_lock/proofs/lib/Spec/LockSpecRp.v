(* Pure facts about LockSpec's grammar that the plain walk of rp_lock_lookup (lib/Prog/rp_lock_lookup.v) uses.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import StrFun LockSpec.
Import ListNotations.
Open Scope Z_scope.

(** The loop [lk]: its fuel only has to cover the text. *)

Lemma lk_nil : forall n p rate found, lk n p rate [] found = found.
Proof. intros [|n] p rate found; reflexivity. Qed.

Lemma lk_fuel : forall f1 f2 p rate t found, (length t <= f1)%nat -> (length t <= f2)%nat ->
  lk f1 p rate t found = lk f2 p rate t found.
Proof.
  induction f1 as [|f1 IH]; intros f2 p rate t found H1 H2.
  - destruct t as [|b t]; [rewrite !lk_nil; reflexivity | cbn [length] in H1; lia].
  - destruct f2 as [|f2].
    + destruct t as [|b t]; [rewrite !lk_nil; reflexivity | cbn [length] in H2; lia].
    + destruct t as [|b t]; [reflexivity|].
      cbn [lk]. destruct (find_byte 10 (b :: t)) as [j|]; [|reflexivity].
      apply IH; rewrite length_skipn; cbn [length] in *; lia.
Qed.

Lemma lk_some : forall p rate t found j, t <> [] -> find_byte 10 t = Some j ->
  lk (length t) p rate t found = lk (length (skipn (S j) t)) p rate (skipn (S j) t) (upd p rate (firstn j t) found).
Proof.
  intros p rate [|b t] found j NE FB; [congruence|].
  cbn [length lk]. rewrite FB. apply lk_fuel; rewrite length_skipn; cbn [length]; lia.
Qed.

Lemma lk_none : forall p rate t found, t <> [] -> find_byte 10 t = None ->
  lk (length t) p rate t found = upd p rate t found.
Proof. intros p rate [|b t] found NE FB; [congruence|]. cbn [length lk]. rewrite FB. reflexivity. Qed.

(** [line_val] with its three fields named. *)

Lemma line_val_spec : forall p rate l (s1 l1 s2 l2 s3 l3 : nat),
  s1 = sep_run l -> l1 = tok_run (skipn s1 l) ->
  s2 = (s1 + l1 + sep_run (skipn (s1 + l1) l))%nat -> l2 = tok_run (skipn s2 l) ->
  s3 = (s2 + l2 + sep_run (skipn (s2 + l2) l))%nat -> l3 = tok_run (skipn s3 l) ->
  line_val p rate l =
    if is_some (find_byte 0 l) then None
    else if (l1 =? 0)%nat || (bz (nth s1 l (Z_to_bv 8 0)) =? 35) then None
    else if (15 <? l1)%nat || negb (l1 =? length p)%nat
            || negb (match memcmp_model (slice l s1 l1) p l1 with Some 0 => true | _ => false end)
    then None
    else
      let per := digits (slice l s2 l2) in
      let lab := digits (slice l s3 l3) in
      if (per <? 0) || negb (lab =? rate) then None
      else if (per <? std_period rate - std_period rate / 20) || (std_period rate + std_period rate / 20 <? per)
      then None
      else Some per.
Proof. intros; subst; reflexivity. Qed.

(* the tail of [line_val] once the name matched *)
Definition tail_val (rate per lab found : Z) : Z :=
  if (per <? 0) || negb (lab =? rate) then found
  else if (per <? std_period rate - std_period rate / 20) || (std_period rate + std_period rate / 20 <? per)
  then found
  else per.

Lemma slice_length : forall l s n, (s + n <= length l)%nat -> length (slice l s n) = n.
Proof. intros l s n H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

(** [digits] *)

Definition isdig (c : Z) : bool := (48 <=? c) && (c <=? 57).

Lemma dig_go_skip_ok : forall l i b v, nth_error l i = Some b -> isdig (bz b) = true ->
  dig_go (skipn i l) v = dig_go (skipn (S i) l) (v * 10 + (bz b - 48)).
Proof.
  intros l; induction l as [|c l IH]; intros [|i] b v N D; cbn in N; try discriminate.
  - injection N as <-. cbn [skipn dig_go]. unfold isdig in D. rewrite D. reflexivity.
  - cbn [skipn]. apply IH; assumption.
Qed.

Lemma dig_go_skip_bad : forall l i b v, nth_error l i = Some b -> isdig (bz b) = false ->
  dig_go (skipn i l) v = -1.
Proof.
  intros l; induction l as [|c l IH]; intros [|i] b v N D; cbn in N; try discriminate.
  - injection N as <-. cbn [skipn dig_go]. unfold isdig in D. rewrite D. reflexivity.
  - cbn [skipn]. eapply IH; eassumption.
Qed.

Lemma dig_go_end : forall l v, dig_go (skipn (length l) l) v = v.
Proof. intros l v. rewrite skipn_all. reflexivity. Qed.

Lemma digits_ok : forall l, (1 <= length l <= 18)%nat -> digits l = dig_go l 0.
Proof.
  intros l H. unfold digits.
  replace ((length l =? 0)%nat || (18 <? length l)%nat) with false; [reflexivity|].
  symmetry. apply orb_false_iff. split; [apply Nat.eqb_neq | apply Nat.ltb_ge]; lia.
Qed.

Lemma digits_bad : forall l, (length l = 0 \/ 18 < length l)%nat -> digits l = -1.
Proof.
  intros l H. unfold digits.
  replace ((length l =? 0)%nat || (18 <? length l)%nat) with true; [reflexivity|].
  symmetry. apply orb_true_iff. destruct H; [left; apply Nat.eqb_eq | right; apply Nat.ltb_lt]; lia.
Qed.

Lemma dig_step_bound : forall v i c, 0 <= v < 10 ^ Z.of_nat i -> 48 <= c <= 57 ->
  0 <= v * 10 + (c - 48) < 10 ^ Z.of_nat (S i).
Proof.
  intros v i c Hv Hc. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

(** [memcmp_model]'s result is a difference of two bytes. *)

Lemma memcmp_model_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H; [injection H as <-; lia|].
  destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
  destruct (bv_unsigned a =? bv_unsigned b); [eapply IH; exact H|].
  injection H as <-. pose proof (bv_unsigned_in_range 8 a). pose proof (bv_unsigned_in_range 8 b).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

(** [std_period]'s values *)

Lemma std_period_pos : forall rate, rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  125000 <= std_period rate <= 272109.
Proof. intros rate [->|[->| ->]]; cbn; lia. Qed.
