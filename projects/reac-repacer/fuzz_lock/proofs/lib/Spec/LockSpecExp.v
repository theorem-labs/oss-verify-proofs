(* Pure facts for the walk of the harness's own reading of the lock, [expected] of fuzz_lock.c:78-118
   (inlined in check_lookup, fuzz_lock.plain 0x12e28-0x130d0): its line loop is [lk], its nf < 3 field
   loop and [number] give [line_val], its [standard] is [std_period], and its (n - 1) >> 16 test is 1 <= n <= 65536.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import StrFun LockSpec.
Import ListNotations.
Open Scope Z_scope.

(** The line loop (fuzz_lock.c:84-116) is [lk]. *)

(* [lk] reads no further once its fuel covers the text *)
Lemma lk_fuel : forall p rate f1 f2 t found, (length t <= f1)%nat -> (length t <= f2)%nat ->
  lk f1 p rate t found = lk f2 p rate t found.
Proof.
  intros p rate f1. induction f1 as [|f1 IH]; intros f2 t found H1 H2.
  - destruct t as [|b t]; [|cbn in H1; lia]. destruct f2; reflexivity.
  - destruct t as [|b r]; [destruct f2; reflexivity|].
    destruct f2 as [|f2]; [cbn in H2; lia|].
    cbn [lk]. destruct (find_byte 10 (b :: r)) as [j|]; [|reflexivity].
    apply IH; rewrite length_skipn; cbn [length] in *; lia.
Qed.

(* the length of the line that starts t: up to its LF, else all of t *)
Definition line_len (t : list byte) : nat :=
  match find_byte 10 t with Some j => j | None => length t end.

Lemma line_len_le : forall t, (line_len t <= length t)%nat.
Proof.
  intros t. unfold line_len. destruct (find_byte 10 t) as [j|] eqn:F; [|lia].
  apply find_byte_Some in F. lia.
Qed.

(* One line of a text t that is not empty: [lk] restores the line's period, then reads on after its LF. *)
Lemma lk_line_lf : forall p rate t found j, find_byte 10 t = Some j ->
  lk (length t) p rate t found =
  lk (length (skipn (S j) t)) p rate (skipn (S j) t) (upd p rate (firstn (line_len t) t) found).
Proof.
  intros p rate t found j F. unfold line_len. rewrite F.
  destruct t as [|b r]; [discriminate|].
  cbn [length lk]. rewrite F. apply lk_fuel; rewrite length_skipn; cbn [length]; lia.
Qed.

Lemma lk_line_end : forall p rate t found, t <> [] -> find_byte 10 t = None ->
  lk (length t) p rate t found = upd p rate (firstn (line_len t) t) found.
Proof.
  intros p rate t found Ht F. unfold line_len. rewrite F, firstn_all.
  destruct t as [|b r]; [congruence|]. cbn [length lk]. rewrite F. reflexivity.
Qed.

Lemma lk_nil : forall f p rate found, lk f p rate [] found = found.
Proof. intros [|f]; reflexivity. Qed.

(* A text the size test lets through restores what [lk] restores from its start. *)
Lemma lock_lookup_lk : forall t p rate, std_period rate <> 0 -> Z.of_nat (length t) <= 65536 ->
  lock_lookup t p rate = lk (length t) p rate t 0.
Proof.
  intros t p rate HS L. unfold lock_lookup.
  replace (std_period rate =? 0) with false by (symmetry; apply Z.eqb_neq; exact HS).
  replace (65536 <? Z.of_nat (length t)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma lock_lookup_0 : forall t p rate, std_period rate = 0 \/ 65536 < Z.of_nat (length t) \/ t = [] ->
  lock_lookup t p rate = 0.
Proof.
  intros t p rate [HS|[L| ->]]; unfold lock_lookup.
  - rewrite HS. reflexivity.
  - replace (65536 <? Z.of_nat (length t)) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite orb_true_r. reflexivity.
  - destruct (_ || _); reflexivity.
Qed.

(** The machine's size test (fuzz_lock.c:81, n > LOCK_MAX): (n - 1) >> 16 is 0 iff 1 <= n <= 65536. *)
Lemma size_test : forall n, 0 <= n < 2^64 ->
  (Z.shiftr ((n - 1) mod 2^64) 16 =? 0) = ((1 <=? n) && (n <=? 65536)).
Proof.
  intros n Hn. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.eq_dec n 0) as [->|N0]; [reflexivity|].
  rewrite Z.mod_small by lia. replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  destruct (Z.leb_spec n 65536) as [L|L].
  - apply Z.eqb_eq. apply Z.div_small. lia.
  - apply Z.eqb_neq. assert (1 <= (n - 1) / 2^16) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(** [standard] (fuzz_lock.c:56): a rate it does not give 0 for is one of the three. *)
Lemma std_period_nz : forall rate, std_period rate <> 0 -> rate = 44100 \/ rate = 48000 \/ rate = 96000.
Proof.
  intros rate H. destruct (std_period_cases rate) as [E|[[E _]|[[E _]|[E _]]]]; [contradiction|auto|auto|auto].
Qed.

(** The fields of a line (fuzz_lock.c:94-104) are [fld]'s. *)

Lemma fld_eq : forall l q, fld l q = ((q + sep_run (skipn q l))%nat, tok_run (skipn (q + sep_run (skipn q l)) l)).
Proof. reflexivity. Qed.

(* a field read from the end of the line is empty *)
Lemma fld_end : forall l q, (length l <= q)%nat -> fld l q = (q, 0%nat).
Proof.
  intros l q H. unfold fld. rewrite !skipn_all2 by lia. cbn [sep_run tok_run]. rewrite Nat.add_0_r.
  reflexivity.
Qed.

(* the separator run after q reaches the end of the line: the field there is empty *)
Lemma fld_sep_end : forall l q, (q + sep_run (skipn q l))%nat = length l -> fld l q = (length l, 0%nat).
Proof. intros l q H. rewrite fld_eq, H. f_equal. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma fld_bound : forall l q, (q <= length l)%nat ->
  (q <= fst (fld l q) /\ fst (fld l q) + snd (fld l q) <= length l)%nat.
Proof.
  intros l q H. unfold fld. cbn [fst snd].
  pose proof (sep_run_le (skipn q l)) as A. rewrite length_skipn in A.
  pose proof (tok_run_le (skipn (q + sep_run (skipn q l)) l)) as B. rewrite length_skipn in B. lia.
Qed.

(* a field that starts before the line's end is not empty *)
Lemma sep_run_stop0 : forall l, (sep_run l < length l)%nat -> tok_run (skipn (sep_run l) l) <> 0%nat.
Proof.
  induction l as [|b r IH]; intros H; cbn [sep_run length] in *; [lia|].
  destruct (is_sep (bz b)) eqn:S; cbn [skipn].
  - apply IH. lia.
  - cbn [tok_run]. rewrite S. cbv iota. discriminate.
Qed.

Lemma sep_run_stop : forall l q, (q + sep_run (skipn q l) < length l)%nat ->
  tok_run (skipn (q + sep_run (skipn q l)) l) <> 0%nat.
Proof.
  intros l q H. rewrite Nat.add_comm, <- skipn_skipn. apply sep_run_stop0. rewrite length_skipn. lia.
Qed.

(* what a line that restores a period holds *)
Lemma line_val_inv : forall p rate l s1 l1 s2 l2 s3 l3 v,
  fld l 0 = (s1, l1) -> fld l (s1 + l1) = (s2, l2) -> fld l (s2 + l2) = (s3, l3) ->
  line_val p rate l = Some v ->
  find_byte 0 l = None /\ l1 <> 0%nat /\ bz (nth s1 l (Z_to_bv 8 0)) <> 35 /\ (l1 <= 15)%nat /\ l1 = length p /\
  memcmp_model (slice l s1 l1) p l1 = Some 0 /\ v = digits (slice l s2 l2) /\ 0 <= v /\
  digits (slice l s3 l3) = rate /\
  std_period rate - std_period rate / 20 <= v <= std_period rate + std_period rate / 20.
Proof.
  intros p rate l s1 l1 s2 l2 s3 l3 v E1 E2 E3 H. unfold line_val in H.
  rewrite E1 in H. cbv beta iota zeta in H. rewrite E2 in H. cbv beta iota zeta in H. rewrite E3 in H.
  cbv beta iota zeta in H.
  destruct (is_some (find_byte 0 l)) eqn:N0; [discriminate|].
  lazymatch type of H with (if ?c then None else _) = _ => destruct c eqn:N1; [discriminate|] end.
  lazymatch type of H with (if ?c then None else _) = _ => destruct c eqn:N2; [discriminate|] end.
  lazymatch type of H with (if ?c then None else _) = _ => destruct c eqn:N3; [discriminate|] end.
  lazymatch type of H with (if ?c then None else _) = _ => destruct c eqn:N4; [discriminate|] end.
  injection H as <-.
  assert (F0 : find_byte 0 l = None)
    by (revert N0; destruct (find_byte 0 l); cbn; intros N0; [discriminate N0 | reflexivity]).
  apply orb_false_iff in N1 as [N1a N1b]. apply Nat.eqb_neq in N1a. apply Z.eqb_neq in N1b.
  apply orb_false_iff in N2 as [N2 N2c]. apply orb_false_iff in N2 as [N2a N2b].
  apply Nat.ltb_ge in N2a. apply negb_false_iff, Nat.eqb_eq in N2b. apply negb_false_iff in N2c.
  apply orb_false_iff in N3 as [N3a N3b]. apply Z.ltb_ge in N3a. apply negb_false_iff, Z.eqb_eq in N3b.
  apply orb_false_iff in N4 as [N4a N4b]. apply Z.ltb_ge in N4a. apply Z.ltb_ge in N4b.
  assert (M : memcmp_model (slice l s1 l1) p l1 = Some 0).
  { revert N2c. destruct (memcmp_model (slice l s1 l1) p l1) as [[|z|z]|]; cbn; intros N2c;
      [reflexivity | discriminate N2c | discriminate N2c | discriminate N2c]. }
  repeat split; auto; lia.
Qed.

Lemma line_val_some : forall p rate l s1 l1 s2 l2 s3 l3,
  fld l 0 = (s1, l1) -> fld l (s1 + l1) = (s2, l2) -> fld l (s2 + l2) = (s3, l3) ->
  find_byte 0 l = None -> l1 <> 0%nat -> bz (nth s1 l (Z_to_bv 8 0)) <> 35 -> (l1 <= 15)%nat -> l1 = length p ->
  memcmp_model (slice l s1 l1) p l1 = Some 0 -> 0 <= digits (slice l s2 l2) ->
  digits (slice l s3 l3) = rate ->
  std_period rate - std_period rate / 20 <= digits (slice l s2 l2) <= std_period rate + std_period rate / 20 ->
  line_val p rate l = Some (digits (slice l s2 l2)).
Proof.
  intros p rate l s1 l1 s2 l2 s3 l3 E1 E2 E3 N0 N1 N2 N3 N4 M D1 D2 B. unfold line_val.
  rewrite E1. cbv beta iota zeta. rewrite E2. cbv beta iota zeta. rewrite E3. cbv beta iota zeta.
  rewrite N0, M. cbn [is_some negb].
  rewrite (proj2 (Nat.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2), (proj2 (Nat.ltb_ge _ _) N3), N4,
    Nat.eqb_refl, D2, Z.eqb_refl.
  rewrite (proj2 (Z.ltb_ge _ _) D1), (proj2 (Z.ltb_ge _ _) (proj1 B)), (proj2 (Z.ltb_ge _ _) (proj2 B)).
  reflexivity.
Qed.

Lemma upd_none : forall p rate l found, (forall v, line_val p rate l = Some v -> False) -> upd p rate l found = found.
Proof. intros p rate l found H. unfold upd. destruct (line_val p rate l) eqn:E; [exfalso; eapply H; eauto|reflexivity]. Qed.

Lemma upd_some : forall p rate l found v, line_val p rate l = Some v -> upd p rate l found = v.
Proof. intros p rate l found v H. unfold upd. rewrite H. reflexivity. Qed.

(* a line with fewer than three fields restores nothing *)
Lemma upd_l1 : forall p rate l found s1, fld l 0 = (s1, 0%nat) -> upd p rate l found = found.
Proof.
  intros p rate l found s1 E1. apply upd_none. intros v H.
  destruct (fld l (s1 + 0)) as [s2 l2] eqn:E2. destruct (fld l (s2 + l2)) as [s3 l3] eqn:E3.
  destruct (line_val_inv p rate l s1 0 s2 l2 s3 l3 v E1 E2 E3 H) as (_ & N & _). lia.
Qed.

Lemma upd_l2 : forall p rate l found s1 l1 s2, fld l 0 = (s1, l1) -> fld l (s1 + l1) = (s2, 0%nat) ->
  upd p rate l found = found.
Proof.
  intros p rate l found s1 l1 s2 E1 E2. apply upd_none. intros v H.
  destruct (fld l (s2 + 0)) as [s3 l3] eqn:E3.
  destruct (line_val_inv p rate l s1 l1 s2 0 s3 l3 v E1 E2 E3 H) as (_ & _ & _ & _ & _ & _ & V & P & _).
  assert (D : digits (slice l s2 0) = -1) by reflexivity. lia.
Qed.

Lemma upd_l3 : forall p rate l found s1 l1 s2 l2 s3, 0 <= rate ->
  fld l 0 = (s1, l1) -> fld l (s1 + l1) = (s2, l2) -> fld l (s2 + l2) = (s3, 0%nat) ->
  upd p rate l found = found.
Proof.
  intros p rate l found s1 l1 s2 l2 s3 R E1 E2 E3. apply upd_none. intros v H.
  destruct (line_val_inv p rate l s1 l1 s2 l2 s3 0 v E1 E2 E3 H) as (_ & _ & _ & _ & _ & _ & _ & _ & L & _).
  assert (D : digits (slice l s3 0) = -1) by reflexivity. lia.
Qed.

(** The NUL scan of a line (fuzz_lock.c:92-93). *)
Definition nulb (l : list byte) : bool := existsb (fun b => bz b =? 0) l.

Lemma nulb_find : forall l, is_some (find_byte 0 l) = nulb l.
Proof.
  unfold nulb. induction l as [|b l IH]; [reflexivity|]. cbn [find_byte existsb].
  destruct (bz b =? 0) eqn:E; unfold bz in E; rewrite E; [reflexivity|]. cbn [orb]. rewrite <- IH.
  destruct (find_byte 0 l); reflexivity.
Qed.

Lemma nulb_snoc : forall l b, nulb (l ++ [b]) = nulb l || (bz b =? 0).
Proof. intros l b. unfold nulb. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r. reflexivity. Qed.

(** [number] (fuzz_lock.c:64) is [digits]. *)

Lemma digits_bad_len : forall l, ((length l = 0)%nat \/ (18 < length l)%nat) -> digits l = -1.
Proof.
  intros l H. unfold digits.
  replace ((length l =? 0)%nat || (18 <? length l)%nat) with true; [reflexivity|].
  symmetry. apply orb_true_iff. destruct H as [H|H]; [left; apply Nat.eqb_eq | right; apply Nat.ltb_lt]; exact H.
Qed.

Lemma digits_good_len : forall l, (1 <= length l <= 18)%nat -> digits l = dig_go l 0.
Proof.
  intros l H. unfold digits.
  replace ((length l =? 0)%nat || (18 <? length l)%nat) with false; [reflexivity|].
  symmetry. apply orb_false_iff. split; [apply Nat.eqb_neq | apply Nat.ltb_ge]; lia.
Qed.

(** [memcmp] of the name: only the first k bytes of the port's string count. *)
Lemma memcmp_model_app_r : forall n l r r', (n <= length r)%nat ->
  memcmp_model l (r ++ r') n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros l r r' H; [reflexivity|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [length] in H; try lia; [reflexivity|].
  cbn [app memcmp_model]. destruct (bv_unsigned a =? bv_unsigned b); [|reflexivity]. apply IH. lia.
Qed.

Lemma memcmp_model_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn [memcmp_model] in H; [injection H as <-; lia|].
  destruct l as [|a l]; destruct r as [|b r]; simpl in H; try discriminate H.
  revert H. destruct (bv_unsigned a =? bv_unsigned b); intros H; [eapply IH; exact H|].
  injection H as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

(** The LF scan of a line (fuzz_lock.c:86-87). *)
Lemma firstn_snoc : forall {X} (l : list X) o b, nth_error l o = Some b -> firstn (S o) l = firstn o l ++ [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|o] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - f_equal. apply IH. exact N.
Qed.

Lemma find_byte_snoc_none : forall c l b, find_byte c l = None -> bv_unsigned b <> c -> find_byte c (l ++ [b]) = None.
Proof.
  intros c l b H N. rewrite find_byte_app_r by exact H. cbn [find_byte].
  rewrite (proj2 (Z.eqb_neq _ _) N). reflexivity.
Qed.

Lemma find_byte_at : forall c l o b, find_byte c (firstn o l) = None -> nth_error l o = Some b -> bv_unsigned b = c ->
  find_byte c l = Some o.
Proof.
  intros c l o b H N E. apply (find_byte_charact c l o b N E).
  intros j b' Hj Nj. apply (find_byte_None c (firstn o l) H j b').
  assert (Lo : (o < length l)%nat) by (apply nth_error_Some; congruence).
  rewrite <- (firstn_skipn o l) in Nj. rewrite nth_error_app1 in Nj by (rewrite length_firstn; lia). exact Nj.
Qed.

Lemma find_byte_all : forall c l, find_byte c (firstn (length l) l) = None -> find_byte c l = None.
Proof. intros c l H. rewrite firstn_all in H. exact H. Qed.
