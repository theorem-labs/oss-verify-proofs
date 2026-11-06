(* Pure facts for the ASan+UBSan walk of name_ok on image B (lib/B/Prog/name_ok.v, name_ok_s1.v): the image-B port of
   lib/A/Prog/name_ok_lem.v (commit ce5629fa227b). The byte test of SegModel.name_ok, the bit
   mask 2^50 + 2^13 + 3 that the loop shifts by (c - 45) after the unsigned guard (c - 45) <= 50, and the string's
   bytes one at a time. No image, no machine: image B's loop tests the same bytes with the same mask (0x8a458 ..
   0x8a490), so the text is the A file's. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Open Scope Z_scope.

(* the byte test name_ok applies to each byte, and its part for the four punctuation bytes '.', '-', ':', '_' *)
Definition nk_ch (c : Z) : bool := isalnum c || (c =? 46) || (c =? 45) || (c =? 58) || (c =? 95).
Definition nk_sp (c : Z) : bool := (c =? 46) || (c =? 45) || (c =? 58) || (c =? 95).
Definition NK_MASK : Z := 1125899906850819.

Lemma nk_mask_eq : NK_MASK = 2 ^ 50 + 2 ^ 13 + 3.
Proof. reflexivity. Qed.

Lemma nk_name_ok : forall s, s <> [] -> ~ In 0 s -> name_ok s = forallb nk_ch s.
Proof.
  intros s Hs Hn. unfold name_ok. rewrite cut_nul_id by exact Hn.
  destruct s as [|x s']; [contradiction | reflexivity].
Qed.

Lemma nk_name_ok_nil : name_ok [] = false.
Proof. reflexivity. Qed.

Lemma nk_ch_sp : forall c, isalnum c = false -> nk_ch c = nk_sp c.
Proof. intros c H. unfold nk_ch, nk_sp. rewrite H. reflexivity. Qed.

Lemma nk_ch_alnum : forall c, isalnum c = true -> nk_ch c = true.
Proof. intros c H. unfold nk_ch. rewrite H. reflexivity. Qed.

Lemma nk_sp_out : forall c, c < 45 \/ 95 < c -> nk_sp c = false.
Proof.
  intros c Hc. unfold nk_sp.
  rewrite (proj2 (Z.eqb_neq c 46)), (proj2 (Z.eqb_neq c 45)), (proj2 (Z.eqb_neq c 58)), (proj2 (Z.eqb_neq c 95))
    by lia.
  reflexivity.
Qed.

(* bit (c - 45) of the mask is set exactly for the four punctuation bytes, over the 51 values the guard admits *)
Lemma nk_bit : forall c, 45 <= c <= 95 ->
  (Z.land (Z.shiftr NK_MASK (c - 45)) 1 =? 0) = negb (nk_sp c).
Proof.
  intros c Hc.
  assert (H : forallb (fun d => Bool.eqb (Z.land (Z.shiftr NK_MASK d) 1 =? 0) (negb (nk_sp (d + 45))))
                (map Z.of_nat (seq 0 51)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (c - 45)). replace (c - 45 + 45) with c in H by lia.
  apply Bool.eqb_prop. apply H. apply in_map_iff. exists (Z.to_nat (c - 45)).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma nk_bit_z : forall c, 45 <= c <= 95 ->
  (Z.land (Z.shiftr NK_MASK (c - 45)) 1 = 0 <-> nk_sp c = false).
Proof.
  intros c Hc. pose proof (nk_bit c Hc) as B.
  split; intros H.
  - rewrite H in B. change (0 =? 0) with true in B.
    destruct (nk_sp c); [discriminate | reflexivity].
  - rewrite H in B. cbn [negb] in B. apply Z.eqb_eq. exact B.
Qed.

(* the unsigned guard `bltu 50, c - 45` on a byte: (c - 45) mod 2^64 <= 50 exactly when 45 <= c <= 95 *)
Lemma nk_mod_neg : forall x, 0 <= x < 45 -> (x - 45) mod 2 ^ 64 = x - 45 + 2 ^ 64.
Proof.
  intros x Hx. change (2 ^ 64) with 18446744073709551616.
  rewrite <- (Z.mod_add (x - 45) 1 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.

Lemma nk_rng_in : forall x, 0 <= x < 256 -> (x - 45) mod 2 ^ 64 <= 50 -> 45 <= x <= 95.
Proof.
  intros x Hx H. destruct (Z.lt_ge_cases x 45) as [L|L].
  - rewrite (nk_mod_neg x) in H by lia. change (2 ^ 64) with 18446744073709551616 in H. lia.
  - rewrite Z.mod_small in H by (change (2 ^ 64) with 18446744073709551616; lia). lia.
Qed.

Lemma nk_rng_out : forall x, 0 <= x < 256 -> 50 < (x - 45) mod 2 ^ 64 -> x < 45 \/ 95 < x.
Proof.
  intros x Hx H. destruct (Z.lt_ge_cases x 45) as [L|L]; [left; exact L|].
  rewrite Z.mod_small in H by (change (2 ^ 64) with 18446744073709551616; lia). lia.
Qed.

(* the loop's view of the bytes: skipn k s is s[k] :: skipn (k + 1) s, and nothing is left at the end *)
Lemma nk_skipn_cons : forall (s : list Z) k x, nth_error s k = Some x -> skipn k s = x :: skipn (S k) s.
Proof.
  induction s as [|y s IH]; intros [|k] x H; cbn in H; try discriminate.
  - inversion H. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma nk_forallb_end : forall (s : list Z) k, (length s <= k)%nat -> forallb nk_ch (skipn k s) = true.
Proof. intros s k H. rewrite skipn_all2 by exact H. reflexivity. Qed.

(* the bytes of a C string with its NUL: byte k exists for k <= |s|, and it is 0 exactly at k = |s| *)
Lemma nk_nth_full : forall (s : list Z) i, (i <= length s)%nat -> nth_error (s ++ [0]) i = Some (nth i (s ++ [0]) 0).
Proof.
  intros s i H. apply nth_error_nth'. rewrite length_app. cbn [length]. lia.
Qed.

Lemma nk_nth_zero : forall (s : list Z) i, ~ In 0 s -> (i <= length s)%nat ->
  (nth i (s ++ [0]) 0 = 0 <-> i = length s).
Proof.
  intros s i NZ H. destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite app_nth2, Nat.sub_diag by lia. split; reflexivity.
  - rewrite app_nth1 by lia. split; [|intros; lia]. intros E. exfalso. apply NZ.
    rewrite <- E. apply nth_In. lia.
Qed.

Lemma nk_nth_app : forall (s : list Z) i, (i < length s)%nat -> nth i (s ++ [0]) 0 = nth i s 0.
Proof. intros s i H. apply app_nth1. exact H. Qed.

Lemma nk_nth_error : forall (s : list Z) i, (i < length s)%nat -> nth_error s i = Some (nth i s 0).
Proof. intros s i H. apply nth_error_nth'. exact H. Qed.

(* the answer in each exit of the loop *)
Lemma nk_step_ok : forall s k c, nth_error s k = Some c -> name_ok s = forallb nk_ch (skipn k s) ->
  nk_ch c = true -> name_ok s = forallb nk_ch (skipn (S k) s).
Proof.
  intros s k c E H Hc. rewrite (nk_skipn_cons s k c E) in H. cbn [forallb] in H. rewrite Hc in H. exact H.
Qed.

Lemma nk_step_fail : forall s k c, nth_error s k = Some c -> name_ok s = forallb nk_ch (skipn k s) ->
  nk_ch c = false -> name_ok s = false.
Proof.
  intros s k c E H Hc. rewrite (nk_skipn_cons s k c E) in H. cbn [forallb] in H. rewrite Hc in H. exact H.
Qed.

Lemma nk_done : forall s k, (length s <= k)%nat -> name_ok s = forallb nk_ch (skipn k s) -> name_ok s = true.
Proof. intros s k Hk H. rewrite H. apply nk_forallb_end. exact Hk. Qed.

Lemma nk_start : forall s, s <> [] -> ~ In 0 s -> name_ok s = forallb nk_ch (skipn 0 s).
Proof. intros s Hs Hn. rewrite skipn_O. apply nk_name_ok; assumption. Qed.

Lemma nk_byte_range : forall s i, Forall (fun c => 0 <= c < 256) s -> (i < length s)%nat -> 0 <= nth i s 0 < 256.
Proof.
  intros s i HF Hi. rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hi.
Qed.
