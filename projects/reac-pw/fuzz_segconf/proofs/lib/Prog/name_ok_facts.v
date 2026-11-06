(** Pure facts for the walks of name_ok (Prog/name_ok.v, U/Prog/name_ok.v): no image. Written new.
    - [nok_ch]: the byte test of SegModel.name_ok; [nok_sp]: its "-.:_" part.
    - [nok_name_ok]: on a NUL-free nonempty string name_ok is forallb nok_ch (cut_nul is the identity).
    - [nok_bit]: bit (c - 0x2d) of the mask 2^50 + 2^13 + 3 (the `srl` + `andi 1` of the loop) is set exactly for
      "-.:_", for c in [0x2d, 0x5f] (the `bltu 0x32` guard), checked by vm_compute over the 51 values;
      [nok_bit_z] is the same as a Prop on (c + -0x2d), the shift once the walk drops its mod 2^64 and mod 64.
    - [nok_rng_in], [nok_rng_out]: the `bltu` guard (c - 0x2d) mod 2^64 <= 0x32 is 0x2d <= c <= 0x5f for a byte;
      [nok_sp_out]: outside [0x2d, 0x5f] no byte is one of "-.:_".
    - [nok_nth_full], [nok_nth_full_zero]: the bytes of a C string with its NUL (as strcasecmp.v's nth_full). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import MState Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Open Scope Z_scope.

Definition nok_ch (ch : Z) : bool := isalnum ch || (ch =? 46) || (ch =? 45) || (ch =? 58) || (ch =? 95).
Definition nok_sp (ch : Z) : bool := (ch =? 46) || (ch =? 45) || (ch =? 58) || (ch =? 95).
Definition NOK_MASK : Z := 1125899906850819.

Lemma nok_mask_eq : NOK_MASK = 2^50 + 2^13 + 3.
Proof. reflexivity. Qed.

Lemma nok_name_ok : forall s, s <> [] -> ~ In 0 s -> name_ok s = forallb nok_ch s.
Proof.
  intros s Hs Hn. unfold name_ok. rewrite cut_nul_id by exact Hn.
  destruct s as [|x s']; [contradiction | reflexivity].
Qed.

Lemma nok_name_ok_nil : name_ok [] = false.
Proof. reflexivity. Qed.

Lemma nok_ch_sp : forall c, isalnum c = false -> nok_ch c = nok_sp c.
Proof. intros c H. unfold nok_ch, nok_sp. rewrite H. reflexivity. Qed.

Lemma nok_ch_alnum : forall c, isalnum c = true -> nok_ch c = true.
Proof. intros c H. unfold nok_ch. rewrite H. reflexivity. Qed.

Lemma nok_sp_out : forall c, c < 45 \/ 95 < c -> nok_sp c = false.
Proof.
  intros c Hc. unfold nok_sp.
  rewrite (proj2 (Z.eqb_neq c 46)), (proj2 (Z.eqb_neq c 45)), (proj2 (Z.eqb_neq c 58)), (proj2 (Z.eqb_neq c 95))
    by lia.
  reflexivity.
Qed.

Lemma nok_bit : forall c, 45 <= c <= 95 ->
  (Z.land (Z.shiftr NOK_MASK (c - 45)) 1 =? 0) = negb (nok_sp c).
Proof.
  intros c Hc.
  assert (H : forallb (fun d => Bool.eqb (Z.land (Z.shiftr NOK_MASK d) 1 =? 0) (negb (nok_sp (d + 45))))
                (map Z.of_nat (seq 0 51)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (c - 45)). replace (c - 45 + 45) with c in H by lia.
  apply Bool.eqb_prop. apply H. apply in_map_iff. exists (Z.to_nat (c - 45)).
  split; [lia|]. apply in_seq. lia.
Qed.

(** The loop's view of the string: skipn k s is s[k] :: skipn (k + 1) s, and nothing at the end. *)
Lemma nok_skipn_cons : forall (s : list Z) k x, nth_error s k = Some x -> skipn k s = x :: skipn (S k) s.
Proof.
  induction s as [|y s IH]; intros [|k] x H; cbn in H; try discriminate.
  - inversion H. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma nok_forallb_end : forall (s : list Z) k, (length s <= k)%nat -> forallb nok_ch (skipn k s) = true.
Proof. intros s k H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma nok_rng_in : forall x, 0 <= x < 256 -> (x + -45) mod 18446744073709551616 <= 50 -> 45 <= x <= 95.
Proof.
  intros x Hx H. destruct (Z.lt_ge_cases x 45) as [L|L].
  - rewrite <- (Z.mod_unique (x + -45) 18446744073709551616 (-1) (x + -45 + 18446744073709551616)) in H by lia.
    lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma nok_rng_out : forall x, 0 <= x < 256 -> 50 < (x + -45) mod 18446744073709551616 -> x < 45 \/ 95 < x.
Proof.
  intros x Hx H. destruct (Z.lt_ge_cases x 45) as [L|L]; [left; exact L|].
  rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma nok_bit_z : forall x, 45 <= x <= 95 ->
  (Z.land (Z.shiftr 1125899906850819 (x + -45)) 1 = 0 <-> nok_sp x = false).
Proof.
  intros x Hx.
  pose proof (nok_bit x Hx) as B. unfold NOK_MASK in B. replace (x - 45) with (x + -45) in B by lia.
  split; intros H.
  - rewrite H in B. change (0 =? 0) with true in B.
    destruct (nok_sp x) eqn:E; [|reflexivity]. rewrite ?E in B. discriminate.
  - rewrite H in B. cbn [negb] in B. apply Z.eqb_eq. exact B.
Qed.

(** Bytes. *)
Lemma nok_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma nok_u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (nok_byte_range b). lia. Qed.

Lemma nok_u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. exact nok_u_byte. Qed.

Lemma nok_land255 : forall b : byte, Z.land (bv_unsigned b) 255 = bv_unsigned b.
Proof.
  intros b. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (nok_byte_range b). change (2 ^ 8) with 256. lia.
Qed.

Lemma nok_nth_full : forall (s : list byte) i, (i <= length s)%nat ->
  exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma nok_nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E.
  assert (Hl : (i < length (s ++ [Z_to_bv 8 0]))%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite length_app in Hl. cbn in Hl.
  destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.
