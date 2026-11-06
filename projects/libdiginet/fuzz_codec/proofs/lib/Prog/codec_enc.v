From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(** A u32 argument v that the caller loaded with lw: the register holds v sign-extended from bit 31. *)
Lemma u32_small : forall v, 0 <= v < 2 ^ 31 -> bv_unsigned (Z_to_bv 64 (s32 v)) = v.
Proof.
  intros v H. unfold s32. replace (v <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  apply unsigned_lit. lia.
Qed.

Lemma u32_big : forall v, 2 ^ 31 <= v < 2 ^ 32 -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned (Z_to_bv 64 (s32 v)).
Proof.
  intros v H. unfold s32. replace (v <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full (v - 2 ^ 32) 1).
  rewrite Z.mod_small by lia. lia.
Qed.

(** An int argument v: the register holds v sign-extended. *)
Lemma s32_nonneg : forall v, 0 <= v < 2 ^ 31 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof. intros v H. apply unsigned_lit. lia. Qed.

Lemma s32_neg : forall v, - 2 ^ 31 <= v < 0 -> bv_unsigned (Z_to_bv 64 v) = v + 2 ^ 64.
Proof.
  intros v H. rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full v 1).
  rewrite Z.mod_small by lia. lia.
Qed.

(** delta_byte's range test (diginet_codec.c:138): `addiw r, delta, -64` then an unsigned compare with
    -128 holds exactly when -64 <= delta <= 63. *)
Lemma delta_range : forall d, - 2 ^ 31 <= d < 2 ^ 31 ->
  (2 ^ 64 - 128 <= bv_swrap 32 (d mod 2 ^ 64 + -64) mod 2 ^ 64 <-> -64 <= d <= 63).
Proof.
  intros d Hd. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  change (2 ^ 32 `div` 2) with (2 ^ 31).
  Z.div_mod_to_equations. lia.
Qed.

(** `snez` of an int argument on (sign-extended): the bit on != 0. *)
Lemma snez_s32 : forall on, - 2 ^ 31 <= on < 2 ^ 31 ->
  (0 <? on mod 18446744073709551616) = negb (on =? 0).
Proof.
  intros on H. destruct (Z.eqb_spec on 0) as [E|E]; [subst on; reflexivity|].
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

(** The UBSan alignment checks: `andi r, p, 3` / `andi r, p, 7` is 0 for p aligned to 4 / 8. *)
Lemma land3_aligned : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma land7_aligned : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma b8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma z8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.

(** The cells of a region, replaced by cells with the same bytes. *)
Lemma rw_cells_rebytes : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma rw_cells_len32 : forall segs m A before,
  rw_cells segs m A [CB 32 before] -> length before = 32%nat.
Proof. intros segs m A before [[[Hw _] _] _]. exact Hw. Qed.

(** ---- checks over every value of one small variable ---- *)

Lemma bf_in : forall z v, 0 <= v < z -> In v (map Z.of_nat (seq 0 (Z.to_nat z))).
Proof.
  intros z v H. apply in_map_iff. exists (Z.to_nat v). split; [lia|]. apply in_seq. lia.
Qed.

Lemma bf_mod : forall (z : Z) (f g : Z -> Z),
  forallb (fun v => f v mod 256 =? g v mod 256) (map Z.of_nat (seq 0 (Z.to_nat z))) = true ->
  forall v, 0 <= v < z -> f v mod 256 = g v mod 256.
Proof.
  intros z f g H v Hv. apply Z.eqb_eq. rewrite forallb_forall in H. apply (H v). apply bf_in. exact Hv.
Qed.

Lemma bf_z : forall (z : Z) (f g : Z -> Z),
  forallb (fun v => f v =? g v) (map Z.of_nat (seq 0 (Z.to_nat z))) = true ->
  forall v, 0 <= v < z -> f v = g v.
Proof.
  intros z f g H v Hv. apply Z.eqb_eq. rewrite forallb_forall in H. apply (H v). apply bf_in. exact Hv.
Qed.

Lemma bf_z2 : forall (z1 z2 : Z) (f g : Z -> Z -> Z),
  forallb (fun u => forallb (fun v => f u v =? g u v) (map Z.of_nat (seq 0 (Z.to_nat z2))))
          (map Z.of_nat (seq 0 (Z.to_nat z1))) = true ->
  forall u v, 0 <= u < z1 -> 0 <= v < z2 -> f u v = g u v.
Proof.
  intros z1 z2 f g H u v Hu Hv. apply Z.eqb_eq. rewrite forallb_forall in H.
  specialize (H u (bf_in z1 u Hu)). rewrite forallb_forall in H. apply (H v). apply bf_in. exact Hv.
Qed.

(** x mod 256 = y mod 256 (bf_m) or x = y (bf_e), where x and y depend on the variable v only and
    0 <= v < z: checked at every v by vm_compute. *)
Ltac bf_m v z :=
  lazymatch goal with
  | |- ?X mod 256 = ?Y mod 256 =>
      let f := lazymatch eval pattern v in X with ?F _ => F end in
      let g := lazymatch eval pattern v in Y with ?G _ => G end in
      refine (bf_mod z f g _ v _); [vm_compute; reflexivity | lia]
  end.
Ltac bf_e v z :=
  lazymatch goal with
  | |- ?X = ?Y =>
      let f := lazymatch eval pattern v in X with ?F _ => F end in
      let g := lazymatch eval pattern v in Y with ?G _ => G end in
      refine (bf_z z f g _ v _); [vm_compute; reflexivity | lia]
  end.

(* x = y over two variables u in [0, z1) and v in [0, z2). *)
Ltac bf_e2 u z1 v z2 :=
  lazymatch goal with
  | |- ?X = ?Y =>
      let f := lazymatch eval pattern u, v in X with ?F _ _ => F end in
      let g := lazymatch eval pattern u, v in Y with ?G _ _ => G end in
      refine (bf_z2 z1 z2 f g _ u v _ _); [vm_compute; reflexivity | lia | lia]
  end.

(** The 32 bytes l of length 32 (hypothesis H) as 32 variables. *)
Ltac destruct32 l H :=
  do 32 (let x := fresh "x" in destruct l as [|x l]; [cbn in H; lia|]);
  destruct l; [|cbn in H; lia].

(** The goals finish leaves on a failing return: rc and the unchanged command (hypothesis HC). *)
Ltac close_fail HC :=
  cbn beta iota;
  lazymatch goal with
  | |- _ /\ _ => split; [reflexivity | exact HC]
  | |- _ = _ => reflexivity
  | |- _ => exact HC
  end.
