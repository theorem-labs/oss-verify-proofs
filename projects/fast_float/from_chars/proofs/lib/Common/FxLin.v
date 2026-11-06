(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition two64 : Z := 18446744073709551616.
Definition M64 : Z := 18446744073709551615.
(* [comment removed for export] *)
Definition w64 (z : Z) : Z := match z with Zneg _ => Z.land z M64 | _ => if Z.ltb z two64 then z else Z.land z M64 end.

Lemma two64_eq : two64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma M64_ones : M64 = Z.ones 64. Proof. reflexivity. Qed.
Lemma w64_land : forall z, w64 z = Z.land z M64.
Proof.
  intros z. unfold w64. destruct z as [|p|p]; try reflexivity. destruct (Z.ltb (Zpos p) two64) eqn:H; [|reflexivity].
  apply Z.ltb_lt in H. rewrite M64_ones, Z.land_ones by lia. symmetry. apply Z.mod_small. unfold two64 in H. lia.
Qed.
Lemma w64_mod : forall z, w64 z = z mod two64.
Proof. intros z. rewrite w64_land, M64_ones, Z.land_ones by lia. reflexivity. Qed.
Lemma w64_range : forall z, 0 <= w64 z < two64.
Proof. intros z. rewrite w64_mod. apply Z.mod_pos_bound. reflexivity. Qed.

(* [comment removed for export] *)
Definition eqm (x y : Z) : Prop := x mod two64 = y mod two64.
Lemma eqm_refl : forall x, eqm x x. Proof. reflexivity. Qed.
Lemma eqm_sym : forall x y, eqm x y -> eqm y x. Proof. unfold eqm; congruence. Qed.
Lemma eqm_trans : forall x y z, eqm x y -> eqm y z -> eqm x z. Proof. unfold eqm; congruence. Qed.
Lemma eqm_add : forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof. unfold eqm. intros a b c d H1 H2. rewrite Z.add_mod, H1, H2, <- Z.add_mod by (unfold two64; lia). reflexivity. Qed.
Lemma eqm_mul : forall a b c d, eqm a b -> eqm c d -> eqm (a * c) (b * d).
Proof. unfold eqm. intros a b c d H1 H2. rewrite Z.mul_mod, H1, H2, <- Z.mul_mod by (unfold two64; lia). reflexivity. Qed.
Lemma eqm_w64 : forall z, eqm (w64 z) z.
Proof. intros z. unfold eqm. rewrite w64_mod. apply Z.mod_mod. unfold two64; lia. Qed.
Lemma eqm_mod : forall z, eqm (z mod two64) z.
Proof. intros z. unfold eqm. apply Z.mod_mod. unfold two64; lia. Qed.

Lemma Z_to_bv_eqm : forall x y, eqm x y -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H.
Qed.
Lemma u_Z_to_bv : forall z, bv_unsigned (Z_to_bv 64 z) = z mod two64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma eqm_u : forall z, eqm (bv_unsigned (Z_to_bv 64 z)) z.
Proof. intros z. rewrite u_Z_to_bv. apply eqm_mod. Qed.

(* [comment removed for export] *)
Record lin : Type := LIN { l_c : Z; l_t : list (positive * Z) }.
Definition valu : Type := positive -> word.
Definition vz (E : valu) (x : positive) : Z := bv_unsigned (E x).

Fixpoint tsum (E : valu) (t : list (positive * Z)) : Z :=
  match t with [] => 0 | (x, k) :: t' => k * vz E x + tsum E t' end.
Definition lz (E : valu) (l : lin) : Z := l_c l + tsum E (l_t l).
Definition lden (E : valu) (l : lin) : word := Z_to_bv 64 (lz E l).

(* [comment removed for export] *)
Fixpoint tadd (a : list (positive * Z)) : list (positive * Z) -> list (positive * Z) :=
  match a with
  | [] => fun b => b
  | (x, kx) :: a' =>
      fix go (b : list (positive * Z)) : list (positive * Z) :=
        match b with
        | [] => a
        | (y, ky) :: b' =>
            match Pos.compare x y with
            | Eq => let k := w64 (kx + ky) in if Z.eqb k 0 then tadd a' b' else (x, k) :: tadd a' b'
            | Lt => (x, kx) :: tadd a' b
            | Gt => (y, ky) :: go b'
            end
        end
  end.

Lemma tadd_nil_r : forall a, tadd a [] = a.
Proof. intros [|[x k] a]; reflexivity. Qed.

Lemma tadd_cons_cons : forall x kx a y ky b,
  tadd ((x, kx) :: a) ((y, ky) :: b) =
  match Pos.compare x y with
  | Eq => let k := w64 (kx + ky) in if Z.eqb k 0 then tadd a b else (x, k) :: tadd a b
  | Lt => (x, kx) :: tadd a ((y, ky) :: b)
  | Gt => (y, ky) :: tadd ((x, kx) :: a) b
  end.
Proof. reflexivity. Qed.

Lemma tadd_sound : forall E a b, eqm (tsum E (tadd a b)) (tsum E a + tsum E b).
Proof.
  intros E a. induction a as [|[x kx] a IHa]; intros b.
  - cbn. apply eqm_refl.
  - induction b as [|[y ky] b IHb].
    + rewrite tadd_nil_r. cbn. replace (kx * vz E x + tsum E a + 0) with (kx * vz E x + tsum E a) by lia. apply eqm_refl.
    + rewrite tadd_cons_cons. destruct (Pos.compare_spec x y) as [->|Hlt|Hgt].
      * cbv zeta. destruct (Z.eqb (w64 (kx + ky)) 0) eqn:Hk.
        -- apply Z.eqb_eq in Hk. cbn [tsum].
           assert (Hz : eqm ((kx + ky) * vz E y) 0).
           { eapply eqm_trans; [apply eqm_mul; [apply eqm_sym, eqm_w64 | apply eqm_refl]|].
             rewrite Hk, Z.mul_0_l. apply eqm_refl. }
           eapply eqm_trans; [apply IHa|].
           replace (kx * vz E y + tsum E a + (ky * vz E y + tsum E b))
             with ((kx + ky) * vz E y + (tsum E a + tsum E b)) by lia.
           apply eqm_sym. eapply eqm_trans; [apply eqm_add; [exact Hz | apply eqm_refl]|]. apply eqm_refl.
        -- cbn [tsum]. eapply eqm_trans; [apply eqm_add; [apply eqm_mul; [apply eqm_w64 | apply eqm_refl] | apply IHa]|].
           replace ((kx + ky) * vz E y + (tsum E a + tsum E b))
             with (kx * vz E y + tsum E a + (ky * vz E y + tsum E b)) by lia. apply eqm_refl.
      * cbn [tsum]. eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply IHa]|].
        cbn [tsum]. replace (kx * vz E x + (tsum E a + (ky * vz E y + tsum E b)))
          with (kx * vz E x + tsum E a + (ky * vz E y + tsum E b)) by lia. apply eqm_refl.
      * cbn [tsum]. eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply IHb]|].
        cbn [tsum]. replace (ky * vz E y + (kx * vz E x + tsum E a + tsum E b))
          with (kx * vz E x + tsum E a + (ky * vz E y + tsum E b)) by lia. apply eqm_refl.
Qed.

Fixpoint tscale (k : Z) (t : list (positive * Z)) : list (positive * Z) :=
  match t with
  | [] => []
  | (x, c) :: t' => let c' := w64 (k * c) in if Z.eqb c' 0 then tscale k t' else (x, c') :: tscale k t'
  end.

Lemma tscale_sound : forall E k t, eqm (tsum E (tscale k t)) (k * tsum E t).
Proof.
  intros E k t. induction t as [|[x c] t IH]; cbn [tscale tsum].
  - replace (k * 0) with 0 by lia. apply eqm_refl.
  - cbv zeta. destruct (Z.eqb (w64 (k * c)) 0) eqn:Hk.
    + apply Z.eqb_eq in Hk. eapply eqm_trans; [apply IH|].
      assert (Hz : eqm (k * c * vz E x) 0).
      { eapply eqm_trans; [apply eqm_mul; [apply eqm_sym, eqm_w64 | apply eqm_refl]|]. rewrite Hk, Z.mul_0_l. apply eqm_refl. }
      replace (k * (c * vz E x + tsum E t)) with (k * c * vz E x + k * tsum E t) by lia.
      apply eqm_sym. eapply eqm_trans; [apply eqm_add; [exact Hz | apply eqm_refl]|]. apply eqm_refl.
    + cbn [tsum]. eapply eqm_trans; [apply eqm_add; [apply eqm_mul; [apply eqm_w64 | apply eqm_refl] | apply IH]|].
      replace (k * (c * vz E x + tsum E t)) with (k * c * vz E x + k * tsum E t) by lia. apply eqm_refl.
Qed.

(* [comment removed for export] *)
Definition lconst (z : Z) : lin := LIN (w64 z) [].
Definition lvar (x : positive) : lin := LIN 0 [(x, 1)].
Definition ladd (a b : lin) : lin := LIN (w64 (l_c a + l_c b)) (tadd (l_t a) (l_t b)).
Definition lscale (k : Z) (a : lin) : lin := LIN (w64 (k * l_c a)) (tscale k (l_t a)).
(* [comment removed for export] *)
Definition negw (c : Z) : Z := let c0 := w64 c in if Z.eqb c0 0 then 0 else two64 - c0.
Fixpoint tneg (t : list (positive * Z)) : list (positive * Z) :=
  match t with
  | [] => []
  | (x, c) :: t' => let c' := negw c in if Z.eqb c' 0 then tneg t' else (x, c') :: tneg t'
  end.
Definition lneg (a : lin) : lin := LIN (negw (l_c a)) (tneg (l_t a)).
Definition lsub (a b : lin) : lin := ladd a (lneg b).
Definition laddc (a : lin) (z : Z) : lin := LIN (w64 (l_c a + z)) (l_t a).
Definition is_const (l : lin) : option Z := match l_t l with [] => Some (w64 (l_c l)) | _ => None end.

Lemma lden_eqm : forall E a b, eqm (lz E a) (lz E b) -> lden E a = lden E b.
Proof. intros. unfold lden. apply Z_to_bv_eqm. assumption. Qed.

Lemma lz_ladd : forall E a b, eqm (lz E (ladd a b)) (lz E a + lz E b).
Proof.
  intros E [ca ta] [cb tb]. unfold lz, ladd; cbn [l_c l_t].
  eapply eqm_trans; [apply eqm_add; [apply eqm_w64 | apply tadd_sound]|].
  replace (ca + cb + (tsum E ta + tsum E tb)) with (ca + tsum E ta + (cb + tsum E tb)) by lia. apply eqm_refl.
Qed.
Lemma lz_lscale : forall E k a, eqm (lz E (lscale k a)) (k * lz E a).
Proof.
  intros E k [ca ta]. unfold lz, lscale; cbn [l_c l_t].
  eapply eqm_trans; [apply eqm_add; [apply eqm_w64 | apply tscale_sound]|].
  replace (k * (ca + tsum E ta)) with (k * ca + k * tsum E ta) by lia. apply eqm_refl.
Qed.
Lemma negw_eq : forall c, negw c = w64 (M64 * c).
Proof.
  intros c. unfold negw. rewrite !w64_mod. unfold two64, M64.
  destruct (Z.eqb_spec (c mod 18446744073709551616) 0) as [H0|H0].
  - replace (18446744073709551615 * c) with (c * 18446744073709551616 - c) by lia.
    rewrite Zminus_mod, Z_mod_mult, H0. reflexivity.
  - replace (18446744073709551615 * c) with ((- c) + c * 18446744073709551616) by lia.
    rewrite Z_mod_plus_full. rewrite Z_mod_nz_opp_full by exact H0. reflexivity.
Qed.
Lemma tneg_eq : forall t, tneg t = tscale M64 t.
Proof. induction t as [|[x c] t IH]; cbn [tneg tscale]; [reflexivity|]. rewrite negw_eq, IH. reflexivity. Qed.
Lemma lneg_eq : forall a, lneg a = lscale M64 a.
Proof. intros [c t]. unfold lneg, lscale; cbn [l_c l_t]. rewrite negw_eq, tneg_eq. reflexivity. Qed.

Lemma lz_lneg : forall E a, eqm (lz E (lneg a)) (- lz E a).
Proof.
  intros E a. rewrite lneg_eq. eapply eqm_trans; [apply lz_lscale|].
  unfold eqm. replace (M64 * lz E a) with (- lz E a + lz E a * two64) by (unfold M64, two64; lia).
  apply Z_mod_plus_full.
Qed.
Lemma lz_lsub : forall E a b, eqm (lz E (lsub a b)) (lz E a - lz E b).
Proof.
  intros E a b. unfold lsub. eapply eqm_trans; [apply lz_ladd|].
  replace (lz E a - lz E b) with (lz E a + - lz E b) by lia. apply eqm_add; [apply eqm_refl | apply lz_lneg].
Qed.
Lemma lz_laddc : forall E a z, eqm (lz E (laddc a z)) (lz E a + z).
Proof.
  intros E [ca ta] z. unfold lz, laddc; cbn [l_c l_t].
  eapply eqm_trans; [apply eqm_add; [apply eqm_w64 | apply eqm_refl]|].
  replace (ca + z + tsum E ta) with (ca + tsum E ta + z) by lia. apply eqm_refl.
Qed.
Lemma lz_lconst : forall E z, eqm (lz E (lconst z)) z.
Proof. intros E z. unfold lz, lconst; cbn [l_c l_t tsum]. rewrite Z.add_0_r. apply eqm_w64. Qed.

Lemma lden_lconst : forall E z, lden E (lconst z) = Z_to_bv 64 z.
Proof. intros. unfold lden. apply Z_to_bv_eqm. apply lz_lconst. Qed.
Lemma lden_lvar : forall E x, lden E (lvar x) = E x.
Proof.
  intros E x. unfold lden, lz, lvar; cbn [l_c l_t tsum]. unfold vz.
  replace (0 + (1 * bv_unsigned (E x) + 0)) with (bv_unsigned (E x)) by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma is_const_sound : forall E l z, is_const l = Some z -> lden E l = Z_to_bv 64 z /\ 0 <= z < two64.
Proof.
  intros E [c t] z H. unfold is_const in H; cbn [l_t l_c] in H. destruct t; [|discriminate]. injection H as <-.
  split; [|apply w64_range]. unfold lden, lz; cbn [l_c l_t tsum]. apply Z_to_bv_eqm. rewrite Z.add_0_r. apply eqm_sym, eqm_w64.
Qed.

(* [comment removed for export] *)
Lemma lden_ladd : forall E a b, lden E (ladd a b) = bv_add (lden E a) (lden E b).
Proof.
  intros E a b. apply bv_eq. rewrite bv_add_unsigned. unfold lden. rewrite !u_Z_to_bv.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  pose proof (lz_ladd E a b) as H. unfold eqm in H. rewrite H.
  rewrite Z.add_mod by (unfold two64; lia). reflexivity.
Qed.
Lemma lden_lsub : forall E a b, lden E (lsub a b) = bv_sub (lden E a) (lden E b).
Proof.
  intros E a b. apply bv_eq. rewrite bv_sub_unsigned. unfold lden. rewrite !u_Z_to_bv.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  pose proof (lz_lsub E a b) as H. unfold eqm in H. rewrite H.
  rewrite Zminus_mod. reflexivity.
Qed.
Lemma lden_laddc : forall E a z, lden E (laddc a z) = Z_to_bv 64 (bv_unsigned (lden E a) + z).
Proof.
  intros E a z. unfold lden at 1. apply Z_to_bv_eqm. eapply eqm_trans; [apply lz_laddc|].
  apply eqm_add; [apply eqm_sym, eqm_u | apply eqm_refl].
Qed.
Lemma lden_lscale : forall E k a, lden E (lscale k a) = Z_to_bv 64 (k * bv_unsigned (lden E a)).
Proof.
  intros E k a. unfold lden at 1. apply Z_to_bv_eqm. eapply eqm_trans; [apply lz_lscale|].
  apply eqm_mul; [apply eqm_refl | apply eqm_sym, eqm_u].
Qed.
