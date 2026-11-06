(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require ExLoad.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxKb AxVal AxVal32 AxBytes.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition amo_k (wd : awidth) : Z := match wd with AW => 2 | AD => 3 end.

(* [comment removed for export] *)
Definition a_aligned (s : store) (wd : awidth) (v : xv) : bool :=
  match v with
  | XL x => (wl x land (match wd with AW => 3 | AD => 7 end) =? 0)%uint63
  | _ => let p := to_kb s v in (amo_k wd <=? lowrun (fst p)) &&& (Z.land (snd p) (Z.ones (amo_k wd)) =? 0)
  end.

Lemma a_aligned_sound (ρ : valuation) (s : store) (wd : awidth) (v : xv) (a : bv 64) :
  sat ρ s -> xv_val ρ v a -> a_aligned s wd v = true -> amo_aligned wd a = true.
Proof.
  intros Hs Hv H. unfold amo_aligned. apply Z.eqb_eq.
  assert (Hk : amo_bytes wd = 2 ^ amo_k wd) by (destruct wd; reflexivity). rewrite Hk.
  assert (Hgen : (amo_k wd <=? lowrun (fst (to_kb s v))) &&& (Z.land (snd (to_kb s v)) (Z.ones (amo_k wd)) =? 0) = true ->
                 bv_unsigned a mod 2 ^ amo_k wd = 0).
  { intros Hc. apply land_true in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.eqb_eq in H2.
    pose proof (to_kb_sound ρ s v a Hs Hv) as Hkb. destruct (lowrun_spec (fst (to_kb s v))) as [_ Hbits].
    rewrite (kb_mod _ _ _ (amo_k wd) ltac:(destruct wd; cbn; lia) (fun i Hi => Hbits i ltac:(lia)) Hkb).
    rewrite Z.land_ones in H2 by (destruct wd; cbn; lia). exact H2. }
  destruct v as [x| | | | |]; try (exact (Hgen H)).
  cbn [a_aligned] in H. cbn [xv_val] in Hv. rewrite Hv. apply Uint63.eqb_spec in H. apply (f_equal to_Z) in H.
  rewrite land_spec' in H. change (to_Z 0%uint63) with 0 in H.
  rewrite wZ_split. pose proof (to_Z_bounded (wl x)) as Hb.
  assert (E : (Z.b2z (wh x) * two63 + to_Z (wl x)) mod 2 ^ amo_k wd = to_Z (wl x) mod 2 ^ amo_k wd).
  { replace (Z.b2z (wh x) * two63) with ((Z.b2z (wh x) * 2 ^ (63 - amo_k wd)) * 2 ^ amo_k wd).
    - rewrite Z.add_comm. apply Z.mod_add. destruct wd; cbn; lia.
    - rewrite <- Z.mul_assoc, <- Z.pow_add_r by (destruct wd; cbn; lia). replace (63 - amo_k wd + amo_k wd) with 63 by lia. reflexivity. }
  rewrite E. destruct wd; cbn [amo_k] in *.
  - change (to_Z 3%uint63) with (Z.ones 2) in H. rewrite Z.land_ones in H by lia. exact H.
  - change (to_Z 7%uint63) with (Z.ones 3) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Definition xv_same (x y : xv) : bool :=
  match x, y with
  | XL a, XL b => w_eqb a b
  | XS t1 o1, XS t2 o2 => w_eqb o1 o2 &&& teqb t1 t2
  | _, _ => false
  end.

Lemma xv_same_sound (ρ : valuation) (x y : xv) (a b : bv 64) : xv_same x y = true -> xv_val ρ x a -> xv_val ρ y b -> a = b.
Proof.
  intros H Hx Hy. apply bv_eq. destruct x as [p|t1 o1| | | |], y as [q|t2 o2| | | |]; cbn [xv_same] in H; try discriminate; cbn [xv_val] in *.
  - rewrite w_eqb_spec in H. apply Z.eqb_eq in H. lia.
  - apply land_true in H as [H1 H2]. rewrite w_eqb_spec in H1. apply Z.eqb_eq in H1. apply wZ_inj in H1. apply teqb_eq in H2. subst.
    rewrite Hx, Hy. reflexivity.
Qed.

(* [comment removed for export] *)
Definition amo_bytes_d (s : store) (op : amoop) (old src : xv) : list xb :=
  match op with
  | AMO_SWAP => bytes_of SZ8 src
  | AMO_ADD => bytes_of SZ8 (a_add s old src)
  | AMO_XOR => bytes_of SZ8 (a_xor s old src)
  | AMO_AND => bytes_of SZ8 (a_and s old src)
  | AMO_OR => bytes_of SZ8 (a_or s old src)
  | _ => repeat BT 8
  end.

Lemma Forall2_BT (ρ : valuation) (n : nat) (bs : list byte) : length bs = n -> Forall2 (xb_bv ρ) (repeat BT n) bs.
Proof. revert bs. induction n as [|n IH]; intros [|b bs] H; try discriminate; constructor; [exact I | apply IH; cbn in H; lia]. Qed.

Lemma amo_bytes_d_sound (ρ : valuation) (s : store) (op : amoop) (old src : xv) (o x : bv 64) :
  sat ρ s -> xv_val ρ old o -> xv_val ρ src x ->
  Forall2 (xb_bv ρ) (amo_bytes_d s op old src) (Z_to_le_bytes 8 (bv_unsigned (amo_val op o x))).
Proof.
  intros Hs Ho Hx.
  assert (E : forall w : bv 64, Z_to_le_bytes 8 (bv_unsigned w) = store_bytes SZ8 w) by reflexivity.
  rewrite E. destruct op; cbn [amo_bytes_d amo_val]; try (apply Forall2_BT; reflexivity).
  - apply bytes_of_sound. exact Hx.
  - apply bytes_of_sound. exact (a_add_sound ρ s old src o x Hs Ho Hx).
  - apply bytes_of_sound. exact (a_xor_sound ρ s old src o x Hs Ho Hx).
  - apply bytes_of_sound. exact (a_and_sound ρ s old src o x Hs Ho Hx).
  - apply bytes_of_sound. exact (a_or_sound ρ s old src o x Hs Ho Hx).
Qed.

(* [comment removed for export] *)
Definition amo_bytes_w (s : store) (op : amoop) (old src : xv) : list xb :=
  match op with
  | AMO_SWAP => bytes_of SZ4 src
  | AMO_ADD => match old, src with
               | XL a, XL b => bytes_of SZ4 (XL (w_add a b))
               | _, _ => repeat BT 4
               end
  | _ => repeat BT 4
  end.

Lemma low32_add_sext (o : bv 32) (x : bv 64) : low32 (sext 64 o + x)%bv = (o + low32 x)%bv.
Proof.
  apply bv_eq. rewrite low32_unsigned, !bv_add_unsigned, low32_unsigned, sext32_unsigned.
  unfold bv_wrap, bv_swrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  set (u := bv_unsigned o). set (X := bv_unsigned x).
  assert (E : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32)
    by (intros z; symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]).
  rewrite E. rewrite Zplus_mod. rewrite E. rewrite <- Zplus_mod. rewrite Zplus_mod_idemp_r.
  replace ((u + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31 + X) with (((u + 2 ^ 31) mod 2 ^ 32) + (X - 2 ^ 31)) by ring.
  rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.

Lemma amo_bytes_w_sound (ρ : valuation) (s : store) (op : amoop) (old src : xv) (o : bv 32) (x : bv 64) :
  sat ρ s -> xv_val ρ old (sext 64 o) -> xv_val ρ src x ->
  Forall2 (xb_bv ρ) (amo_bytes_w s op old src) (Z_to_le_bytes 4 (bv_unsigned (amo_val op o (low32 x)))).
Proof.
  intros Hs Ho Hx. destruct op; cbn [amo_bytes_w amo_val]; try (apply Forall2_BT; apply length_Z_to_le_bytes).
  - exact (bytes_of_sound ρ SZ4 src x Hx).
  - destruct old as [a| | | | |]; try (apply Forall2_BT; apply length_Z_to_le_bytes).
    destruct src as [b| | | | |]; try (apply Forall2_BT; apply length_Z_to_le_bytes).
    rewrite <- low32_add_sext.
    apply (bytes_of_sound ρ SZ4 (XL (w_add a b)) (sext 64 o + x)%bv).
    cbn [xv_val] in *. rewrite bv_add_unsigned, Ho, Hx. rewrite <- !wbv_unsigned, <- bv_add_unsigned, <- wbv_add. reflexivity.
Qed.
