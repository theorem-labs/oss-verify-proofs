(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint rom_bytes (a : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (Z_to_bv 64 a) with
            | Some b => match rom_bytes (a + 1) n' with Some r => Some (b :: r) | None => None end
            | None => None
            end
  end.
Definition img_word (a : Z) : option Z :=
  match rom_bytes a 8 with Some bs => Some (bytes_le_to_Z bs) | None => None end.
Fixpoint mk_img_acc (n : nat) (k : Z) (t : tree Z) : tree Z :=
  match n with
  | O => t
  | S n' => mk_img_acc n' (k + 1) (match img_word (8 * k) with Some w => tset (Z.to_pos (k + 1)) w t | None => t end)
  end.
(* [comment removed for export] *)
Definition mk_img (lo : Z) (n : nat) : tree Z := mk_img_acc n (Z.shiftr lo 3) TEmpty.

#[using="Type"] Lemma rom_bytes_spec : forall n a bs, rom_bytes a n = Some bs ->
  length bs = n /\ forall j b, nth_error bs j = Some b -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat j)) = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros a bs H; cbn [rom_bytes] in H.
  - injection H as <-. split; [reflexivity|]. intros [|j] b Hb; discriminate.
  - destruct (seg_rom segs (Z_to_bv 64 a)) as [b0|] eqn:Hb0; [|discriminate].
    destruct (rom_bytes (a + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) r Hr) as [Hlen Hn]. split; [cbn; lia|].
    intros [|j] b Hb; cbn [nth_error] in Hb.
    + injection Hb as <-. rewrite Z.add_0_r. exact Hb0.
    + replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact (Hn j b Hb).
Qed.

#[using="Type"] Lemma testbit_small : forall x k, 0 <= x < 256 -> 8 <= k -> Z.testbit x k = false.
Proof. LiaFast.lf_pins LiaFast.u0. intros x k Hx Hk. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). apply Z.mod_pow2_bits_high; lia. Qed.

#[using="Type"] Lemma byte_of_le : forall bs j b, nth_error bs j = Some b ->
  Z_to_bv 8 (Z.land (Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)) 255) = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b0 bs IH]; intros j b Hj; [destruct j; discriminate|].
  rewrite byte_land255. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b0) as R0. unfold bv_modulus in R0. change (2 ^ Z.of_N 8) with 256 in R0.
  destruct j as [|j]; cbn [nth_error] in Hj.
  - injection Hj as <-. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite Z.mul_0_r, Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    apply Z.bits_inj'. intros k Hk. destruct (Z.lt_ge_cases k 8).
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec_low by lia. rewrite orb_false_r. reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia. symmetry. apply testbit_small; lia.
  - rewrite <- (IH j b Hj). rewrite byte_land255. apply Z_to_bv8_bits. intros k Hk.
    rewrite !Z.shiftr_spec by lia. rewrite Z.lor_spec. rewrite testbit_small by lia.
    rewrite orb_false_l. rewrite Z.shiftl_spec by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma mk_img_acc_ok : forall n k t, 0 <= k -> img_ok segs t -> img_ok segs (mk_img_acc n k t).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros k t Hk Ht; cbn [mk_img_acc]; [exact Ht|].
  apply IH; [lia|].
  destruct (img_word (8 * k)) as [w|] eqn:Hw; [|exact Ht].
  intros p v Hp j Hj. destruct (Pos.eq_dec p (Z.to_pos (k + 1))) as [->|Hne].
  - rewrite tget_tset_same in Hp. injection Hp as <-.
    unfold img_word in Hw. destruct (rom_bytes (8 * k) 8) as [bs|] eqn:Hbs; [|discriminate]. injection Hw as <-.
    destruct (rom_bytes_spec 8 _ _ Hbs) as [Hlen Hn].
    destruct (nth_error bs (Z.to_nat j)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    rewrite Z2Pos.id by lia. replace (k + 1 - 1) with k by lia.
    pose proof (Hn (Z.to_nat j) b Hb) as Hr. rewrite Z2Nat.id in Hr by lia. rewrite Hr.
    f_equal. rewrite <- (byte_of_le bs (Z.to_nat j) b Hb). rewrite Z2Nat.id by lia. reflexivity.
  - rewrite tget_tset_other in Hp by congruence. exact (Ht p v Hp j Hj).
Qed.

#[using="Type"] Lemma mk_img_ok : forall lo n, 0 <= lo -> img_ok segs (mk_img lo n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros lo n Hlo. apply mk_img_acc_ok; [apply Z.shiftr_nonneg; lia|].
  intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma img_bytes_spec : forall img n a bks, img_ok segs img -> 0 <= a -> img_bytes img a n = Some bks ->
  length bks = n /\ forall j v, nth_error bks j = Some v -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat j)) = Some (Z_to_bv 8 v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros img n. induction n as [|n IH]; intros a bks Himg Ha H; cbn [img_bytes] in H.
  - injection H as <-. split; [reflexivity|]. intros [|j] v Hv; discriminate.
  - destruct (tget (wkey a) img) as [w|] eqn:Hw; [|discriminate].
    destruct (img_bytes img (a + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) r Himg ltac:(lia) Hr) as [Hlen Hn]. split; [cbn; lia|].
    intros [|j] v Hv; cbn [nth_error] in Hv.
    + injection Hv as <-. rewrite Z.add_0_r.
      pose proof (Himg _ _ Hw (Z.land a 7) ltac:(pose proof (Z.land_nonneg a 7); change 7 with (Z.ones 3); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound a 8 ltac:(lia)); change (2^3) with 8; lia)) as Hb.
      unfold wkey in Hb. rewrite Z2Pos.id in Hb by (pose proof (Z.shiftr_nonneg a 3); lia).
      replace (8 * (Z.shiftr a 3 + 1 - 1) + Z.land a 7) with a in Hb.
      { rewrite Hb. reflexivity. }
      rewrite Z.shiftr_div_pow2 by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
      pose proof (Z.div_mod a 8 ltac:(lia)). lia.
    + replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact (Hn j v Hv).
Qed.

End WithSegs.
