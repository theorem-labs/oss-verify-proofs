(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition wa (z : Z) : word := Z_to_bv 64 z.

Lemma u_wa : forall z, bv_unsigned (wa z) = z mod 2^64.
Proof. intros. unfold wa. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.

Lemma u_wa_small : forall z, 0 <= z < 2^64 -> bv_unsigned (wa z) = z.
Proof. intros. rewrite u_wa. apply Z.mod_small. lia. Qed.

Lemma wa_eqm : forall a b, a mod 2^64 = b mod 2^64 -> wa a = wa b.
Proof. intros a b H. apply bv_eq. rewrite !u_wa. exact H. Qed.

Lemma wa_u : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.



Lemma mod_mod_div : forall z a b, 0 < a -> 0 < b -> (z mod (a * b)) mod a = z mod a.
Proof.
  intros z a b Ha Hb. rewrite (Z.div_mod z (a * b)) at 2 by lia.
  replace (a * b * (z / (a * b))) with ((b * (z / (a * b))) * a) by ring.
  rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Lemma mod64_32 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. intros. change (2^64) with (2^32 * 2^32). apply mod_mod_div; lia. Qed.
Lemma mod64_64s : forall z, (z mod 2^64) mod 64 = z mod 64.
Proof. intros. change (2^64) with (64 * 2^58). apply mod_mod_div; lia. Qed.
Lemma mod64_32s : forall z, (z mod 2^64) mod 32 = z mod 32.
Proof. intros. change (2^64) with (32 * 2^59). apply mod_mod_div; lia. Qed.

Lemma swrap32_eqm : forall x y, x mod 2^32 = y mod 2^32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
  intros x y H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  change (2^32 `div` 2) with (2^31). f_equal.
  rewrite <- (Z.add_mod_idemp_l x (2^31)), <- (Z.add_mod_idemp_l y (2^31)) by lia.
  change (2 ^ Z.pos 32) with (2^32). rewrite H. reflexivity.
Qed.

Section ZEval.
Variable E : env.

Fixpoint zeval (e : expr) : Z :=
  match e with
  | ELit z => z
  | EAlu ALU_ADD a b => zeval a + zeval b
  | EAlu ALU_SUB a b => zeval a - zeval b
  | EAlu ALU_AND a b => Z.land (zeval a mod 2^64) (zeval b mod 2^64)
  | EAlu ALU_OR a b => Z.lor (zeval a mod 2^64) (zeval b mod 2^64)
  | EAlu ALU_SRL a b => Z.shiftr (zeval a mod 2^64) (zeval b mod 64)
  | EAlu ALU_SLL a b => Z.shiftl (zeval a mod 2^64) (zeval b mod 64)
  | EMd M_MUL a b => zeval a * zeval b
  | EAluw ALU_ADD a b => bv_swrap 32 (zeval a + zeval b)
  | EAluw ALU_SLL a b => bv_swrap 32 (Z.shiftl (zeval a mod 2^64) (zeval b mod 32))
  | EExt sx lo n a => ext_Z sx lo n (zeval a mod 2^64)
  | _ => bv_unsigned (edenot E e)
  end.

#[using="Type"] Lemma zeval_sound : forall e, edenot E e = wa (zeval e).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    try (cbn [zeval]; rewrite wa_u; reflexivity).
  - reflexivity.
  - destruct op; cbn [zeval edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb.
    + rewrite alu_add. unfold v_add. apply wa_eqm. rewrite !u_wa. rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
    + rewrite alu_sub. unfold v_sub. apply wa_eqm. rewrite !u_wa. rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
    + rewrite alu_sll. unfold v_sll. rewrite !u_wa. rewrite mod64_64s. reflexivity.
    + rewrite alu_srl. unfold v_srl. rewrite !u_wa. rewrite mod64_64s. reflexivity.
    + rewrite alu_or. unfold v_or. rewrite !u_wa. reflexivity.
    + rewrite alu_and. unfold v_and. rewrite !u_wa. reflexivity.
  - destruct op; cbn [zeval edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb.
    + rewrite w_addw. unfold v_addw. rewrite !u_wa. unfold wa. f_equal. apply swrap32_eqm.
      rewrite Zplus_mod. rewrite !mod64_32. rewrite <- Zplus_mod. reflexivity.
    + rewrite w_sllw. unfold v_sllw. rewrite !u_wa. rewrite mod64_32s. reflexivity.
  - destruct op; cbn [zeval edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb.
    rewrite m_mul. unfold v_mul. apply wa_eqm. rewrite !u_wa. rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
  - cbn [zeval edenot]. rewrite IHa. unfold ext_val. rewrite u_wa. reflexivity.
Qed.

#[using="Type"] Lemma adenot_z : forall e off, adenot E (SA e off) = wa (zeval e + off).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros e off. unfold adenot, v_addi. cbn [a_base a_off]. rewrite zeval_sound. rewrite u_wa.
  apply wa_eqm. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma estart_z : forall e off, 0 <= zeval e < 2^64 -> estart E (SA e off) = zeval e + off.
Proof. LiaFast.lf_pins LiaFast.u0. intros e off H. unfold estart. cbn [a_base a_off]. rewrite zeval_sound, u_wa_small by exact H. reflexivity. Qed.

#[using="Type"] Lemma elenZ_lit : forall z, 0 <= z < 2^64 -> elenZ E (ELit z) = z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z H. unfold elenZ. cbn [edenot]. apply u_small. exact H. Qed.

#[using="Type"] Lemma flat_z : forall e off n, 0 <= zeval e < 2^64 -> 0 <= zeval e + off -> zeval e + off + n <= 2^64 -> 0 < n ->
  flat E (SA e off) n.
Proof. LiaFast.lf_pins LiaFast.u0. intros e off n H1 H2 H3 H4. unfold flat. rewrite estart_z by exact H1. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kword_z : forall segs m e off w v,
  (1 <= w <= 8)%nat -> 0 <= zeval e < 2^64 -> 0 <= zeval e + off -> zeval e + off + Z.of_nat w <= 2^64 ->
  rdn segs m (wa (zeval e + off)) w = Some (word_to_le_bytes w (wa (zeval v))) ->
  kentry_ok segs E m (KWord (SA e off) w v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs m e off w v Hw H1 H2 H3 Hr. cbn [kentry_ok]. split; [lia|]. split; [apply flat_z; lia|].
  rewrite adenot_z, zeval_sound. exact Hr.
Qed.

#[using="Type"] Lemma krange_z : forall segs m e lo hi, lo <= zeval e mod 2^64 <= hi -> kentry_ok segs E m (KRange e lo hi).
Proof. LiaFast.lf_pins LiaFast.u0. intros segs m e lo hi H. cbn [kentry_ok]. rewrite zeval_sound, u_wa. lia. Qed.

#[using="Type"] Lemma kalign_z : forall segs m e k, 0 < k -> (zeval e mod 2^64) mod k = 0 -> kentry_ok segs E m (KAlign e k).
Proof. LiaFast.lf_pins LiaFast.u0. intros segs m e k Hk H. cbn [kentry_ok]. rewrite zeval_sound, u_wa. auto. Qed.

#[using="Type"] Lemma kdisj_z : forall segs m e1 o1 n1 e2 o2 n2,
  0 <= zeval e1 < 2^64 -> 0 <= zeval e2 < 2^64 -> 0 <= n1 < 2^64 -> 0 <= n2 < 2^64 ->
  (zeval e1 + o1 + n1 <= zeval e2 + o2 \/ zeval e2 + o2 + n2 <= zeval e1 + o1) ->
  kentry_ok segs E m (KDisj (SA e1 o1) (ELit n1) (SA e2 o2) (ELit n2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs m e1 o1 n1 e2 o2 n2 H1 H2 H3 H4 H. cbn [kentry_ok]. rewrite !estart_z by assumption.
  rewrite !elenZ_lit by assumption. exact H.
Qed.

#[using="Type"] Lemma kwr_z : forall segs m e off n,
  0 <= zeval e < 2^64 -> 0 <= zeval e + off -> zeval e + off + n <= 2^64 -> 0 < n < 2^64 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok segs m (wa (zeval e + off + d)) k = true) ->
  kentry_ok segs E m (KWr (SA e off) (ELit n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs m e off n H1 H2 H3 H4 H. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [apply flat_z; lia|].
  rewrite estart_z by exact H1. exact H.
Qed.



End ZEval.

Lemma sc_br_z : forall segs base E t c a b,
  branch_taken c (wa (zeval E a)) (wa (zeval E b)) = t -> sc_denot segs base E (SCBr t c a b).
Proof. intros. cbn [sc_denot]. rewrite !zeval_sound. assumption. Qed.

Lemma br_eq_z : forall x y, branch_taken BC_EQ (wa x) (wa y) = (x mod 2^64 =? y mod 2^64).
Proof.
  intros. cbn [branch_taken]. unfold bv_eqb. rewrite !u_wa. reflexivity.
Qed.
Lemma br_ne_z : forall x y, branch_taken BC_NE (wa x) (wa y) = negb (x mod 2^64 =? y mod 2^64).
Proof. intros. cbn [branch_taken]. unfold bv_eqb. rewrite !u_wa. reflexivity. Qed.
Lemma br_geu_z : forall x y, branch_taken BC_GEU (wa x) (wa y) = negb (x mod 2^64 <? y mod 2^64).
Proof. intros. cbn [branch_taken]. unfold bv_ltu. rewrite !u_wa. reflexivity. Qed.
Lemma br_ltu_z : forall x y, branch_taken BC_LTU (wa x) (wa y) = (x mod 2^64 <? y mod 2^64).
Proof. intros. cbn [branch_taken]. unfold bv_ltu. rewrite !u_wa. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rng64 : forall X lo hi, lo <= X <= hi -> ((0 <=? lo) && (hi <? 2^64)) = true -> 0 <= X < 2^64.
Proof. intros X lo hi H B. apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. Qed.
Lemma rng_lo : forall X lo hi k, lo <= X <= hi -> (0 <=? lo + k) = true -> 0 <= X + k.
Proof. intros X lo hi k H B. apply Z.leb_le in B. lia. Qed.
Lemma rng_hi : forall X lo hi k w, lo <= X <= hi -> (hi + k + w <=? 2^64) = true -> X + k + w <= 2^64.
Proof. intros X lo hi k w H B. apply Z.leb_le in B. lia. Qed.
Lemma rng_sub : forall X lo hi lo' hi', lo <= X <= hi -> ((lo' <=? lo) && (hi <=? hi')) = true -> lo' <= X <= hi'.
Proof. intros X lo hi lo' hi' H B. apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia. Qed.

Ltac zrange :=
  match goal with
  | H : ?lo <= ?X <= ?hi |- 0 <= ?X < 2^64 => exact (rng64 X lo hi H eq_refl)
  | H : ?lo <= ?X <= ?hi |- 0 <= ?X + ?k => exact (rng_lo X lo hi k H eq_refl)
  | H : ?lo <= ?X <= ?hi |- ?X + ?k + ?w <= 2^64 => exact (rng_hi X lo hi k w H eq_refl)
  | H : ?lo <= ?X <= ?hi |- ?lo2 <= ?X <= ?hi2 => exact (rng_sub X lo hi lo2 hi2 H eq_refl)
  end.

(* [comment removed for export] *)
Lemma Z_to_bv8_eqm : forall a b, a mod 2^8 = b mod 2^8 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). exact H. Qed.

Lemma mod_pow2_bits_eq : forall a b k, 0 <= k -> a mod 2^k = b mod 2^k -> forall i, 0 <= i < k -> Z.testbit a i = Z.testbit b i.
Proof.
  intros a b k Hk H i Hi. rewrite <- (Z.mod_pow2_bits_low a k i) by lia. rewrite <- (Z.mod_pow2_bits_low b k i) by lia.
  rewrite H. reflexivity.
Qed.

Lemma bits_eq_mod_pow2 : forall a b k, 0 <= k -> (forall i, 0 <= i < k -> Z.testbit a i = Z.testbit b i) -> a mod 2^k = b mod 2^k.
Proof.
  intros a b k Hk H. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i k) as [Hl|Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_eqm : forall n a b, a mod 2^(8 * Z.of_nat n) = b mod 2^(8 * Z.of_nat n) ->
  Z_to_le_bytes n a = Z_to_le_bytes n b.
Proof.
  induction n as [|n IH]; intros a b H; [reflexivity|]. cbn [Z_to_le_bytes]. f_equal.
  - apply Z_to_bv8_eqm. apply bits_eq_mod_pow2; [lia|]. intros i Hi.
    apply (mod_pow2_bits_eq a b (8 * Z.of_nat (S n))); [lia | exact H | lia].
  - apply IH. apply bits_eq_mod_pow2; [lia|]. intros i Hi. rewrite !Z.shiftr_spec by lia.
    apply (mod_pow2_bits_eq a b (8 * Z.of_nat (S n))); [lia | exact H | lia].
Qed.

Lemma le_wa_eqm : forall n x y, x mod 2^(8 * Z.of_nat n) = y mod 2^(8 * Z.of_nat n) -> (n <= 8)%nat ->
  word_to_le_bytes n (wa x) = word_to_le_bytes n (wa y).
Proof.
  intros n x y H Hn. unfold word_to_le_bytes. apply Z_to_le_bytes_eqm. rewrite !u_wa.
  assert (Hd : forall z, (z mod 2^64) mod 2^(8 * Z.of_nat n) = z mod 2^(8 * Z.of_nat n)).
  { intros z. replace (2^64) with (2^(8 * Z.of_nat n) * 2^(64 - 8 * Z.of_nat n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply mod_mod_div; apply Z.pow_pos_nonneg; lia. }
  rewrite !Hd. exact H.
Qed.

Lemma v_addi_wa : forall z k, 0 <= z < 2^64 -> v_addi (wa z) k = wa (z + k).
Proof. intros z k H. unfold v_addi. rewrite u_wa_small by exact H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac zlit := lazymatch goal with
  | |- (?a <= ?b <= ?c)%nat => split; apply Nat.leb_le; reflexivity
  | |- ?a <= ?b < ?c => split; [apply Z.leb_le; reflexivity | apply Z.ltb_lt; reflexivity]
  | |- ?a < ?b < ?c => split; apply Z.ltb_lt; reflexivity
  | |- ?a <= ?b <= ?c => split; apply Z.leb_le; reflexivity
  | |- ?a < ?b => apply Z.ltb_lt; reflexivity
  | |- ?a <= ?b => apply Z.leb_le; reflexivity
  end.

Ltac litmods := repeat match goal with
  | |- context [?x mod ?k] =>
      lazymatch x with Z.pos _ => idtac | Z0 => idtac | Z.neg _ => idtac end;
      lazymatch k with Z.pos _ => idtac | Z.pow (Z.pos _) (Z.pos _) => idtac end;
      let v := eval vm_compute in (x mod k) in change (x mod k) with v
  end.

Lemma mod64_of_range : forall x lo hi, lo <= x <= hi -> (0 <=? lo) = true -> (hi <? 2^64) = true -> x mod 2^64 = x.
Proof. intros x lo hi H1 H2 H3. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.mod_small. lia. Qed.
