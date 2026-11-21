(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_tr_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land7_mod8 : forall a, a mod 8 = 0 -> Z.land a 7 = 0.
Proof. intros a H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.
Lemma land7_al16 : forall a, a mod 16 = 0 -> Z.land a 7 = 0.
Proof. intros a H. apply land7_mod8. Z.div_mod_to_equations. lia. Qed.
Lemma land3_mod4 : forall a, a mod 4 = 0 -> Z.land a 3 = 0.
Proof. intros a H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. exact H. Qed.
Lemma land1_mod2 : forall a, a mod 2 = 0 -> Z.land a 1 = 0.
Proof. intros a H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. exact H. Qed.

Ltac al8 X := first [ rewrite (land7_al16 X) by (Z.div_mod_to_equations; lia) | rewrite (land7_mod8 X) by (Z.div_mod_to_equations; lia) ].
Ltac al4 X := rewrite (land3_mod4 X) by (Z.div_mod_to_equations; lia).
Ltac al2 X := rewrite (land1_mod2 X) by (Z.div_mod_to_equations; lia).

Ltac gF := zstep; br_false.
Ltac gT := zstep; br_true.

Lemma ltu_neg_false : forall p a, 0 <= a -> a + Z.pos p <= 2^64 -> bv_ltu (Z_to_bv 64 (Zneg p)) (Z_to_bv 64 a) = false.
Proof.
  intros p a Ha Hp. unfold bv_ltu. rewrite (Z_to_bv_eqm (Zneg p) (2^64 - Z.pos p)).
  2:{ rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia. f_equal. }
  rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.
Ltac gN := zstep; lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; apply ltu_neg_false; lia] end.

Lemma b0h_w : forall X, 0 <= X < 2^16 -> bv_unsigned (Z_to_bv 64 X) mod 2^8 = wrap8 X mod 2^8.
Proof. intros X HX. rewrite unsigned_lit by lia. rewrite wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.
Lemma b0h_land : forall X, 0 <= X < 2^16 -> bv_unsigned (Z_to_bv 64 X) mod 2^8 = wrap8 (Z.land X 255) mod 2^8.
Proof.
  intros X HX. rewrite unsigned_lit by lia. rewrite !wrap8_mod by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma xor_guard : forall a b, 0 < a -> 0 < b -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (b <? 1)) = 1.
Proof. intros a b Ha Hb. rewrite (proj2 (Z.ltb_lt 0 a) Ha). rewrite (proj2 (Z.ltb_ge b 1)) by lia. reflexivity. Qed.
Ltac gX := rewrite xor_guard by lia; gF.

Lemma shl_guard0 : forall v k, 0 <= v -> 0 <= k < 32 -> v < 2^(31 - k) ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 v) ((Z.lxor k 18446744073709551615) mod 32)) = 0.
Proof.
  intros v k Hv Hk Hs. rewrite zb_lxor_ones by lia.
  replace ((18446744073709551615 - k) mod 32) with (31 - k).
  2:{ replace (18446744073709551615 - k) with ((31 - k) + 576460752303423487 * 32) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  assert (R : 0 <= v < 2^31).
  { split; [lia|]. eapply Z.lt_le_trans; [exact Hs|]. apply Z.pow_le_mono_r; lia. }
  rewrite (bv_wrap_small 32 v) by (unfold bv_modulus; cbn; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (split; [lia|]; exact Hs). reflexivity.
Qed.

Lemma land16_small : forall x, 0 <= x < 2^16 -> Z.land x 65535 = x.
Proof. intros x H. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

Lemma xor_guard1 : forall b, 0 < b -> Z.lxor 1 (Z.b2z (b <? 1)) = 1.
Proof. intros b Hb. rewrite (proj2 (Z.ltb_ge b 1)) by lia. reflexivity. Qed.

Lemma shl_guard_ok : forall bv, 0 <= bv < 32 -> Z.land (Z.b2z (bv <? 32)) (Z.b2z (0 <? 1)) = 1.
Proof. intros bv H. rewrite (proj2 (Z.ltb_lt bv 32)) by lia. reflexivity. Qed.
Ltac shl_g0 := rewrite shl_guard0 by first [lia | apply (Z.lt_le_trans _ (2^15)); [lia| apply Z.pow_le_mono_r; lia]].
Ltac shl_g1 := rewrite shl_guard_ok by lia.

Lemma xor_guard_sub : forall a b, 0 < a -> 0 <= b -> a <> b -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (Z.lxor a b <? 1)) = 1.
Proof.
  intros a b Ha Hb Hne. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
  assert (NZ : Z.lxor a b <> 0) by (intros E0; apply Hne; apply Z.lxor_eq; exact E0).
  pose proof (Z.lxor_nonneg a b) as NN.
  replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma xor_guard_sub0 : forall a, 0 < a -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (a <? 1)) = 1.
Proof. intros a Ha. rewrite (proj2 (Z.ltb_lt 0 a) Ha). replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Ltac gXsub := first [ rewrite xor_guard_sub by lia | rewrite xor_guard_sub0 by lia ]; zs; br_false.

Lemma mod32_add_mod64 : forall x b, (x + b mod 18446744073709551616) mod 2^32 = (x + b) mod 2^32.
Proof.
  intros x b. rewrite (Z.div_mod b 18446744073709551616) at 2 by lia.
  replace (x + (18446744073709551616 * (b / 18446744073709551616) + b mod 18446744073709551616))
     with ((x + b mod 18446744073709551616) + (4294967296 * (b / 18446744073709551616)) * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma swrap32_add_mod64 : forall a b, bv_swrap 32 (a + b mod 18446744073709551616) = bv_swrap 32 (a + b).
Proof.
  intros a b. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). f_equal.
  rewrite <- (Z.add_assoc a), (Z.add_comm (b mod _)), Z.add_assoc. rewrite mod32_add_mod64. f_equal. lia.
Qed.
Lemma wz_add_mod64 : forall a b, Z_to_bv 64 (a + b mod 18446744073709551616) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply Z_to_bv_eqm. rewrite (Z.div_mod b 18446744073709551616) at 2 by lia.
  replace (a + (18446744073709551616 * (b / 18446744073709551616) + b mod 18446744073709551616))
     with ((a + b mod 18446744073709551616) + (b / 18446744073709551616) * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma slti0_false : forall i, 0 <= i < 2^63 -> (Z.lxor i 9223372036854775808 <? 9223372036854775808) = false.
Proof.
  intros i Hi. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma xor_guard_idx : forall q p i, p <= q -> 0 <= i < 2^63 ->
  Z.lxor (Z.lxor (Z.b2z (q <? p)) (Z.b2z (Z.lxor i 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof. intros q p i Hq Hi. rewrite slti0_false by exact Hi. rewrite (proj2 (Z.ltb_ge q p)) by lia. reflexivity. Qed.

Lemma eqb_neg_false : forall p a, 0 <= a -> a + Z.pos p < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 (Zneg p)) = false.
Proof.
  intros p a Ha Hp. unfold bv_eqb. rewrite (Z_to_bv_eqm (Zneg p) (2^64 - Z.pos p)).
  2:{ rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia. f_equal. }
  rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.
Lemma eqb_neg_false' : forall p a, 0 <= a -> a + Z.pos p < 2^64 -> bv_eqb (Z_to_bv 64 (Zneg p)) (Z_to_bv 64 a) = false.
Proof.
  intros p a Ha Hp. unfold bv_eqb. rewrite (Z_to_bv_eqm (Zneg p) (2^64 - Z.pos p)).
  2:{ rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia. f_equal. }
  rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma slt_lxor : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  (Z.lxor a 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. change 9223372036854775808 with (2^63). rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec a b); [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia].
Qed.

Ltac lit_logic :=
  repeat match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with
      | context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
      | context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
      | context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
      end
  end.
Ltac guard_b2z :=
  repeat match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with
      | context [Z.b2z (?a <? ?b)] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
      | context [Z.b2z (?a =? ?b)] => first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
      end
  end; cbn [Z.b2z]; lit_logic.

Ltac guard_al c :=
  match c with
  | context [Z.land ?X 7] => al8 X
  | context [Z.land ?X 3] => al4 X
  | context [Z.land ?X 1] => al2 X
  | _ => idtac
  end.
Ltac guard_notb c :=
  match c with
  | context [Z.lxor ?X 18446744073709551615] => rewrite (zb_lxor_ones X) by lia
  | _ => idtac
  end.
Ltac gdecide_false :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    try guard_al c; try guard_notb c; try (rewrite xor_guard by lia); try (rewrite xor_guard1 by lia); try (rewrite xor_guard_sub by lia);
    try (rewrite xor_guard_idx by lia); try (rewrite slti0_false by lia); try (rewrite !slt_lxor by lia); try guard_b2z;
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c' then _ else _) _ _ _ _) =>
      first [ br_false
            | replace c' with false; [cbv iota| symmetry; apply ltu_neg_false; lia]
            | replace c' with false; [cbv iota| symmetry; apply eqb_neg_false; lia]
            | replace c' with false; [cbv iota| symmetry; apply eqb_neg_false'; lia] ] end
  end.
Ltac ustep T :=
  let t := eval cbv in T in
  zs2;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 t else _) _ _ _ _) => gdecide_false
       | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 t) _ _ _ _) => br_true
       end).
Ltac uwalk X T :=
  let x := eval cbv in X in
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 x) _ _ _ _) => fail
          | _ => ustep T
          end).
Ltac at_pc X :=
  let x := eval cbv in X in
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 x) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ ?p _ _ _ _) => fail 0 "not at pc" x "but" p
  end.
