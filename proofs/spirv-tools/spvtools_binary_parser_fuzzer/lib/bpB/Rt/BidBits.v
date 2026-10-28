(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BZBridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition cb1 (size : Z) : Z := Z.lor size (size ≫ 1 mod 18446744073709551616) mod 18446744073709551616.
Definition cb2 (e1 : Z) : Z := Z.lor e1 (e1 ≫ 2 mod 18446744073709551616) mod 18446744073709551616.
Definition cb3 (e2 : Z) : Z := Z.lor e2 (e2 ≫ 4 mod 18446744073709551616) mod 18446744073709551616.
Definition cb4 (e3 : Z) : Z := Z.lor e3 (e3 ≫ 8 mod 18446744073709551616) mod 18446744073709551616.
Definition cb5 (e4 : Z) : Z := Z.lor e4 (e4 ≫ 16 mod 18446744073709551616) mod 18446744073709551616.
Definition cb6 (e5 : Z) : Z := Z.lor e5 (e5 ≫ 32 mod 18446744073709551616) mod 18446744073709551616.
Definition cb7 (e6 : Z) : Z := Z.lxor e6 18446744073709551615 mod 18446744073709551616.
Definition cb8 (e7 : Z) : Z := (e7 - Z.land (e7 ≫ 1 mod 18446744073709551616) 6148914691236517205 mod 18446744073709551616) mod 18446744073709551616.
Definition cb9 (e8 : Z) : Z := (Z.land e8 3689348814741910323 + Z.land (e8 ≫ 2 mod 18446744073709551616) 3689348814741910323) mod 18446744073709551616.
Definition cb10 (e9 : Z) : Z := (e9 + e9 ≫ 4) mod 18446744073709551616.
Definition cb11 (e10 : Z) : Z := ((Z.land e10 1085102592571150095 mod 18446744073709551616 * 72340172838076673) mod 18446744073709551616) ≫ 56 mod 18446744073709551616.
Definition cb12 (e11 : Z) : Z := bv_swrap 32 (62 - e11) mod 18446744073709551616.
Definition cb13 (size e12 : Z) : Z := size ≫ (e12 mod 64) mod 18446744073709551616.
Definition cb14 (e12 : Z) : Z := bv_swrap 32 (18446744073709551615 ≪ (e12 mod 32)) mod 18446744073709551616.
Definition cb15 (size e14 : Z) : Z := Z.land size (Z.lxor e14 18446744073709551615 mod 18446744073709551616) mod 18446744073709551616.
Definition cb16 (e11 e13 e15 : Z) : Z := (Z.lor (Z.lxor (e11 ≪ 1 mod 18446744073709551616) 126 mod 18446744073709551616) (Z.land e13 1 mod 18446744073709551616) + Z.b2z (0 mod 18446744073709551616 <? e15) mod 18446744073709551616 + -2) mod 18446744073709551616.

Definition cidbits (size : Z) : Z :=
  let e1 := cb1 size in
  let e2 := cb2 e1 in
  let e3 := cb3 e2 in
  let e4 := cb4 e3 in
  let e5 := cb5 e4 in
  let e6 := cb6 e5 in
  let e7 := cb7 e6 in
  let e8 := cb8 e7 in
  let e9 := cb9 e8 in
  let e10 := cb10 e9 in
  let e11 := cb11 e10 in
  let e12 := cb12 e11 in
  let e13 := cb13 size e12 in
  let e14 := cb14 e12 in
  let e15 := cb15 size e14 in
  let e16 := cb16 e11 e13 e15 in
  e16.

Fixpoint forall_range (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S k => if f a then forall_range f (a + 1) k else false end.
Definition forall_rangeZ (f : Z -> bool) (a n : Z) : bool := forall_range f a (Z.to_nat n).
Lemma forall_range_spec : forall f n a x, forall_range f a n = true -> a <= x < a + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|k IH]; intros a x H Hx; [cbn in Hx; lia|].
  cbn [forall_range] in H. destruct (f a) eqn:E; [|discriminate].
  destruct (Z.eq_dec x a) as [->|NE]; [exact E|]. eapply IH; [exact H|]. lia.
Qed.
Lemma forall_rangeZ_spec : forall f a n x, forall_rangeZ f a n = true -> 0 <= n -> a <= x < a + n -> f x = true.
Proof. intros f a n x H Hn Hx. eapply forall_range_spec; [exact H|]. rewrite Z2Nat.id by exact Hn. exact Hx. Qed.

Definition M64 : Z := 18446744073709551615.
Lemma mod64_land : forall x, x mod 18446744073709551616 = Z.land x 18446744073709551615.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod6_land : forall x, x mod 64 = Z.land x 63.
Proof. intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod5_land : forall x, x mod 32 = Z.land x 31.
Proof. intros x. change 31 with (Z.ones 5). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma swrap32_land : forall z, bv_swrap 32 z = Z.land (z + 2147483648) 4294967295 - 2147483648.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by (clear; lia). reflexivity.
Qed.

Definition cf1 (size : Z) : Z := Z.land (Z.lor size (Z.land (size ≫ 1) 18446744073709551615)) 18446744073709551615.
Definition cf2 (e1 : Z) : Z := Z.land (Z.lor e1 (Z.land (e1 ≫ 2) 18446744073709551615)) 18446744073709551615.
Definition cf3 (e2 : Z) : Z := Z.land (Z.lor e2 (Z.land (e2 ≫ 4) 18446744073709551615)) 18446744073709551615.
Definition cf4 (e3 : Z) : Z := Z.land (Z.lor e3 (Z.land (e3 ≫ 8) 18446744073709551615)) 18446744073709551615.
Definition cf5 (e4 : Z) : Z := Z.land (Z.lor e4 (Z.land (e4 ≫ 16) 18446744073709551615)) 18446744073709551615.
Definition cf6 (e5 : Z) : Z := Z.land (Z.lor e5 (Z.land (e5 ≫ 32) 18446744073709551615)) 18446744073709551615.
Definition cf7 (e6 : Z) : Z := Z.land (Z.lxor e6 18446744073709551615) 18446744073709551615.
Definition cf8 (e7 : Z) : Z := Z.land (e7 - Z.land (Z.land (Z.land (e7 ≫ 1) 18446744073709551615) 6148914691236517205) 18446744073709551615) 18446744073709551615.
Definition cf9 (e8 : Z) : Z := Z.land (Z.land e8 3689348814741910323 + Z.land (Z.land (e8 ≫ 2) 18446744073709551615) 3689348814741910323) 18446744073709551615.
Definition cf10 (e9 : Z) : Z := Z.land (e9 + e9 ≫ 4) 18446744073709551615.
Definition cf11 (e10 : Z) : Z := Z.land ((Z.land (Z.land (Z.land e10 1085102592571150095) 18446744073709551615 * 72340172838076673) 18446744073709551615) ≫ 56) 18446744073709551615.
Definition cf12 (e11 : Z) : Z := Z.land (Z.land (62 - e11 + 2147483648) 4294967295 - 2147483648) 18446744073709551615.
Definition cf13 (size e12 : Z) : Z := Z.land (size ≫ (Z.land e12 63)) 18446744073709551615.
Definition cf14 (e12 : Z) : Z := Z.land (Z.land (18446744073709551615 ≪ (Z.land e12 31) + 2147483648) 4294967295 - 2147483648) 18446744073709551615.
Definition cf15 (size e14 : Z) : Z := Z.land (Z.land size (Z.land (Z.lxor e14 18446744073709551615) 18446744073709551615)) 18446744073709551615.
Definition cf16 (e11 e13 e15 : Z) : Z :=
  Z.land (Z.lor (Z.land (Z.lxor (Z.land (e11 ≪ 1) 18446744073709551615) 126) 18446744073709551615) (Z.land (Z.land e13 1) 18446744073709551615)
          + Z.land (Z.b2z (Z.land 0 18446744073709551615 <? e15)) 18446744073709551615 + -2) 18446744073709551615.

Lemma cf1_eq : forall x, cb1 x = cf1 x. Proof. intros. unfold cb1, cf1. rewrite !mod64_land. reflexivity. Qed.
Lemma cf2_eq : forall x, cb2 x = cf2 x. Proof. intros. unfold cb2, cf2. rewrite !mod64_land. reflexivity. Qed.
Lemma cf3_eq : forall x, cb3 x = cf3 x. Proof. intros. unfold cb3, cf3. rewrite !mod64_land. reflexivity. Qed.
Lemma cf4_eq : forall x, cb4 x = cf4 x. Proof. intros. unfold cb4, cf4. rewrite !mod64_land. reflexivity. Qed.
Lemma cf5_eq : forall x, cb5 x = cf5 x. Proof. intros. unfold cb5, cf5. rewrite !mod64_land. reflexivity. Qed.
Lemma cf6_eq : forall x, cb6 x = cf6 x. Proof. intros. unfold cb6, cf6. rewrite !mod64_land. reflexivity. Qed.
Lemma cf7_eq : forall x, cb7 x = cf7 x. Proof. intros. unfold cb7, cf7. rewrite !mod64_land. reflexivity. Qed.
Lemma cf8_eq : forall x, cb8 x = cf8 x. Proof. intros. unfold cb8, cf8. rewrite !mod64_land. reflexivity. Qed.
Lemma cf9_eq : forall x, cb9 x = cf9 x. Proof. intros. unfold cb9, cf9. rewrite !mod64_land. reflexivity. Qed.
Lemma cf10_eq : forall x, cb10 x = cf10 x. Proof. intros. unfold cb10, cf10. rewrite !mod64_land. reflexivity. Qed.
Lemma cf11_eq : forall x, cb11 x = cf11 x. Proof. intros. unfold cb11, cf11. rewrite !mod64_land. reflexivity. Qed.
Lemma cf12_eq : forall x, cb12 x = cf12 x. Proof. intros. unfold cb12, cf12. rewrite !mod64_land, swrap32_land. reflexivity. Qed.
Lemma cf13_eq : forall x y, cb13 x y = cf13 x y. Proof. intros. unfold cb13, cf13. rewrite !mod64_land, mod6_land. reflexivity. Qed.
Lemma cf14_eq : forall x, cb14 x = cf14 x. Proof. intros. unfold cb14, cf14. rewrite !mod64_land, swrap32_land, mod5_land. reflexivity. Qed.
Lemma cf15_eq : forall x y, cb15 x y = cf15 x y. Proof. intros. unfold cb15, cf15. rewrite !mod64_land. reflexivity. Qed.
Lemma cf16_eq : forall x y z, cb16 x y z = cf16 x y z. Proof. intros. unfold cb16, cf16. rewrite !mod64_land. reflexivity. Qed.

Definition cidfast (size : Z) : Z :=
  let e11 := cf11 (cf10 (cf9 (cf8 (cf7 (cf6 (cf5 (cf4 (cf3 (cf2 (cf1 size)))))))))) in
  let e12 := cf12 e11 in
  cf16 e11 (cf13 size e12) (cf15 size (cf14 e12)).

Lemma forall_range_ext : forall f g n a, (forall x, f x = g x) -> forall_range f a n = forall_range g a n.
Proof. intros f g n. induction n as [|k IH]; intros a E; [reflexivity|]. cbn [forall_range]. rewrite (E a), (IH (a + 1) E). reflexivity. Qed.
Lemma forall_rangeZ_ext : forall f g a n, (forall x, f x = g x) -> forall_rangeZ f a n = forall_rangeZ g a n.
Proof. intros f g a n E. unfold forall_rangeZ. apply forall_range_ext. exact E. Qed.

Lemma cid_chkF_lo : forall_rangeZ (fun s => Z.eqb (cidfast s) (class_id s)) 513 32512 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma cid_chkF_hi : forall_rangeZ (fun s => Z.eqb (cidfast s) (class_id s)) 33025 32512 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cidbits_unfold : forall size, cidbits size = cb16 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size))))))))))) (cb13 size (cb12 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size))))))))))))) (cb15 size (cb14 (cb12 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size)))))))))))))).
Proof. intros size. reflexivity. Qed.

Lemma cidbits_fast : forall size, cidbits size = cidfast size.
Proof.
  intros size. rewrite cidbits_unfold. unfold cidfast.
  rewrite !cf16_eq, !cf15_eq, !cf14_eq, !cf13_eq, !cf12_eq, !cf11_eq, !cf10_eq, !cf9_eq, !cf8_eq, !cf7_eq, !cf6_eq, !cf5_eq, !cf4_eq, !cf3_eq, !cf2_eq, !cf1_eq.
  reflexivity.
Qed.
Lemma cid_chk_lo : forall_rangeZ (fun s => Z.eqb (cidbits s) (class_id s)) 513 32512 = true.
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_lo|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.
Lemma cid_chk_hi : forall_rangeZ (fun s => Z.eqb (cidbits s) (class_id s)) 33025 32512 = true.
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_hi|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.

Lemma cidbits_ok : forall size e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16,
  512 < size <= 65536 ->
  e1 = cb1 size ->
  e2 = cb2 e1 ->
  e3 = cb3 e2 ->
  e4 = cb4 e3 ->
  e5 = cb5 e4 ->
  e6 = cb6 e5 ->
  e7 = cb7 e6 ->
  e8 = cb8 e7 ->
  e9 = cb9 e8 ->
  e10 = cb10 e9 ->
  e11 = cb11 e10 ->
  e12 = cb12 e11 ->
  e13 = cb13 size e12 ->
  e14 = cb14 e12 ->
  e15 = cb15 size e14 ->
  e16 = cb16 e11 e13 e15 ->
  e16 = class_id size.
Proof.
  intros size e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 SZ He1 He2 He3 He4 He5 He6 He7 He8 He9 He10 He11 He12 He13 He14 He15 He16.
  assert (C : Z.eqb (cidbits size) (class_id size) = true).
  { destruct (Z.lt_ge_cases size 33025).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 513 32512 size cid_chk_lo ltac:(lia) ltac:(lia)).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 33025 32512 size cid_chk_hi ltac:(lia) ltac:(lia)). }
  apply Z.eqb_eq in C. rewrite cidbits_unfold in C. subst. exact C.
Qed.

Lemma class_id_chk : forall_rangeZ (fun s => (1 <=? class_id s) && (class_id s <? 32)) 1 65536 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_id_range : forall size, 1 <= size <= 65536 -> 1 <= class_id size < 32.
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => (1 <=? class_id s) && (class_id s <? 32)) 1 65536 size class_id_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
Qed.

Lemma class_size_ge_chk : forall_rangeZ (fun s => s <=? class_size (class_id s)) 1 65536 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_size_ge : forall size, 1 <= size <= 65536 -> size <= class_size (class_id size).
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => s <=? class_size (class_id s)) 1 65536 size class_size_ge_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply Z.leb_le in C. exact C.
Qed.
