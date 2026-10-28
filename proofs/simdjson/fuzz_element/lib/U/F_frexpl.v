(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_letf2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition frexpl_entry := 0xc8830%Z.

Lemma frexpl_unfold : forall n x e,
  frexpl (S n) x e =
   (let hi := hi64 x in
    let se := Z.shiftr hi 48 in
    let ee := Z.land se 0x7fff in
    if ee =? 0 then
      if negb (f128_le x F128_ZERO =? 0) then
        let k := f128_of_d D_0x1p120 in
        match frexpl n (f128_mul x k) e with Some (x, e) => Some (x, e - 120) | None => None end
      else Some (x, 0)
    else if ee =? 0x7fff then Some (x, e)
    else
      let e := ee - 0x3ffe in
      let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff)) 0x3ffe000000000000 in
      Some (mk128 hi (lo64 x), e))%Z.
Proof. reflexivity. Qed.

Definition frexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (bv_unsigned sp - 32) (bv_unsigned sp)
    /\ rw_cells usegs m' P [C4 (Z_to_bv 64 e')]
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frx_mant : forall h, (0 <= h < 2^64)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 16) 18446744073709551615) 16 = Z.land h 281474976710655.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
  change 18446744073709551615%Z with (Z.ones 64). change 281474976710655%Z with (Z.ones 48).
  destruct (Z.lt_ge_cases i 48).
  - rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 48) by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma frx_sign : forall h, (0 <= h < 2^64)%Z ->
  Z.land (Z.shiftl (Z.land (Z.shiftr h 48) 32768) 48) 18446744073709551615 = Z.land h 9223372036854775808.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.land_spec. change 18446744073709551615%Z with (Z.ones 64).
  change 32768%Z with (2^15)%Z. change 9223372036854775808%Z with (2^63)%Z.
  rewrite (Z.pow2_bits_eqb 63) by lia.
  destruct (Z.lt_ge_cases i 48).
  - rewrite Z.shiftl_spec_low by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite Bool.andb_false_r.
  - rewrite Z.shiftl_spec_high, Z.land_spec, Z.shiftr_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. replace (i - 48 + 48)%Z with i by lia.
      destruct (Z.eqb_spec 15 (i - 48)), (Z.eqb_spec 63 i); try lia; now rewrite ?Bool.andb_true_r, ?Bool.andb_false_r.
    + rewrite Z.ones_spec_high by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite !Bool.andb_false_r.
Qed.

Ltac frx_finish X E' :=
  apply evt_done; unfold frexpl_post; exists X, E';
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
         | repeat match goal with |- _ /\ _ => split end; try assumption ].

Lemma f128_le_cases : forall a b, (f128_le a b = -1 \/ f128_le a b = 0 \/ f128_le a b = 1)%Z.
Proof.
  intros a b. unfold f128_le, nez64. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try lia.
  all: destruct (Z.eqb _ 0); cbn; lia.
Qed.
Lemma f128_le_land64_zero : forall a b, Z.land (f128_le a b) 18446744073709551615 = 0%Z <-> f128_le a b = 0%Z.
Proof.
  intros a b. destruct (f128_le_cases a b) as [E|[E|E]]; rewrite E; vm_compute; split; intros; lia.
Qed.

Lemma frexpl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
  stk usegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
  mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
  (bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (32 <= bv_unsigned sp)%Z ->
  (let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
   Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
  evt usegs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc8830) fc None m (seg_rom usegs)).
Proof.
  intros until E. intros ST MI CE SEP SPLO PRE.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM. pose_word_ranges.

  set (P := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 P) by (unfold P; rewrite Z_to_bv_bv_unsigned; reflexivity).
  cbv zeta in PRE. rewrite hi64_words in PRE by lia.
  unfold frexpl_post. change FREXPL_FUEL with 2%nat. rewrite frexpl_unfold.
  rewrite hi64_words, lo64_words by lia. cbv zeta.
  carve_frame 32%nat ST.
  do 6 zstep. do 4 zstep. name_reg 12%Z ee.
  zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
  -
    do 6 zstep. release_frame FR ST (bv_unsigned sp).
    frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z E. decide_tests_b. reflexivity.
  - zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
    +
      do 7 zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (Z.shiftl (Z.land (Z.shiftr (bv_unsigned a1) 48) 32768) 48)) with (Z_to_bv 64 (Z.land (bv_unsigned a1) 9223372036854775808))
        by (rewrite <- (Z_to_bv_land64 (Z.shiftl _ 48)); f_equal; symmetry; apply frx_sign; lia).
      zstep. zstep. zstep. reg_rewrite 11%Z Z.lor_assoc.
      zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
      frx_finish (mk128 (Z.lor (Z.lor (Z.land (bv_unsigned a1) 0x8000000000000000) (Z.land (bv_unsigned a1) 0x0000ffffffffffff)) 0x3ffe000000000000) (bv_unsigned a0))%Z (ee - 16382)%Z.
      decide_tests_b. reflexivity.
    +
      do 3 zstep. zstep. call letf2_spec. 1:{ assumption. }
      zsimp. rewrite Kz. rewrite Z.mul_0_r, Z.add_0_r.
      zstep. if_cases Kl; zify_cond Kl; rewrite f128_le_land64_zero in Kl.
      *   do 3 zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
        frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z 0%Z. decide_tests_b. unfold F128_ZERO. rewrite Kl. reflexivity.
      * exfalso. unfold F128_ZERO in PRE. change (2^64)%Z with 18446744073709551616%Z in PRE.
        destruct PRE as [PRE|PRE]; [exact (PRE Kz)|]. rewrite PRE in Kl. exact (Kl eq_refl).
Qed.
