(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BellsX BacX.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma amo_aligned_lit : forall wd P,
  P mod (amo_bytes wd) = 0 -> 0 <= P < 2^64 -> amo_aligned wd (Z_to_bv 64 P) = true.
Proof. intros wd P H B. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite H. reflexivity. Qed.

Lemma unsigned_lit32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma low32_lit : forall x, (0 <= x < 2^32)%Z -> bv_unsigned (low32 (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. unfold low32. rewrite bv_extract_unsigned, unsigned_lit by lia.
  cbn [N.add]. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. apply Z.mod_small. lia.
Qed.

Lemma Z_to_le_bytes_4_mod32 : forall z, Z_to_le_bytes 4 (z mod 2^32) = Z_to_le_bytes 4 z.
Proof. intros z. apply (Z_to_le_bytes_mod 4 z 32). cbn. lia. Qed.

Lemma mod_mod_mul : forall a n m, 0 < n -> 0 < m -> (a mod (n * m)) mod n = a mod n.
Proof.
  intros a n m Hn Hm. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm n), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma le4_congr : forall a b : Z, a mod 2^32 = b mod 2^32 -> le4 (Z_to_bv 64 a) = le4 (Z_to_bv 64 b).
Proof.
  intros a b H. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32)%Z.
  rewrite <- (Z_to_le_bytes_4_mod32 (a mod _)), <- (Z_to_le_bytes_4_mod32 (b mod _)).
  rewrite !mod_mod_mul by lia. rewrite H. reflexivity.
Qed.

Lemma amo_val_add_d : forall a b : Z,
  amo_val AMO_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold amo_val. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma amoadd_w_bytes : forall (X : word) (s : bv 32),
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 X))) s))
  = le4 (Z_to_bv 64 (bv_unsigned X + bv_unsigned s)).
Proof.
  intros X s. unfold amo_val. rewrite bv_add_unsigned. rewrite bv_extract_unsigned.
  cbn [N.add]. rewrite Z.shiftr_0_r. rewrite le_bytes_to_word_le4.
  transitivity (Z_to_le_bytes 4 (bv_unsigned X + bv_unsigned s)).
  - rewrite <- (Z_to_le_bytes_4_mod32 (bv_unsigned X + bv_unsigned s)). f_equal.
    change (bv_modulus 32) with (2^32)%Z.
    unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z.
    rewrite (Z.mod_small (_ mod 2^32) (2^32)) by (apply Z.mod_pos_bound; lia).
    rewrite Zplus_mod_idemp_l. reflexivity.
  - unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32)%Z.
    rewrite <- (Z_to_le_bytes_4_mod32 (_ mod _)). rewrite mod_mod_mul by lia. rewrite Z_to_le_bytes_4_mod32. reflexivity.
Qed.

Lemma lor_lockbit : forall v, 0 <= v < 2^31 ->
  Z.lor v 18446744071562067968 = v + 18446744071562067968.
Proof.
  intros v Hv.
  assert (D : Z.land v 18446744071562067968 = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 31).
    - replace (Z.testbit 18446744071562067968 n) with false; [apply Bool.andb_false_r|].
      change 18446744071562067968 with (8589934591 * 2^31). rewrite Z.mul_pow2_bits by lia.
      symmetry. apply Z.testbit_neg_r. lia.
    - destruct (Z.eq_dec v 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
      rewrite (Z.bits_above_log2 v n); [reflexivity|lia|].
      apply (Z.lt_le_trans _ 31); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma lockword_mod : forall v, 0 <= v < 2^31 ->
  (Z.lor v 18446744071562067968) mod 2^32 = (v + 2^31) mod 2^32.
Proof.
  intros v Hv. rewrite lor_lockbit by lia.
  change 18446744071562067968 with (2^31 + 4294967295 * 2^32).
  replace (v + (2^31 + 4294967295 * 2^32)) with ((v + 2^31) + 4294967295 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma C4_cell_congr : forall segs m A (a b : Z),
  a mod 2^32 = b mod 2^32 -> rw_cells segs m A [C4 (Z_to_bv 64 a)] -> rw_cells segs m A [C4 (Z_to_bv 64 b)].
Proof.
  intros segs m A a b H C. destruct C as [[Hwf Hb] Hw].
  split; [split|]; [exact Hwf| |exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. rewrite (le4_congr a b H). exact (fun x => x).
Qed.

Lemma lock_cell : forall segs m A v, 0 <= v < 2^31 ->
  rw_cells segs m A [C4 (Z_to_bv 64 (Z.lor v 18446744071562067968))] -> rw_cells segs m A [C4 (Z_to_bv 64 (v + 2^31))].
Proof. intros segs m A v Hv C. eapply C4_cell_congr; [|exact C]. apply lockword_mod. exact Hv. Qed.

Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_cbv; simp_is_x0; simp_regs;
          first [ rewrite amo_aligned_lit by (cbn [amo_bytes]; first [assumption | lia | (Z.div_mod_to_equations; lia)])
                | match goal with |- context [amo_aligned ?wd ?a] =>
                    fail 100 "astep: cannot prove the alignment of" a "(need: P mod 4|8 = 0 and 0 <= P < 2^64 in context, address as Z_to_bv 64 P)" end
                | fail 100 "astep: no lr/sc/amo at" pc ];
          cbv beta iota zeta delta [negb];
          try (rewrite Z.eqb_refl; cbv beta iota zeta);
          simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; try (rewrite amoadd_w_bytes; try rewrite unsigned_lit32 by lia); try rewrite amo_val_add_d; mem_after_store_opt ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.

Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

