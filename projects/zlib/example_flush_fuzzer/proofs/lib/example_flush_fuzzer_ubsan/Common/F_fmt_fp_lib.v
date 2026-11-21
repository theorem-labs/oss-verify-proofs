(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import SFW1_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.


Lemma hi64_range : forall x, (0 <= hi64 x < 2^64)%Z.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_range : forall x, (0 <= lo64 x < 2^64)%Z.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.



Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].


Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv)%Z W -> (A <= a)%Z -> (a + n <= A + N)%Z -> (0 <= n)%Z -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.


Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.







