(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Export SFModel Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Export Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section ZLemmas.
Local Open Scope Z_scope.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
    apply zb_land_pow2_bit0; assumption.
Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.
End ZLemmas.

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

Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
  bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
  intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

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

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition A_FMT_emit : Z := 0x10c74.
Definition A_FMT_usage : Z := 0x10ffe.
Definition A_FMT_too_big : Z := 0x11dfc.
Definition A_FMT_cannot_open : Z := 0x128f5.
Definition A_FMT_read_error : Z := 0x1290a.
Definition A_NULLSTR : Z := 0x133b6.
