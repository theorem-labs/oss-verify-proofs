(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Abbreviation two32 := 4294967296%Z.
Abbreviation two64 := 18446744073709551616%Z.
Definition ONES64 : Z := 18446744073709551615.

Lemma two64_pow : two64 = 2 ^ 64. Proof. reflexivity. Qed.

Lemma u64_of_Z : forall z, bv_unsigned (Z_to_bv 64 z) = z mod two64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma zv_mod : forall a, Z_to_bv 64 (a mod two64) = Z_to_bv 64 a.
Proof. intros a. symmetry. rewrite two64_pow. apply Z_to_bv_64_mod. Qed.

Lemma zv_eq : forall a b, a mod two64 = b mod two64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (zv_mod a), <- (zv_mod b), H. reflexivity. Qed.


Lemma word_zv : forall x : word, x = Z_to_bv 64 (bv_unsigned x).
Proof. intros x. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma mod64_land : forall a, a mod two64 = Z.land a ONES64.
Proof. intros a. unfold ONES64. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod32_land : forall a, a mod two32 = Z.land a 4294967295.
Proof. intros a. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.


Lemma mod32_range : forall a, 0 <= a mod two32 < two32.
Proof. intros a. apply Z.mod_pos_bound. lia. Qed.

Lemma mod_small_64 : forall a, 0 <= a < two64 -> a mod two64 = a.
Proof. intros. apply Z.mod_small. lia. Qed.



Ltac bits_ext :=
  apply Z.bits_inj'; intros ?n ?Hn;
  repeat first [ rewrite Z.land_spec | rewrite Z.lor_spec | rewrite Z.lxor_spec
               | rewrite Z.lnot_spec by lia | rewrite Z.bits_0 ];
  repeat match goal with |- context [Z.testbit ?x n] => let b := fresh "b" in set (b := Z.testbit x n) in *; clearbody b end;
  repeat match goal with b : bool |- _ => destruct b end; reflexivity.

Lemma land_mod64 : forall a b, Z.land (a mod two64) (b mod two64) = (Z.land a b) mod two64.
Proof. intros a b. rewrite !mod64_land. bits_ext. Qed.

Lemma lor_mod64 : forall a b, Z.lor (a mod two64) (b mod two64) = (Z.lor a b) mod two64.
Proof. intros a b. rewrite !mod64_land. bits_ext. Qed.

Lemma lxor_mod64 : forall a b, Z.lxor (a mod two64) (b mod two64) = (Z.lxor a b) mod two64.
Proof. intros a b. rewrite !mod64_land. bits_ext. Qed.


Lemma lor_mod32 : forall a b, Z.lor (a mod two32) (b mod two32) = (Z.lor a b) mod two32.
Proof. intros a b. rewrite !mod32_land. bits_ext. Qed.



Lemma mod32_mod64 : forall a, (a mod two64) mod two32 = a mod two32.
Proof.
  intros a. change two64 with (two32 * two32).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma mod64_mod32 : forall a, (a mod two32) mod two64 = a mod two32.
Proof. intros a. apply Z.mod_small. pose proof (mod32_range a). lia. Qed.


Lemma zv_add : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros. unfold v_add. rewrite !u64_of_Z. apply zv_eq. rewrite <- Z.add_mod by lia. reflexivity. Qed.

Lemma zv_addi : forall a i, v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros. unfold v_addi. rewrite u64_of_Z. apply zv_eq. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Lemma zv_addi_sub : forall a i k, (i + k = 0)%Z -> v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a - k).
Proof. intros a i k H. rewrite zv_addi. f_equal. lia. Qed.

Lemma zv_sub : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros. unfold v_sub. rewrite !u64_of_Z. apply zv_eq.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma zv_mul : forall a b, v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros. unfold v_mul. rewrite !u64_of_Z. apply zv_eq. rewrite <- Z.mul_mod by lia. reflexivity. Qed.

Lemma zv_and : forall a b, v_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof. intros. unfold v_and. rewrite !u64_of_Z, land_mod64. apply zv_mod. Qed.

Lemma zv_or : forall a b, v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros. unfold v_or. rewrite !u64_of_Z, lor_mod64. apply zv_mod. Qed.

Lemma zv_xor : forall a b, v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros. unfold v_xor. rewrite !u64_of_Z, lxor_mod64. apply zv_mod. Qed.

Lemma bv_wrap64_is_mod : forall i, bv_wrap 64 i = i mod two64.
Proof. intros. reflexivity. Qed.

Lemma zv_andi : forall a i, v_andi (Z_to_bv 64 a) i = Z_to_bv 64 (Z.land a i).
Proof. intros. unfold v_andi. rewrite u64_of_Z, bv_wrap64_is_mod, land_mod64. apply zv_mod. Qed.

Lemma zv_ori : forall a i, v_ori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lor a i).
Proof. intros. unfold v_ori. rewrite u64_of_Z, bv_wrap64_is_mod, lor_mod64. apply zv_mod. Qed.

Lemma zv_xori : forall a i, v_xori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lxor a i).
Proof. intros. unfold v_xori. rewrite u64_of_Z, bv_wrap64_is_mod, lxor_mod64. apply zv_mod. Qed.

Lemma lxor_m1_64 : forall a, 0 <= a < two64 -> Z.lxor a (-1) mod two64 = ONES64 - a.
Proof.
  intros a Ha. rewrite Z.lxor_m1_r. unfold Z.lnot, ONES64.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zv_not : forall a, 0 <= a < two64 -> v_xori (Z_to_bv 64 a) (-1) = Z_to_bv 64 (ONES64 - a).
Proof. intros a Ha. rewrite zv_xori. apply zv_eq. rewrite lxor_m1_64 by lia. symmetry. apply Z.mod_small. unfold ONES64. lia. Qed.

Lemma zv_slli : forall a s, 0 <= s -> v_slli (Z_to_bv 64 a) s = Z_to_bv 64 (a * 2 ^ s).
Proof.
  intros a s Hs. unfold v_slli. rewrite u64_of_Z, Z.shiftl_mul_pow2 by lia. apply zv_eq.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

Lemma zv_srli : forall a s, 0 <= a < two64 -> v_srli (Z_to_bv 64 a) s = Z_to_bv 64 (Z.shiftr a s).
Proof. intros a s Ha. unfold v_srli. rewrite u64_of_Z, mod_small_64 by lia. reflexivity. Qed.


Lemma zv_srli_mod : forall a s, v_srli (Z_to_bv 64 a) s = Z_to_bv 64 (Z.shiftr (a mod two64) s).
Proof. intros a s. unfold v_srli. rewrite u64_of_Z. reflexivity. Qed.

Lemma zv_zext32 : forall a, v_srli (Z_to_bv 64 (a * 2 ^ 32)) 32 = Z_to_bv 64 (a mod two32).
Proof.
  intros a. rewrite zv_srli_mod. f_equal. rewrite Z.shiftr_div_pow2 by lia.
  change two64 with (two32 * 2 ^ 32). rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

Lemma zv_lui : forall i, v_lui i = Z_to_bv 64 (i mod two64).
Proof. intros. unfold v_lui. symmetry. apply zv_mod. Qed.

Definition sx32 (x : Z) : Z := if x <? 2147483648 then x else x + 18446744069414584320.



Lemma sx32_small : forall x, 0 <= x < 2147483648 -> sx32 x = x.
Proof. intros x Hx. unfold sx32. destruct (Z.ltb_spec x 2147483648); lia. Qed.

Lemma swrap32_sx32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sx32 (z mod two32)).
Proof.
  intros z. apply zv_eq. unfold bv_swrap, bv_wrap, sx32.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with two32.
  pose proof (mod32_range z) as Hr.
  rewrite <- (Z.add_mod_idemp_l z) by lia.
  destruct (Z.ltb_spec (z mod two32) 2147483648).
  - rewrite (Z.mod_small (z mod two32 + 2147483648)) by lia. f_equal. lia.
  - replace (z mod two32 + 2147483648) with ((z mod two32 - 2147483648) + 1 * two32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (z mod two32 - 2147483648)) by lia.
    replace (z mod two32 + 18446744069414584320) with ((z mod two32 - 2147483648 - 2147483648) + 1 * two64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.






Lemma zv_addiw : forall a i, v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (sx32 ((a + i) mod two32)).
Proof.
  intros. unfold v_addiw. rewrite u64_of_Z, swrap32_sx32. do 2 f_equal.
  rewrite <- mod32_mod64, Z.add_mod_idemp_l, mod32_mod64 by lia. rewrite <- (mod32_mod64 (a + i)). reflexivity.
Qed.

Lemma zv_addiw_sub : forall a i k, i + k = 0 -> v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (sx32 ((a - k) mod two32)).
Proof. intros a i k H. rewrite zv_addiw. replace (a + i) with (a - k) by lia. reflexivity. Qed.

Lemma zv_sextw : forall a, v_addiw (Z_to_bv 64 a) 0 = Z_to_bv 64 (sx32 (a mod two32)).
Proof. intros. rewrite zv_addiw, Z.add_0_r. reflexivity. Qed.

Lemma zv_addw : forall a b, v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (sx32 ((a + b) mod two32)).
Proof.
  intros. unfold v_addw. rewrite !u64_of_Z, swrap32_sx32. do 2 f_equal.
  rewrite <- mod32_mod64, <- Z.add_mod, mod32_mod64 by lia. reflexivity.
Qed.

Lemma zv_subw : forall a b, v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (sx32 ((a - b) mod two32)).
Proof.
  intros. unfold v_subw. rewrite !u64_of_Z, swrap32_sx32. do 2 f_equal.
  rewrite <- mod32_mod64, <- Zminus_mod, mod32_mod64. reflexivity.
Qed.

Lemma zv_srliw : forall a s, 0 < s -> v_srliw (Z_to_bv 64 a) s = Z_to_bv 64 (Z.shiftr (a mod two32) s).
Proof.
  intros a s Hs. unfold v_srliw. rewrite u64_of_Z.
  change (bv_wrap 32 (a mod two64)) with ((a mod two64) mod two32). rewrite mod32_mod64.
  pose proof (mod32_range a) as Hr.
  assert (Hq : 0 <= Z.shiftr (a mod two32) s < 2147483648).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
    assert (2 ^ 1 <= 2 ^ s) by (apply Z.pow_le_mono_r; lia).
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 1) with 2 in *. nia. }
  f_equal. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  rewrite bv_wrap_small; [lia|]. change (bv_modulus 32) with two32. lia.
Qed.

Lemma mod2_mod64 : forall a, (a mod two64) mod 2 = a mod 2.
Proof.
  intros a. change two64 with (2 * 9223372036854775808).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma mul63_mod64 : forall x, (x * 2 ^ 63) mod two64 = (x mod 2) * 2 ^ 63.
Proof.
  intros x. change two64 with (2 * 2 ^ 63). rewrite Z.mul_mod_distr_r by lia. reflexivity.
Qed.

Lemma zv_srai63_slli63 : forall a,
  v_srai (v_slli (Z_to_bv 64 a) 63) 63 = Z_to_bv 64 (if Z.odd a then ONES64 else 0).
Proof.
  intros a. unfold v_srai, v_slli. rewrite u64_of_Z, Z_to_bv_signed, Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with two64. change (bv_half_modulus 64) with (2 ^ 63).
  rewrite <- Z.add_mod_idemp_l by lia. rewrite mul63_mod64, mod2_mod64, Zmod_odd.
  destruct (Z.odd a).
  - replace (1 * 2 ^ 63 + 2 ^ 63) with (0 + 1 * two64) by reflexivity.
    rewrite Z.mod_add by lia. apply zv_eq. reflexivity.
  - reflexivity.
Qed.

Lemma zv_mulhu : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  v_mulhu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b / two64).
Proof.
  intros a b Ha Hb. unfold v_mulhu. rewrite !u64_of_Z, !mod_small_64 by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zv_sltu : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !u64_of_Z, !mod_small_64 by lia.
  destruct (a <? b); reflexivity.
Qed.




Lemma zc_eq_mod : forall a b, c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a mod two64 =? b mod two64).
Proof. intros. unfold c_eq, bv_eqb. rewrite !u64_of_Z. reflexivity. Qed.

Lemma zc_ltu_mod : forall a b, c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a mod two64 <? b mod two64).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u64_of_Z. reflexivity. Qed.





Lemma land_split : forall a m, Z.land a m + Z.land m (Z.lnot a) = m.
Proof.
  intros a m. rewrite Z.add_nocarry_lxor; bits_ext.
Qed.

Lemma land_range : forall a m, 0 <= m -> 0 <= Z.land a m <= m.
Proof.
  intros a m Hm. split; [apply Z.land_nonneg; lia|].
  pose proof (land_split a m). 
  assert (0 <= Z.land m (Z.lnot a)) by (apply Z.land_nonneg; lia). lia.
Qed.







Lemma lor_range : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply (Z_bounded_by_bits n); [lia | apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high n a k) by lia. rewrite (Z_testbit_high n b k) by lia. reflexivity.
Qed.




Section RT.
  Context {fx : FPState}.
End RT.


Ltac rwR :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

Ltac zlit1 e :=
  let v := eval cbv in e in
  lazymatch v with
  | e => fail
  | _ => change e with v
  end.

Ltac is_closed_Z e :=
  match e with
  | _ => let chk := constr:(eq_refl : ltac:(let v := eval cbv in e in exact v) = ltac:(let v := eval cbv in e in exact v)) in idtac
  end.

Ltac znf1 :=
  match goal with
  | |- context [regupd _ _ ?v] =>
      lazymatch v with
      | Z_to_bv 64 _ => fail
      | v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_add a b)
      | v_addi (Z_to_bv 64 ?a) (Zneg ?p) => let k := constr:(Zpos p) in rewrite (zv_addi_sub a (Zneg p) k eq_refl)
      | v_addi (Z_to_bv 64 ?a) ?i => rewrite (zv_addi a i)
      | v_sub (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_sub a b)
      | v_mul (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_mul a b)
      | v_and (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_and a b)
      | v_or (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_or a b)
      | v_xor (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_xor a b)
      | v_andi (Z_to_bv 64 ?a) ?i => rewrite (zv_andi a i)
      | v_ori (Z_to_bv 64 ?a) ?i => rewrite (zv_ori a i)
      | v_xori (Z_to_bv 64 ?a) ?i => rewrite (zv_xori a i)
      | v_slli (Z_to_bv 64 ?a) ?s => rewrite (zv_slli a s) by lia
      | v_addiw (Z_to_bv 64 ?a) 0 => rewrite (zv_sextw a)
      | v_addiw (Z_to_bv 64 ?a) (Zneg ?p) => let k := constr:(Zpos p) in rewrite (zv_addiw_sub a (Zneg p) k eq_refl)
      | v_addiw (Z_to_bv 64 ?a) ?i => rewrite (zv_addiw a i)
      | v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_addw a b)
      | v_subw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => rewrite (zv_subw a b)
      | v_srliw (Z_to_bv 64 ?a) ?s => rewrite (zv_srliw a s) by lia
      | v_srli (Z_to_bv 64 (?a * 2 ^ 32)) 32 => rewrite (zv_zext32 a)
      | v_srai (Z_to_bv 64 (?a * 2 ^ 63)) 63 => rewrite <- (zv_slli a 63) by lia; rewrite (zv_srai63_slli63 a)
      | v_lui ?i => rewrite (zv_lui i)
      | v_auipc ?p ?i => let e := constr:(v_auipc p i) in wlit_closed e; rewrite (word_zv (v_auipc p i))
      end
  end.

Ltac zfold :=
  match goal with
  | |- context [regupd _ _ (Z_to_bv 64 ?e)] =>
      first [ is_Z_lit e
            | tryif check_closed_term e then (let v := eval cbv in e in change (Z_to_bv 64 e) with (Z_to_bv 64 v)) else idtac ]
  | _ => idtac
  end
 with is_Z_lit e := WalkTac.is_Z_lit e.

Lemma bv_lit_zv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x).
Proof. exact word_zv. Qed.

Ltac zlits :=
  repeat match goal with
  | |- context [regupd _ _ ?v] =>
      match v with
      | context [@BV 64 ?z ?p] =>
          rewrite (bv_lit_zv (@BV 64 z p)); imm_norm
      end
  end.

Ltac znorm := gres; imm_norm; rwR;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end;
  repeat znf1; zfold.

Ltac stepz F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; znorm
  | _ => stepi F D; znorm
  end.

Ltac zval e tac :=
  match goal with
  | |- context [regupd ?X ?r ?v] =>
      lazymatch v with
      | Z_to_bv 64 e => idtac
      | _ => replace (regupd X r v) with (regupd X r (Z_to_bv 64 e)) by (f_equal; symmetry; tac)
      end
  end.

Ltac condZ :=
  rwR; rewrite ?zc_ltu_mod, ?zc_eq_mod;
  rewrite ?mod_small_64 by lia;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ]; lia.
