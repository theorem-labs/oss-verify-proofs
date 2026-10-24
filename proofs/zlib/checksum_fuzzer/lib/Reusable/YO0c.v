(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0a YO0b.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma wd_range (x : word) : 0 <= bv_unsigned x < 2^64.
Proof. apply (bv_unsigned_in_range 64 x). Qed.
Lemma w32_range (x : bv 32) : 0 <= bv_unsigned x < 2^32.
Proof. apply (bv_unsigned_in_range 32 x). Qed.
Lemma bv_wrap64 z : bv_wrap 64 z = z mod 2^64.
Proof. reflexivity. Qed.
Lemma bv_wrap32 z : bv_wrap 32 z = z mod 2^32.
Proof. reflexivity. Qed.
Lemma wrap64_swrap32 z : bv_wrap 64 (bv_swrap 32 z) = sx32 z.
Proof.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2^32). change (2 ^ Z.of_N 64) with (2^64). change (2^32 `div` 2) with (2^31).
pose proof (Z.mod_pos_bound z (2^32) ltac:(lia)) as Hl.
rewrite <- (sx32_lo32 z). unfold lo32.
rewrite <- (Zplus_mod_idemp_l z). set (l := z mod 2^32) in *.
destruct (Z_lt_le_dec l (2^31)).
- rewrite (Z.mod_small (l + 2^31)) by lia. rewrite sx32_small by lia.
replace (l + 2^31 - 2^31) with l by lia. apply Z.mod_small. lia.
- replace (l + 2^31) with ((l - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add, (Z.mod_small (l - 2^31)) by lia.
rewrite sx32_big by lia. replace (l - 2^31 - 2^31) with ((l + 2^64 - 2^32) + (-1) * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma bv_signed_s64 (x : word) : bv_signed x = s64 (bv_unsigned x).
Proof.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, s64.
change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
pose proof (wd_range x). set (u := bv_unsigned x) in *.
destruct (u <? 2^63) eqn:E.
- apply Z.ltb_lt in E. rewrite Z.mod_small by lia. lia.
- apply Z.ltb_ge in E. replace (u + 2^63) with ((u - 2^63) + 1 * 2^64) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Lemma bv_signed32_eq (v : bv 32) : bv_wrap 64 (bv_signed v) = sx32 (bv_unsigned v).
Proof. unfold bv_signed. apply wrap64_swrap32. Qed.
Lemma sext64_32_unsigned (v : bv 32) : bv_unsigned (sext 64 v) = sx32 (bv_unsigned v).
Proof. unfold sext. rewrite bv_sign_extend_unsigned. apply bv_signed32_eq. Qed.
Lemma zext64_unsigned {n} (v : bv n) : (n <= 64)%N -> bv_unsigned (zext 64 v) = bv_unsigned v.
Proof. intros. unfold zext. apply bv_zero_extend_unsigned. assumption. Qed.
Lemma low32_unsigned (x : word) : bv_unsigned (low32 x) = lo32 (bv_unsigned x).
Proof.
unfold low32. rewrite bv_extract_unsigned. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma sext64_imm_unsigned {n} (imm : bv n) : bv_unsigned (sext 64 imm) = (bv_signed imm) mod 2^64.
Proof. unfold sext. rewrite bv_sign_extend_unsigned. reflexivity. Qed.
Lemma sext32_imm_unsigned {n} (imm : bv n) : bv_unsigned (sext 32 imm) = (bv_signed imm) mod 2^32.
Proof. unfold sext. rewrite bv_sign_extend_unsigned. reflexivity. Qed.
Lemma zext32_unsigned {n} (v : bv n) : (n <= 32)%N -> bv_unsigned (zext 32 v) = bv_unsigned v.
Proof. intros. unfold zext. apply bv_zero_extend_unsigned. assumption. Qed.
Lemma shmask64 (y : word) : bv_unsigned (bv_and y (Z_to_bv 64 63)) = bv_unsigned y mod 64.
Proof.
rewrite bv_and_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 63) with (Z.ones 6).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma shmask32 (y : bv 32) : bv_unsigned (bv_and y (Z_to_bv 32 31)) = bv_unsigned y mod 32.
Proof.
rewrite bv_and_unsigned, Z_to_bv_unsigned. change (bv_wrap 32 31) with (Z.ones 5).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma alu64_add (x y : word) : bv_unsigned (alu64 ALU_ADD x y) = add64 (bv_unsigned x) (bv_unsigned y).
Proof. cbn [alu64 alu]. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma alu64_sub (x y : word) : bv_unsigned (alu64 ALU_SUB x y) = sub64 (bv_unsigned x) (bv_unsigned y).
Proof. cbn [alu64 alu]. rewrite bv_sub_unsigned. reflexivity. Qed.
Lemma alu64_and (x y : word) : bv_unsigned (alu64 ALU_AND x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof. cbn [alu64 alu]. apply bv_and_unsigned. Qed.
Lemma alu64_or (x y : word) : bv_unsigned (alu64 ALU_OR x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof. cbn [alu64 alu]. apply bv_or_unsigned. Qed.
Lemma alu64_xor (x y : word) : bv_unsigned (alu64 ALU_XOR x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof. cbn [alu64 alu]. apply bv_xor_unsigned. Qed.
Lemma alu64_sll (x y : word) : bv_unsigned (alu64 ALU_SLL x y) = sll64 (bv_unsigned x) (bv_unsigned y mod 64).
Proof. cbn [alu64 alu]. rewrite bv_shiftl_unsigned, shmask64. reflexivity. Qed.
Lemma alu64_srl (x y : word) : bv_unsigned (alu64 ALU_SRL x y) = Z.shiftr (bv_unsigned x) (bv_unsigned y mod 64).
Proof. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, shmask64. reflexivity. Qed.
Lemma slli_unsigned (x : word) (sh : bv 6) :
bv_unsigned (alu64 ALU_SLL x (zext 64 sh)) = sll64 (bv_unsigned x) (bv_unsigned sh).
Proof.
rewrite alu64_sll, zext64_unsigned by (cbv; discriminate).
pose proof (bv_unsigned_in_range 6 sh) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 6) with 64 in H.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma srli_unsigned (x : word) (sh : bv 6) :
bv_unsigned (alu64 ALU_SRL x (zext 64 sh)) = Z.shiftr (bv_unsigned x) (bv_unsigned sh).
Proof.
rewrite alu64_srl, zext64_unsigned by (cbv; discriminate).
pose proof (bv_unsigned_in_range 6 sh) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 6) with 64 in H.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma alu64_sltu (x y : word) : bv_unsigned (alu64 ALU_SLTU x y) = sltu (bv_unsigned x) (bv_unsigned y).
Proof.
cbn [alu64 alu]. unfold bv_ltu, sltu. destruct (bv_unsigned x <? bv_unsigned y); reflexivity.
Qed.
Lemma alu64_slt (x y : word) :
bv_unsigned (alu64 ALU_SLT x y) = (if s64 (bv_unsigned x) <? s64 (bv_unsigned y) then 1 else 0).
Proof.
cbn [alu64 alu]. unfold bv_lts. rewrite <- !bv_signed_s64.
destruct (bv_signed x <? bv_signed y); reflexivity.
Qed.
Lemma alu64_xor_allones (x y : word) : bv_unsigned y = 2^64 - 1 ->
bv_unsigned (alu64 ALU_XOR x y) = not64 (bv_unsigned x).
Proof.
intros Hy. rewrite alu64_xor, Hy. change (2^64 - 1) with (Z.ones 64).
unfold not64. pose proof (wd_range x).
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, testbit_mod_pow2, Z.testbit_ones by lia.
replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn.
destruct (i <? 64) eqn:E.
- rewrite Z.lnot_spec by lia. apply xorb_true_r.
- apply Z.ltb_ge in E. rewrite (testbit_high_false (bv_unsigned x) 64 i) by lia. reflexivity.
Qed.
Lemma alu64_xori_m1 (x : word) : bv_unsigned (alu64 ALU_XOR x (Z_to_bv 64 (-1))) = not64 (bv_unsigned x).
Proof. apply alu64_xor_allones. reflexivity. Qed.
Lemma neg_unsigned (y : word) : bv_unsigned (alu64 ALU_SUB (Z_to_bv 64 0) y) = neg64 (bv_unsigned y).
Proof. rewrite alu64_sub. apply sub64_0_l. Qed.
Lemma seqz_unsigned (x : word) : bv_unsigned (alu64 ALU_SLTU x (Z_to_bv 64 1)) = (if bv_unsigned x =? 0 then 1 else 0).
Proof.
rewrite alu64_sltu. unfold sltu. change (bv_unsigned (Z_to_bv 64 1)) with 1.
pose proof (wd_range x).
destruct (bv_unsigned x <? 1) eqn:E1, (bv_unsigned x =? 0) eqn:E2; try reflexivity;
first [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1]; first [apply Z.eqb_eq in E2|apply Z.eqb_neq in E2]; lia.
Qed.
Lemma alu32_add_unsigned (a b : bv 32) : bv_unsigned (alu32 ALU_ADD a b) = (bv_unsigned a + bv_unsigned b) mod 2^32.
Proof. cbn [alu32 alu]. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma alu32_sub_unsigned (a b : bv 32) : bv_unsigned (alu32 ALU_SUB a b) = (bv_unsigned a - bv_unsigned b) mod 2^32.
Proof. cbn [alu32 alu]. rewrite bv_sub_unsigned. reflexivity. Qed.
Lemma alu32_sll_unsigned (a b : bv 32) :
bv_unsigned (alu32 ALU_SLL a b) = (Z.shiftl (bv_unsigned a) (bv_unsigned b mod 32)) mod 2^32.
Proof. cbn [alu32 alu]. rewrite bv_shiftl_unsigned, shmask32. reflexivity. Qed.
Lemma alu32_srl_unsigned (a b : bv 32) :
bv_unsigned (alu32 ALU_SRL a b) = Z.shiftr (bv_unsigned a) (bv_unsigned b mod 32).
Proof. cbn [alu32 alu]. rewrite bv_shiftr_unsigned, shmask32. reflexivity. Qed.
Lemma sext64_alu32 (r : bv 32) : bv_unsigned (sext 64 r) = sx32 (bv_unsigned r).
Proof. apply sext64_32_unsigned. Qed.
Lemma addw_unsigned (x : word) (b : bv 32) :
bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) b)) = addw (bv_unsigned x) (bv_unsigned b).
Proof.
rewrite sext64_32_unsigned, alu32_add_unsigned, low32_unsigned.
unfold addw. rewrite <- (sx32_lo32 (bv_unsigned x + _)). unfold lo32.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma addw_rr_unsigned (x y : word) :
bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (low32 y))) = addw (bv_unsigned x) (bv_unsigned y).
Proof.
rewrite addw_unsigned, low32_unsigned. apply addw_congr; [reflexivity|apply lo32_mod].
Qed.
Lemma addiw_unsigned (x : word) (imm : bv 12) :
bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (sext 32 imm))) = addw (bv_unsigned x) (bv_signed imm).
Proof.
rewrite addw_unsigned, sext32_imm_unsigned. apply addw_congr; [reflexivity|apply Z.mod_mod; lia].
Qed.
Lemma subw_unsigned (x : word) (b : bv 32) :
bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) b)) = subw (bv_unsigned x) (bv_unsigned b).
Proof.
rewrite sext64_32_unsigned, alu32_sub_unsigned, low32_unsigned.
unfold subw. rewrite <- (sx32_lo32 (bv_unsigned x - _)). unfold lo32.
rewrite Zminus_mod_idemp_l. reflexivity.
Qed.
Lemma subw_rr_unsigned (x y : word) :
bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) (low32 y))) = subw (bv_unsigned x) (bv_unsigned y).
Proof.
rewrite subw_unsigned, low32_unsigned. apply subw_congr; [reflexivity|apply lo32_mod].
Qed.
Lemma negw_unsigned (y : word) :
bv_unsigned (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 y))) = negw (bv_unsigned y).
Proof.
rewrite subw_rr_unsigned. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
unfold subw, negw. f_equal.
Qed.
Lemma sllw_unsigned (x : word) (b : bv 32) :
bv_unsigned (sext 64 (alu32 ALU_SLL (low32 x) b)) = sllw (bv_unsigned x) (bv_unsigned b).
Proof.
rewrite sext64_32_unsigned, alu32_sll_unsigned, low32_unsigned.
unfold sllw. rewrite <- (sx32_lo32 (Z.shiftl (bv_unsigned x) _)). unfold lo32.
pose proof (Z.mod_pos_bound (bv_unsigned b) 32 ltac:(lia)).
rewrite <- shiftl_mod32 by lia. reflexivity.
Qed.
Lemma sllw_rr_unsigned (x y : word) :
bv_unsigned (sext 64 (alu32 ALU_SLL (low32 x) (low32 y))) = sllw (bv_unsigned x) (bv_unsigned y).
Proof.
rewrite sllw_unsigned, low32_unsigned. unfold sllw, lo32. f_equal. f_equal.
apply Z.mod_mod_divide. exists (2^27). reflexivity.
Qed.
Lemma slliw_unsigned (x : word) (sh : bv 5) :
bv_unsigned (sext 64 (alu32 ALU_SLL (low32 x) (zext 32 sh))) = sllw (bv_unsigned x) (bv_unsigned sh).
Proof. rewrite sllw_unsigned, zext32_unsigned; [reflexivity|]. cbv; discriminate. Qed.
Lemma srlw_unsigned (x : word) (b : bv 32) :
bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) b)) = srlw (bv_unsigned x) (bv_unsigned b).
Proof.
rewrite sext64_32_unsigned, alu32_srl_unsigned, low32_unsigned. reflexivity.
Qed.
Lemma srlw_rr_unsigned (x y : word) :
bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (low32 y))) = srlw (bv_unsigned x) (bv_unsigned y).
Proof.
rewrite srlw_unsigned, low32_unsigned. unfold srlw, lo32. f_equal. f_equal.
apply Z.mod_mod_divide. exists (2^27). reflexivity.
Qed.
Lemma srliw_unsigned (x : word) (sh : bv 5) :
bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (zext 32 sh))) = srlw (bv_unsigned x) (bv_unsigned sh).
Proof. rewrite srlw_unsigned, zext32_unsigned; [reflexivity|]. cbv; discriminate. Qed.
Lemma mul64_unsigned (x y : word) : bv_unsigned (mul_div M_MUL x y) = mul64 (bv_unsigned x) (bv_unsigned y).
Proof. cbn [mul_div]. rewrite bv_mul_unsigned. reflexivity. Qed.
Lemma mulhu_unsigned (x y : word) :
bv_unsigned (mul_div M_MULHU x y) = Z.shiftr (bv_unsigned x * bv_unsigned y) 64.
Proof.
cbn [mul_div]. unfold bv_mulhuu. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (wd_range x). pose proof (wd_range y).
unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma divu_unsigned (x y : word) : bv_unsigned (mul_div M_DIVU x y) = divu64 (bv_unsigned x) (bv_unsigned y).
Proof.
cbn [mul_div]. unfold divu64. destruct (bv_unsigned y =? 0) eqn:E.
- rewrite Z_to_bv_unsigned. reflexivity.
- apply bv_divu_unsigned.
Qed.
Lemma branch_eq (x y : word) : branch_taken BC_EQ x y = (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma branch_ne (x y : word) : branch_taken BC_NE x y = negb (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma branch_ltu (x y : word) : branch_taken BC_LTU x y = (bv_unsigned x <? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma branch_geu (x y : word) : branch_taken BC_GEU x y = negb (bv_unsigned x <? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma branch_lt (x y : word) : branch_taken BC_LT x y = (s64 (bv_unsigned x) <? s64 (bv_unsigned y)).
Proof. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_s64. reflexivity. Qed.
Lemma branch_ge (x y : word) : branch_taken BC_GE x y = negb (s64 (bv_unsigned x) <? s64 (bv_unsigned y)).
Proof. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_s64. reflexivity. Qed.
Lemma lit64_unsigned z : bv_unsigned (Z_to_bv 64 z) = z mod 2^64.
Proof. apply Z_to_bv_unsigned. Qed.
Lemma lit64_small z : 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite lit64_unsigned. apply Z.mod_small. lia. Qed.
Lemma word_eq (x y : word) : x = y <-> bv_unsigned x = bv_unsigned y.
Proof. apply bv_eq. Qed.
Lemma take_first_word (a0 a1 : word) (m : Z) :
0 < m < 2^32 ->
bv_unsigned a0 = sx32 m ->
a1 = alu64 ALU_AND a0 (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 a0))) ->
bv_unsigned a1 = sx32 (lowbit m) /\ bv_unsigned a1 <> 0.
Proof.
intros Hm H0 ->. rewrite alu64_and, negw_unsigned, H0, negw_and_sx32.
split; [reflexivity|apply sx32_lowbit_nonzero; lia].
Qed.
Lemma take_idx_word (a1 a2 : word) (C : word) (m : Z) :
0 < m < 2^32 ->
bv_unsigned a1 = sx32 (lowbit m) -> bv_unsigned C = DBJ_MUL ->
a2 = sext 64 (alu32 ALU_SRL (low32 (mul_div M_MUL a1 C)) (zext 32 (Z_to_bv 5 27))) ->
0 <= bv_unsigned a2 < 32 /\ znth (bv_unsigned a2) DEBRUIJN = ctz32 m.
Proof.
intros Hm H1 HC ->. rewrite srliw_unsigned, mul64_unsigned, H1, HC.
change (bv_unsigned (Z_to_bv 5 27)) with 27. apply dbj_ctz32. lia.
Qed.
Lemma take_rest_word (a0 a1 r : word) (m : Z) :
0 < m < 2^32 ->
bv_unsigned a0 = sx32 m -> bv_unsigned a1 = sx32 (lowbit m) ->
r = sext 64 (alu32 ALU_SUB (low32 a0) (low32 a1)) ->
bv_unsigned (low32 r) = m - lowbit m.
Proof.
intros Hm H0 H1 ->. rewrite low32_unsigned, subw_rr_unsigned, H0, H1.
destruct (subw_mask_first m ltac:(lia)) as (E & _ & _ & L). rewrite E. exact L.
Qed.
