(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_free () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0A'"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1snd"; "1true"; "2and"; "2eq"]; ["2iff"; "2not"; "2or"; "3N"; "3Z"; "4Segment"; "6sxv"; "5sxv"; "7b8"; "7wz"; "8cell"; "8cells_bytes"; "8cells_size"; "8cells_wf"; "9bytes_at"; "9le1"]; ["9le4"; "9sx32"; "9wr_at"; "9zxb"; ":rw_cells"; ";IB"; ";Known"; ";M"; ";UNIT"; ";a_check"; ";aadd"; ";aptr"; ";area"; ";area_of"; ";bit"; ";c_secret"]; [";cell_read"; ";cellval"; ";ctx"; ";free"; ";g_meta"; ";get_meta_rec"; ";get_shadow"; ";get_stride"; ";ghdr"; ";m_avail"; ";m_freed"; ";m_last_idx"; ";m_maplen"; ";m_mem"; ";m_set_freed"; ";m_sizeclass"]; [";mask_upto"; ";meta"; ";mstate"; ";optr"; ";optr_eqb"; ";ret"; ";s_areas"; ";s_groups"; ";shadow"; ";size_class"; ";slot_start'"; ";upd_meta"; ";wr16"; ";wr8"; "<add"; "<div"]; ["<land"; "<le"; "<lor"; "<lt"; "<modulo"; "<mul"; "<of_nat"; "<opp"; "<pow"; "<shiftl"; "<shiftr"; "<sub"; "<testbit"; "0a"; "0a'"; "0ar"]; ["0avail"; "0b"; "0b3"; "0base"; "0bs"; "0cs"; "0cs'"; "0cs1"; "0cs2"; "0e"; "0f"; "0freed"; "0g"; "0gh"; "0hi"; "0i"]; ["0idx"; "0k"; "0li"; "0lo"; "0m"; "0mr"; "0mword"; "0n"; "0n'"; "0o"; "0off16"; "0p"; "0po"; "0q"; "0reserved"; "0segs"]; ["0sh"; "0st"; "0st'"; "=lookup"; ">Z_to_bv"; ">bv"; ">bv_swrap"; ">bv_unsigned"; "?N_countable"; "?Z_countable"; "?prod_countable"; "@prod_eq_dec"; "Agmap"; "Agmap_lookup"; "Beq_dec"; "Ceq_dec"]; ["0v"; "0w"; "0x"; "0y"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.
Lemma sxv_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "@'D'>&RAz&Fr1%211%5241&RC&RH+2+R0%3221%5271%=271pY2?1").
Proof. intros v. unfold sxv. apply Z.mod_pos_bound. lia. Qed.
Lemma swrap32_eq' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "D'D'?&T6yQ0r1%3221&RK&RD&R>&RH+2+O%3221%5291+Q0%6251%9231%;215%A3B=1pY:C1").
Proof. intros z. reflexivity. Qed.
End CEIL_WRAP_1.
Ltac pow_lits :=
change (2^64)%Z with 18446744073709551616%Z in *;
change (2^63)%Z with 9223372036854775808%Z in *;
change (2^33)%Z with 8589934592%Z in *;
change (2^32)%Z with 4294967296%Z in *;
change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma sxv_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "D'D'>&RAzr1%3221&RC&RH+2+O%3221%5271%;271'?&Gr2%211%43A12p061pY2C1").
Proof. intros v. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma mod64_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "?'D'?&RDr1&RH+2+R0%3221%6251+Q0%6251%9231%:292%<3=21pY:>1").
Proof. intros z. apply mod_mod_pow2. lia. Qed.
Lemma sxv_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free ">'D'?&RD&Gr1%211&RH+2+Q0%3221%8251%9272%;3<21pY2=1").
Proof. intros v. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.
Lemma sx32_wz_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "L'D'>&RAzr1%3221&RC&RH+2+R0%3221%5271%;271'?'T5yR0%211&Q1&Ir2%211%411&G%114%611%<3941p0>1pY2K1").
Proof. intros v. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.
Lemma sextw_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "F'D'?'T5yR0%211&T4&T6yQ0&R>&T7&I&Gr1%211%411%62<1z%9221%<2;1%>2@1%C3@16pY2E1").
Proof. intros v.
rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
Lemma sextw_sxv' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "C'D'?'T5yR0%211&T4&T6yQ0&T7&I&Gr1%211%411%62;1%9281%;2=1%@3=14pY2B1").
Proof. intros v. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.
Lemma self_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q@'D'>&RAzr1%3221&RC+X0%2241%8241'?'T5yR0%211&T4&T6yQ0&RI+1&RD&T7&R@&Q3&Hr2%211%411%72?1+O%8221%@2B1%;2C1+Q0%>221%A2@1%D2C1%F2H1&I&G&RH+2%D2A=%3221%511%711%Q33Q091p0Q51pV6Q?1").
Proof. intros b3.
intros. rewrite zxb_b8, (wz_unsigned b3) by lia.
assert (0 <= Z.land b3 31 < 32).
{ split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma all_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q9'D&RAzr1%3221'?'T5yR0%211&T4&T6yQ0&R>&T7&RI+2&RDr2+Q0%3221%6251%;2:1%=2?1%:2@1-1%=221%@2?1%B2D1&I&G&RK&RH+1%E2>1%32C1%5213%711%911%Q13N;1p0Q31pW>Q81").
Proof. intros mword.
intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.
Lemma lor_range64 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "H'D'>&RAzr2%3221&RC&RH+2+R0%3221%5271%;271&RBr4r3%3221%?2>1%<228%B221p081p091pV4F1pULG1").
Proof. intros a b. intros. apply (zr_lor a b); unfold inr64; lia. Qed.
Lemma land_range64 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "H'D'>&RAzr2%3221&RC&RH+2+R0%3221%5271%;271&R@r4r3%3221%?2>1%<228%B221p0?1p091pV4F1pULG1").
Proof. intros a b. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.
Lemma sxv_testbit_lo : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "M'D'>&RAzr2%3221&RC&RH+2+Q0%3221%5271%;271%7294%=291'?'4&RL&Gr4%211r3%5221%6242%93821p0;1p0>1pW0K1pY2L1").
Proof. intros v i.
intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.
Lemma sxv_cases : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q3'D'>&RAzr1%3221&RC&RH+2+Q0%3221%5271%;271'Br2+O%9281%;231'?&G%116%33E17%E251%E279&RK&R>+R0%D2C1%32>1%521C%<3N:1%N281%C2:1p0E1pY2Q21").
Proof. intros v.
intros. unfold sxv. rewrite swrap32_eq'.
destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.
Lemma free_assert_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q>'D'>&RAzr3%3221&RC&RH+2+Q0%3221%5271%;271%7294%=291'?'4&RLr6r4%3221(6%73621r5%7261%:3914&R@&G%E2D:%211&RBr8%511r7%711%5231%:271%F3Q51Q2p0=1p0A1p0J1p0M1p0N1pW2Q;1pV2Q<1pVHQ=1").
Proof. intros freed avail idx.
intros HF HA HI TF TA.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 64).
2:{ rewrite (Z.bits_above_log2 (sxv (2^idx))); [reflexivity| apply sxv_range |].
pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. cbn; lia.
apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
destruct (Z.lt_ge_cases idx 31).
- rewrite (sxv_small (2^idx)) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx n); [|reflexivity]. subst n. cbn.
rewrite !sxv_testbit_lo by lia. rewrite TF, TA. reflexivity.
- assert (idx = 31) by lia. subst idx.
assert (Hlt : forall v, 0 <= v < 2^32 -> Z.testbit v 31 = false -> v < 2^31).
{ intros v Hv Hb. destruct (Z.lt_ge_cases v (2^31)); auto.
exfalso. assert (Z.testbit v 31 = true); [|congruence].
rewrite Z.testbit_true by lia. replace (v / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity. }
pose proof (Hlt freed HF TF). pose proof (Hlt avail HA TA).
rewrite (sxv_small freed), (sxv_small avail) by lia.
destruct (Z.lt_ge_cases n 31).
+ replace (Z.testbit (sxv (2^31)) n) with false; [reflexivity|].
symmetry. rewrite sxv_testbit_lo by lia. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
+ assert (Lg : forall v, 0 <= v < 2^31 -> Z.testbit v n = false).
{ intros v Hv. destruct (Z.eq_dec v 0) as [->|]. apply Z.bits_0.
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia| lia]. }
rewrite (Lg freed), (Lg avail) by lia. apply andb_false_r.
Qed.
Lemma sxv_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "G'D'>&RAzr1%3221&RC&RH+2+Q0%3221%5271%;271&@'?&Gr2%211%43B1?%53C3@%7221p091pY2F1").
Proof. intros v. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.
Lemma add_bit_nocarry : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q1'D'>&RAzr2%3221&RC&RH+2+Q0%3221%5271%;271%7294%=291'?'4&RLr4r3%3221(6%73621&R>r5%B2A7%3221%E21Ap061p0?1p0B1pW2O1pY2Q01").
Proof. intros v idx.
intros Hv Hi Hb.
assert (HL : Z.land v (2^idx) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
rewrite (Z.add_nocarry_lxor _ _ HL).
assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed.
Lemma sxv_congr : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "D'D'?&RDr2&RH+2+Q0%3221%6251r1%8213%:3;31&Gr3%211%31<%?3@21p061pY4B1pY2C1").
Proof. intros v w. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.
Lemma lor_sxv_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "M'D'>&RAzr2%3221&RC&RH+2+Q0%3221%5271%;271'?&RD&RB&Gr4%211r3%411%6231%821<%8264%;3H21p0=1p0>1pULK1pVFL1").
Proof. intros f a.
intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.
Lemma addw_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "E'D'?'T5yR0%211&T4&T6yQ0&R>r2r1%3221%6251%82:1&I&G%115%311%A3>51pY8C1pY6D1").
Proof. intros x y. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.
Lemma wz_inj : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "N'D'>&RAzr2%3221&RC&RH+2+R0%3221%5271%;271'?'T5yR0%211&Ir4%211r3%411%93631r5%;3H16p031p0>1p0?1pV4L1pULM1").
Proof. intros a b. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.
Lemma sxv_eq_iff : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "D'D&@'?&Gr2%211r1%411%63831&RD&RH+2+Q0%3221%52:1%6292%>3@21%@291pY4B1pY2C1").
Proof. intros v w. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.
Lemma free_all_test : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "QD'D'>&RAzr4%3221&RC&RH+2+Q0%3221%5271%;271r3%<2:1%>2:1%:2<7&@'?&G&R>r6%?2>1%411&RBr8%711r7%911%5231%:271%<11&RKr5+1%?221%M2L1%5213%C11%E3Q781%@2?=%E21C%H3Q:15%J241p0L1p0N1p0Q21p0Q31pW6Q@1pW2QA1pV2QB1pVHQC1").
Proof. intros freed avail idx li.
intros HF HA HI HL. rewrite sxv_eq_iff.
rewrite <- Zplus_mod_idemp_r, lor_sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32 by lia.
assert (X1 : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
assert (XY : 2^idx < 2^(li+1)) by (apply Z.pow_lt_mono_r; lia).
assert (Y32 : 2^(li+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
pose proof (Z_lor_range freed avail ltac:(lia) ltac:(lia)).
assert (HLr : Z.lor freed avail < 2^32).
{ apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |]. intros k Hk.
rewrite Z.lor_spec, (Z_testbit_high 32 freed k), (Z_testbit_high 32 avail k) by lia. reflexivity. }
set (X := 2^idx) in *. set (Y := 2^(li+1)) in *. set (L := Z.lor freed avail) in *.
clearbody X Y L. rewrite (Z.mod_small X) by lia. mlia.
Qed.
Lemma le4_congr : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "N'T5yR0%211'?'D&RD&T7r2%2271&RH+2+Q0%3221%8251r1%92>1%;214%>3=41'8y8%D11%311&Q0r3%211%31B%G3521p0:1pV4J1pULK1").
Proof. intros a b. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.
Lemma free_store_val : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "QA'D'>&RAzr2%3221&RC&RH+2+Q0%3221%5271%;271%7294%=291'?'4&RLr4r3%3221(6%73621'8'T5y8%211%411&Q0&I&G&R>%I2H>%311r5%511%5231%711%911%;11%9268%<11%>11%L3@41p0F1p0O1p0Q21pW2Q?1pVHQ@1").
Proof. intros freed idx.
intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.
Lemma self_word' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q:'D'>&RAzr1%3221&RC+X0%2241%8241'?'T5yR0%211&T4&T6yQ0&RI+1&RD&T7&R@r2+O%3221%;2=1%62>1+Q0%9221%<2;1%?2>1%A2C1&I&G&RH+2%221<%411%611%M3J81p0O1pV6Q91").
Proof. intros b3.
intros.
assert (0 <= Z.land b3 31 < 32).
{ split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma sllw2_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q1'D&RAzr1%3221'?'T5yR0%211&T4&T6yQ0&RI+2&RDr2+Q0%3221%6251%9281%;2=1&I&G&RH&R>+1%2291%42>1%611%811%I3F:1p0K1pVDQ01").
Proof. intros e.
intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma addiw_m1_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "K'D'?'T5yR0%211&T4&T6yQ0&R>&T7&I&Gr1%211%411%62<1-1%9221%<2;1%>2@1&RK+1%22:1%<11%>11%H3E61pY8J1").
Proof. intros y.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
Lemma rw_cells_congr : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q?'8'E%211'T5yR0%211';y8%511%311p051'D'J%=11'?%?17&Kr2%211r1%411%73631'9&Lr3%211%319%=3521&M%115&Q4r8r7r6r5%544321r9%741653p031p0:1p0=1p0D1pV>M1pV<N1p2Q11pW:Q31pX0Q<1").
Proof. intros segs m A cs cs'. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.
Lemma le1_neg1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "D'?'8'T5y8%211%411&O&T4yR0-1%3221%511(5&H+WO%211(:%11=%63>31%C3>81").
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.
End CEIL_WRAP_2.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Definition frozen (P : Prop) : Prop := P.
Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
[(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.
Definition free_triv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) (P G v : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (free_W sp P G) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2 /\ wmono asegs m m2
/\ m' = write_to_mem (write_to_mem (write_to_mem m2 (wa (P - 3)) [b8 255]) (wa (P - 2)) (le2 (wz 0)))
(wa (G + 28)) (le4 (wz v)).
End CEIL_WRAP_3.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
Section CEIL_WRAP_4.
Context {RUNp : RunP}.
Lemma wr_at_sub : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q4'8'E%211'T5yR0%211';y8%511%311p051'D&Q2r6r5r4r3%544321&RA%1253&R>%1265%2298%5221r9r8%>421<;p041p091p0<1pWBC1p4D1pW@E1p2F1pW:H1pX0Q11").
Proof.
intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.
Lemma rw_cells_prefix : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "O'8'E%211'T5yR0%211';y8%511%311p051'D'J%=11&Q4r5r4r3&3r2r1%33921%847651r6%:41987p031pVB=1pV@>1p2A1pW:C1pX0L1").
Proof.
intros segs m A cs1 cs2 [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
split; [split; [exact WF1 | exact B1] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.
Lemma bytes_at_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "O'8'E%211'T5yR0%211';y8%511%311p051'D%<14&Nr5r4r3r1%544321'?%13954r7r6%:42187p041p071pV:>1pUN@1pULA1pW:C1pX0L1").
Proof. intros; subst; assumption. Qed.
Lemma rw_cells_of_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q:'8'E%211'T5yR0%211';y8%511%311p051'D'J%=11&Mr1%211&Nr5r4r3&Kr2%211%746541&Q2r6&RF&L%119%311%645=<1&Q4r7%2418@?p041p0<1p0E1pV<I1p2L1pW:N1pX0Q71").
Proof. intros. split; [split|]; assumption. Qed.
Lemma area_of_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Q4&Q;'D'?&RD&<'Cr2%33261+TP0%6221z%93:21'>&RA%1248&RC+S5%22;1%6241&Q=&Q:r4&R>+H&RE+Q8r3%3221%6251%9281%;11%M3O1:p0>1p0F1pW4Q11pULQ31").
Proof.
intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.
Lemma page_off_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "L'D'?&RDr3+TP0%3221z%63721'>&RA%1247&RC%1298%5231&R>r6r5%3221r4%5221%B21@%D3E13p091p0@1p0A1pY6I1pWDJ1pV4K1").
Proof.
intros b o x Hb Ho Hx.
replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.
Lemma base16_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "E'D'?&RDr2+TP0%3221z%63721+@%7261%93:14&R>r4r3%3221%=217%?3@1:p071p0;1pWJC1pV4D1").
Proof.
intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.
Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
[(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.
Lemma rd8_known {R} st q v (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.
Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.
Lemma get_meta_rec_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "C'R2&Q;'D'?'R1&QE&R=r3r2r4%43321r1%7221%8242%;3:21pVJ>1pY2>1pWL@1pX4B1").
Proof. intros st q v g. reflexivity. Qed.
Lemma get_meta_rec_wr16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "C'R2&Q;'D'?'R1&QE&R<r3r2r4%43321r1%7221%8242%;3:21pVJ>1pY2>1pWL@1pX4B1").
Proof. intros st q v g. reflexivity. Qed.
Lemma optr_eqb_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free ";&Q;'?'4&R4(2r1%2261%4211(=%83721pWL:1").
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_free_trivial_model := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_free "Y5'R2&Q;'QH'Q<'D'R8&QFr8&7'Cr7%33271%6251&<%135:7&R>r4&RE+X0r3%3221%6251&R@r6+O%3221&Q:r;&RK&RG&Q8r2%?221%411%6214%9281'R1&QEr=%221<&R;r<&QN&QJr1%211&Q>%11L%Q1231%711&R<-2%J2>1z&R=-3%N2B1+WOr>%53321%:3871%E3D<1&RJr:+5%3221&R:r5%22QA1&QG%11QC&Q5%Q<221%Q?251'?&RD+@%22R61%43R:1I'QA&Q@r9+4%QG221%42E1(Q6%11Q1%=3831+3%QM2J1%:2QO1%61Q1%B3=21+2%R22R31%?2QF1%F3A15+1%R62QI1%C2QM1%J3E19';%11S4&T3'T<&T;&T>&T?%34S32S81&T:&T8&T9%36S762S<51%94S@51S?&T=%14SB73SA&R7rF%211%@6SFSE64QH1(2rC%22SH1%QA3E41&R3&QDrD%211rE%92T01%QH3631&QM%11S9%=2T4RL%QL3:21%Q21T4%Q04T7LHT5%G4T8MIT6&Q=rG%211&R6rI%211%Q96T?T=8741%I2T>A%R83;21&Q9%11O&Q?&QBrJ%211%411%R@3TF61&RA&QI%11S3%32S91r?%SE11%62S<1rH%82S>1&QKrA%211%<2Q>1'4&RLrB%?11%321Q>(6%S43621%T41QF%721Q@%S73914&RC&QO%11QF+Q@%4221'>&R9%61QI%211%U:21Q@%Q121J%U>2QBRL%U=241%=2M1%9241p0;1%Q72=9%@1R>+QO%SK3V121p041&A&QL%11RD%T03V61TE%411&R?%51R2+TP0%UN221%421UB%UE21S@%QG2QK1p081%Q22RDTD%V83V<VARErL%UK221%QM2S31rN%V=3VAVFS5%UO21R@%T<231%TC3T>1T7rO%VB3VFVKRD%T@221%TG3TB1T;rK%UH11%TJ3W01U?%N11&RB%UL1A%R<1B%3221%UL1A%VL221&R0%R91G%211%U53W;41%Q911&Q7%11WB&QCrQ:rQ9%SN2WE1%4231&R5%12WIQ3%U@3831p0;1p0G1p0L1p0Q11p0Q71p0Q<1p0Q>1p0QL1p0R21p0RC1p0RG1p0RO1p0S41p0S71p0S;1p0S@1p0SI1p0T61p0T;1p0TC1p0U;1p0U@1p0UE1p0UK1p0V51tVDXCV;1tWNXAVD1tX6XFVI1tW<WCW@1tV8XGWE1tW2XEX01tWFXFX51tWJXGX=1tX2XGX@1pVNXI1pW8XJ1pV6XK1pV0XM1pVLXO1pVJY11pWHY21pX4Y41")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 2%nat 0%nat).
Variable gh : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 3%nat 0%nat).
Variable ar : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 4%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 5%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 6%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_free_trivial_model) 7%nat 0%nat).
Lemma free_trivial_model : ltac:(sec_stmt2 constr:(SEC_T_free_trivial_model) 8%nat 0%nat).
Proof.
intros sh po off16 idx base mr st' reserved e AL C4 C3 C2 C1 Hgh Hg Hmem Har Hchk AV FR B3
Hidx Hav Hfr Hsc Hsc63 Hml RES5 RESe E1 E0 Hfz Hall.
unfold free, free_hdr, get_meta, guard. fold po. rewrite (proj2 (Z.eqb_eq _ _) AL).
rewrite (rd16_known st (aadd p (-2)) lo hi) by (cbn [fst snd aadd]; fold po; first [replace (po + -2) with (po - 2) by lia; exact C2 | replace (po + -2 + 1) with (po - 1) by lia; exact C1]).
cbv beta.
rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
cbv beta.
rewrite (rd8_known st (aadd p (-4)) 0) by (cbn [fst snd aadd]; fold po; replace (po + -4) with (po - 4) by lia; exact C4).
cbv beta. cbn [Z.eqb negb].
fold off16. fold base. unfold get_group. rewrite Hgh, Hg. fold mr. rewrite Hmem, optr_eqb_refl.
fold idx. replace (idx <=? m_last_idx mr) with true by (symmetry; apply Z.leb_le; lia).
unfold testbit. rewrite Hav, Hfr. cbn [negb].
rewrite Har, Hchk, Z.eqb_refl.
match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 16)) _] =>
replace (if c then x else y) with true end.
2:{ destruct (Z.ltb_spec (m_sizeclass mr) 48).
- specialize (Hsc ltac:(lia)). symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- specialize (Hsc63 ltac:(lia)). symmetry. apply Z.eqb_eq. lia. }
match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 17)) _] =>
replace (if c then x else y) with true end.
2:{ destruct (Z.eqb_spec (m_maplen mr) 0); cbn [negb]; [reflexivity|]. symmetry. apply Z.leb_le. apply Hml. assumption. }
unfold slot_start. rewrite Hmem.
assert (He : aadd (aadd base (UNIT + get_stride mr * idx)) (get_stride mr - IB) = e) by (unfold e, slot_start'; rewrite Hmem; reflexivity).
rewrite He.
assert (Fe : fst e = fst p) by (rewrite <- He; reflexivity).
unfold get_nominal_size.
rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
cbv beta. fold reserved.
replace (5 <=? reserved) with false by (symmetry; apply Z.leb_gt; lia).
fold po. replace (reserved <=? snd e - po) with true by (symmetry; apply Z.leb_le; lia).
rewrite (rd8_known st (aadd e (- reserved)) 0) by (cbn [fst snd aadd]; rewrite Fe; fold sh; replace (snd e + - reserved) with (snd e - reserved) by lia; exact E1).
cbv beta. cbn [Z.eqb].
rewrite (rd8_known st e 0) by (rewrite Fe; exact E0).
unfold guard. cbn [Z.eqb]. unfold Malloc.ret at 1. rewrite sbind_ret_l.
unfold free_tail, guard. rewrite !get_meta_rec_wr16, !get_meta_rec_wr8. fold mr.
unfold testbit. rewrite Z.lor_spec, Hfr, Hav. cbn [orb negb].
replace (m_freed mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfz).
replace (Z.lor (m_freed mr) (m_avail mr) + bit idx =? mask_upto (m_last_idx mr)) with false by (symmetry; apply Z.eqb_neq; exact Hall).
cbn [orb negb]. reflexivity.
Qed.
End SE.
End CEIL_WRAP_4.
