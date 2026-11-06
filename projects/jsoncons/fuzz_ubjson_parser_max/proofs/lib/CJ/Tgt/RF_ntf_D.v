(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_D MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_ntf_D () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_ntf_D.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5mw_ok"; "6fg_usage_st"; "7meta_slot"; "7meta_word"]; ["7wz"; "8cell"; "8cells_size"; "9evt"; ":mkR"; ":stk"; ";MS"; "<mem_inv"; "=alloc_ceiling"; ">rw_cells"; "?aptr"; "?conc"; "?get_meta_rec"; "?m_sizeclass"; "?meta"; "?mstate"]; ["?usage"; "@rsegs"; "Arfg_post"; "BRCTX"; "Brmrep"; "Cseg_rom"; "Dadd"; "Dland"; "Dle"; "Dlor"; "Dlt"; "Dlxor"; "Dpow"; "Dsub"; "Dtestbit"; "0a"]; ["0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0b"; "0fc"; "0fr"; "0g"; "0gp"; "0k"; "0lo"; "0m"; "0mr"]; ["0n"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "EZ_to_bv"]; ["Ebv"; "Ebv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0u"; "0w"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma testbit_false_ge : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_D "L'8'6&Q8zr2%3221&Q:&Q<+2r1%3221%5271%;271r4%<215'7'1&Q>r6%221?(2%63521p081pSJG1p0C1p0=1pT2J1pS0K1").
Proof. intros a n.
intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma lor_lxor_ones64 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_D "N'8'6&Q8zr2%3221&Q:&Q<+2+R0%3221%5271%;271'7&Q9&Q;r4+_oooooooooooO%3221r3%5213%7231&Q7%1274%9217%<3I41p0>1p0?1pS@L1pS0M1").
Proof. intros a b.
intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
destruct (Z.lt_ge_cases n 64) as [L|G].
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.
Lemma usage_sub_word : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_D "Q>'8'6&Q8zr2%3221&Q:&Q<+2+R0%3221%5271%;271'7'R@yR0%211&R?&Q6r4&Q9&RA&Q;r3+_oooooooooooO%3221%92;1%62<1+_ooooooooooo0%9221%<2;1%>2@1&@&Q=&Q7+O%22=1+1%D221%62D1%811%L3I:1p0N1p0O1pUHQ<1pUFQ=1").
Proof. intros u w.
intros Hu Hw.
assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
rewrite unsigned_lit by lia.
change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
rewrite lor_lxor_ones64 by lia.
assert (HL : 0 <= Z.land w 31 < 32).
{ split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite zb_lxor_ones by lia. unfold wz.
rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c324) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.
Section SE.
Local Abbreviation SEC_T_rntf_fg := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_D "V4'R@yR0%211&:y5%2213yQ0%711'5y8%:11%311p0:1'3'A%211'O&J'8'N&Lr3r2%3221&Q4v;r4r6%43321&G&Q1r7%3221&>r5%2281&<%11;&Q:&M%116+Q@%4221'6&Q8z&Q0r9%91E%3221%6251&Q<+2+R0%3221%A261%=261p0?1&Ir;&Q6&RArQ9%22QN1-S0%5221r:%94Q5821'7'4&B%11<uS0%53421&Er=rQ;%@2R<1%B21>%54QA4Q01&H%11QH%Q621@&Q=rQ=%H2RD1+S0%4221%Q<2M1&C&Q2rQ?rQ>rQ<rQ8rQ7rOrNrMrLrKrJrIrHrGrQ:rQ2rQ1rQ0rFrErDrCrBrAr<r>r@&=%123Q<%RA1QM&?%11QOr?%Q2Q3Q1Q0Q8ONMLKJIHGFEDQ@CQNBA@?>=<;:9875QA421&F&D&R?%R32SOQ4%R521R1%32T11&K%12@QI%62T41rQ6rQ5rQ4rQ3&Q3%<2T:1%>OQA:QHQ?R0Q3R>Q>Q=76543Q2Q1Q01Q<Q;Q:Q9Q8Q7Q6Q5Q4ONML+c`g@%?2T=1(0%11T>&Q5%11SD%F77Q25Q13N1%QK3SFH1p0QM1p0R41p0R81p0R?1p0RF1p0S11p0SF1p0SI1p0SM1p0T21tT0T<T81pSLT>1pSFT@1pTNTB1pSDTD1pSNTH1pSBTN1pDU11pUBU51pU@U61pU>U71pU<U81pT<U91pT:U:1pTJU;1pTHU<1pTFU=1pTDU>1pTBU?1pT@U@1pT>UA1pS>UB1pS<UC1pS:UD1pS8UE1pS6UF1pS4UG1pS2UH1pT8UI1pT6UJ1pU:UK1pU8UL1pU6UM1pUDUN1pSHUO1pTLV01pT4V11")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 9%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 10%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 11%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 15%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 16%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 17%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 18%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 19%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 20%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 21%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 22%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 23%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 24%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 25%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 26%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 27%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 28%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 29%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 30%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 31%nat 0%nat).
Variable fr : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 32%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 33%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 34%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_fg) 35%nat 0%nat).
Lemma rntf_fg : ltac:(sec_stmt2 constr:(SEC_T_rntf_fg) 36%nat 0%nat).
Proof.
intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
pose proof (meta_word_range mr MW) as MWR.
pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(pose_ceil; unfold RCTX in *).
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
rmeta_chunk MR MSL CH. fold mr in CH.
st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
clear CH.
unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
- unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
specialize (UR ltac:(lia)).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (954560, 954560 + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
st1.
replace (wa (954560 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (954560 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. st1. st1.
rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
pose proof MR as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (954560 + m_sizeclass mr * 8 + 464)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
clear USG.
rraw_store_finish (954560 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CH' : rw_cells rsegs mX (conc st g) (meta_cells st mr)) end.
{ pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
clear CH. unfold meta_cells in CH'.
st1. clear CH'.
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
End SE.
End CEIL_WRAP_1.
