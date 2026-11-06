(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_get_meta () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_get_meta.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0B"; "1None"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1snd"; "2and"; "2eq"; "2iff"; "2not"]; ["3N"; "3Z"; "0F"; "0G"; "4ov_read_bytes"; "5bvmap"; "0P"; "0RUNp"; "6sxv"; "7b8"; "7meta_slot"; "7wz"; "8C4"; "8C8"; "8cell"; "9evt"]; [":mkR"; ";MS"; "<le2"; "<le8"; "<mem_inv"; "<wa"; "=rw_cells"; ">rsegs"; "?rget_meta_post"; "?runlock_post"; "@RCTX"; "@RMLOCK"; "@RSIZE_CLASSES"; "@rget_meta_entry"; "@rmrep"; "@runlock_entry"]; ["AKnown"; "ARKGroup"; "AUNIT"; "Aa_check"; "Aaadd"; "Aaptr"; "Aarea"; "Aarea_of"; "Ac_secret"; "Acell_read"; "Acellval"; "Aconc"; "Actx"; "Ag_meta"; "Aget_meta_rec"; "Aget_shadow"]; ["Aghdr"; "Am_avail"; "Am_freeable"; "Am_freed"; "Am_last_idx"; "Am_maplen"; "Am_mem"; "Am_sizeclass"; "Ameta"; "Amstate"; "Aoptr"; "Ar_base"; "Ar_kind"; "Ar_len"; "Aregion"; "Arkind"]; ["Around_up_pg"; "As_areas"; "As_groups"; "As_regions"; "Ashadow"; "Asize_class"; "Bseg_rom"; "Cadd"; "Cland"; "Cle"; "Clt"; "Cmodulo"; "Cmul"; "Copp"; "Cpow"; "Cshiftl"]; ["Cshiftr"; "Csub"; "Ctestbit"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0ar"; "0avail"; "0b3"; "0base"]; ["0fc"; "0freeable"; "0freed"; "0g"; "0gh"; "0gp"; "0gw"; "0hi"; "0i"; "0idx"; "0last_idx"; "0lo"; "0m"; "0maplen"; "0mr"; "0mword"]; ["0next"; "0off16"; "0p"; "0po"; "0prev"; "0r"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"]; ["0s7"; "0s8"; "0s9"; "0sc"; "0secret"; "0sh"; "0sp"; "0st"; "Dlookup"; "EZ_to_bv"; "Ebv"; "Ebv_swrap"; "Ebv_unsigned"; "FN_countable"; "FZ_countable"; "Fprod_countable"]; ["Gprod_eq_dec"; "Hgmap"; "Hgmap_lookup"; "Ieq_dec"; "Jeq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma land_pow2_testbit : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "I'A&RIzr2%3221&>'=&RHr4&RN+2r3%3221%6251%83>1<'4&S2%1296(6%=3421%?261p0A1p0B1pWBG1pV8H1").
Proof. intros a i.
intros Ha Hi. split.
- intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
rewrite H, Z.bits_0 in T. discriminate.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.
Lemma sllw1_word' : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "Q3'A'<&RIzr1%3221&RJ+Q0%2241%8241'='TJyR0%211&TI&TKyQ0&RO+1&RKr2%221>%5241%8271%:2<1&K&H&RN+2%2219%411%611%F3C81p0H1pWBQ21").
Proof. intros i. intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.
Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).
Lemma rget_meta_tail : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "TA'TJyR0%211&Ey5%2213yQ0%711':y8%:11%311p0:1'A'<&RIzr3%3221&RJ+RPP0%2241%8241&RN+2+R0%3221%82:1%>2:1+Q8%7261%<2>1%B2>1'=&S0r5+<%3221r4%63J21&?%83L6I%211r8&S1&RLr6+X0%3221+1%6221%Q4281p0:1&O&Q7&Q8rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rJrIrHrGrFrErDrCrBrAr@r?r>r=rLrKr<r;r:r9%NNMLKJIHGFEDCBA@?>=<;:987654Q:321&Q1&Q0&K%11Q>r7%311rOrNrM%8OQ7Q6Q5Q4Q3Q2Q1Q0O>64321@?NMLKJIHGFEDCBA&TI+c\RH%22S11(2%11S2&RF%11Q@%A78E5D3C1%QC3QBC1p0QE1p0R31p0R;1p0R@1p0RG1pWLS11pX0S21pX4S31pWJS51pW2S;1pQ6S>1pW>SB1pZHSC1pZFSD1pZDSE1pZBSF1pXFSG1pXDSH1pY6SI1pY4SJ1pY2SK1pY0SL1pXNSM1pXLSN1pXJSO1pXHT01pVHT11pVFT21pVDT31pVBT41pV@T51pXBT61pX@T71pZ@T81pZ>T91pZ<T:1pZJT;1pW<T<1pY>T=1pX>T>1").
Proof.
intros until maplen. intros O16 MW ML MW4 Hml.
st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
- st1. unfold rget_meta_post. finish.
- st1. st1. st1. if_cases K2; zify_cond K2.
+ st1. unfold rget_meta_post. finish.
+ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rget_meta_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "[A'TJyR0%211&Ey5%2213yQ0%711':y8%:11%311p0:1'A&RHr;+O%3221&RGr8&RL+Q0r7%3221%6251+R0r6%7221%:241+TP0r5%;221%>241'=&TLrQ:%22Q31rA%53I21&RKrB+@%3221z%;3O21&RIr>%K261%N217rC%5221rD%Q221;&RN+2%221N%;241&S1rEr@%Q82C1%4231%521E%N3QB>1%I26Q3%8271%Q13QEA1rF%G2I1rG+Q8%QE221%K21A'8%11R0%R311&D&Q7rJ&Q5rI+4%I221%411u1%948721(3(5&I%11Q>(9%11RA%53RB31%72C1%QM3C91rK+3%Q82C1%C11%G4F41?%<1Q1%>3RK1:%@2L1%R63L41rL%Q@2:QC%K11u2%Q04O421&Q2&K%11Q<%311%K2Q71%RA3Q761rM%Q51Q6u8%Q:4Q9321&Q3%:1I%211%Q42Q@1%RJ3Q@51&Q6rN'N(M%11R5r?%311%41;(L%G1R0%211%31Hr=%K11%;11%QA1=%QE3>21%QF3?61%QG3@81%QH3A<1%QI3B>1%QJ3CA1%F4R5EQ:1rO%R51QE%R94R821Q0%Q81S>%Q011%R22R>1%SH3R>41rQ0&Q:%R=11%RA4R@31Q8%Q@1S=%Q811%R:2RF1%T03RF41&RJ+Q@%22S11rQ2&Q<%TC2SAS2%TF221%RJ11%RN4RM51QO&RE%11S7%QO11%R111%RI2S51%T?3S561p0=1'<%T62T8R0+X0%C2R21%4231+RPP0%F2R51%7261%T52T4U5%I2R81%:291%T@2TBS=%L2S>T7%=221%TC2TER3%O2R4U<%@221%Q12R6T=%B241%Q32R8U<%D261%TB2TAT1%Q62R;1%G291%TM2S;Q5'4&S2rQ5%221S6(6%U?3521%524RN%UA3713rQ3%QB21QArQ4%Q;11%V321R4rQ9%U<221+1%V92R81%V8261%QK251%Q<251p0;1%UC2QM;+QO%V13VEE1p031&?%V43VH@UJ%211rQ;%VD2KQD%U@21?%UM231p051&O&Q8rRBrRArR@rR?rR>rR=rR<rR;rR:rR1rR0rQOrQNrQMrQLrQKrQJrQIrQHrQGrQFrQErQDrR3rR2rQ?%TJ11rQCrQBrQA%ONNMLKJIHGFEDCBA@?>=<;:98764Q5321&Q1&Q0rR9rR8rR7rR6rR5rR4%7OQ7Q6Q5Q4Q3Q2Q1Q0O654321@?NMLKJIHGFEDCBA&TI+c[k4%22XG1(2%11XH&RF%11V?%@78D5C3B1%QB3VAB1p0QD1p0QM1p0R21p0R@1p0RC1p0RJ1p0RL1p0S01p0S31p0S61p0S:1p0S>1p0S?1p0SC1p0SG1p0SM1p0T>1p0TG1p0TO1p0UG1p0V11p0V=1p0VG1p0W>1p0WC1p0WF1p0WJ1p0X21p0X91p0X@1p0XG1tX0YAXN1tWDYBY>1pX2YN1pX:YO1pY:YE1pWLYF1pY8YG1pW4YH1pWFYI1pW6YJ1pVLYK1pX4YL1pVNYM1p2YN1p4YO1pQ8Z01pQ>Z11pWJZ31pW2Z91pQ6Z<1pZHZ@1pZFZA1pZDZB1pZBZC1pXFZD1pXDZE1pY6ZF1pY4ZG1pY2ZH1pY0ZI1pXNZJ1pXLZK1pXJZL1pXHZM1pVHZN1pVFZO1pVD[01pVB[11pV@[21pV>[31pV<[41pV:[51pXB[61pX@[71pZ@[81pZ>[91pZ<[:1pZJ[;1pW<[<1pY>[=1pX>[>1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 33%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 34%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 35%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 36%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 37%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 38%nat 0%nat).
Variable off16 : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 39%nat 0%nat).
Variable avail : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 40%nat 0%nat).
Variable freed : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 41%nat 0%nat).
Variable last_idx : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 42%nat 0%nat).
Variable freeable : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 43%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 44%nat 0%nat).
Variable maplen : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 45%nat 0%nat).
Variable secret : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 46%nat 0%nat).
Variable prev : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 47%nat 0%nat).
Variable next : ltac:(sec_ty2 constr:(SEC_T_rget_meta_walk) 48%nat 0%nat).
Lemma rget_meta_walk : ltac:(sec_stmt2 constr:(SEC_T_rget_meta_walk) 49%nat 0%nat).
Proof.
intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.
assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
- specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
- specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (110048 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (110048 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
End SE.
Lemma rget_meta_spec : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "\K'TJyR0%211&Ey5%2213yQ0%711':y8%:11%311p0:1'R9&QE'R>'R0'QF'A'RD&QOr9&7'@r8%33271%6251&;%135:7&RGr4&RL+X0r3%3221%6251&RHr6+O%3221&QDr<&S1&RM&QBr2%?221%411%6214%9281'R8&QNr>r;%3221&Q>vGr?r@%43321&Q4&Q7rA%3221'=%QI1QB&TH'U1&U3&TM%34Q?21QG&U2%14QA43QI%QC3QBQG?&RC%11=%:6QEQM6431(3%12QOE%?3>31'R?&R<%11H(QA%D3421&TLrQ<%22RF1&R;%11K%QM21R5%K3R941&RKr:+@%3221z%Q13R?21&RI%125Q>%R526Q?%R8217%421QMr=%R;21:&R@&R=rE%211%411%<261'QJ&QI+4%R82QN1%32QJ1(Q@%11E%QF3731+3%R>2QO1%92QO1rC%711%QL3=31+2%RD2R41%?2R11%R03A15rB+1%RI2R51%D231%R53F1:%SN1SF&U0&U4%24SBR5SG1&TO&TN%26SER8R7SJ41%R:4SO41SM%R74T052SN&RBrL%211%R@6T4T254RI1rH%R72T41%RE3?31&R:&QMrI%211rJ%R>2T=1%RL3631&JrNrK%3221%T63T:T?A%R02R21&R6%11Q3%RH2TGQ;%S63@21%TO1TF%S54TJOLTG%S24TKQ0MTH&QG%11=&RArQ1%211%S=6U1TN7641%S32TOQ0%SA3:21&QCrM%211&QH&QLrQ2%211%411%SJ3U861'<&R1%11RB%RL2RN1&RJ&RN+Q0%22R51%4261%9261&R3rF%211%S62S81%:227%?221rQ5%F11%H11%S<2S>1+R0%@2RC1%B241%G241&R4%11R1%SC2SE1%G22E%L221&R2%11R1%SH2SJ1%L22RN%Q1221&R7%11R4%SM2SO1%Q122A%Q6221&R5%11R4%T22T41+Q8%Q62S91%Q8241%Q=241%F1RI%T82R<1'4&S2%QA1QJrO%3221(6%UA3621%Q=1RDrQ0%8221%UE3:15%I18+Q@%QI221&RE%M17%211%VM21R5rQ3%TL221%W22R8SM%W1251%R2241%R7241p0;1%U22=:%Q81RH+QO%V73WE21p041&?%Q81RM%V;3WI1U;%311%Q;1RF%W?21W>%W521T=%U>2R51p051&O&Q8rRBrRArR@rR?rR>rR=rR<rR;rR:rR1rR0rQOrQNrQMrQLrQKrQJrQIrQHrQGrQFrQErQDrR3rR2&K&QKrQ@rQ=%3221%511rQCrQBrQA%Q3NQ2Q1Q0ONMLKJIHGFEDCBA@?>=<;:4S;321&Q1&Q0rR9rR8rR7rR6rR5rR4%7OQ;Q:Q9Q8Q7Q6Q5Q4Q3654321DCQ2Q1Q0ONMLKJIHGFE&TI&Q=%22Z11(2%11Z2&RF%11X9%@78D5C3B1%QF3X;B1p0QH1p0R21p0R81p0RG1p0RL1p0S41p0S71p0S?1p0SE1p0SK1p0T11p0T:1p0TA1p0TL1p0U61p0UB1p0UG1p0UJ1p0UO1p0V71p0VH1p0VN1p0W31p0W:1p0WC1p0WL1p0X01p0X31p0X:1p0XB1p0XH1p0Y91p0Y>1tWNYHYD1tW0ZMYJ1tWDZJZ51tX4ZKZ:1tX8ZLZB1tY<ZLZE1pW@ZN1pWHZO1pVN[01pVJ[21pW:[41pW8[71pX<[71pX6[91pY@[;1pWJ[=1pW2[C1pQ6[F1pZH[J1pZF[K1pZD[L1pZB[M1pXF[N1pXD[O1pY6\01pY4\11pY2\21pY0\31pXN\41pXL\51pXJ\61pXH\71pVH\81pVF\91pVD\:1pVB\;1pV@\<1pV>\=1pV<\>1pV:\?1pXB\@1pX@\A1pZ@\B1pZ>\C1pZ<\D1pZJ\E1pW<\F1pY>\G1pX>\H1").
Proof.
intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). pose_ceil.
destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.
destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m MR) as RC.
destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
{ unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). pose_ceil.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
unfold rget_meta_entry.
eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
- intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.
Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).
Lemma runlock_spec : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_get_meta "SG'TJyR0%211&Ey5%2213yQ0%711':y8%:11%311p0:1'='A&TLrI%22@1&Q;%63521&Q6&Q7r2rJ%92G1(5'N(L&Kz%211%411(9%117%93831%?4>=;1&O&Q9rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3%Q1Q1Q0ONMLKJIHGQFFEDCBA@?>=<;:987654321&Q1&Q0%1OQ3Q2Q1Q0ONMLKJQBQIIHGFEDCBA@?>=<;:987&TI&Q?%22R;1(2%11R<&RF%11QK%:78>5=3<1%Q>3QM<1p0Q@1p0R11pWJR91pW2R?1pQ6RB1pZHRF1pZFRG1pZDRH1pZBRI1pXFRJ1pXDRK1pY6RL1pY4RM1pY2RN1pY0RO1pXNS01pXLS11pXJS21pXHS31pVHS41pVFS51pVDS61pVBS71pV@S81pV>S91pV<S:1pV:S;1pXBS<1pX@S=1pZ@S>1pZ>S?1pZ<S@1pZJSA1pW<SB1pY>SC1pX>SD1").
Proof.
intros until m. intros HA LK. unfold runlock_entry.
step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
{ exfalso. rewrite wz_unsigned in K by lia. lia. }
step. apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.
