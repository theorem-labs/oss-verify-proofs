(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W12.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RF_malloc_entry RAllocSlot_iface RASlot_I RMallocKit_A3 RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W12 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_entry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2eq"; "2ex"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "6stc_q"; "7wz"; "8evt"; "9mkR"; ":MS"; ";mem_inv"; "<size_class"; "=rsegs"]; [">rt1_regs"; "?RSIZE_CLASSES"; "?ralloc_meta_entry"; "?ralloc_slot_entry"; "@seg_rom"; "Aadd"; "Amul"; "0a0"; "0a1"; "0a2"; "0a2'"; "0a3"; "0a3'"; "0a4"; "0a4'"; "0a5"]; ["0a6"; "0a7"; "0cnt"; "0fc"; "0gp"; "0j"; "0m"; "0ms'"; "0n'"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"]; ["0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sc"; "0sp"; "BZ_to_bv"; "Bbv"; "0szc"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"]; ["0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Lemma rag_entry_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W12 "SA'QIyR0%211&7y5%2213yQ0%711'1y8%:11%311p0:1&=&?r1%3221&:'6'2&<&@vQF&QH+ccW0%22H1rNrMrLrKrJrIrH&E&A&F+2%22?1%5241%@2Q61rFrErDrCrBrAr@r?%I2Q?;&9&>%11M%311%N2QDCr;r:r9r8r7r6%Q7KQ6Q3Q2Q1Q0ONMLEDCBA@?>=<87654321r5&B%Q82QN1r4(0%11R0r3&D%11QG%QB7:976431%QD3QEQH1qR@QF1rGr>r=r<%QHKQGQCQBQAQ@Q?Q>Q=4Q5Q4Q3Q2Q1Q0ON321GFEDCB@+ccV8%QH2R>1r2%QM74A2>?1<%R13R4:1p0R31pR>R81pR8R>1p<RA1pT4RE1pT2RF1pT0RG1pSNRH1pRLRI1pRJRJ1pS<RK1pS:RL1pS0RM1pRNRN1pR4RO1pR2S01pR0S11pQLS21pQHS31pQDS41pQBS51pQ@S61pRHS71pSLS81pSJS91pSHS:1pT6S;1pR:S<1pS@S=1pRDS>1").
Proof.
intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (size_class_range sc SC) as SZR.
step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (110048 + 2 * sc) with (110048 + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed.
End AG1.
Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then 0x9d348 else 0x9ccec)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9cce0) fc None m (seg_rom rsegs)).
Proof.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.
Lemma rstc_q_eq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W12 ":'2'4vQ5&8&FvQJvQ2%3221%511%93871").
Proof.
unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.
Section SE.
Local Abbreviation SEC_T_rnest_call_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W12 "T1'QIyR0%211&7y5%2213yQ0%711'1y8%:11%311p0:1&=&?r1%3221&:'6'3'2r4&<&;&QH+ccf8%22I1rQ4rQ3rQ2rQ1rQ0rOrNrMvQ5%<2Q31&9vQ8%211r3r2rHrGrFrDrCrBrAr@r?&A%L2QC1r>r=r<r;r:r9%Q4OQ1Q0ONMLKJIGDCBQ<A@?G>=<;:97654321r8&C%Q62QM1r7(0%11QOr6&D%11QF%Q?7:976431%QB3QDQA1qQNR51%QE2R61qQJR71%QG2R81qQFR91%QI2R:1qR@QK1rLrKrJrIrE&FvQJ+@%3221vQ2%5221%QD11r5%R4OQMQLQKQJQI=<;:QAQ@Q?92Q>Q=Q<Q;Q:Q9Q6Q5Q4Q3Q7Q2Q1OLI1+cc_H%R52RL1%R873R91QFMQEJ%R>3RAB1p0R@1pR>RE1pR8RK1p<RN1pT4S21pT2S31pT0S41pSNS51pRLS61pRJS71pS:S81pS8S91pS6S:1pS4S;1pS2S<1pS0S=1pRNS>1pR4S?1pR2S@1pR0SA1pQHSB1pQDSC1pQBSD1pQ@SE1pRHSF1pRFSG1pSLSH1pSJSI1pSHSJ1pT6SK1pR:SL1pS@SM1pRDSN1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 15%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 16%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 17%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 18%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 19%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 20%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 21%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 22%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 23%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 24%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 25%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 26%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 27%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 28%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 29%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 30%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rnest_call_walk) 31%nat 0%nat).
Lemma rnest_call_walk : ltac:(sec_stmt2 constr:(SEC_T_rnest_call_walk) 32%nat 0%nat).
Proof.
intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
unfold RSIZE_CLASSES, ralloc_slot_entry in *.
assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x9cec8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 110048) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 641768) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 110048) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9cebc) fc None m (seg_rom rsegs))).
{ intros a0' a2' a3' jv ->.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite SysStep.sextw_small by lia. step. step.
apply evt_done. do 3 eexists. reflexivity. }
step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
-
apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
-
assert (Q10 : 10 <= q) by (unfold n' in K; nia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].
step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.
step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.
step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
assert (K13 : 3 <= k <= 12).
{ unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
step. rewrite ?zxb_b8 by lia. clear DBR.
step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (110048 + (i + 1) * 2) with (110048 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.
assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x9cec8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 110048) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 641768) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 110016) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 110048) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9cea0) fc None m (seg_rom rsegs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.
step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (110048 + i1 * 2) with (110048 + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.
step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End SE.
End STC.
Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then 0x9cf40 else 0x9cecc)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9cec8) fc None m (seg_rom rsegs)).
Proof.
intros until idx. intros IR MI.
step. if_cases K; zify_cond K.
- replace (idx =? -1) with true.
2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
apply evt_done. reflexivity.
- replace (idx =? -1) with false.
2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.
