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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_enframe () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_enframe.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1cons"; "1nil"; "1option"; "2and"; "2eq"; "2or"; "3Z"; "0E"; "0F"; "4bvmap"; "0P"; "0P0"; "5wz"; "6C4"]; ["6C8"; "6cell"; "7evt"; "8mkR"; "9MS"; ":mem_inv"; ":wr_at"; ";rw_cells"; "<rsegs"; ">renframe_off_mem"; "=ren3_post"; "?fold_off"; "@seg_rom"; "Aadd"; "Adiv"; "Aland"]; ["Ale"; "Alor"; "Alt"; "Amodulo"; "Amul"; "Aopp"; "Apow"; "Ashiftl"; "Asub"; "0T0"; "0a"; "0a3"; "0a7"; "0avail"; "0d"; "0fc"]; ["0freed"; "0gp"; "0gw"; "0k"; "0m"; "0mword"; "0n"; "0next"; "0nw"; "0off"; "0off'"; "0off0"; "0p0w"; "0prev"; "0r"; "0ra"]; ["0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0slack"; "0sp"; "BZ_to_bv"; "Bbv"]; ["Bbv_swrap"; "Bbv_unsigned"; "0stride"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
let r := E - P - n in
let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].
Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ m' = renframe_tail_mem m P E n k q
/\ mem_inv rsegs m'.
Lemma lor_shl5 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "Q2'8'5&Q0zr1%3221&Q2+Q0%2241%8241r3%9281'6&Q1&Q4r4&Q6+2+5%3221%6251%821;&M&O+O%22?1&Q7%12<9%6231%A3M81p0C1p0F1pS8Q01pSNQ11").
Proof. intros r k.
intros Hk Hr. replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2 by lia.
assert (D : Z.land (r * 2 ^ 5) k = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 5).
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit k i) with false; [apply andb_false_r|]. symmetry.
destruct (Z.eq_dec k 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.
End CEIL_WRAP_1.
Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_renframe_tail_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "UK'R?yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8'6&RAr<%22@1r7%53621r4%73841&Q8&Mr9r3%3221+4%6221%?3@;1&E&Hr;%3221&Fr:+3%?221%@2>3%@213%649H31&Q0+1%D281&Q6+2+R0%3221%7251+@%K2?1%:21Q3r>r=%=221%Q023G%?213&Q2r?%Q5271%Q621Q<+O%B2A1%6231r@%Q;21=%9214rB%K2C1z%M216'5+Q0%@291%3241&B&JrQErQDrQCrQBrQ>rQ=rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1&R>rF%22RN1rJrIrHrErC&NrD%RA291%RB21QG%421QH%NIMLKJIHGFEDCBA@?>;:98<76Q71&D&CrQArQ@rQ?rQ<&>%11Q?rKrA%H2SD1rL%61ArQ;rQ0rOrNrM%AOQ@Q?Q>Q=@?>Q<Q;=;:N8765Q:Q9Q8Q7Q6Q5Q4Q3Q2Q14321+caPD%Q22SN1(1%11SO&L%11S4%I77Q45Q33Q21%QJ3S6K1p0R01p0QM1p0R21p0R31p0R61p0R91p0R=1p0RE1p0RH1p0RL1p0S01p0S91p0SA1p0SF1p0SO1p0T21pU6T91pS8T:1pS>T;1p2T<1pDT=1pJT>1pLT?1pS:TA1pS0TG1pFTJ1pSBTN1pSJTO1pUDU01pUBU11pU@U21pU>U31pT8U41pT6U51pTHU61pTFU71pTDU81pTBU91pT@U:1pT>U;1pT<U<1pT:U=1pRJU>1pS6U?1pT4U@1pT2UA1pU<UB1pU:UC1pU8UD1pUFUE1pS4UF1pTLUG1pT0UH1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 8%nat 0%nat).
Variable gw : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 9%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 10%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 11%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 12%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 13%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 14%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 15%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 16%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 17%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 18%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 19%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 20%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 21%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 22%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 23%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 24%nat 0%nat).
Variable p0w : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 25%nat 0%nat).
Variable nw : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 26%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 27%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 28%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 29%nat 0%nat).
Variable P0 : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 30%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 31%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 32%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 33%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 34%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 35%nat 0%nat).
Variable stride : ltac:(sec_ty2 constr:(SEC_T_renframe_tail_walk) 36%nat 0%nat).
Lemma renframe_tail_walk : ltac:(sec_stmt2 constr:(SEC_T_renframe_tail_walk) 37%nat 0%nat).
Proof.
intros HP0 HN HE MI WR ETOP BP P0P PNE EP PB P16 B0 N0 HK S0.
pose proof (bv_unsigned_in_range _ p0w) as PWR. change (bv_modulus 64) with (2^64) in PWR.
set (r := E - P - n).
assert (K31 : Z.land k 31 = k) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
step.
step. rewrite (unsigned_lit P), (wz_unsigned B), (swrap32_small (P - B)) by lia.
step. rewrite HN.
step. rewrite HP0. replace (P0 + stride + -4) with E by lia.
step. step. rewrite (unsigned_lit (P - B + -16)), Z.shiftr_div_pow2 by lia.
change (2 ^ 4) with 16. replace (P - B + -16) with (P - B - 16) by lia.
step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.
sok 0 1%nat (P + -3).
step. rewrite (le1_wz k) by lia. sdk.
lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 k] |- _ =>
pose proof (bytes_at_write_same rsegs mp a [b8 k] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
replace a with (P - 3) in BK by lia end.
sok 1 2%nat (P + -2).
step. change (le2 (Z_to_bv 64 ((P - B - 16) / 16))) with (le2 (wz ((P - B - 16) / 16))). sdk.
step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
-
step. step.
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia. step. step. rewrite ?(unsigned_lit 0), ?(unsigned_lit k) by lia.
rewrite Z.lor_0_l.
sok 0 1%nat (P + -3).
step. change (le1 (Z_to_bv 64 k)) with (le1 (wz k)). rewrite (le1_wz k) by lia. sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
rewrite K31. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
-
step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.
step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
step. replace (E + (0 - r)) with (E - r + 0) by lia.
step.
sok (n + 3) 1%nat (E - r + 0).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
+
step.
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia.
step. rewrite (unsigned_lit r), Z.shiftl_mul_pow2 by lia.
step. rewrite (unsigned_lit (r * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 r k) by lia.
sok 0 1%nat (P + -3).
step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
+
sok (E - P - 2) 1%nat (P0 + stride + -9).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
sok (E - P - 1) 4%nat (P0 + stride + -8).
step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
step.
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia.
step. step. rewrite ?(unsigned_lit 5), (unsigned_lit k) by lia. change (5 ≪ 5) with (5 * 2 ^ 5). rewrite (lor_shl5 5 k) by lia.
sok 0 1%nat (P + -3).
step. rewrite (le1_wz (Z.land k 31 + Z.shiftl 5 5)) by (rewrite K31; change (Z.shiftl 5 5) with 160; lia). sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End SE.
Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
if off =? 0 then m
else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
(wa (P0 + 16 * off - 4)) [b8 0].
Lemma renframe_off_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "W>'R?yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8'6&RAr@%22@1r9%53621r7%73841&E&Hr<%3221&Gr=rQ3%>2L1(2'A(@rA%211%31C&>r;%211%711(?r6%611%311r5%911%611r4%<11%A11(3%11D%F3E31%G3F71%H3G;1%I3H@1%J3IE1%K3JG1%Q04Q3OM1&Fr>&Q8+4%22Q41%54Q941K&Q0&M%127Q;&Q6+2+R0%3221%7251'7r?%921Q@rQ6%QN2R<1%=231+Q8%>231%D27C%A221%:251+@%C2;1%E21R6z%G21R8%H22?%H2R:L%J21QJ&Q2rB%Q121Q0%Q221QN+O%M2L1%6231rE&Q4%12ARE%Q4231rD%Q;221%=218rF%Q:2G1'5rC%Q=2G1+Q0%D231%5231%>2N;rG%QG21QF%QH21;%QE241&B&JrQJrQIrQHrQGrQCrQBrQ?rQ>rQ=rQ<rQ;rQ:rQ9rQ8rQ7&R>rJ%Q62QFQ7%R9221%42T;1rMrL&IrK%2318Q>rH%RA2:1%RG21RF&NrI%RJ2<1%RK21R4%421R5%Q2IQ1Q0ONMLKJIHGFEDCR>>=<9?6Q7Q@1&D&CrQFrQErQDrQA%SM1QGrQ0rQ@%L2U3BrQ1%T21@%O2U6R4rQ5rQ4rQ2%?OQBQAQ@Q?>=<Q>Q=;:987654Q<Q;Q:Q9Q8Q7Q6Q5Q4RO32T?1+c`o@%Q52U<1(1%11U=&L%11TJ%G77Q55Q43Q21%QL3TLI1p0QN1p0R71p0R51p0R<1p0R?1p0RG1p0RO1p0S21p0S41p0S71p0S;1p0SG1p0T01p0T71p0U91p0U>1p0UA1pS<UH1pS2UI1pRLUJ1pSDUK1pS8UL1pS>UM1pU6UN1p2UO1pLV01pS:V21pS0V81pFV;1pS@V?1pSLV@1pSBVA1pSJVB1pUDVC1pUBVD1pU@VE1pU>VF1pT8VG1pT6VH1pTHVI1pTFVJ1pTDVK1pTBVL1pT@VM1pT>VN1pT<VO1pT:W01pRHW11pS6W21pT4W31pT2W41pU<W51pU:W61pU8W71pUFW81pS4W91pTLW:1pT0W;1").
Proof.
intros until mword. intros HP HN MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OFF0 OFFS.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
step. step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit off) in KO by lia.
-
subst off. unfold renframe_off_mem. rewrite Z.eqb_refl.
replace (P0 + 16 * 0) with P0 by lia.
replace p0w with (Z_to_bv 64 P0) by (rewrite <- HP; apply Z_to_bv_bv_unsigned).
eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
+ apply unsigned_lit. lia.
+ eapply wr_at_sub; [exact WR | lia | lia].
-
step.
step. rewrite (unsigned_lit off), Z.shiftl_mul_pow2, (swrap32_small (off * 2 ^ 4)) by lia.
step. rewrite HP.
pose proof (wr_at_store_ok rsegs m _ _ 1 1 WR ltac:(lia) ltac:(lia)) as SO1.
replace (P0 - 4 + 1) with (bv_unsigned p0w + -3) in SO1 by lia.
change (wa (bv_unsigned p0w + -3)) with (Z_to_bv 64 (bv_unsigned p0w + -3)) in SO1.
step. rewrite le1_neg32. sdk.
lazymatch goal with W : wr_at rsegs ?mc (P0 - 4) _ |- _ =>
pose proof (wr_at_store_ok rsegs mc _ _ 2 2 W ltac:(lia) ltac:(lia)) as SO2;
replace (P0 - 4 + 2) with (bv_unsigned p0w + -2) in SO2 by lia;
change (wa (bv_unsigned p0w + -2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in SO2 end.
step. change (le2 (Z_to_bv 64 off)) with (le2 (wz off)). sdk.
lazymatch goal with W : wr_at rsegs ?mc (P0 - 4) _ |- _ =>
pose proof (wr_at_store_ok rsegs mc _ _ (16 * off) 1 W ltac:(lia) ltac:(lia)) as SO3;
replace (P0 - 4 + 16 * off) with (P0 + off * 2 ^ 4 + -4) in SO3 by lia;
change (wa (P0 + off * 2 ^ 4 + -4)) with (Z_to_bv 64 (P0 + off * 2 ^ 4 + -4)) in SO3 end.
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
step.
replace (P0 + off * 2 ^ 4) with (P0 + 16 * off) by lia.
unfold renframe_off_mem. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
replace (write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off))) (wa (P0 + 16 * off - 4)) [b8 0])
with mc end.
2:{ repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)). }
eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
eapply wr_at_sub; [exact WR | lia | lia].
Qed.
Lemma swrap32_add_2p64 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "I'8'5&Q0&Q5&Q6+2+O%3221%511r1%8221&Q2%1235%<231'6&R@yQ0&M+`PPPPPPPPPPP0r2%3221%6251%83F13p0:1pRNH1").
Proof. intros d.
intros Hd. unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
replace (18446744073709551616 + d + 2147483648) with ((d + 2147483648) + 4294967296 * 4294967296) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_renframe_fold_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "X3'R?yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8&N&Q8r8+4%3221r7%5221+@%8221&Kr6r1%3221'6&RArC%22M1r<%53C21r:%73E41r5%E25Cr;%G221%<3J41&E&Hr@%3221&GrArQ7%C2Q>1(2'A(@rE%211rD%411&>r?%211%811(?%51K%211r9%811%511%:1QA%@11(3%11C%E3D31%F3E61%G3F:1%H3G>1%I3HC1%J3IF1%O4Q2NL1&FrB%QO2Q1QM%34Q621G&Q0&M%125Q8&Q6+2+R0%3221%7251'7%82QLQ<rQ:%QO2RJ1%<231+Q8%=231%R@2R2R>%@221%9251%A2R5R=%C21Q>z%E21Q@%F22R9%F2QBRF%H21QE&Q2rF%RL21RJ%RM21QI+O%K2J1%6231%Q02<RG&Q4r2%22RN1rH%Q4221%Q521S5rI%Q8221rLr3%:2S61%Q;231rK%S?221%F21Ap081p0A1pSFSE1rJ%QD2S?1'5rG%QG2Q31+Q0%Q0231%5231+X0%Q3261%8261&B&JrQKrQJrQIrQHrQFrQErQBrQArQ@rQ?rQ>rQ=rQ<rQ;rQ9&R>rM%Q@2T<RD%RA221%42U21rQ0rO&IrN%2318RK%RH29Q<%TK21TI%TL29QB%TM21TG%TO21TH%OINMLKJIHGFEDCBARD@;:96<4Q;QG1&D&C%B2U@SL%C2UATErQGrQD%SN1QNrQ3rQC%I2UGQKrQ4%T31R1%L2UJR7rQ8rQ6rQ5%?OQ?Q>Q=Q<>=<Q;Q:;:987654Q9Q8Q7Q6Q5Q4Q3Q2S5Q13TA21+c`mD%Q22V01(1%11V1&L%11TL%G77Q25Q13O1%QI3TNI1p0QK1p0QO1p0R61p0R91p0RM1p0S51p0S81p0S:1p0S=1p0S@1p0SK1p0T41p0T91p0U:1p0U?1p0UE1p0UH1tSDV<UO1tTJV=V41pRDV>1pS<V?1pS2V@1pRLVA1pSHVB1pS8VC1pS>VD1pU6VE1p2VF1pLVG1pS:VI1pS0VO1pFW21pS@W61pSLW71pSBW81pSJW91pUDW:1pUBW;1pU@W<1pU>W=1pT8W>1pT6W?1pTHW@1pTFWA1pTDWB1pTBWC1pT@WD1pT>WE1pT<WF1pT:WG1pRHWH1pS6WI1pT4WJ1pT2WK1pU<WL1pUFWM1pS4WN1pTLWO1pT0X01")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 3%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 4%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 5%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 6%nat 0%nat).
Variable gw : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 7%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 8%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 9%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 10%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 11%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 12%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 13%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 14%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 15%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 22%nat 0%nat).
Variable p0w : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 23%nat 0%nat).
Variable nw : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 24%nat 0%nat).
Variable prev : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 25%nat 0%nat).
Variable next : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 26%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 27%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 28%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 29%nat 0%nat).
Variable P0 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 30%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 31%nat 0%nat).
Variable stride : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 32%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 33%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 34%nat 0%nat).
Variable off0 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 35%nat 0%nat).
Variable avail : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 36%nat 0%nat).
Variable freed : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 37%nat 0%nat).
Variable mword : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 38%nat 0%nat).
Variable T0 : ltac:(sec_ty2 constr:(SEC_T_renframe_fold_walk) 39%nat 0%nat).
Lemma renframe_fold_walk : ltac:(sec_stmt2 constr:(SEC_T_renframe_fold_walk) 40%nat 0%nat).
Proof.
intros slack off HP HN HT0 MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OF.
assert (SL : 0 <= slack <= stride) by (subst slack; Z.div_mod_to_equations; lia).
pose proof (fold_off_le_slack off0 slack OF ltac:(lia)) as FO. fold off in FO.
assert (S16 : 16 * slack <= stride - 4 - n) by (subst slack; Z.div_mod_to_equations; lia).
step. if_cases K1; zify_cond K1; rewrite ?(unsigned_lit slack), ?(unsigned_lit off0) in K1 by lia.
-
assert (EO : off = off0) by (subst off; rewrite fold_off_eq; replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
-
step. rewrite (unsigned_lit T0), HT0 by lia.
replace ((stride - 4 - n) ≫ 5) with (slack ≫ 1) by (subst slack; rewrite <- (Z.shiftr_div_pow2 _ 4), Z.shiftr_shiftr by lia; reflexivity).
pose proof (Z_shiftr_range slack 1 ltac:(lia) ltac:(lia)) as R1.
step. rewrite (unsigned_lit (slack ≫ 1)), (unsigned_lit slack) by lia.
set (m1 := Z.lor slack (slack ≫ 1)).
pose proof (Z_lor_range slack (slack ≫ 1) ltac:(lia) R1) as RM1. fold m1 in RM1.
step. rewrite (unsigned_lit m1) by lia. pose proof (Z_shiftr_range m1 2 RM1 ltac:(lia)) as R2.
step. rewrite (unsigned_lit m1), (unsigned_lit (m1 ≫ 2)) by lia. rewrite (Z.lor_comm (m1 ≫ 2) m1).
set (m2 := Z.lor m1 (m1 ≫ 2)). pose proof (Z_lor_range m1 (m1 ≫ 2) RM1 R2) as RM2. fold m2 in RM2.
step. rewrite (unsigned_lit m2) by lia. pose proof (Z_shiftr_range m2 4 RM2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit m2), (unsigned_lit (m2 ≫ 4)) by lia. rewrite (Z.lor_comm (m2 ≫ 4) m2).
set (m3 := Z.lor m2 (m2 ≫ 4)). pose proof (Z_lor_range m2 (m2 ≫ 4) RM2 R3) as RM3. fold m3 in RM3.
assert (SM : m3 = smear slack) by reflexivity.
step. rewrite (unsigned_lit off0), (unsigned_lit m3) by lia.
set (x := Z.land off0 m3).
assert (RX : 0 <= x <= off0) by (subst x; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
step. rewrite v_sltu_b2z, (unsigned_lit slack), (unsigned_lit x) by lia.
step. rewrite (unsigned_lit slack) by lia.
destruct (Z.ltb_spec slack x) as [LT|GE]; cbn [Z.b2z].
+ pose proof (fold_assert_ok off0 slack OF ltac:(lia) ltac:(rewrite <- SM; exact LT)) as FA. rewrite <- SM in FA. fold x in FA.
step. step. rewrite (zb_lxor_ones slack) by lia. rewrite (unsigned_lit (18446744073709551615 - slack)) by lia.
change 18446744073709551615 with (Z.ones 64) at 1. rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by lia.
rewrite (Z.mod_small (18446744073709551615 - slack)) by lia.
step. rewrite (unsigned_lit (18446744073709551615 - slack)), (unsigned_lit x) by lia.
replace (18446744073709551615 - slack + x) with (18446744073709551616 + (x - (slack + 1))) by lia.
rewrite swrap32_add_2p64 by lia.
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit (x - (slack + 1))) in K2 by lia; [|exfalso; lia].
assert (EO : off = x - (slack + 1)).
{ subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
rewrite <- SM. fold x. replace (slack <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
+ step. step. change (Z.land 0 _) with 0.
step. rewrite (unsigned_lit x), Z.add_0_l, (swrap32_small x) by lia.
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit x) in K2 by lia; [|exfalso; lia].
assert (EO : off = x).
{ subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
rewrite <- SM. fold x. replace (slack <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
Qed.
End SE.
Lemma land_m4096 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_enframe "J'8'5&Q0zr1%3221&Q2&Q6+2+R0%3221%5271%;271'6&Or2+_ooooooooolP0%3221&Q8&Q3+TP0%2261%4271%:3G61p0<1pRFI1").
Proof. intros a.
intros Ha.
replace (a - a mod 4096) with (Z.shiftl (Z.shiftr a 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.lt_ge_cases i 12).
- rewrite Z.shiftl_spec_low by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb]. rewrite !andb_false_r. reflexivity.
- rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.lt_ge_cases i 64).
+ replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. rewrite andb_true_r. reflexivity.
+ replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
(B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let P0 := B + 16 + stride * k in
let slack := (stride - 4 - n) / 16 in
let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
let off := fold_off off0 slack in
bv_unsigned nw = n ->
stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
wr_at rsegs m (P0 - 4) stride ->
ov_read_bytes rsegs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
ov_read_bytes rsegs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
ov_read_bytes rsegs m (wa (P0 - 4)) 1 = Some [b8 0] ->
P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
(forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c338) fc None m (seg_rom rsegs)).
Proof.
intros until v16. intros mword P0 slack off0 off HN HS SC48 MI MM WR R3 R2 R4 PTOP SEPG B0 N0 NS SS PBS HK CT LI FB SC ML VB V16.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (MW5 : Z.land (Z.shiftr mword 5) 126 = 2 * sc) by (subst mword; apply mword_sc; lia).
assert (MW12 : Z.land mword 18446744073709547520 = 4096 * maplen).
{ rewrite land_m4096 by lia. subst mword. Z.div_mod_to_equations. lia. }
assert (MZ : Z.shiftr mword 12 = maplen).
{ rewrite Z.shiftr_div_pow2 by lia. subst mword. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
assert (L255 : Z.land (sxv ctr) 255 = Z.land ctr 255).
{ change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
rewrite <- (mod_mod_pow2 (sxv ctr) 8 32), sxv_mod32, (mod_mod_pow2 ctr 8 32) by lia. reflexivity. }
assert (OF0 : 0 <= off0 < 256).
{ subst off0. destruct (vb3 =? 0); (split; [apply Z.land_nonneg; lia|]);
change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia. }
assert (SK0 : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
assert (ST16 : 16 <= stride /\ B + 16 <= P0).
{ split; [| subst P0; lia]. rewrite HS. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
- apply andb_prop in E. destruct E as [_ E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. lia.
- pose proof (size_class_range sc ltac:(specialize (SC48 eq_refl); lia)). lia. }
destruct ST16 as [ST16 BP0].
step. step. rewrite (wz_unsigned mword), MZ by lia.
assert (JOIN : forall a5',
evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) (Z_to_bv 64 stride) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c378) fc None m (seg_rom rsegs))).
{ intros a5'.
pose proof (sxv_range ctr) as RC.
assert (Eoff0 : off0 = (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255)) by reflexivity.
assert (EP0 : P0 = B + 16 + stride * k) by reflexivity.
assert (Eoff : off = fold_off off0 slack) by reflexivity.
assert (Esl : slack = (stride - 4 - n) / 16) by reflexivity.
clearbody off slack off0 P0 mword. clear MW1 MW5 MW12 MZ HS SC48.
step. step. step. rewrite ?(wz_unsigned k), ?(wz_unsigned B), ?(unsigned_lit stride) by lia.
replace (wa (P0 - 3)) with (Z_to_bv 64 (B + stride * k + 13)) in R3 by (unfold wa; f_equal; lia).
lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
step. rewrite ?zxb_b8 by lia. clear R3.
step. rewrite HN. step. step. replace (B + stride * k + 16) with P0 by lia.
set (p0w := Z_to_bv 64 P0). assert (HP0 : bv_unsigned p0w = P0) by (subst p0w; apply unsigned_lit; lia). clearbody p0w.
replace (wa (P0 - 2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in R2 by (unfold wa; f_equal; lia).
replace (wa (P0 - 4)) with (Z_to_bv 64 (bv_unsigned p0w + -4)) in R4 by (unfold wa; f_equal; lia).
step. if_cases KB; zify_cond KB; rewrite ?(wz_unsigned vb3), ?(unsigned_lit vb3) in KB by lia.
-
clear R2. unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
step. rewrite ?(wz_unsigned (sxv ctr)), ?L255 by lia.
step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
replace (Z.land ctr 255) with off0 by (rewrite Eoff0, KB; reflexivity).
rewrite Eoff, Esl. eapply renframe_fold_walk.
all: lazymatch goal with
| |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WR
| |- _ => idtac end.
all: first [lia | exact PBS].
-
unfold frozen in R2.
step. rewrite ?zx16_wz by lia. clear R2. step. rewrite (wz_unsigned v16) by lia.
unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
step. rewrite ?(unsigned_lit (v16 + 1)) by lia.
step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
replace (Z.land (v16 + 1) 255) with off0 by (rewrite Eoff0; replace (vb3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
rewrite Eoff, Esl. eapply renframe_fold_walk.
all: lazymatch goal with
| |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WR
| |- _ => idtac end.
all: first [lia | exact PBS]. }
assert (JOIN2 : forall a5', stride = 16 * size_class sc -> sc < 48 ->
evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) (wz mword) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c35c) fc None m (seg_rom rsegs))).
{ intros a5' HS16 SC'.
lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
lazymatch type of R3 with ?T => change T with (frozen T) in R3 end.
lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
pose proof (Z_shiftr_range mword 5 MWR ltac:(lia)) as R5.
pose proof (size_class_range sc ltac:(lia)) as SZ.
step. rewrite (wz_unsigned mword) by lia. step. step. rewrite (unsigned_lit (mword ≫ 5)), MW5 by lia.
step. step. rewrite ?(unsigned_lit (2 * sc)) by lia.
pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS. unfold RSIZE_CLASSES in RS.
step. rewrite ?zx16_wz by lia.
step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia.
replace (size_class sc * 2 ^ 4) with stride by lia.
apply JOIN. }
step. if_cases KM; zify_cond KM; rewrite ?(unsigned_lit maplen) in KM by lia.
-
apply JOIN2; [| apply SC48]; rewrite ?HS; replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); rewrite ?andb_false_r; cbn [negb andb]; try reflexivity.
all: destruct (last_idx =? 0); reflexivity.
-
step. rewrite (wz_unsigned mword), MW1 by lia.
step. if_cases KL; zify_cond KL; rewrite ?(unsigned_lit last_idx) in KL by lia.
+
apply JOIN2; [| apply SC48]; rewrite ?HS; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
+
step. step. rewrite (wz_unsigned mword) by lia. rewrite MW12.
step. replace (4096 * maplen + -16) with stride.
2:{ rewrite HS. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
step. apply JOIN.
Qed.
End CEIL_WRAP_2.
