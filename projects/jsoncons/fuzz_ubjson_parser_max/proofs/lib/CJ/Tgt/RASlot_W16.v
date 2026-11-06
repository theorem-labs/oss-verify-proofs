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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W11 ASlot_W15 ASlot_W16.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RASlot_W2 RASlot_W4 RASlot_W11.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W16 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W16.CEIL_WRAP_1.MMC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "0RUNp"; "6mm_cnt_red"; "6mm_final"; "6mm_usage1"; "7wz"; "8mem"; "9evt"]; [":mkR"; ";MS"; "<mstate"; "<usage"; "=rsegs"; ">rmmc_post"; "?RMLOCK"; "?rmrep"; "@seg_rom"; "Aadd"; "Ab2z"; "Ale"; "Alt"; "Amul"; "Apow"; "0a1"]; ["0a2"; "0a3"; "0a4"; "0a5"; "0a5'"; "0a6"; "0a6'"; "0a7"; "0a7'"; "0c1"; "0cnt"; "0fc"; "0gp"; "0i"; "0m"; "0ms'"]; ["0nos"; "0ra"; "0req"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s3'"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sc"]; ["0size"; "0sp"; "0st"; "BZ_to_bv"; "Bbv"; "0t0"; "0t0'"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0u0"; "0u1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.
Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(res : Z * Z) : machine_state -> Prop :=
fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d178) fc None m (seg_rom rsegs).
Section SE.
Local Abbreviation SEC_T_rj2c_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W16 "SJ'R4yR0%211&8y5%2213yQ0%711&>'5'2&K+1r2%3221+Q0%5231%7231z%8216&L&N+2+QM%3221%52<1%@271&?&D&ErNrMrLrKrIrH&R3vQO%22Q51rGvQB%52Q81rAr@r?r>&=vR0%211r=r<r;r:r9r8r7r6r5&;r3r4vQ@%45?F321%Q2HQ1Q0ONMLIHFEDCB?>=<;:98761&A&@rJ%E18+TP0%G11&I+@%22I1%K11&J%11>%Q82R;1rFrErDrCrB%Q41F%BOQEQDQCQBAQAQ@Q=Q<@>:76543Q:2Q9Q8Q7Q6Q31Q2Q1Q0ONM+cdXL%QA2RD1(0%11RE&H%11QM%J77Q35Q23Q11%R03QOL1p0R21p0R<1pU0RE1pRDRF1pRNRH1pRHRJ1p>RM1pTJS11pTHS21pTFS31pTDS41pS<S51pS:S61pSJS71pSHS81pSFS91pSDS:1pS@S;1pR@S<1pR<S=1pR8S>1pR6S?1pS8S@1pTBSA1pT@SB1pT<SC1pTLSD1pRJSE1pT4SF1pS4SG1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 7%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 8%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 9%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 10%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 11%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 12%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 13%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 14%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 15%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 22%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 24%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 25%nat 0%nat).
Variable c1 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 26%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_rj2c_walk) 27%nat 0%nat).
Lemma rj2c_walk : ltac:(sec_stmt2 constr:(SEC_T_rj2c_walk) 28%nat 0%nat).
Proof.
intros CR UR.
assert (SCR : 16 <= size * c1 < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR.
unfold rmmc_post.
step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
step. step. step. step. step. step.
rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
set (nd0 := round_up_pg (size * c1 + 16)).
pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
fold nd0 in RUR.
assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
{ unfold mm_final, UNIT. reflexivity. }
step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{
apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
do 9 eexists. reflexivity. }
replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.
step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
{
apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
do 9 eexists. reflexivity. }
replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).
step. step. step. step. step.
rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
replace (-20 + - req) with (- (req + 20)) by lia.
set (rq' := round_up_pg (req + 20)).
pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
{ unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
rewrite ES in EF. clear ES. unfold PGSZ in EF.
step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
-
replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+
apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
do 9 eexists. reflexivity.
+ replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.
step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
*
step. step. step.
apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
do 9 eexists. reflexivity.
* apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
do 9 eexists. reflexivity.
-
replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
step. step. step.
apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rred_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W16 "TJ'R4yR0%211&8y5%2213yQ0%711'1y8%:11%311p0:1'5'2&K+1r2%3221+Q0%5231%7231z%8216&L&N+2+QM%3221%52<1%@271&?&D'7'4'3r6&A&@rQ3rQ2rQ1rQ0rNrM&R3vQO%22Q>1rL&=r9%211+TP0%411&IvR0+@%3221%911&JvQ@%211%A2QM1&Mr:%22:1%A11r5r4r3vQB%J2R61r1rHrGrFrE%L1F&:%15Q1H?MC%O11rCrBrAr@r?r>%QAOQ@Q?Q>Q=R6Q<Q;Q8Q7Q4Q2MIEDCB@?>=<;:7654321r=+cdXL%Q=2RI1r<(0%11RKr;&H%11R0%QL7:976431%QO3R1QN1qSBS11%R22S21qT>S31%R42S41qRBS51%R62S61qR>S71%R82S81qR:S91%R:2S:1qS0R<1rKrJrI%R01Q<%QC2QKQ>%R211rD%R41QAr8%RAOR;R7987Q>Q=R8Q<6R2QMQI4Q;3Q6Q@2Q5Q4Q3Q2Q:Q1OLIQGR51r7+cdU8%R=2SI1%RF7431RGNQHK%RM3RL?1p0RO1p0S91pU0SB1pRFSC1pRNSE1pRHSK1p>SN1pTJT21pTHT31pTFT41pTDT51pS<T61pS:T71pSNT81pSJT91pSHT:1pSFT;1pSDT<1pR@T=1pR<T>1pR8T?1pS8T@1pTBTA1pT@TB1pT<TC1pTLTD1pRJTE1pT4TF1pS4TG1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 7%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 8%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 9%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 10%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 11%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 12%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 13%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 14%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 15%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 16%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 17%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 18%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 19%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 20%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 21%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 22%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 23%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 24%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 25%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_rred_walk) 26%nat 0%nat).
Lemma rred_walk : ltac:(sec_stmt2 constr:(SEC_T_rred_walk) 27%nat 0%nat).
Proof.
intros CR UR.
assert (SCR : 16 <= size * cnt < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR. pose proof (ASlot_W16.land3_range sc) as L3.
assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d11c) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d118) fc None m (seg_rom rsegs))).
{ intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }
step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
{ eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{ eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
rewrite Bool.andb_false_r. reflexivity. }
assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
assert (ER : mm_cnt_red sc size cnt u1 nos =
(if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt)).
{ unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold PGSZ in ER.
step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
-
replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
+
replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
step. step. step.
step. if_cases KC; zify_cond KC.
*
rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
assert (E0 : Z.land sc 3 = 0) by lia.
step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
*
assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
{ intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
clear KC. step. step.
step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
{
apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
do 5 eexists. reflexivity. }
rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).
step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
-- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
-- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+
rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
*
replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
*
step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
-
rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
+
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
+
step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
Qed.
End SE.
Lemma rusage1_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W16 "TD'R4yR0%211&8y5%2213yQ0%711'B'1y8%;11%311p0;1'5&Gv9r3r2%43321'2&Kz%2215&L&N+2+QL%3221%52;1%:271&Cr6r1%3221%>2=1%<228%A221pRLH1&?&D'7'4'3&A&@rQ5rQ4rQ3rQ2rQ1rQ0rO&R3vQO%22QF1rN&=&<r8%2316L%411rMrLrKrJrIrHrGrFrErDrC&I&F&M+8%221G%5241%J2R>1rBrAr@r?r>r=r<r;%Q;OQ:Q9Q8Q7Q6Q5Q4Q1Q0KJIHGQGFEDCBA@987654321r:+cdU8%Q62RJ1r9(0%11RLr7&H%11QI%QF7:976431%QH3QJRA1qR:S21%QK2S31qS0QM1r4%Q?11+O%QE2S91%QNOQKQJQIQHQGQCQ=QDQ<3Q;Q:Q9Q81Q7Q6Q5Q4Q3KJLIHGFEDB?+cdTD%QH2S<1r5%R374QD2@A1>%R93R8:1p0R;1p0RD1p0S01pTNS61pRNS81pT6S>1pRHS@1p>SC1pTJSG1pTHSH1pTFSI1pTDSJ1pS<SK1pS:SL1pSNSM1pSLSN1pSHSO1pSFT01pSDT11pS@T21pS>T31pR@T41pR<T51pR6T61pR4T71pR2T81pR0T91pS8T:1pTBT;1pT@T<1pT<T=1pTLT>1pRJT?1pT4T@1pS4TA1").
Proof.
intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.
step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
{ apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
eexists. reflexivity. }
apply Z.ltb_ge in K.
step. rewrite ?(unsigned_lit sc) by lia.
step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
{
assert (ODD : Z.even sc = false).
{ rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).
pose proof (rmrep_usage_read st m (sc + 1) (wa (954560 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
replace (wa (954560 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (954552 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
pose proof (USR (sc + 1)) as U1R.
step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.
Lemma rmmc_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W16 "TE'R4yR0%211&8y5%2213yQ0%711'B'1y8%;11%311p0;1'5&Gv9r4r3%43321'2&K+1%2215+Q0%4271%6231z%721:&L&N+2+QL%3221%52@1%?271&Cr8r1%3221%C2=1%<228%F221pRLM1&?&D&ErMrLrKrJrHrG&R3vQO%22QF1rFvQB%52QI1rCrB&F%92QM1&I&M+8%221<%4261%?2R31&=vR0%211r@r?r>r=r<r;r:r9r7&;&<r5%23Q?N1&:r6vQ@%35Q2B241%85CQ0512%Q<HQ;Q:Q9Q8Q7Q6Q3Q2Q0ONLFCBA@?>=<;:1&A&@rI%I1;+TP0%K11+@%Q32L1%N11&J%11>%QA2S51%Q72Q1A%Q311+O%QE2S91rErD%Q81GrA%COR0QOQNQMBQLQKQHQGA?<97543QE2QDQCQAQ;Q81Q7Q6Q5Q4Q3Q2+cdTD%QL2S@1(0%11SA&H%11R8%K77Q85Q73Q61%R;3R:M1p0R=1p0RF1p0S01p0S81pTNS>1pRFS?1pRNSA1pT6SG1pRHSI1p>SL1pTJT01pTHT11pTFT21pTDT31pS<T41pS:T51pSNT61pSFT71pSDT81pR@T91pR<T:1pS8T;1pTBT<1pT@T=1pT<T>1pTLT?1pRJT@1pT4TA1pS4TB1").
Proof.
intros until u0. intros MR CR UR USR.
assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
{ unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
cbv beta. intros ms' (a5' & ->).
eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
{ unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
do 9 eexists. reflexivity.
Qed.
End MMC.
End CEIL_WRAP_1.
