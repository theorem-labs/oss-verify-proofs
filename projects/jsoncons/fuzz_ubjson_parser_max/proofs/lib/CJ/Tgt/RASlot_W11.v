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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W11.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RASlot_W2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W11 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W11.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W11.CEIL_WRAP_1.HALVE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "0Fr"; "4machine_state"]; ["4ov_read_bytes"; "5bvmap"; "6b8"; "6wz"; "7CB"; "7cell"; "8evt"; "9mkR"; ":MS"; ";mem_inv"; ";wa"; "<ro_cells"; "=halve_big"; "=halve_even"; "=med_cnt"; "=size_class"]; ["=small_cnt"; ">rsegs"; "@rcnt_regs"; "?rcnt_regs"; "?rmed_cnt_bytes"; "?rsmall_cnt_bytes"; "ARMED_CNT"; "ARMLOCK"; "ARSIZE_CLASSES"; "ARSMALL_CNT"; "ARSSP_GUARD"; "Bseg_rom"; "Cadd"; "Cdiv"; "Ceqb"; "Ceven"]; ["Cland"; "Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "0a0"; "0a1"; "0a2"; "0a2'"; "0a3"; "0a3'"; "0a4"; "0a4'"; "0a5"; "0a6"]; ["0a7"; "0cnt"; "0cnt0"; "0fc"; "0gmw"; "0gp"; "0i"; "0m"; "0ms'"; "0ra"; "0rqw"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"]; ["0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s9"; "0sc"; "0size"; "0sp"; "DZ_to_bv"; "Dbv"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"]; ["0t5"; "0t6"; "0tp"; "0u"; "0usage"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rsmall_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RMED_CNT 4 with Some bs => bs | None => [] end).
Lemma rsmall_cnt_ro : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "K'RJyR0%211'7y8%511%311p051&I&Q1r1%3221&Kr2&Q9(3'E(DuK&Q5%3221(6%116%83731%<4?;:1p0>1pT@C1").
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
Lemma rmed_cnt_ro : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "K'RJyR0%211'7y8%511%311p051&I&Q1r1%3221&Kr2&Q6(3'E(Du4&Q4%3221(6%116%83731%<4?;:1p0>1pT@C1").
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.
Section SE.
Local Abbreviation SEC_T_rsmall_cnt_read := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "QK'RJyR0%211'7y8%511%311p051'<&I&Q1r3%3221'9&QAz%2215&QB+9%2281%7241+3%52;1%:271':'4%11E%H11&@r6&J&Q<&Q9&QCr5%22>1%5241r4%7221%911u1%=4O<21(1(3&B&Q0%12<9%311(6%11Q<%73Q=31%92I1%L3I;1p0N1p0Q21p0Q;1pT>Q@1pU>QA1pT@QC1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rsmall_cnt_read) 0%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rsmall_cnt_read) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_rsmall_cnt_read) 2%nat 0%nat).
Lemma rsmall_cnt_read : ltac:(sec_stmt2 constr:(SEC_T_rsmall_cnt_read) 3%nat 0%nat).
Proof.
intros MI Hsc Hi.
destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
rewrite (bytes_at_read rsegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
unfold small_cnt. rewrite !Nat2Z.id.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.
End SE.
Lemma rmed_cnt_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "QB'RJyR0%211'7y8%511%311p051'<&I&Q1r2%3221'9&QAz%2215&QB+4%2281%7241':'4%11B%E11&@r4&J&Q<&Q6r3%3221%511u1%94H821(1(3&B&N%119%311(6%11Q5%73Q631%92E1%H3E;1p0J1p0Q31pT>Q81pT@Q:1").
Proof.
intros m i MI Hi.
destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read rsegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.
Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.
Lemma rhalve_big_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "T9'5'<'RJyR0%211&Ay5%2213yQ0%711'7y8%:11%311p0:1'9&QAzrO%3221&QB&QE+2&QDrQ0%211%5241%7291%=291+Q0%>261&I&Q1r3%3221&F'?';':&H&Q2rQ4rQ3rQ2rQ1rNrMrLr2r1rJrIrHrGrF&C&LrQ6rQ5vRG%43321%611rDrCrBrAr@r?r>r=r<r;r:%Q1LQ0ONMQAQGLKJIHGFEDC<;:987654321r9&RI+cc\<%22R:1r8(0%11R<r7&Q;%11QC%Q=7;:76431%Q?3QAQD1qSHRB1%QB2RC1qSDRD1%QD2RE1qTBQF1rK%Q51QArE%QFLQBR6R<QAQ@Q?3Q<Q;2Q:Q9Q81Q0ONMLKJIHGFD@=r6+cc[H%F2RN1r5r4%QM76532D1A%R23R5;1p0R41p0R91p0R<1pT@RK1pT8S11pNS41pV4S81pV2S91pV0S:1pUNS;1pTNS<1pTLS=1pU<S>1pU:S?1pU8S@1pU6SA1pU4SB1pU2SC1pU0SD1pT2SE1pT0SF1pSNSG1pSJSH1pSFSI1pTJSJ1pTHSK1pULSL1pUJSM1pUHSN1pV6SO1pT<T01pUBT11pTDT21pT4T61pLT81").
Proof.
induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
- cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
- cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
step. rewrite (unsigned_lit (size * cnt)) by lia.
step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
+
rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
rewrite (F_malloc_entry.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
+ rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
Lemma land2_half_parity : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "D'<&QAzr1%3221':'2&Q?&Q=r2+2%3221%511&Q>&Q@%1265%321>%<3;51p0>1pT4C1").
Proof. intros cnt.
intros H.
assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.eq_dec n 1) as [->|NE].
- change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
- replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.
Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.
Lemma rhalve_even_loop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "T@'5'<'RJyR0%211&Ay5%2213yQ0%711'7y8%:11%311p0:1'9&QA+2rO%3221&QB&QE&QDrQ0%211%4281%6281%<281+Q0%=261':'2&Q?rQ1%211(8%63521&I&Q1r4%3221&F'?';r3&H&Q3vS4vRGrQ5rQ4rQ3rQ2rNrM&C&MrQ7rQ6%3321<%511r2r1rJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;%Q1NQ0ONMLKQ>QHQMJICBA@?>=<;:987654321r:&RI+cc[H%22R@1r9(0%11RBr8&Q;%11QC%Q=7;:76431%QM3QAQ?1qSLRH1%QB2RI1qSHRJ1%QD2RK1qTBQF1rLrK%Q<1Q@%QFNQEQDQ@R3R=RBQ?Q>32Q5Q41Q3Q2Q1Q0ONMLKJIHGFD@=r7+ccZ@%F2S41r6r5%QM76532D1A%R23R5;1p0R41p0R91p0RA1p0RD1pT@S21pT8S81pNS;1pV4S?1pV2S@1pV0SA1pUNSB1pTNSC1pTLSD1pU<SE1pU:SF1pU8SG1pU6SH1pU4SI1pU2SJ1pU0SK1pT2SL1pT0SM1pSNSN1pSJSO1pSBT01pTJT11pTHT21pULT31pUJT41pUHT51pV6T61pT<T71pUBT81pTDT91pT4T=1pLT?1").
Proof.
induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
- change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
- cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
+
replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
step. apply evt_done. do 2 eexists. reflexivity.
+ replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
step. rewrite (wz_unsigned cnt) by lia. rewrite (F_malloc_entry.srliw_small cnt 1) by lia.
step. rewrite (wz_unsigned cnt) by lia. step.
assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
{ rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
*
step.
assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
apply evt_done. do 2 eexists. reflexivity.
Qed.
Lemma rhalve_even_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "T:'5'<'RJyR0%211&Ay5%2213yQ0%711'7y8%:11%311p0:1'9&QA+1rO%3221&QB&QE+2&QDrQ0%211%5241%7291%=291+Q0%>261&I&Q1r3%3221&F'?';':&H&Q3vS4vRGrQ4rQ3rQ2rQ1rNrMrL&C&MrQ6rQ5%3321=%511r2r1rIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:%Q2NQ1Q0ONMLQBQHKJICBA@?>=<;:987654321r9&RI+cc[H%22R;1r8(0%11R=r7&Q;%11QD%Q>7;:76431%Q@3QBQE1qSLRC1%QC2RD1qSHRE1%QE2RF1qTBQG1rKrJ%Q<1QA%QGNQFQEQAR7R=Q@Q?Q>32Q5Q41Q3Q2Q1Q0ONMLKJIHGFD@=r6+ccZ8%F2RO1r5r4%QN76532D1A%R33R6;1p0R51p0R:1p0R=1pT@RL1pT8S21pNS51pV4S91pV2S:1pV0S;1pUNS<1pTNS=1pTLS>1pU<S?1pU:S@1pU8SA1pU6SB1pU4SC1pU2SD1pU0SE1pT2SF1pT0SG1pSNSH1pSJSI1pSBSJ1pTJSK1pTHSL1pULSM1pUJSN1pUHSO1pV6T01pT<T11pUBT21pTDT31pT4T71pLT91").
Proof.
intros until m; intros CR C32 MI; unfold rcnt_regs.
step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
-
assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
step. step. apply evt_done. do 2 eexists. reflexivity.
- assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.
Lemma rcnt0_range : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "8'9&QAzvR2%3221+Q0%5231%7231").
Proof.
unfold cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
- pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rcount_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W11 "SL'RJyR0%211&Ay5%2213yQ0%711&I&Q1vR7%3221&F'?';':r4&H&Q3vS3vRGr:rOrNrMrLrKrJ&RIvRF%22M1r9r3r2r1rDrCrBr8&CvR2%211&Q:%?2Q:1rA&Q7%B2Q=1&Q<&QC+8%221E%4261%H2QC1&Q8%J2QE1r@r?r>r=r<r;%Q;NQ:Q9Q8Q7Q6Q5Q4Q3Q2ONMLKJIHGDBA?97654321r7+cc\<%Q42QO1r6(0%11R1&Q;%11QL%QE798653QL1%QH3QJQG1qSLR61%QK2R71qSHR81%QM2R91qSDR:1%QO2R;1qTBR11&GrIrHrGrFr5rE+2%Q72QJ1%QL2RG1&O%11QM%QD11%=OKR2R1<;:9QN87QIQHQGQ@Q5Q4Q3R<4QAQ2Q>Q81Q6Q1Q0R7QMQFN+ccW<%R22RM1%R>73QO1QNLREJ%RD3RGB1p0RF1pT8RK1pNRN1pTFS21pT:S31pV<S41pV4S51pV2S61pV0S71pUNS81pTNS91pTLS:1pU6S;1pT2S<1pT0S=1pSNS>1pSJS?1pSFS@1pSBSA1pS@SB1pS>SC1pULSD1pUJSE1pUHSF1pV6SG1pT<SH1pUBSI1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 5%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 6%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 7%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 13%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 14%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 15%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 16%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 17%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 18%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 19%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 20%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 21%nat 0%nat).
Variable gmw : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 22%nat 0%nat).
Variable rqw : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 23%nat 0%nat).
Variable Fr : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 24%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rcount_walk) 25%nat 0%nat).
Lemma rcount_walk : ltac:(sec_stmt2 constr:(SEC_T_rcount_walk) 26%nat 0%nat).
Proof.
intros MI.
pose proof (size_class_range sc SC) as SZR.
pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
pose proof rcnt0_range as C0R.
unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.
pose proof (rmrep_usage_read st m sc (wa (954560 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
step. clear RDU.
step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
-
apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
step. clear RDM. rewrite zxb_b8 by lia.
eapply evt_cut.
{ eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
eapply evt_mono.
{ eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
-
assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
replace (wa (110144 + 3 * sc + 0)) with (Z_to_bv 64 (110144 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
step. clear RD0. rewrite zxb_b8 by lia.
step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
{ replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
replace (wa (110144 + 3 * sc + 1)) with (Z_to_bv 64 (110144 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
step. clear RD1. rewrite zxb_b8 by lia.
step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
{ replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
replace (wa (110144 + 3 * sc + 2)) with (Z_to_bv 64 (110144 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
step. clear RD2. rewrite zxb_b8 by lia. step.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SE.
End COUNT.
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.
Lemma rcnt2_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (if big then 0x9cdb4 else 0x9cdf8)) fc None m (seg_rom rsegs))
(MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9cd8c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI. unfold rcnt_regs.
assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
-
assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
-
step. rewrite ?unsigned_lit by lia. step. step.
assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
{ unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
{ rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
rewrite EV. clear EV.
assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.
End CEIL_WRAP_1.
