(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_F () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["1None"; "1Some"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1snd"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "0F"; "4machine_state"; "4ms_mem"]; ["5bvmap"; "0P"; "0RUNp"; "6pgal"; "7C4"; "7cell"; "8evt"; "9mkR"; "9stk"; "9wmono"; ":MS"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">aptr"; ">c_avail_meta_area_count"]; [">c_avail_meta_areas"; ">conc"; ">ctx"; ">mstate"; ">optr"; ">r_len"; ">region"; ">round_up_pg"; ">s_regions"; "?rsegs"; "@ram_fp"; "@ram_frame"; "@ram_ret_post"; "ARMLOCK"; "ARSSP_GUARD"; "Armprotect_entry"]; ["Armrep"; "Brpres_except"; "Cseg_rom"; "Dadd"; "Dle"; "Dlt"; "Dpow"; "Dsub"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"]; ["0e"; "0fc"; "0gp"; "0junk"; "0lo"; "0m"; "0m0"; "0ms'"; "0p"; "0r"; "0raw"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"]; ["0s1o"; "0s2"; "0s2o"; "0s3"; "0s3o"; "0s4"; "0s4o"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "Elookup"; "FZ_to_bv"]; ["Fbv"; "Fbv_unsigned"; "GN_countable"; "Hgmap"; "Hgmap_lookup"; "Ieq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ram_disp_fin : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_F "V0'S0yR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'Q3&N'Q6&Q@vBr3r4%43321&:'9'<&O&Q2%117%311z%73621%911'8&QDr5%911%;11%4281&QE&QF+2+R0%3221%5271%<271&Q4&Q0r6%F11%311(1%12Q4A%M3731%Q<1Q5&RN';'S3&S5&S2%34421Q;&S4%14643Q=&3%138Q7@&Q8r7%211%=6<QC8641%B2QDQ2%Q>3@21&C&7%13AQ@7%311r8%43DQC1%Q;2Q?1&QCr9%83HQG1+TP0%4221&Q7&Q5%11:%311%QE251&F&Q9'>r1&J&Gr@rQ;rQ:rQ9rQ8rQ7rQ6&RO%12S3E&Q1r<r;%3221%62S81%72S9R>rQ3rQ2rQ1rQ0rOrNrM&Q>%@2SB1&Q=%B2SD1rLrKrJrIrHrGrFrErDrCrBrA%Q7OQ6Q5Q4Q3Q2Q1Q0NIHGFEDCBA?=<;:987654321r?+caj8%Q22T41r>(0%11T6r=&QB%11QD%QB7:976431%SG3QEQD1qT@QF1rQ5rQ4%QFO>QCQBQAQ@Q?2Q=1Q6Q5Q4Q3Q2Q1Q0KNLJIHGFEDCBA@QE+ca]8%Q@2TB1%QJ73>1;<Q>9%QO3QN71p0R11p0R<1p0R@1p0RE1p0S71p0S@1p0SN1p0T91pTDT?1pTBTA1pULTC1pT<TE1pT4TK1pLTN1pVNU21pVJU31pVHU41pVFU51pVDU61pU0U71pTNU81pUHU91pUFU:1pUDU;1pUBU<1pU@U=1pU<U>1pT0U?1pSNU@1pSLUA1pSJUB1pSHUC1pSFUD1pSDUE1pSBUF1pTLUG1pVBUH1pV@UI1pV>UJ1pVLUK1pT6UL1pUJUM1").
Proof.
intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). pose_ceil.
pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
assert (AL : Z.land (conc st p) 4095 = 0).
{ rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
assert (PB : 0 <= conc st p < 2^64) by lia.
clear RBAL RU RBC RL0 WR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
st1. st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
rewrite CF.
st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
st1. st1.
st1. st1. rewrite ?AL, ?AL'. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
apply evt_done. reflexivity.
Qed.
Lemma ram_to_mprotect : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_F "S?'S0yR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'<&F&Q9'>'9r1&J&G&RO+cajH%22F1rQ2rQ1rQ0rOrNrM+TP0%:2N1r2%<2Q01+3%>2Q21rIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7%Q3OQ0ONMLKJHFFHDCBA@?>=<;:987654321r5&Q?%Q52QI1r4(0%11QKr3&QB%11QA%Q>7:976431%QA3QBQ@1qT@QC1rL%Q@2R4QCrKrJr6%QEOAQ@Q?Q>Q=Q<5Q:432Q5Q4Q3Q2Q1Q0ONMLKJIHGFEDC1+caj8%QF2R:1%QI73A1>?Q<<%QO3QN:1pQ4R11pT<R31pT4R91pLR<1pVNR@1pVJRA1pVHRB1pVFRC1pVDRD1pU0RE1pTNRF1pUHRG1pUFRH1pUDRI1pUBRJ1pU@RK1pU<RL1pU8RM1pU4RN1pT0RO1pSNS01pSLS11pSJS21pSHS31pSFS41pSDS51pSBS61pVBS71pV@S81pV>S91pVLS:1pT6S;1pUJS<1").
Proof.
intros.
st1. st1. st1. st1.
apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.
Lemma ram_mp_ok0 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_F "S8'S0yR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1&F&Q9'>'9r1&J&Gr5rQ2rQ1rQ0rOrNrMrLrK&ROz%22N1rJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7r6%Q2OQ1Q0ONMLKJIFEDCBA@?>=<;:987654321r4+caeH%K2QG1r3(0%11QIr2&QB%11Q@%Q=7:976431%Q@3QAQ?1qT@QB1%Q?O<Q<Q;Q:Q9Q8Q7Q6Q2Q3Q1Q0ONMLKJIHGFEDCBA@?>Q>+cajH%Q72R31%QC73<19:QD7%QI3QH51pT<QK1pT4R11pLR41pVNR81pVJR91pVHR:1pVFR;1pVDR<1pU0R=1pTNR>1pUHR?1pUFR@1pUDRA1pUBRB1pU@RC1pU<RD1pU8RE1pU4RF1pT0RG1pSNRH1pSLRI1pSJRJ1pSHRK1pSFRL1pSDRM1pTLRN1pTHRO1pVBS01pV@S11pV>S21pVLS31pT6S41pUJS51").
Proof.
intros.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_ram_mp_fail := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_F "VK'S0yR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'4%114'<'Q3&Q@vBr1r5%43321&K&Q9r6%3221'9rQ:&RO+iSU@%22M1%53M41&Mr8&QC&S1rQ;%22Q41-U4%5221(2'E(D%?2Q:G%211(5%115%73631%@4I?91'8&QD+1%221L+SoO%42N1%6231&:r7+Q6%Q13Q<21%411&QA&Q:r9rQ@%N2R01%43931r<r;%83321&Ir=%23QA15rQB%Q72R91-R0%Q:221&Q;rArBrCrDrErF%78R2A654321%QE4QN>91&Hr>rQC%QF2RH1%QH21?%54R44H1&L%11R;%Q<21G&QGrQE%QN2S01+R0%4221%QB2=1&F'>&Q<rKrQGrQFrJrIrHrGrQ7rQ6rQ5rQ4rQ3rQ2rQ1r@z%RL2SG1%BIS7A@?I>=<;Q6:987654Q7Q83Q2Q9Q21S6&?%11S8%RJ2KRFr?%S22SM1%RE11%RH3RG1RB%S14S:651%RA291qT@M1&J&G%S32T5L%S521QL%S<2T71rQDrQArQ?-1%SA2T<1rQ>rQ=rQ<rQ9rQ8&Q>%SH2TC1&Q=%SJ2TE1rQ0rOrNrMrL%GOQDDQLCR4RCBRLA?>=<SHT1;:86Q=Q<Q;Q:Q9Q8Q754321+cajH%T22TM1(0%11TN&QB%11T;%O77RB5RC3RE1%QO3T=Q11p0R11p0R81p0R<1p0RC1p0S11p0S51p0S?1p0SE1p0SM1p0T?1p0TF1p0TK1pULU11pT2U31pT:U41pT8U61pT<U91pT>U:1pT4U@1pLUC1pU>UG1pU:UH1pU6UI1pU2UJ1pTJUK1pTFUL1pVNUM1pVJUN1pVHUO1pVFV01pVDV11pU0V21pTNV31pUHV41pUFV51pUDV61pUBV71pU@V81pU<V91pT0V:1pSNV;1pSLV<1pSJV=1pSHV>1pSFV?1pSDV@1pTLVA1pTHVB1pVBVC1pV@VD1pV>VE1pVLVF1pT6VG1pUJVH1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 14%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 15%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 16%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 17%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 18%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 19%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 26%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 27%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 28%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 29%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 30%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 31%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 32%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 33%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 34%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 35%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 36%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 37%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 38%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 39%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 40%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_mp_fail) 41%nat 0%nat).
Lemma ram_mp_fail : ltac:(sec_stmt2 constr:(SEC_T_ram_mp_fail) 42%nat 0%nat).
Proof.
intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
subst tp. rewrite (unsigned_lit 0xc8cb0) in * by lia. change (822448 + -164) with 822284 in *.
change (Z_to_bv 64 e) with (wz e) in ERR.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *).
st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
st1. st1. st1. st1.
st1. rewrite sx32_wz by lia. st1. st1.
assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
rewrite CF; clear CF.
st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. split.
- unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
- cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.
End SE.
End CEIL_WRAP_1.
