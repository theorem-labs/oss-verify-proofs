(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_G.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_am_G () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_G."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["1None"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "0RUNp"; "6mm_ok_st"; "7evt"; "8mkR"]; ["8stk"; "8wmono"; "9MS"; ":mem_inv"; ";alloc_ceiling"; "<rw_cells"; "=rsegs"; ">ram_fp"; ">ram_frame"; ">ram_ret_post"; "?RMLOCK"; "?RSSP_GUARD"; "?rmmap_entry"; "?rmrep"; "@rpres_except"; "ABrkDead"]; ["Abrkstate"; "Ac_avail_meta_area_count"; "Ac_brk"; "Ac_meta_alloc_shift"; "Actx"; "Amstate"; "Ar_base"; "Aregion"; "As_regions"; "Bseg_rom"; "Cadd"; "Cle"; "Clt"; "Cmodulo"; "Cmul"; "Cpow"]; ["Cshiftl"; "Csub"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0gp"; "0junk"; "0lo"; "0m"]; ["0m'"; "0m0"; "0ms'"; "0n"; "0r"; "0raw"; "0rid"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2o"; "0s3o"; "0s4"]; ["0s4o"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st0"; "Dlookup"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "FN_countable"; "Ggmap"; "Ggmap_lookup"]; ["Heq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ram_disp_dead : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_G "T;'RKyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'Q5&Mv<r1r2%43321'5'8&Q1&Q4%116%311z%73621'Q0&Q2r3%811%311(O%>3621&>&F':&B&?r9rQ4rQ3rQ2rQ1rQ0rO&RJ+TP0%22Q?1&QA&Q?+2+R0%3221+1%6221%:2QG1%;2QHQ0-1%=2QJ1rKrJrIrHrGrF&K%E2R21&J%G2R41rErDrCrBrAr@r?r>r=r<r;r:%Q<OQ;Q:Q9Q8Q7Q6Q5Q2JIGFEDCBA?=<;:987654321r8+c]`4%Q72RD1r7(0%11RFr6&Q9%11QH%QG7:976431%R:3QIR=1qT6QJ1rNrMrL%QLO?QIQHQGQFQE3QB21Q6Q5Q4Q3Q2Q1LOMKJIHGFEDCBAQK+c]ZD%QF2S31r5%R174@2=>1;%R53R491p0R71p0R?1p0RH1pU@RN1pT0S01pSHS61pDS91pVFS=1pV@S>1pV>S?1pV<S@1pV:SA1pTHSB1pTFSC1pU<SD1pU:SE1pU8SF1pU6SG1pU4SH1pU0SI1pSFSJ1pSDSK1pSBSL1pS@SM1pS>SN1pS<SO1pS:T01pS8T11pTDT21pV8T31pV6T41pV4T51pVBT61pSJT71pU>T81").
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (950384 + 912) with 951296 in C6.
st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1.
change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.
Lemma ram_to_mmap : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_G "T?'RKyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'Q5&Mv<r1r2%43321'4&Q;z&Q3&Q4%117%311%6251+Q8%8231%:231'8&Q@+2r3%;11%=11%5241&>&F':'5&B&?&RJ+c]a@%22Q<1rQ4rQ3rQ2rQ1rQ0rO+TP0%:2QD1%;2QEQ5%<2QFQ2&Q>%12Q85%?2QI1+Q2%A2QK1-1%C2QM1rGrF&K%G2R11&J%I2R31rDrCrBrAr@r?r>r=r<r;r:%Q6OQ3Q2Q1Q0ONMKJIFIDBIA@><B;:987654321r8&L%Q82RB1r7(0%11RDr6&Q9%11QC%QA7:976431%QC3QDR;1qT6QE1rNrMrLrKrJrIrHrEr9%QLOEQGQFQEQDQC9QA876543Q7Q62Q4Q2Q1Q0ONMLKJIHG1+c]`4%QM2S71r5%R174F2CD1A%R63R5?1tT8R>R81p0R@1p0RL1pU@S21pT0S41pSHS:1pDS=1pVFSA1pV@SB1pV>SC1pV<SD1pV:SE1pTHSF1pTFSG1pU<SH1pU:SI1pU8SJ1pU6SK1pU4SL1pU0SM1pSFSN1pSDSO1pSBT01pS@T11pS>T21pS<T31pS:T41pS8T51pTDT61pV8T71pV6T81pV4T91pVBT:1pSJT;1pU>T<1").
Proof.
intros until st. intros MR SH n.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
st1. st1. st1.
rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
{ rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
st1. st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.
Lemma ram_mm_fail : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_G "U<'RKyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'8'Q5&Mv<r1r4%43321&C&Fr5%3221&N&Gr3&RLrQ:%22N1%534<1r7r6%93321&Ar8%23?15&E&Q:rQ<%=2Q91-R0%4221&Hr<r=r>r?r@rA%78Q2C654321%>4N@91&@r9rQ=%L2QH1%B21?%54Q44J1&Q;&D%11Q<%321J&QArQ?%Q52R11+R0%4221%92>1&>&IrErQ@rQ>rDrCrBrQ1rQ0rOrNrMrLrKr:&RJz%22RG1%BHR7A@H?>=<Q6Q7;:98765Q8Q94Q2Q:Q21&B&?rF%R02RLD%QF21QC%92RN1rQ;rQ9-1%=2S21rQ8rQ7rQ6rQ5rQ4rQ3rQ2&K%F2S;1&J%H2S=1rJrIrHrG%HOGDQBQ9QKR:CREB@?>=<;:975@Q5Q4Q3Q2Q1Q0O4321+c]a@%O2SD1(0%11SE&Q9%11S2%Q077R95R:3R<1%QE3S4Q21p0QG1p0QN1p0R31p0R:1p0RJ1p0RN1p0S91p0S>1pU@SD1pSNSF1pSLSH1pT0SK1pT4SL1pSHT21pDT51pU2T91pTNT:1pTLT;1pTJT<1pTBT=1pT<T>1pVFT?1pV@T@1pV>TA1pV<TB1pV:TC1pTHTD1pTFTE1pU<TF1pU:TG1pU8TH1pU6TI1pU4TJ1pSFTK1pSDTL1pSBTM1pS@TN1pS>TO1pS<U01pS:U11pTDU21pT@U31pV8U41pV6U51pV4U61pVBU71pSJU81pU>U91").
Proof.
intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *).
st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.
Section SE.
Local Abbreviation SEC_T_ram_mm_ok := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_G "XK'RKyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'8'Q5'7'Q7&Mv<r3r9%43321&C&Fr:%3221&Gr7&RLrQ>%22O1r1%645821r;rQ?%72Q41r2%;4:421p061pS6J1'5%Q31I&RI'RN&S0&RM%34O21N&RO%14Q143Q0r5&Q8r6%211%;6Q6Q57541(1r4%22Q81%A3@41&Q6%11:%D3Q?1Q4&Q=+TP0%22N1z%I3QD21&Q<r<%2241&Q;&Q:r=+XP0%3221&D%11QI%7231'4+1%:218&Q?+2+QN%3221%B2=1%8261&Q3&Q4%11E%311%E2J1%I228%?221&Nr>rArQE%R52S21%R83431rDrC%83321&ArE%23RA15&ErQG%R?2S<1-R0%Q7221&HrIrJrKrLrMrN%78S3B654321%=4RO?91&@rFrQH%RN2SK1%QE21?%54S54I1%QH2QBF&QArQJ%S42T11+R0%4221%QN2;1&>':'6&B&?rQ5&RJrQM%S@2T=1%R721Q1%42T?1rQLrQKrQI%82TCRDrH%R>21RF%;2TF1%<2TGRF%R01Q@%R211%RC21R;%@2TK1rG%N21R>%C2TN1rQDrQCrQBrQA&K%I2U41&J%K2U61-1%M2U81rQ@rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6%Q9OQ8Q3Q2Q1QBQ0QHOLKGDRACBA@><:9T?TD87654321+c]gD%Q92UD1(0%11UE&Q9%11U0%QA77R45R53TI1%TA3QDTE1%U03RCR;Q>%RN31R9TL%RF3U5R:TM%U72U6TNrOrQ0rQ1rQ2rQ3rQ4%RF8UBRD654321%RL4U>U6QH1%R?4U?U7RGQI&=%13S1S5Q=%UH3UG1U:%SM241%SN261%SO2?1%T02A1%T12C1%T22F1qT2V61%R;2V71qT6R=1%UG2VDR3%T>21S8%R;2VF1rQF%R=2VHS@%R>2VIS0%RAOG4RJR8S0S?3R721SIQKQJQIQHQAUGQFQDQBULQ@Q?Q>Q=Q<Q;Q:Q9R@F+c]a@%RA2VL1%RE73S:1S;Q7S=Q5%RI3V6;1p0RK1p0S21p0S41p0S;1p0SJ1p0SN1p0T81p0T@1p0TJ1p0U31p0U71p0U=1p0UA1p0V41p0VC1p0VH1pT:VN1pT>W01pU@W21pUBW31pT8W51pVDW61pSNW71pSLW91pT0W<1pT4W=1pSHWC1pDWF1pU2WJ1pTNWK1pTLWL1pTJWM1pTBWN1pT<WO1pVFX01pV@X11pV>X21pV<X31pV:X41pTHX51pTFX61pU<X71pU:X81pU8X91pU6X:1pU4X;1pSFX<1pSDX=1pSBX>1pS@X?1pS>X@1pS<XA1pS:XB1pV8XC1pV6XD1pV4XE1pVBXF1pSJXG1pU>XH1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 5%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 6%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 7%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 8%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 9%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 10%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 11%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 12%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 13%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 14%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 15%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 16%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 17%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 18%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 19%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 20%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 21%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 22%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 23%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 24%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 25%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 26%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 27%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 28%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 29%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 32%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 33%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 34%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 35%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 36%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 37%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 38%nat 0%nat).
Variable st0 : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 39%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 40%nat 0%nat).
Variable rid : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 41%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_ram_mm_ok) 42%nat 0%nat).
Lemma ram_mm_ok : ltac:(sec_stmt2 constr:(SEC_T_ram_mm_ok) 43%nat 0%nat).
Proof.
intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
assert (AL : Z.land (x + 4096) 4095 = 0).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
change (x mod 4096 = 0) with (pgal x) in XAL.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *).
st1.
assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1. st1. st1. st1.
replace ((n + -1) * 1) with (n - 1) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
lazymatch goal with H : rw_cells rsegs ?mX 950384 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.
st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros y Hy. apply ram_fp_stack. lia.
- intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.
End SE.
End CEIL_WRAP_1.
