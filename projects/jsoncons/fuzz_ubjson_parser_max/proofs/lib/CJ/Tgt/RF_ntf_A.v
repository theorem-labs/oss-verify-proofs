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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocModel_B F_ntf_A F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_ntf_A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_ntf_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1app"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5sxv"; "6fm_facts"]; ["7fm_st"; "7ivs_covered"; "8aor_st"; "9meta_slot"; "9wz"; ":C8"; ":CB"; ":cell"; ";evt"; "<mkR"; "<munch"; "<stk"; "<wmono"; "=MS"; ">le8"; ">mem_inv"]; ["?alloc_ceiling"; "@rw_cells"; "Aaptr"; "Aconc"; "Aget_meta_rec"; "Am_freed"; "Amstate"; "Brsegs"; "Crntf_frame"; "Drfree_fp"; "Drntf_ret_post"; "ERCTX"; "ERSSP_GUARD"; "Ermrep"; "Fseg_rom"; "Gadd"]; ["Gle"; "Glt"; "Gpow"; "Gsub"; "0W"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0g"; "0gp"]; ["0i"; "0j0"; "0junk"; "0lo"; "0m"; "0m0"; "0ra"; "0raw"; "0rest"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2"]; ["0s2o"; "0s3"; "0s3o"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st'"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0t0"]; ["0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0z1"; "0z2"; "0z3"; "0z4"; "0z5"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 (wz canary_val); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End CEIL_WRAP_1.
Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl rsegs mX) as WMq end.
Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | tauto ]]);
clear MUq WMq CH end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
#[using="Type"] Lemma rntf_ret : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_A "V0'RMyR0%211&<y5%2213yQ0%711'5y8%:11%311p0:1'4'7':%2211%411%518'Q6&Q=v=r2r;%43321&O&Q7r<%3221'9rQ7&RL&Q<%22Q01%53Q041&Q1r>&Q?&RNrQ?%22Q71-S0%5221&Q8r7r8r9r:%57KE4321I%>4G=71&Kr?r5rQ@%@2QE1%B21>%64N541&Q@&Q0%11Q6r6%4221&QCrQB%J2QO1+S0%4221%:2G1&J(3(6rQC%Q22R71%;218%44QKQK12rA%73QL21rCrB%;3321&LrD%23QH15&A&Q9rQE%Q@2RE1%33QLQ81%521;&H&Q:rQFrQDr@rQ4rQ3rQ2rQ1rQ0rOrNrMrHrGr=rFrQ<rQ=%BIRGNAG@Q1?QIR8>=<;:98765RE43RA21&M&IrQG%R:2S?E%R<21R8%RC2SA1rQArQ>rQ;rQ:rQ9rQ8rQ6rQ5rLrKrJrI%AO@=Q:Q3QHR0<R:RH;DE:987S165Q1Q0ONMLKJ4321+caS@%S22T01(1%11T1rE&Q>%11S<%J78Q16Q0431%Q?3S>L1p0QA1p0QH1p0QL1p0R91p0R@1p0RF1p0RN1p0S>1p0SE1p0SJ1pT8T41pUHT11pUFT21pU6TD1pU2TE1pTNTF1pTFTG1pT@TH1pT6T91pS:T;1pT:TA1pT<TB1pSLTH1pHTK1pV<TO1pV:U01pV8U11pV6U21pTLU31pTJU41pUBU51pU@U61pU>U71pU<U81pU:U91pU8U:1pU4U;1pU0U<1pSJU=1pSHU>1pSFU?1pSDU@1pSBUA1pS@UB1pS>UC1pS<UD1pTHUE1pTDUF1pV4UG1pV2UH1pV0UI1pV>UJ1pT0UK1pUDUL1pT>UM1").
Proof.
intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
(pose_ceil; unfold RSSP_GUARD, rntf_frame in *). subst s1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
finish.
Qed.
#[using="Type"] Lemma rntf_aor : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_A "V;'RMyR0%211&<y5%2213yQ0%711'5y8%:11%311p0:1'4%114'Q6&Q2':&Q=v=r4r;%43321&O&Q7r<%3221&Cr6r5%3221'9rQ4&D&>&QB+2%2218%411%611%93Q681'8&Q@z%221@&QA+Q0%22C1%7241rQ8&RL&Q<%22QC1%F3QC41&Q5&Q4r:r9%3221%511%B2A1%J2I?%A231%F231&Q1rB&Q?&RNrQA%22R41-S0%5221&Q8rAr=r>r?r@%67QK5QE4321%?4QG>81&KrCrQB%@2RB1%B21>%54QM4L1&Q0%11R4%Q>21Q0&QCrQD%H2RJ1+S0%4221%QD2R91&H&Q:rDrQErQCrQ3rQ2rQ1rQ0rOrNrMrHrGrF&B%13Q3Q4Q5%R?1R5%AIRN@?G>Q0Q@Q8Q4RA=<;:98765RHQ54211&M&IrQF%QB2SDC%QD21Q@%R52SF1rQ@rQ?rQ>rQ=rQ<rQ;rQ:&Q3%12QDQE+L%R0221%RA2T21rQ9rQ7rQ6rQ5rLrKrJrI%IOHEQBQ9QJR8DCBA@?>98RK765S<Q8Q7Q6Q5Q4Q3Q24321+caR8%RL2T=1(1%11T>&Q>%11SJ%Q177Q85Q73Q61%QE3SLQ31p0QG1p0QN1p0R21p0R91p0RJ1p0S51p0S;1p0SD1p0SO1p0T41p0T91pT8T?1pT2T@1pSNTB1pUFTD1pU6U21pU2U31pTNU41pTFU51pT@U61pT6TK1pT:TN1pSLU41pHU71pV<U;1pV:U<1pV8U=1pV6U>1pTLU?1pTJU@1pUBUA1pU@UB1pU>UC1pU<UD1pU:UE1pU8UF1pU4UG1pU0UH1pSJUI1pSHUJ1pSFUK1pSBUL1pS@UM1pS>UN1pS<UO1pTHV01pTDV11pV4V21pV2V31pV0V41pV>V51pT0V61pUDV71pT>V81").
Proof.
intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
(pose_ceil; unfold NSLOTS in *).
assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
set (mr := get_meta_rec st g) in *.
pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
{ apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
subst a1.
st1. rewrite sx32_wz_sxv by lia. st1.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep (aor_st st g i) mX) end.
{ unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
- reflexivity.
- cbn. tauto. }
clear MUg MM.
st1. st1.
eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | pose_ceil; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.
#[using="Type"] Lemma rntf_frame_remerge : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_A "R4'RMyR0%211'5y8%511%311p051':'4%115'G%311&Q1&Q7r9r8(3(Fu8r7%3221(Er6%211r5%411r4%611r3%811r2%:11r1%A3G21%B3H51%C3I81%D3J;1%E3K>1%F3LB1%K4JIH1r:uQ@&2&N%11I%21G%31F%41E%51D%73Q=21%83Q>41%93Q?61%:3Q@81%;3QAQ61%Q52=1%Q73Q=1I%Q<4Q;@Q:1p0B1pTBQ?1pVHQJ1pVFQK1pVDQL1pVBQM1pV@QN1pT4QG1p2QJ1pT:QL1").
Proof.
intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
eapply rw_cells_congr; [| | | exact H].
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
- reflexivity.
- split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rntf_fm := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_A "U@'RMyR0%211&<y5%2213yQ0%711'5y8%:11%311p0:1'4%114'Q6&Q2':&Q=v=r3r:%43321&O&Q7r;%3221&Cr5r4%3221&?r6%2215'9rQ5&RL&Q<%22Q51%53Q541&Q1r?&Q?&RNrQ=%22Q<1-S0%5221&Q8r>r9r<r=%57Q243Q0L21%>4N=71&Kr@r7rQ>%@2QJ1%B21>%64Q5541&Q@&Q0%11Q=r8%4221&QCrQ@%J2R41+S0%4221%:2F1&H&Q:rArQArQ?rQ1rQ0rOrNrMrLrKrJrErDrC&@%12Q7R1rQ8rQ9%CIR:BAI@Q5QDQ<Q9?>=<;:9876R8Q:5321&M&IrQB%QF2S0E%QH21QD%QO2S21rQ<rQ;rQ:&Q3%12QER?%R52S81rQ7rQ6rQ4rQ3&Q;%R;2S>1rQ2rIrHrGrF%FOEBQAQ8QKR9A@?<IJ;:RB9865Q7Q6Q5Q4Q3Q2Q1Q04321+c`m<%RC2SF1(1%11SG&Q>%11S3%N77Q65Q53Q41%QD3S5Q01p0QF1p0QM1p0R31p0R;1p0RK1p0S21p0S61p0S;1p0S@1pT8SF1pSNSH1pUFSJ1pU6T81pU2T91pTNT:1pTFT;1pT@T<1pT6T11pT:T41pSLT:1pHT=1pV<TA1pV:TB1pV8TC1pV6TD1pTLTE1pTJTF1pUBTG1pU@TH1pU>TI1pU<TJ1pU:TK1pU8TL1pU4TM1pSJTN1pSHTO1pSFU01pSDU11pSBU21pS@U31pS>U41pTHU51pTDU61pV4U71pV2U81pV0U91pV>U:1pT0U;1pUDU<1pT>U=1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 9%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 10%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 11%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 15%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 16%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 17%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 18%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 19%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 20%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 21%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 22%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 23%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 24%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 25%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 26%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 27%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 28%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 29%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 30%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 31%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 32%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 33%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 34%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 35%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 36%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 37%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 38%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 39%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_fm) 40%nat 0%nat).
Lemma rntf_fm : ltac:(sec_stmt2 constr:(SEC_T_rntf_fm) 41%nat 0%nat).
Proof using Type ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk raw s0o s1o s2o s3o st g lo.
intros MR MI MSL FMF S1 FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(pose_ceil; unfold RCTX, rntf_frame in *).
rmeta_chunk MR MSL CH.
pose proof MR as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.
st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRf : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MUs.
rmeta_open (conc st g) MUg WMg.
st1. st1.
st1. st1.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
assert (CH' : rw_cells rsegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
clear CH; rename CH' into CH
end end.
st1. st1.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
assert (CH' : rw_cells rsegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear CH; rename CH' into CH
end end.
rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
set (st0 := put_meta g meta0 st) in MR0.
assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).
rmeta_chunk MR0 MSL0 CH0.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
clear CH0 K1 K2.
st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
-
destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1.
clear CHh.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH.
st1.
rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
st1. clear CH.
rmeta_open (conc st head) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
rewrite get_meta_rec_put_same.
rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
st1.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | pose_ceil; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
-
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1. st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.
clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1. rewrite FMH in C1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
{ eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
st1.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | pose_ceil; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
Qed.
End SE.
End CEIL_WRAP_2.
