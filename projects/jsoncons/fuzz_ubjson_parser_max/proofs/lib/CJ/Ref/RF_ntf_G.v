(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B MallocKit_A3 MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_ntf_A RF_ntf_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_ntf_G () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_ntf_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_ntf_G.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1snd"; "2and"; "2eq"; "2ex"; "2not"; "3N"]; ["3Z"; "0F"; "4bvmap"; "0RUNp"; "5fm_facts"; "6fm_st"; "7mw_ok"; "8grp_del"; "9b8"; "9meta_slot"; "9meta_word"; "9wz"; ":cell"; ":cells_size"; ";evt"; "<mkR"]; ["<stk"; "=MS"; ">bytes_at"; ">mem_inv"; "?alloc_ceiling"; "@rw_cells"; "Arsegs"; "Brntf_frame"; "Crnest_call_post"; "Drntf_ret_post"; "ERCTX"; "ERSSP_GUARD"; "Ermrep"; "FUNIT"; "FUnknown"; "Fa_check"]; ["Faadd"; "Faptr"; "Farea"; "Farea_of"; "Fc_secret"; "Fcell_read"; "Fcellval"; "Fconc"; "Fctx"; "Fg_meta"; "Fget_meta_rec"; "Fget_shadow"; "Fghdr"; "Fm_avail"; "Fm_freeable"; "Fm_freed"]; ["Fm_last_idx"; "Fm_maplen"; "Fm_mem"; "Fm_sizeclass"; "Fmeta"; "Fmstate"; "Foptr"; "Fs_areas"; "Fs_groups"; "Fsize_class"; "Gseg_rom"; "Hadd"; "Hland"; "Hle"; "Hlt"; "Hmul"]; ["Hopp"; "Hpow"; "Hsub"; "Htestbit"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0ar1"; "0b3"; "0base1"; "0fc"]; ["0fr"; "0g"; "0g1"; "0gh1"; "0ghp"; "0gp"; "0h"; "0hi8"; "0idx1"; "0junk"; "0lo"; "0lo8"; "0m"; "0mr"; "0mr1"; "0o"]; ["0off16"; "0p"; "0ra"; "0raw"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2o"; "0s3"; "0s3o"; "0s4"; "0s5"; "0s6"]; ["0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st0"; "Ilookup"; "JZ_to_bv"; "Jbv"; "Jbv_unsigned"; "KN_countable"; "KZ_countable"; "Kprod_countable"; "Lprod_eq_dec"; "Mgmap"; "Mgmap_lookup"]; ["Neq_dec"; "Oeq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x9b2fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b074) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.
Section SE.
Local Abbreviation SEC_T_rntf_nest_call := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_G "^2'T8yR0%211&By5%2213yQ0%711'9y8%:11%311p0:1'6'L%211'R5&QA'QL'QB'@'R4&QJr=r<%3221r>r:%6221&R<r7+O%3221&Q<vCr@rB%43321&Q3&Q6rC%3221&IrA%2281&Fr6%211'<&R1%11Dz%43Q021&R6&R2r8%211(1%12Q9B%;3631%QD1Q:&T6'T>&T='?&T@&TA%4432Q?1&T<&T:&T;%36762QC51%:4QG51QF&T?%14QI73QHrD&R8rF%211%B6QNQM7541%G2QNQ5%Q13E21';&R=r1%22Q21&R>+<%2241%7241'='QF&QE&QKrJ&5rH%23Q1R=1%5241&R;&:%13Q5RA5r3%4221%<261(Q>%11F%QK3@31qV>RH1%C2RI1p0E1pW0RK1&Q2&RB&QG%12CQ6+4%4221(3&H%11R5%21RFr?%411%51S2(8%11SD%93SE31%:3SF51%;3SG81%<3SH:1%C4RLQ5>1%QA2RARI+X0%Q@2RK1%QE231&R?%124S5%Q72S21%RK3SGS01&Q@rK&R@&Q=%821S<%311%Q1213%7261%S43T3QF1rN%R:11%RJ6T6T5R?R=:1%RO2T6QH%S93RM21&QIrI%211%S42T<@%S>3S921rQ0rL%SG221%S<1SJ%S:2TB>%SD3S?21&QM%11RK%RD2SD1&RA+2+Q0%3221%RF261%RK261&QOrE%211%RN2SN1%RL227%S1221&R0%11S8%S32T31%S122=%S6221&QNrG%211%S92T91%S722D%S<221&R3%11S0%S>2T>1+R0%S=231%SB231%TD1Q:%SC2TC1+Q8%Q02O1%SC241%SH241%V31UH%T>4UKT9T5UI%T44ULT:T6UJ&QCrQ4%211&R7rQ8%211%TG6V3V18741rQ1%TM2V31%U73<31&Q?rQ2%211&QD&QHrQ9%211%411%U@3V<61rQ:%611%811%TA2UA1%QM2QLQ3%T@231%TE231rM%QE11%TG2R:1'2&RC%R81RH%2216(4%V03521rO%R411%721RN%V43915%QF1RF+Q@%U1221&R9%QJ1Q4%211%SC21RL%U921Q=+1%TK2RO1%SG251%U:2QA1%U?251p0;1%U@2=:%R51Q;+QO%VF3WB21p041&>%VH1Q@%VJ3WF1VG%311rQ6rQ3%VM11%T721T:%TO21C%UN251p071&Q5rQC&T9rR@%22XF1-S0%UF221rQB%84WD721'7&M%11:uS0%W@3421&Q0rQErQ7rRB%@2Y41%V321>%64X0541&Q4%11X7%VG21RHrRD%G2Y;1+S0%UM221%VL2RB1&N&Q8rRErRCrR>rR6rR5rR4rR3rR2rR1rR0rQOrQJrQIrQFrQH&GrQD%234Q11%VB25Q:rQG%EGDKCBA@?>=<;:98S5763Q442Q31&Q1&OrRF&T7%QF2Z:I%W921QD%32Z<1rRArR?%VN2AQ>%72Z@1rR=&K&J%11SH%311rR<rR;rR:rR9rR8&Q:%C2ZL1rR7rQNrQMrQLrQK%KOJFQHQ@QOER=DQ?BA=<;:9865Q>Q=Q<Q;Q:Q9Q8Q74321+c\f@%K2[41(0%11[5&R:%11Z2%Q377Q=5Q<3Q:1%QK3Z4Q51p0QM1p0R31p0R71p0R?1p0RE1p0RO1p0S;1p0SA1p0T01p0T51p0T<1p0T@1p0TH1p0U21p0U@1p0UG1p0UN1p0V51p0V;1p0VB1p0VL1p0W01p0W41p0W:1p0W@1p0WJ1p0WO1p0X01p0X11p0X61p0XK1p0YJ1p0ZA1p0ZI1p0ZO1p0[31p0[71p0[<1tVB[N[B1tVN[N[G1tVL[O[K1pVF\11pW2\21pV@\31pVH\41pUL\51pUJ\71pV8\91pV:\:1pV6\<1pUN\=1pW4\>1pV4\?1pX:\A1pV2\C1pVJ\G1pV0\M1pQ4]01pYB]41pY@]51pY>]61pY<]71pWB]81pW@]91pX6]:1pX4];1pX2]<1pX0]=1pWN]>1pWL]?1pWH]@1pUH]A1pUF]B1pUD]C1pUB]D1pU@]E1pU<]F1pW>]G1pW:]H1pY:]I1pY8]J1pY6]K1pYD]L1pV<]M1pX8]N1pW6]O1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 27%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 28%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 29%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 30%nat 0%nat).
Variable fr : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 31%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 32%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 33%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 34%nat 0%nat).
Variable base1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 35%nat 0%nat).
Variable g1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 36%nat 0%nat).
Variable ghp : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 37%nat 0%nat).
Variable gh1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 38%nat 0%nat).
Variable ar1 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 39%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 40%nat 0%nat).
Variable lo8 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 41%nat 0%nat).
Variable hi8 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 42%nat 0%nat).
Variable off16 : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 43%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_nest_call) 44%nat 0%nat).
Lemma rntf_nest_call : ltac:(sec_stmt2 constr:(SEC_T_rntf_nest_call) 45%nat 0%nat).
Proof.
intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B. pose_ceil.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).
destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
{ rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
assert (Hao : area_of g1 = a).
{ rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
{ rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
(pose_ceil; unfold RCTX, AREA_HDR, META_SIZE, NSLOTS in *).
assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.
change (frozen (conc st p mod 16 = 0)) in P16m.
change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
clear HGm AAL RBAL RgBAL SpA BbA.
destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
pose proof (rmrep_ctx_secret_read st mX MR) as RC;
pose proof (bytes_at_read rsegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
pose proof (bytes_at_read rsegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
pose proof (bytes_at_read rsegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
end.
rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.
st1.
eapply evt_cut.
{ eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
(m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
(m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
all: lazymatch goal with
| |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
| |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
| |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
| |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
| |- ov_read_bytes _ _ (wa 950384) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
| |- rw_cells _ _ (conc _ _) _ => exact MM
| |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
| |- _ => idtac
end.
all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
| lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0x9b2e8)) with (Z_to_bv 64 0x9b2e8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
st1.
unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
st1.
clear CH MM RG RA RC R4 R2.
pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rw_cells_store_ok_at rsegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
clear RWp.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
end.
rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
apply (rmrep_grp_del_eq st _ g p) in MR2.
st1. st1.
apply evt_done. unfold rnest_call_post. do 14 eexists.
split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
cbv delta [mkR]. unfold RCTX. reflexivity. }
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_group; [exact Hp | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.
End SE.
Lemma rntf_nest_ret : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_G "UE'T8yR0%211&By5%2213yQ0%711'9y8%:11%311p0:1'6%114'R5&QA'@&Q<vCr3r;%43321&Q3&Q6r<%3221&Ir5r4%3221&Dr6%2215'<&QGr7%2215r8%4217%63G31rQ7&T7&Q;%22Q;1%;3Q;41&Q5rA&R;&T9rQ?%22QB1-S0%5221&Q7r@r=r>r?%57Q84Q6Q2321%>4Q4=71&Q0rBrQ@%?2QO1%A21=%54Q:4L1&R=&Q4%11QBr9%4221r:&RBrQB%J2R:1+S0%4221%;261&N&Q9rCrQCrQArQ3rQ2rQ1rQ0rOrNrMrLrGrFrE&E%12Q8R7rQ;rQ:%CIR@BAI@Q5QDQ<Q9?>=<;:9876R>Q;5321&Q1&O+c\gL%QM2S61%QG2S7F%QI21QE%R02S91rQ>rQ=rQ<rQ9rQ8rQ6rQ5rQ4&Q:%R:2SC1%RB2QLRL%R<2SE1rKrJrIrH%FODAQAQ8QLR9@?>JI=<RB;:975Q7Q6Q5Q4Q3Q2Q1Q04321(0%11SK&R:%11S7%L75Q4IQ33Q21%QB3S9N1p0QD1p0QL1p0R21p0R91p0RI1p0RO1p0S71p0S;1p0S@1p0SE1pVFSK1pV4SM1pX:SO1pX<T01pWJT>1pWFT?1pWDT@1pW<TA1pW8TB1pVDT71pVJT:1pV0T@1pQ4TC1pYBTG1pY@TH1pY>TI1pY<TJ1pWBTK1pW@TL1pX6TM1pX4TN1pX2TO1pX0U01pWNU11pWLU21pUHU31pUFU41pUDU51pUBU61pU@U71pU>U81pU<U91pU:U:1pW>U;1pW:U<1pY:U=1pY8U>1pY6U?1pYDU@1pV<UA1pX8UB1").
Proof.
intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose_ceil.
st1. st1. st1.
rewrite <- Hcg.
eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | pose_ceil; lia].
Qed.
End CEIL_WRAP_1.
