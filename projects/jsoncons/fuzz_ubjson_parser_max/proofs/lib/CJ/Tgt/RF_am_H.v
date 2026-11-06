(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F F_am_G F_am_H.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C RF_am_F RF_am_G.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_H () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_H."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree.Exc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_am_H.CEIL_WRAP_1.BRKNODES."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3N"; "3Z"; "0F"; "4machine_state"]; ["5bvmap"; "0RUNp"; "6brk_mem"; "6brk_res"; "7b8"; "7zeros"; "8C1"; "8C4"; "8C8"; "8CB"; "8cell"; "9brk_ans"; "9dec_brk"; "9dec_brk0"; ":evt"; ";mkR"]; [";munch"; ";wmono"; "=exc"; "<enode"; "<epost"; "<impl"; ">MS"; "?mem_inv"; "@NBrk"; "@at_node"; "@node"; "Arw_cells"; "BBrkDead"; "BBrkLive"; "BBrkUntried"; "Bbrkstate"]; ["Bc_avail_meta_area_count"; "Bc_brk"; "Bc_seq"; "Bconc"; "Bctx"; "Bmstate"; "Bset_brk"; "Bupd_ctx"; "Crsegs"; "Drbrk_regs"; "ERCTX"; "ERMLOCK"; "ERSSP_GUARD"; "Ermmap_entry"; "Ermrep"; "Fseg_rom"]; ["Gadd"; "Gle"; "Glt"; "Gmodulo"; "Gpow"; "Gsub"; "0a"; "0a0"; "0a1"; "0a2"; "0a2'"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"]; ["0cur"; "0fc"; "0gp"; "0m"; "0m'"; "0m0"; "0ms'"; "0nw"; "0off"; "0old"; "0pc"; "0q0"; "0q1"; "0q2"; "0r"; "0req"]; ["0rid"; "0s0"; "0s1"; "0s10"; "0s11"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "HZ_to_bv"; "Hbv"; "0t0"]; ["0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0w0"; "0w1"; "0w10"; "0w2"; "0w3"; "0w4"; "0w5"; "0w6"; "0w7"]; ["0w8"; "0w9"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ram_disp_untried : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "T5'S>yR0%211&@y5%2213yQ0%711'4y8%:11%311p0:1'QE&QNvAr1r2%43321'8'=&Q@&QD%116%311z%73621'Q?&QAr3%811%311(Q>%>3621&N&QH'?&Q6&Or9rQ4rQ3rQ2rQ1rQ0rO&S=+TP0%22Q?1%32Q@H+SoO%52QB1rKrJrIrHrG+VF%<2QI1&QL%>2QK1&QK%@2QM1rErDrCrBrAr@r?r>r=r<r;r:%Q5OQ4Q3Q2Q1Q0ONKJJHGFEDCA?=<;:987654321r8+ca_4%Q02R=1r7(0%11R?r6&QO%11QA%Q@7:976431%R33QBR61qU>QC1rNrMrLrF%QFO@QCQBQAQ@Q?4Q<32Q8Q7Q6Q5Q41MQ0NLKJIHGFEDCBQE+ca]8%Q@2RM1r5%QK74A2>?1<%QO3QN:1p0R11p0R91p0RB1pVJRH1pU8RJ1pU4S01pNS31pX6S71pW<S81pW:S91pW8S:1pW6S;1pV:S<1pV8S=1pVFS>1pVDS?1pVBS@1pV@SA1pV>SB1pV<SC1pU0SD1pTNSE1pTLSF1pTJSG1pTHSH1pTDSI1pTBSJ1pT@SK1pV6SL1pW4SM1pW2SN1pW0SO1pW>T01pU6T11pVHT21").
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in C6.
st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.
Lemma ram_disp_live : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "U1'S>yR0%211&@y5%2213yQ0%711'4y8%:11%311p0:1'QE'<'=&QNvAr3r4%43321'8&Q@&QD%115%311z%63<21'Q?&QAr5%811%311(Q=%12?@%>3731&R2&QCr6(5%14JI:E%4231%62@1&R0r7%64ON7?%9221+TP0%5221&R4+2+R0%3221%A251&N&QH'?r1&Q6&Or=rQ8rQ7rQ6rQ5rQ4rQ3&S=%12R3Er9r8%Q04QIQH1K%Q3231%N21J%72R91-1%92R;1rOrNrMrLrK+VF%@2RB1&QL%B2RD1&QK%D2RF1rIrHrGrFrErDrCrBrAr@r?r>%Q9OQ8Q7Q6Q5Q4Q3Q2Q0JJHGFEDCA?=<;:987654321r<+ca^<%Q42S61r;(0%11S8r:&QO%11QF%QD7:976431%RJ3QGQF1qU>QH1rQ2rQ1rQ0rJ%QJO@QGQFQEQDQC4QA32Q8Q7Q6Q5Q41MQ0NLKJIHGFEDCBQI+ca]8%QD2SF1%QN73@1=>QC;%R33R291p0R51p0RA1p0RI1p0S21p0S:1pUBS@1pV2SB1pVJSD1pU8SF1pU4SL1pNSO1pX6T31pW<T41pW:T51pW8T61pW6T71pV:T81pV8T91pVFT:1pVDT;1pVBT<1pV@T=1pV>T>1pV<T?1pU0T@1pTNTA1pTLTB1pTJTC1pTHTD1pTDTE1pTBTF1pT@TG1pV6TH1pW4TI1pW2TJ1pW0TK1pW>TL1pU6TM1pVHTN1").
Proof.
intros until off. intros MR CNT BRK C0 C1b.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in C6.
st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).
Definition rbrk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Lemma ram_brk0_node : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "QJ&Q5'Q:&QH&Q9%112'Q2'=%211&Q3(Q8z%211&M%54<721&Q4'?'7'8r1&Q6&QI&S=yR0r2%3221%511v>+ca_8%7261vRA(0'S>%11:%311vRC&QO%11Q2%B7<;98431%E3GD1&R1%12NA&R2&R4+2+R0%3221%52G1%O271%Q02:1qU>Q21qUNQ<1%Q52Q=1%O2NQ:%Q111+ca_4%Q22Q11%Q573N1KGFD%QI7QHQGQEQBQ<61").
Proof.
unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x9c5e4 + 4)%Z with 0x9c5e8%Z by reflexivity.
apply evt_done. split; [reflexivity| exact Hr].
Qed.
Section SE.
Variables (pc : Z).
Lemma ram_brk_node_at : (pc = 0x9c5cc \/ pc = 0x9c608) -> forall cur req, req <> 0 ->
impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
(epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom rsegs)))
(MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
intros Hpc cur req NZ. unfold rbrk_regs.
destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
[ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
| rewrite apply_mem_none ];
apply evt_done; reflexivity).
Qed.
End SE.
End BRKNODES.
Lemma ram_bu_mid : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "V1'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'='7&R2zr1%3221&R4+2+R0%3221%8261%:261'8&R3r2+TP0%3221%53A1>&Q;&QHr4&R0&QJ+l@%3221(1'J(Fr9%211(Iu7r8%3221(Hr7%211(3%11<%>3=31%?3>71%@3?<1%H4GFB1&Q7r5%22J1&N'?'9r3&Q6&Or?rQ6rQ5rQ4rQ3rQ2rQ1&S=%12R:Q=+XP0%Q92N1%42R=1%52R>QMrOrNrMrL+VF%;2RD1&QL%=2RF1&QK%?2RH1rKrJrIrHrGrFrErDrCrBrAr@%Q4OQ3Q2Q1Q0ONMKHHGR9FEDCA?=<;:987654321r;+ca`8%O2S81r:(0%11S:&QO%11R<%Q>798653RL1%RE3QBQ@1&Q0'6%12S4S4(5+lH%RB2RA1+m0%RD2RC1%54S:S:31%R617%RC3821%;31RAS9&Q1%13RLRCS;%R52RMS<r>%RG11r=%RF2RE1%QJ2T3RE%RD11%RN3RM1RA%RO3RN41%S03RO71%S84S7SFS21%SJ2;1%SK2=1%SL2@1%SM2M1qU:T01%R@2T11qTFT>1%RB2T?1qU>RD1r<rQ0%R;2TDRJ+SoO%R=2TF1%RFO5RAR@R?4R8R7R=R931R6R5QNQMQLR3R1QOQKQJQIQHQGQFQEQDQCREHF+ca_8%R@2TI1r6%RK74S=2S:Q@1Q>%S03SK;1p0S21p0S61p0T01p0T71pU2TC1pU8TE1pU4TI1pNTL1pULU41pUJU11pUHU41pX6U71pW<U81pW:U91pW8U:1pW6U;1pV:U<1pV8U=1pVFU>1pVDU?1pVBU@1pV@UA1pV>UB1pV<UC1pTNUD1pTLUE1pTJUF1pTHUG1pTDUH1pW4UI1pW2UJ1pW0UK1pW>UL1pU6UM1pVHUN1").
Proof.
intros until cur. intros CR CAL TC MI.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (land_neg_aligned cur CR CAL) as AL.
assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
change (cur mod 4096 = 0) with (pgal cur) in CAL.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in TC. change (954560 + 920) with 955480 in MU. change (954560 + 928) with 955488 in MU.
st1. st1. rewrite ?AL, ?AL'. st1. st1.
replace (0 + cur) with cur by lia.
st1. st1. st1. st1.
replace (8192 + cur) with (cur + 8192) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.
Lemma ram_bu_ok : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "TM'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'=&R2zr1%3221&R0r2+XP0%3221&R4+2+R0%3221%<251&Q;&QHr4&QJ+l@%>221(1'J(Fr8%211(Iu7r7%3221(H&S=r3%22Q>1%411(3%11>%@3?31%A3@91%B3A>1%I4HGD1&N'?'8&Q6&O+caa<%@2QL1rQ3rQ2rQ1rQ0rOrN+TP0%H2R41r5%QC21QA%K2R71%L2R83%M2R9QI+QB%O2R;1-1%Q12R=1rH+VF%Q42R@1&QL%Q62RB1&QK%Q82RD1rGrFrErDrCrBrAr@r?r>r=r<%Q7OQ5Q4Q3Q2Q1Q0OMJIMHFDHCA?=<;:987654321&QM%QG2S31(0%11S4r6&QO%11R;%Q@78R46R0431%QB3QCRI1qU>QD1r:rM%RK2R@RI%R32S?1rLrKrJrIr;%QKO9QGQFQEQDQC8QA665432Q7Q0Q5Q3Q1ONMLKJIHGFE1+ca`<%R;2SG1%QO73R?1BCQC@%R33RL>1p0R51p0S01p0S:1pU2S?1pU8SA1pU4SE1pNSH1pUJSL1pUHSO1pX6T21pW<T31pW:T41pW8T51pW6T61pV:T71pV8T81pVFT91pVDT:1pVBT;1pV@T<1pV>T=1pV<T>1pTNT?1pTLT@1pTJTA1pTHTB1pTDTC1pTBTD1pW4TE1pW2TF1pW0TG1pW>TH1pU6TI1pVHTJ1").
Proof.
intros until cur. intros C0 C1b TC.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in TC.
st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. reflexivity.
Qed.
Lemma ram_b_store : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "X7'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'='7&R1zr1%3221&R2&R4+2+R0%3221%5271%;271&Q;&QHr3&QJ(1'J(HrC%211(GrB%211rA%411r@%911r?%;11r>%=11r=%?11r<%A11r;%C11r:%E11r9%G11(3%11J%L3K31%M3L61%N3M91%O3N<1%Q03O?1%Q13Q0B1%Q23Q1E1%Q33Q2H1%Q43Q3K1%Q53Q4N1%Q63Q5Q21%Q;4Q:Q9Q81r4&R0+l@%22Q<1(F%11E(Iu7r8%3221r7%QA11%QD3QC1I%QE3QD41%QF3QE91%QK4QJ?<1&Q7r5%22QM1&N'?'9'8r2&Q6&OrIrQCrQBrQArQ@rQ?rQ>&S=+1%22S:1&R5+TP0%22L1%62S>1rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6&QL%@2SH1&QK%B2SJ1rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJ%Q7OQ6Q5Q4Q3Q2Q1Q0MIHGFEDCBA?=<;:987654321+caeH%Q12T91(0%11T:&QO%11SA%Q?77RI5RG3SL1%QB3QDQA1&Q0'6%12T4T4(5+Q8%R=2SG1+Q@%R?2SI1%54T:T:31+lH%RB2SL1+m0%RD2SN1%:4T?T?31%S51<%T03=21%T13>81%A31RBT?&Q1%13T7RDTA%R=2T8TBrH%T511rG%T411rF%T611rE%T;11rD%T=11%T>1R5%T?1T9%TB3TAT3SG%TC3TBT61%TD3TCT91%TE3TD41%TF3TE61%TG3TFTC1%TH3TG91%TI3TH<1%TJ3TI?1%TK3TJB1%TL3TKE1%U14U0U:TN1%SB1T>%SA2S@T=%RG2UOS>%TO11%U23U11T7%U33U241%U43U361%U94U8UBSJ1%UF291%UG2Q21%UH2Q41%UI2Q71%UJ2QJ1qU:UM1%S?2UN1qU>SA1%S52V=S1%S62V>SF%S?OQ8S;S:S9S8S0RO21RNRMRLRKRJRIRDRCRGRERBRAR@R?R>R=R<R;R:R9S>Q:+caa<%S92VA1r6%SD74T42T2R81R6%SJ3UH81p0SL1p0T01p0TA1p0UN1pU@V;1pU8V=1pU4VA1pNVD1pULVL1pUJVI1pUHVL1pWDVO1pX4W01pX2W11pX0W21pWNW31pWLW41pWJW51pWHW61pWFW71pWBW81pW@W91pX6W:1pW<W;1pW:W<1pW8W=1pW6W>1pV:W?1pV8W@1pVFWA1pVDWB1pVBWC1pV@WD1pV>WE1pV<WF1pU0WG1pTNWH1pTLWI1pTJWJ1pTHWK1pTDWL1pTBWM1pT@WN1pW4WO1pW2X01pW0X11pW>X21pU6X31pVHX41").
Proof.
intros until nw. intros NW HC TC MI.
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in TC.
change (954560 + 40) with 954600 in MU. change (954560 + 48) with 954608 in MU. change (954560 + 920) with 955480 in MU. change (954560 + 928) with 955488 in MU.
st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.
Lemma ram_bl_ok : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "X5'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'='7&R1zr1%3221&R2&R4+2+R0%3221%5271%;271&Q;&QHr3&QJ(1'J(HrC%211(GrB%211rA%411r@%911r?%;11r>%=11r=%?11r<%A11r;%C11r:%E11r9%G11(3%11J%L3K31%M3L61%N3M91%O3N<1%Q03O?1%Q13Q0B1%Q23Q1E1%Q33Q2H1%Q43Q3K1%Q53Q4N1%Q63Q5Q21%Q;4Q:Q9Q81r4&R0+l@%22Q<1(F%11E(Iu7r8%3221r7%QA11%QD3QC1I%QE3QD41%QF3QE91%QK4QJ?<1&Q7r5%22QM1&N'?'9'8r2&Q6&OrIrQBrQArQ@rQ?rQ>rQ=&S=+1%22S:1&R5+TP0%22L1%62S>1%72S?NrQ<rQ;rQ:rQ9rQ8rQ7rQ6&QL%@2SH1&QK%B2SJ1rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJ%Q7OQ6Q5Q4Q3Q2Q1Q0MIHGFEDCBA?=<;:987654321+caeH%Q12T91(0%11T:&QO%11SA%Q?77RI5RG3SL1%QB3QDQA1&Q0'6%12T4T4(5+Q8%R=2SG1+Q@%R?2SI1%54T:T:31+lH%RB2SL1+m0%RD2SN1%:4T?T?31%S51<%T03=21%T13>81%A31RBT?&Q1%13T7RDTA%R=2T8TBrH%T511rG%T411rF%T611rE%T;11rD%T=11%T>1R5%T?1T9%TB3TAT3SG%TC3TBT61%TD3TCT91%TE3TD41%TF3TE61%TG3TFTC1%TH3TG91%TI3TH<1%TJ3TI?1%TK3TJB1%TL3TKE1%U14U0U:TN1%SB1T>%SA2S@T=%TN1R@%U13U01T6%U23U131%U33U251%U84U7UASI1%UE281%UF2Q11%UG2Q31%UH2Q61%UI2QI1qU:UL1%S>2UM1qU>S@1%S42V<S0%S52V=SE%S>OQ7S:S9S8S7RNRM211RLRKRJRIRHRCRBRFRDRAR@R?R>R=R<R;R:R9R8S=Q9+ca^@%S82V@1r6%SC74T32T1R71R5%SI3UG81p0SK1p0SO1p0T@1p0UM1pU@V:1pU8V<1pU4V@1pNVC1pULVK1pUJVH1pUHVK1pWDVN1pX4VO1pX2W01pX0W11pWNW21pWLW31pWJW41pWHW51pWFW61pWBW71pW@W81pX6W91pW<W:1pW:W;1pW8W<1pW6W=1pV:W>1pV8W?1pVFW@1pVDWA1pVBWB1pV@WC1pV>WD1pV<WE1pU0WF1pTNWG1pTLWH1pTJWI1pTHWJ1pTDWK1pTBWL1pW4WM1pW2WN1pW0WO1pW>X01pU6X11pVHX21").
Proof.
intros until nw. intros NW HC TC MI.
st1. rewrite bv_eqb_refl. cbv iota.
eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.
Lemma ram_brk_dead : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "V>'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'QE&QNvAr1r3%43321&Q0(1'6'=%2211(5&R0&QJ+lH%3221+m0%5241%749931(3%11:%>3;31r4%A321C&Q1&QHr5%33215'8&Q@&QD%119%311z%63I21&Q;r6+l@%J2I1'J(Fr<%211(Iu7r;%3221(Hr:%211%O1;%Q<3<21%Q=3=61%Q>3>;1%C4MB@1r=&D&QB%L1F%211%411%Q13R861&E%11C%Q43R991&Q7r9%22Q:1&N'?'9'7r2&Q6&OrCrQ?rQ>rQ=rQ<rQ;rQ:rQ9rQ8&S=%12S3QD-1%32S51rQ5rQ4rQ3rQ2rQ1rQ0&QL%;2S=1&QK%=2S?1rOrNrMrLrKrJrIrHrGrFrErD%Q4OQ3Q2Q1Q0ONMLKIGFEDCBA?=<;:987654321r?+cabH%M2SO1r>(0%11T1&QO%11RM%Q>798653SD1%RL3QCQ@1%SC3S4R@SF%S23S1RASG%QJ2S2SH&QG&QF(Q<%211%421RC%T03SO1SN%QK271%QL291%QM2;1%QN2=1qU:T71%R12T81qU>R31rArQ7rQ6rB%R3O4QOQNQMQLQKQJ32QEQDQCQBQAQ@Q;Q:Q>Q<Q9Q8Q7Q6Q5Q4Q3Q2Q1Q0R21+cab0%QK2TM1%R773RI1S7LS0J%R=3SH91p0R?1p0RC1p0RG1p0RO1p0SD1p0SL1p0T11p0TD1pVJTJ1pU8TL1pU<TM1pU4U11pNU41pULU<1pUJU91pUHU<1pX6U?1pW<U@1pW:UA1pW8UB1pW6UC1pV:UD1pV8UE1pVFUF1pVDUG1pVBUH1pV@UI1pV>UJ1pV<UK1pU0UL1pTNUM1pTLUN1pTJUO1pTHV01pTDV11pTBV21pT@V31pV6V41pV4V51pW4V61pW2V71pW0V81pW>V91pU6V:1pVHV;1").
Proof.
intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
lazymatch type of C1 with rw_cells _ _ _ ?cs =>
assert (C1' : rw_cells rsegs m RCTX cs)
by (eapply RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
clear C1.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (954560 + 912) with 955472 in TC.
change (954560 + 920) with 955480 in MU, MU0. change (954560 + 928) with 955488 in MU, MU0.
st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
{ eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
- unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
- first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (954560 + 912) with 955472.
replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with H : rw_cells rsegs ?mX 955472 _ |- _ => exact H end. }
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.
Lemma ram_bl_fail : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "U>'S>yR0%211&@y5%2213yQ0%711'4y8%:11%311p0:1'QE'=&QNvAr2r3%43321'8&Q@&QD%115%311z%63<21&R2%123:&R0r4+TP0%3221&R4+2+R0%3221%:251&Q7&QHr7%3221&N'?'9'7&Q6&Or=rQ4rQ3rQ2rQ1rQ0rO&S=%12QGIr8%M21K%42QJ1%52QKQ3-1%72QM1rNrMrLrKrJ+VF%>2R41&QL%@2R61&QK%B2R81rIrHrGrFrErDrCrBrAr@r?r>%Q7OQ6Q5Q4Q3Q2Q1Q0NKJHGFEDCA?=<;:987654321r<+cabH%Q22RH1r;(0%11RJr1&QO%11QH%QB7:976431%R=3QFR@1&Q0(1'6%12RGRG(5&QJ+lH%R<221+m0%R>241%64RNRN31(3%119%<3:31r:%?321D&Q1%13R<3F%R>2R=G&QG&QF(Q<%211r9%5221%S<3S;1N%R?281%R@2:1%RA2=1%RB2N1qU:SD1%RE2SE1qU>RG1r6%S721S5%R>2T41%R?2T53%RHOQ=RDRCRBRAR8R7R?21R9R6R5R4QMQLR2R0QNQKQJQIQHQGQFQEQDQCQBRGQ@+ca^@%RB2T81%RL73J1AQ>RAQ;%S13S491p0S31p0S81p0SB1p0SE1p0SM1pUDT31pVJT51pU8T71pU4T=1pNT@1pX6TD1pW<TE1pW:TF1pW8TG1pW6TH1pV:TI1pV8TJ1pVFTK1pVDTL1pVBTM1pV@TN1pV>TO1pV<U01pTNU11pTLU21pTJU31pTHU41pTDU51pW4U61pW2U71pW0U81pW>U91pU6U:1pVHU;1").
Proof.
intros until old. intros MR CNT O0 O1 MI.
pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
st1.
assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.
Lemma ram_bu_fail : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_H "VL'S>yR0%211y8%411'2%112&@y5%2217yQ0%;11'4%119p0<1'QE'=&QNvAr2r4%43321&Q0(1'6%1299(5&R0&QJ+lH%3221+m0%5241%74AA31(3%11:%=3;31r5%@321B&Q1&QHr6%33215'8&Q@&QD%119%311z%63Q121&R2%123>&R4+2+R0%3221%62?1&Q;r9+l@%Q12Q01'J(Fr>%211(Iu7r=%3221(H&S=r7%22R71%411%Q81=%QD3>21%QE3?81%QF3@=1%E4Q6DB1r?&D&QB%Q51H%211%411%Q:3RA61&E%11E%Q=3RB91&Q7r<%22QC1&N'?'9'7&Q6&OrErQ=rQ<rQ;rQ:rQ9rQ8+TP0%Q42S91+XP0%RA2Q91%Q72S<1%Q82S=QN-1%Q:2S?1rQ6rQ5rQ4rQ3rQ2+VF%QA2SF1&QL%QC2SH1&QK%QE2SJ1rQ1rQ0rOrNrMrLrKrJrIrHrGrF%Q7OQ6Q5Q4Q3Q2Q1Q0NKJHGFEDCA?=<;:987654321rB+cabH%R52T:1rA(0%11T<r1&QO%11S9%QB7:976431%S83QFT01%SN3S@R55%S>3S=R66%QM2S>7&QG&QF(Q<%211%421RL%T;3T:1=%QN271%QO291%R02;1%R12=1qU:TC1%R42TD1qU>R61rCrQ7r;%T<21QL%S22U71%S32U83rD%R:O7R6R5R4R36QJR132QIQHQGQFQ?Q>QDQBQ@Q=Q<Q;Q:Q9Q8Q7Q6Q5Q4R91r@+ca`<%S82U=1%R?7431S0Q1S<N%RD3T8=1p0RF1p0RJ1p0RN1p0S61p0SM1p0T31p0T61p0T>1p0TC1p0U51pU2U;1pVJU=1pU8U?1pU<U@1pU4UD1pNUG1pUJUK1pUHUN1pX6V11pW<V21pW:V31pW8V41pW6V51pV:V61pV8V71pVFV81pVDV91pVBV:1pV@V;1pV>V<1pV<V=1pTNV>1pTLV?1pTJV@1pTHVA1pTDVB1pTBVC1pW4VD1pW2VE1pW0VF1pW>VG1pU6VH1pVHVI1").
Proof.
intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
{ apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
rewrite CF; clear CF.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.
End CEIL_WRAP_1.
