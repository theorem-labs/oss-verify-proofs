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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_free_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_free_C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_free_C.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5wz"; "6C4"]; ["6C8"; "6CB"; "6cell"; "7evt"; "8mkR"; "8munch"; "8stk"; "8wmono"; "9MS"; ":le4"; ":mem_inv"; ";alloc_ceiling"; "<rw_cells"; "=mstate"; ">rsegs"; "?rffin_post"]; ["?rfmun_post"; "@rrepfoot"; "ARATP"; "Armrep"; "Bseg_rom"; "Cadd"; "Cle"; "Clt"; "Cpow"; "Csub"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"]; ["0a5"; "0a6"; "0a7"; "0bw"; "0e'"; "0errv"; "0ew"; "0fc"; "0gp"; "0junk"; "0len"; "0lo"; "0lw"; "0m"; "0m'"; "0q0"]; ["0q1"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"]; ["DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.
Section SE.
Local Abbreviation SEC_T_rfree_fin0 := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_C "V1'RAyR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2%114':'M'8rQ6&R@&Q2%22D1%53D41&Q3v=r3r6%43321&J&Nr7%3221&Lr8&Q5&RBrQ;%22Q41-Q@%5221(1'B(Au8%221>(@rL%211rM%411rQ4%611rQ5%811r>%:11(3%11@%B3A31%C3B61%D3C91%E3D<1%F3E?1%G3FC1%Q04Q3OI1r9rQ:%Q02R21-U4%Q3221(?r5%211%Q13Q01@%Q:4Q=951&Fr:rQ=%Q;2R=1%Q=21Q9%54QC4Q?1&Q6&K%11QK%321C&Q9rQ?%QD2RF1+Q@%4221%92>1&C&OrCrQ@rQ>rQ9rQ2rQ1rQ0rOrNrKrJrIr?r;'6%12RMRM(5%R;2S=@%J21G%34S1S112%QI15%R:3621r=%HGGFNEQBDCBA@?R4R6>=<;QN:21Q8QC&H&DrD%RF2:RB%S62SH1rQ<rAr@rB&>z%211rQ8rQ7rQ3rHrGrFrE%BOA?QBQ9QK>S4=<;876SFRDRF5Q7Q6Q5Q4Q3RHRJQ2Q1Q04321+c_k0%SG2T91(0%11T:&Q4%11SA%J77Q65RI3L1%QE3SCL1p0QG1p0QN1p0R31p0R:1p0RE1p0SG1p0SL1p0T21pS<TG1pU0T:1pSHT<1pSDT>1pSLTA1pS@TG1pHTJ1pT2TN1pT0TO1pS8U01pT4U11pUHU21pUDU31pUBU41pU@U51pU>U61pT<U71pT:U81pTLU91pTJU:1pTHU;1pTFU<1pTDU=1pTBU>1pT@U?1pT>U@1pS6UA1pS4UB1pS2UC1pS0UD1pRNUE1pRLUF1pT8UG1pT6UH1pU<UI1pU:UJ1pU8UK1pUFUL1pSBUM1pTNUN1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 7%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 27%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 28%nat 0%nat).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 29%nat 0%nat).
Variable bw : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 30%nat 0%nat).
Variable q0 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 31%nat 0%nat).
Variable q1 : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 32%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 33%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 34%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 35%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 36%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 37%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 38%nat 0%nat).
Variable errv : ltac:(sec_ty2 constr:(SEC_T_rfree_fin0) 39%nat 0%nat).
Lemma rfree_fin0 : ltac:(sec_stmt2 constr:(SEC_T_rfree_fin0) 40%nat 0%nat).
Proof using Type sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo st errv.
intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
(pose_ceil; unfold RMLOCK, RNEED_LOCKS, RATP in *). subst tp.
rewrite (unsigned_lit 822448) in ERR by lia. change (822448 + -164) with 822284 in ERR.
st1. st1. st1. st1.
st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x9bf74)) with (Z_to_bv 64 0x9bf74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 822448) by lia. change (822448 + -164) with 822284. exact ERR.
Qed.
End SE.
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x9bf90) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.
#[using="Type"] Lemma rfree_tomunmap : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_C "V7'RAyR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2%114':'M'8rQ7&R@&Q2%22D1%53D41&Q3v=r3r7%43321&J&Nr8%3221'7&Q7zr6%3221&Q8+2+R0%3221%8261%:261&Lr:&Q5&RBrQ=%22Q?1-Q@%5221(1'B(Au8r9%3221(@rN%211rO%411rQ6%611%71Q>r@%911(3%11@%B3A31%C3B61%D3C81%E3D;1%F3E>1%G3FB1%Q04Q>OI1r;rQ<%Q02R=1-U4%Q3221(?%11Q?%Q03O1?%Q94QG841&Fr<rQ?%Q:2RG1%Q<21Q8%54QM4Q>1&Q6&K%11R5%321B&Q9rQA%QC2S01+Q@%4221%92>1&C&Q0rErQBrQ@rQ;rQ4rQ3rQ2rQ1rQ0rMrLrKrAr=r>r?rD&>%11Q3%DICBJAQ=@?>=<;QNR0:987QI654Q>R>31&H&DrF%R@2SMF%RB21R>%S=2SO1rQ>rCrBrQ:rQ9rQ8rQ5rJrIrHrG%@O?<Q<Q3QE;RM:9EC876SJR>5Q1Q0ONMR@RBLKJ4321+c_k0%SK2T=1(0%11T>&Q4%11SE%H77Q05RB3M1%Q?3SGJ1p0QA1p0QH1p0QM1p0R41p0R>1p0S@1p0SL1p0T11p0T71pS<TL1pU0T?1pSFTA1pSHTB1pSDTD1pSLTG1pS@TM1pHU01pT2U41pT0U51pS8U61pT4U71pUHU81pUDU91pUBU:1pU@U;1pU>U<1pT<U=1pT:U>1pTLU?1pTJU@1pTHUA1pTFUB1pTDUC1pTBUD1pT@UE1pT>UF1pS6UG1pS4UH1pS2UI1pS0UJ1pRNUK1pRLUL1pT8UM1pT6UN1pU<UO1pU:V01pU8V11pUFV21pSBV31pTNV41").
Proof.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
(pose_ceil; unfold RMLOCK, RNEED_LOCKS, RATP in *). subst tp.
rewrite (unsigned_lit 822448) in ERR by lia. change (822448 + -164) with 822284 in ERR.
st1. st1. st1. st1.
st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x9bf74)) with (Z_to_bv 64 0x9bf74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
st1. st1. st1. st1.
replace (ret_pc (Z_to_bv 64 0x9bf7c)) with (Z_to_bv 64 0x9bf7c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 822448) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [rewrite (unsigned_lit 822448) by lia; change (822448 + -164) with 822284; exact ERR| exact MR2].
Qed.
Section SE.
Local Abbreviation SEC_T_rerrno_avoids_repfoot := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_C "Q1'M'RAyR0%211'4y8%511%311p051':&Q3v=r3r2%43321'7&Q6+iSP<%2215&Q7+iSP@%2281%7241&9&Q1r5%221>%411p061p0?1pRFE1pSLG1pU0Q01")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rerrno_avoids_repfoot) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rerrno_avoids_repfoot) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rerrno_avoids_repfoot) 2%nat 0%nat).
Lemma rerrno_avoids_repfoot : ltac:(sec_stmt2 constr:(SEC_T_rerrno_avoids_repfoot) 3%nat 0%nat).
Proof using Type st m a.
intros MR Ha.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rmrep_transport_frame_errno := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_C "QE'M'RAyR0%211'4y8%511%311p051':&Q3v=r4r3%43321&E(1'6%1299(5&Q9r2+Q@%3221%54??13+iSP<+iSP@%84BB21(3%11;%>3<31%?3=71%A31DC&G&Nr5%3321H&Q6&K%11L%D2LB%4221r8r6%Q23Q121p041p0:1p0?1p0Q21pTNQ81pSNQ:1pSLQ;1pU0QD1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_frame_errno) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_frame_errno) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_frame_errno) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_frame_errno) 3%nat 0%nat).
Lemma rmrep_transport_frame_errno : ltac:(sec_stmt2 constr:(SEC_T_rmrep_transport_frame_errno) 4%nat 0%nat).
Proof using Type st m m' sp.
intros MR MU WM HS.
eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil. lia.
+ destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). pose_ceil. lia.
+ destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). pose_ceil. lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.
End SE.
#[using="Type"] Lemma rfree_fin1 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_C "V@'RAyR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2%114':'M'8rQ9&R@&Q2%22D1%53D41&Q3v=r3r6%43321&J&Nr7%3221&Lr8&Q5&RBrQ>%22Q41-Q@%5221(1'B(Au8%221>(@rM%211rN%411rQ7%611rQ8%811r?%:11(3%11@%B3A31%C3B61%D3C91%E3D<1%F3E?1%G3FC1%Q04Q3OI1&I%11<r5%311%QD3QG31r:-U4%Q62Q31(?r=%211%Q43Q31C%Q=4Q@751&Fr;r9rQA%Q?2RA1%QA21Q=%64QG541&Q6&K%11QO%321B&Q9rQC%QH2RJ1+Q@%4221%92?1&C&OrErQDrQBrQ=rQ4rQ3rQ2rQ1rQ0rOrLrKr@r<'6%12S1S1(5%R?2SA@%J21G%34S5S512+iSP<+iSP@%64S8S821%R018%RA3921%RB3:61r>%LGKJQ2IRHHGFEDCBR<R>A@?R6>21Q=QF&H&DrF%RN2>RJ%S>2T01rQ@rQ?rCrBrQ<rQ;rQ:rQ6rQ5%S82T:Q8%S:21R5%SJ2T<1rDrJrIrHrG%EODBQIQ@R2A@?>=<;T1ROS1:965Q<Q;Q:Q9S3S5Q8Q74321+c_l@%T22TD1(0%11TE&Q4%11SL%M77Q=5S43O1%QL3SNO1p0QN1p0R51p0R:1p0RB1p0RK1p0S11p0T31p0T81p0T>1pS<U31pU0TF1pSHTH1pSDTJ1pSLTM1pS@U31pHU61pS:U:1pSJU;1pS8U<1pS>U=1pT4U>1pUHU?1pUDU@1pUBUA1pU@UB1pU>UC1pT<UD1pT:UE1pTLUF1pTJUG1pTHUH1pTFUI1pTDUJ1pTBUK1pT@UL1pT>UM1pS6UN1pS4UO1pS2V01pS0V11pRNV21pRLV31pRJV41pRHV51pT8V61pT6V71pU<V81pU:V91pU8V:1pUFV;1pSBV<1pTNV=1").
Proof.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (822284, 822288)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
(pose_ceil; unfold RATP in *). subst tp.
rewrite (unsigned_lit 822448) in ERR by lia. change (822448 + -164) with 822284 in ERR.
rewrite (unsigned_lit 822448) by lia. change (822448 + -164) with 822284.
st1.
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | pose_ceil; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 822448) by lia. change (822448 + -164) with 822284.
eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End CEIL_WRAP_1.
