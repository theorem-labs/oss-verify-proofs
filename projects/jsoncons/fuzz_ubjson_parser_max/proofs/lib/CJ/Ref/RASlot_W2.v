(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_W2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "0G"; "4machine_state"; "5bvmap"; "0RUNp"]; ["6sxv"; "7wz"; "8evt"; "9mkR"; "9munch"; "9stk"; "9wmono"; ":MS"; ":ret_pc"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">rsegs"; "?rta_frame"; "@RSSP_GUARD"; "@rmrep"]; ["Alowbit"; "Am_set_avail"; "Amstate"; "Aupd_meta"; "Bseg_rom"; "Cadd"; "Cle"; "Clt"; "Cpow"; "Csub"; "0W"; "0a0"; "0a1"; "0a1'"; "0a2"; "0a2'"]; ["0a3"; "0a3'"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0g"; "0gp"; "0gw"; "0junk"; "0k"; "0lo"; "0m"; "0m'"; "0m0"]; ["0mask"; "0ms'"; "0rav"; "0s0"; "0s0v"; "0s1"; "0s10"; "0s11"; "0s1v"; "0s2"; "0s2v"; "0s3"; "0s3v"; "0s4v"; "0s5"; "0s5v"]; ["0s6"; "0s6v"; "0s7"; "0s7v"; "0s8"; "0s8v"; "0s9"; "0s9v"; "0sp"; "0st"; "0st'"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0t0"; "0t1"]; ["0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 (wz canary_val); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
#[using="Type"] Lemma ras_ret : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W2 "VO'RLyR0%211&>y5%2213yQ0%711'4y8%:11%311p0:1'2'6':%2211%411%518'Q2&Ov?r2r5%43321&I&Lr6%3221&Kr7&Q5&RMrQC%22Q11-T@%5221&MrErDrCrBrAr@r?r>r=r<r;%<<J;:987654321%E4HD>1&Er8r4rQD%G2QF1%I21E%64O541&Q6&J%11Q7%321Q6&Q9rQF%Q02QO1+T@%4221%92Q81&D(1(5rQG%Q82R71%;218%44QKQK12r:%73QL21%931NM&F%13QEQ1Q0&B'='9'7'8&G&CrQMrQLrQKrQJrQIrQHrFrGrQEr3rQBrQArQ@rQ?rQ>rHrIrJrKrLrMrNrOrQ6rQ5rQ4rQ3rQ2rQ1%NOR>MLKJIHGFEDRNCBA@?>=<;:987654321&H%11R@(0%11SFr1&Q4%11S1%Q778RE6RD431%Q93Q<R81%RN2SMQ7%R121QN%QJ4SASA12%QL3SA1RF%QN31RI9%QE3S9RJ:%S;2S:;%RB4S;<RG7%SB3SARI=%QD221%QE241%QF261%QG281%QH2>1qSNT01%QK2T11qS0T<1%QM2T=1qRLT>1%QO2T?1qT4R11&RK%SD2TCQI%SF21SB%32TE1rQ=rQ<rQ;rQ:rQ9rQ8&N%;2TM1rQ7rQ0%R;OQG;R5RJS2R2S;T0R0QOQNQMQL:9876532QCQBQAQ@Q?Q>1QDQEQF+c`gD%@2U21%R?73SI1SHQ<SFQ9%RE3T;C1p0RG1p0RJ1p0S51p0S<1p0SA1p0SI1p0T@1p0TE1pSJTO1pUFTL1pSFTN1pRFU01pSLU61pT0U71pS>U=1pHU@1pT6UD1pT:UE1pTBUF1pTFUG1pTJUH1pTLUI1pU0UJ1pU4UK1pU8UL1pU<UM1pU@UN1pV>UO1pV:V01pV8V11pV6V21pV4V31pT@V41pT>V51pU>V61pU:V71pU6V81pU2V91pTNV:1pTHV;1pTDV<1pS<V=1pS:V>1pS8V?1pS6V@1pS2VA1pRNVB1pRJVC1pRHVD1pT<VE1pT8VF1pV2VG1pV0VH1pUNVI1pV<VJ1pSBVK1pUBVL1").
Proof.
intros until lo. intros MR' MI FR ST LO LOLE MU WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
(pose_ceil; unfold RSSP_GUARD, rta_frame in *).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.
Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.
Section SE.
Local Abbreviation SEC_T_rfin_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W2 "W>'RLyR0%211&>y5%2213yQ0%711'2y8%:11%311'8':&RMr?%22?1v<%63521&K&LvQM&Q5rQ<%:2G1-T@%4221&Mr2r>r=r<r;r:r9r8r7r6r5%<<;H:987654321%E4DC>1&EvQLrQ=%N2Q;1%G21D%54JI41&Q6&Q9rQ>%Q42QA1+T@%4221%62;1&I%12Q3Q2&B'='9'4%11QBp0QK1'7zr1%B221&Q7+Q0%2241%7241&Q0vR0%211&Q8+2%221;%R03QO41&G&CrQFrQErQDrQCrQBrQAr@rA&A%11Hr4r3rQ;rQ:rQ9rBrCrDrErFrGrHrIrQ1rQ0rOrNrMrL%NORMMLKJIHGFDR6CBREA@?>=<;:987654321&H%11RO(0%11S>&Q4%11RN%Q677RF5RE3RG1%S83QKR?1&D(1'6%12S;S;(5%S<2SIQ;%R;21R8%34S?S?12+Q8%S82S=1%64SBSBS>1(3%119%<3:31%=3;71%?31S?S8&F%13SBSAS:%RA2SCS;%RO4SDS<RN>&Ov?&Q3vQG&Q1%RN2R7R6%211vRI%63521%9381SF%RE2;1%RF2=1%RG2?1%RH2B1%RI2Q31%RJ2R<1%RK2RD1qSHT=1%S12T>1qSNRO1%S32S01qS4TL1%S52TM1qS0TN1%S72TO1qRLU01%S92U11qT4S;1&RKrQ@%TI2U61%TB21T?%42U81rQ?&@%11S5%RF11rQ8rQ7rQ6rQ5rQ4rQ3rQ2&N%A2UE1rKrJ%S;ORH@?T8T>U2RNRMRLRI<;:98765RC3RBRAR@R?R>21RDRERFRG+c_QD%F2UJ1%S?73TI1THR<U7R:%T53U9I1p0T71p0T:1p0TB1p0TI1p0U@1pSFUH1pS>UM1pHV01pT6V41pT:V51pTBV61pTFV71pTJV81pTLV91pU0V:1pU4V;1pU8V<1pU<V=1pU@V>1pSDV?1pV>V@1pV:VA1pV8VB1pV6VC1pV4VD1pT@VE1pT>VF1pU>VG1pU:VH1pU6VI1pU2VJ1pTNVK1pTHVL1pTDVM1pS<VN1pS:VO1pS8W01pS6W11pS2W21pRNW31pT<W41pT8W51pV2W61pV0W71pUNW81pV<W91pSBW:1pUBW;1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 7%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 15%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 16%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 17%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 18%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 19%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 26%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 27%nat 0%nat).
Variable gw : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 28%nat 0%nat).
Variable s9v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 29%nat 0%nat).
Variable s8v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 30%nat 0%nat).
Variable s7v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 31%nat 0%nat).
Variable s6v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 32%nat 0%nat).
Variable s5v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 33%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 34%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 35%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 36%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 37%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 38%nat 0%nat).
Variable rav : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 39%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 40%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 41%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rfin_walk) 42%nat 0%nat).
Lemma rfin_walk : ltac:(sec_stmt2 constr:(SEC_T_rfin_walk) 43%nat 0%nat).
Proof using MR MSL MASK CLO sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc junk.
intros HG FR ST LO MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
unfold meta_cells in CH. rewrite <- HG in CH.
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
assert (P2 : 0 < 2 ^ k <= mask).
{ destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
(pose_ceil; unfold rta_frame, RSSP_GUARD in *).
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
step.
lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
(meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
[| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
| reflexivity | cbn; tauto ];
rewrite HG in H;
pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
end.
step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. step. step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
step.
rewrite ?LB in MR1.
eapply evt_mono.
{ eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
[exact MR1 | assumption | exact FR | exact ST | pose_ceil; lia | lia | exact MU | exact WM]. }
cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End SE.
End FIN.
End CEIL_WRAP_1.
