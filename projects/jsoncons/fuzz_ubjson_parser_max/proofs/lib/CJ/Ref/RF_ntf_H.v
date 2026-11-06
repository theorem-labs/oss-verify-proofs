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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F F_ntf_H MallocKit_A3 MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_ntf_H () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_H."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_ntf_H.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_ntf_H.CEIL_WRAP_1.ENTRY."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1false"; "1list"; "1option"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "3Z"; "0F"; "0RUNp"; "4sxv"; "5ntf_cond"; "6mw_ok"]; ["7meta_word"; "7wz"; "8evt"; "9mkR"; "9stk"; ":MS"; ";rsegs"; "=rmid_ctx"; "<rentry_post"; ">RCTX"; ">RSSP_GUARD"; ">rmrep"; "?bit"; "?conc"; "?get_meta_rec"; "?m_avail"]; ["?m_freeable"; "?m_freed"; "?m_last_idx"; "?m_sizeclass"; "?mask_upto"; "?meta"; "?okay_to_free"; "@seg_rom"; "Aadd"; "Ale"; "Alor"; "Alt"; "Amodulo"; "Apow"; "Ashiftl"; "Ashiftr"]; ["0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0g"; "0gp"; "0i"; "0junk"; "0lo"; "0m"; "0m1"; "0mr"; "0ra"]; ["0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s2x"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "BZ_to_bv"]; ["Bbv"; "Bbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs).
Definition rentry_cases (ms' : machine_state) : Prop :=
(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x9b3f4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x9b1d8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x9b29c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x9b230 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x9b1ac (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.
Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.
Lemma meta_word_sc52 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "I'Q5&?r1%211'7':&Q?&RAyR0&R?&Q>&@r2%211+QD%5221%7281%:291+QJ%=221&Q3%119%B3A31p0D1pSNH1").
Proof. intros mr.
intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "A'Q5&?r1%211'7':&Q<&@r2%211+Q0%5221&Q2%115%:3931p0<1pSN@1").
Proof. intros mr.
intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).
Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.
Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96) /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.
Lemma rmaskw_zero : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "E&8'7':&Q:&=&Q1&NvR>vQG%3221%511%711&O%114%:11%<241z%@3?21%?285%B3A13%D231").
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
Lemma rmaskw_range : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "H'6&Q9z&Q:&=&Q1&NvR>vQG%3221%511%711&O%114%:11%<241%?2>1&Q;&Q=+2+R0%3221%5271%G271").
Proof. apply lor_range64; apply sxv_range. Qed.
Ltac rpost_common MU WM MI ST FR MR m1 junk :=
apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].
Section SE.
Local Abbreviation SEC_T_rntf_notall := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "SH'R@yR0%211'4y8%511%311p051'3%114&Gr2r1%3221'7'1&>vR>vQGvQI%43321(2%83721&B&F&HvQOvR=vQHvRIvR0vR1vR4vR6vR7vR8vR9vR:vR;vR<vR2vR3v;vQFvQKvQL%EGDCBA@?>=<;:9876543MLK21&E&C&R?&Q8&RA%12QCI-S0%4221%62QF1r@r?r>&J%;2QK1&M%12Q=Q<%>2QN1&A&=&Q=+2%221QA%411%611&Q3&N%12QHQG%311%J2R:1&Q:&Q1%115%>11&O%118%A11%7241%Q32RC1r=r<r;r:r9r8r7r6r5%Q>OR4Q7R2R1Q6Q5Q4R0Q2OHC:98765QMQLQKQJQIQHQGQFQE4321+c\^@%Q?2RO1(0%11S0r4&Q7%11R=%QG78QL6QK431%R@3R?QI1p0RB1p0RL1pSFS11pSLS41pUBS:1pU@S;1pU>S<1pU<S=1pT<S>1pS<S?1pS:S@1pS8SA1pS6SB1pU:SC1pU8SD1pU6SE1")) (only parsing).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 0%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 1%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 2%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 3%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 4%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 5%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 6%nat 0%nat).
Variable s2x : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 7%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 8%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 9%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 10%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 11%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 12%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rntf_notall) 13%nat 0%nat).
Lemma rntf_notall : ltac:(sec_stmt2 constr:(SEC_T_rntf_notall) 14%nat 0%nat).
Proof.
intros (MU & WM & MI & ST & FR & MR) HC.
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). pose_ceil. pose_ceil.
st1. rewrite ?(unsigned_lit (conc st g)) by lia.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
-
rpost_common MU WM MI ST FR MR m1 junk.
left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
-
assert (M0 : mask = 0) by (apply MZ; lia).
rpost_common MU WM MI ST FR MR m1 junk.
right; left. split; [exact HC|]. split; [exact M0|].
do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rntf_fge := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "T3'R@yR0%211'4y8%511%311p051'3%114&Gr2r1%3221'7':&Q8&Q:&Q1&NvR>vQG%3221%511&O%113%9231&LvQI%211%>241&Q4&Q2%11;%311%E3D51'1&Q6%12BA(5%J3421&B&F&HvQOvR=vQHvRIvR0vR1vR4vR6vR7vR8vR9vR:vR;vR<vR2vR3v;vQFvQKvQL%EGDCBA@?>=<;:9876543Q<Q;Q421&E&C&R?&RA%12R4H-S0%QG221%52R71r@r?r>&J%:2R<1&M%12QKQJ%=2R?1&A&=&Q=+2%221QI%411%611&Q3%11R3%G2RI1%91R4%:1R3%R<221%K2RM1r=r<r;r:&I%Q12S31r9r8r7r6%Q7OQMQ1QKQJQ0ONQILIB?;:9875QFQEQDQCQBQAQ@Q?Q>4321+c\\8%Q82S:1(0%11S;r5&Q7%11R6%Q@78QE6QD431%R93R8QB1p0R;1p0RA1p0S81pSFS=1pSLS@1pUBSF1pU@SG1pU>SH1pU<SI1pS<SJ1pS:SK1pS8SL1pS6SM1pU:SN1pU8SO1pU6T01")) (only parsing).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 0%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 1%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 2%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 3%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 4%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 5%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 6%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 7%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 8%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 9%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 10%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 11%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rntf_fge) 12%nat 0%nat).
Lemma rntf_fge : ltac:(sec_stmt2 constr:(SEC_T_rntf_fge) 13%nat 0%nat).
Proof.
intros (MU & WM & MI & ST & FR & MR) HALL OKT.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
(pose_ceil; unfold RCTX in *).
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
rmeta_chunk MR MSL CH.
st1. clear CH.
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
- destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
specialize (G50 HC ltac:(congruence)).
st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (950384 + 80 + 8 * sc)) with (Z_to_bv 64 (950384 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.
st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
+ pose proof (NINJ ltac:(lia)) as ->.
rpost_common MU WM MI ST FR MR m1 junk.
do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
+ assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
rpost_common MU WM MI ST FR MR m1 junk.
do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
- st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
rpost_common MU WM MI ST FR MR m1 junk.
do 2 right; left. split; [exact HC|]. split; [exact NX|].
do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rntf_okchk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_H "T3'R@yR0%211'4y8%511%311p051'3%114&Gr2r1%3221'7':&Q8&Q:&Q1&NvR>vQG%3221%511&O%113%9231&LvQI%211%>241&Q4&Q2%11;%311%E3D51&9&Q0%11@z%J3I21%511&B&F&HvQOvR=vQHvRIvR0vR1vR4vR6vR7vR8vR9vR:vR;vR<vR2vR3v;vQFvQKvQL%EGDCBA@?>=<;:9876543Q=Q<Q521&E&C&R?&RA%12R5H-S0%QH221%52R81r?r>r=&J%:2R=1&M%12QLQK%=2R@1&A&=&Q=+2%221QJ%411%611&Q3%11R4%G2RJ1%91R5%:1R4%R=221%K2RN1r<&@%11R<%O2S21r;r:r9r8r7r6%Q7OQMQ1QKQJQ0ONQILIB?;:765QGQFQEQDQCQBQAQ@Q?Q>4321+c\VH%Q82S;1(0%11S<r5&Q7%11R6%Q@78QE6QD431%R93R8QB1p0R;1p0RB1p0S91pSFS>1pSLSA1pUBSG1pU@SH1pU>SI1pU<SJ1pS<SK1pS:SL1pS6SM1pU:SN1pU8SO1pU6T01")) (only parsing).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 0%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 1%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 2%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 3%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 4%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 5%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 6%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 7%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 8%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 9%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 10%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rntf_okchk) 11%nat 0%nat).
Lemma rntf_okchk : ltac:(sec_stmt2 constr:(SEC_T_rntf_okchk) 12%nat 0%nat).
Proof.
intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose_ceil.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).
st1. st1. st1.
st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
{
eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
assert (SC48 : sc < 48) by lia. clear K2.
assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
specialize (USG SC48).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (RS' : ov_read_bytes rsegs m1 (Z_to_bv 64 (110048 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (110048 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.
assert (K690 : forall (t0' : word),
m_maplen mr <> 0 ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 110048) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 950384) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b12c) fc None m1 (seg_rom rsegs))).
{ intros t0' MLNZ.
assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
assert (GSR : 0 < get_stride mr < 2^64).
{ unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }
st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
replace (110048 + sc * 2) with (110048 + 2 * sc) by lia.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
{ eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
assert (OKF : okay_to_free st g =
if negb (optr_eqb (m_next mr) (Some g)) then true
else if negb (is_bouncing sc st) then true
else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
{ rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }
rmeta_chunk MR MSL CH.
st1. clear CH.
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
{ assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
pose proof (NINJ ltac:(lia)) as Enx. subst nx.
rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.
st1. rewrite ?(unsigned_lit sc) by lia. st1.
st1. if_cases K7; zify_cond K7.
{ assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.
st1.
pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
pose proof (BND (sc - 7)) as BR.
replace (Z_to_bv 64 (950384 + 880 + (sc - 7))) with (Z_to_bv 64 (950384 + (sc + -7) + 880)) in RDB by (f_equal; lia).
st1. clear RDB. st1.
st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
{ replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
replace (wa (950384 + 464 + 8 * sc)) with (Z_to_bv 64 (950384 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.
st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
{ replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.
st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
- replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
- replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (K678 :
(m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 110048) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 950384) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b114) fc None m1 (seg_rom rsegs))).
{ intros COND.
assert (STR : get_stride mr = 16 * size_class sc).
{ unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
- replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
apply K690. lia. }
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
{ apply K678. left. lia. }
st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
{ apply K678. right. lia. }
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
apply K690. lia.
Qed.
End SE.
Section SE.
Variables (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word).
Lemma rntf_entry : rmrep st m -> stk rsegs m lo (bv_unsigned sp) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b074) fc None m (seg_rom rsegs)).
Proof.
intros MR ST.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR.
pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof rmaskw_range as MWR'.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & _) & _).
(pose_ceil; unfold RGOT_SSP, RSSP_GUARD in *). unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MR G4 G5.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
rmeta_chunk MR1 MSL CH.
st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
st1. rewrite (meta_word_freeable _ MW).
st1. rewrite (meta_word_sc52 _ MW).
clear CH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
st1. rewrite addiw_m1_word.
pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
- assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
-
apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End SE.
End ENTRY.
End CEIL_WRAP_1.
