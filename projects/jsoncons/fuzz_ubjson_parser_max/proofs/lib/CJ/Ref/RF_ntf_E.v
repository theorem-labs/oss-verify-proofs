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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_C F_ntf_E MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_ntf_E () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_ntf_E.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5sxv"; "6deq_mid"]; ["7meta_slot"; "7pw"; "7wz"; "8cell"; "8cells_size"; "9evt"; ":mkR"; ":stk"; ";MS"; "<le4"; "<mem_inv"; "=alloc_ceiling"; ">rw_cells"; "?rsegs"; "@rat9c_post"; "ARCTX"]; ["Armrep"; "BLActive"; "Bactive"; "Baptr"; "Bconc"; "Bget_meta_rec"; "Bm_next"; "Bm_prev"; "Bmstate"; "Boptr"; "Cseg_rom"; "Dadd"; "Dland"; "Dle"; "Dlt"; "Dmodulo"]; ["Dmul"; "Dpow"; "Dsub"; "0a"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0b"; "0f"; "0fc"; "0fr"; "0g"; "0gp"]; ["0lo"; "0m"; "0n"; "0nx"; "0pv"; "0q"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"]; ["0s8"; "0s9"; "0sc"; "0sp"; "0st"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]; ["0y"; "0z"]]).
Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b238) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.
#[using="Type"] Lemma rntf_deqself : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_E "UM'RFyR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2'C%211'Q8&Q3':&Q0v=r4r6%43321&J&Mr7%3221&@r5%2281'5&Q=z%2215&Q>+Q@%2281%7241'6&Q9&Q6&Q5r8%221B%411(1%12NE%93831&Lr;&Q;&RGrQ8%22QE1-S0%5221r:%94Q1821'3&D%11;uS0%H3421&Gr=rQ:%?2R21%A21=%54Q<4J1&K%11QCr9%Q9221&QBrQ<%H2R;1+S0%4221%Q?2F1&E&NrQ>rQ=rQ;rQ7rQ6rOrNrMrLrKrJrIrHrGrQ9rQ5rQ2rQ1rQ0rFrErDrCrBrAr>r@&?(Q1r<%211%431Q@6r?%Q2Q3Q1Q0Q8ONMLKJIHGFEDQACQNBA@?>=<;:9R1872QB41&H&F&RE%R32SFQ4%R521R1%32SH1&Q4%12@QJ%62SK1&O&Q@+8%22A1%R>241%<2T11rQ4rQ3%?2T48%AOQD=QKQBR4Q6RAQAQ@:4Q532Q4Q3Q21Q?Q>Q=Q<Q;Q:Q9Q8Q7Q1Q0ON+c\a@%B2T71(0%11T8&Q:%11SC%I77Q45Q33Q11%QN3SEK1p0R01p0R71p0R<1p0RC1p0RI1p0S41p0S?1p0SH1p0SL1p0T11pT2T71pU6T81pSNT:1pU:T<1pSLT>1pT4TB1pSJTH1pHTK1pUNTO1pULU01pUJU11pUHU21pTFU31pTDU41pU4U51pU2U61pU0U71pTNU81pTLU91pTJU:1pTHU;1pSDU<1pSBU=1pS@U>1pS>U?1pS<U@1pS:UA1pTBUB1pT@UC1pUFUD1pUDUE1pUBUF1pV0UG1pT0UH1pU8UI1pT>UJ1").
Proof.
intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(pose_ceil; unfold RCTX in *).
st1.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (950384 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
clear ACTS.
rraw_store_finish (950384 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
{ unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
rewrite EQ.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
Section SE.
Local Abbreviation SEC_T_rntf_deq := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_E "W;'RFyR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2'C%211'Q8&Q3':&Q0v=r6r8%43321&J&Mr9%3221&@r7%2281'5&Q=zr5%3221&Q>+Q@%2241%8241'6&Q9&Q6&Q5r:%221C%411(1%12OJ%93831&Q7r;%9218%311%>3=16&8%@3Q7<5%211r<%C3Q:?1%511r>%Q2214r?%Q4216'9&Q2r@%221:(0%11QE%O3N31'7rAr=%9221r1%N2QL1%Q63Q531%QC263%QA221qT<R01%:2R11%B2<1rQ7&A%12=;%Q?3RE31&LrD&Q;&RGrQ@%22RL1-S0%5221rC%94R8821'3&D%11;uS0%QN3421&GrFrQB%?2S91%A21=%54RC4Q=1&K%11RJ%R?21Q<&QBrQD%G2SA1+S0%4221%RE2Q<1&E&NrQFrQErQCrQ?rQ>rQ8rQ6rQ5rQ4rQ3rQ2rQ1rQ0rQArQ=rQ;rQ:rQ9rOrNrMrLrKrJrBrGrI&?(Q1%11QE%331Q>5rH%Q1Q3Q0OQ7NMLKR4JIHGFEDQ?CQLBA@?>=<;:98762Q@QH1&H&F&RE%R12TKQ3%R321QO%32TM1&Q4%12?QH%62U01&O&Q@+8%22R51%R<241%<2U61rE%:2H1%?2U91rQ<%A2U;:%COQE?QLQCR4Q8RAQBQA<6Q732Q6Q5Q41Q@RIQ?Q>Q=Q<Q;Q:Q9Q3Q2Q1Q0+c\]<%D2U>1%S;1U>&Q:%11TI%J76Q54Q43Q11%QN3TKL1p0R01p0R71p0R;1p0RB1p0RH1p0S31p0S81p0SL1p0SO1p0T21p0T61p0T:1p0T@1p0TK1p0U51p0U91p0U>1pT2UD1pU6UE1pT:UG1pT8UH1pSNUI1pU:UK1pSLUM1pT4V11pSJV71pHV:1pUNV>1pULV?1pUJV@1pUHVA1pTFVB1pTDVC1pU4VD1pU2VE1pU0VF1pTNVG1pTLVH1pTJVI1pTHVJ1pSDVK1pSBVL1pS@VM1pS>VN1pS:VO1pTBW01pT@W11pUFW21pUDW31pUBW41pV0W51pT0W61pU8W71pT>W81")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 13%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 14%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 15%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 16%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 17%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 18%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 19%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 26%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 27%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 28%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 29%nat 0%nat).
Variable fr : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 30%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 31%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 32%nat 0%nat).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 33%nat 0%nat).
Variable pv : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 34%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 35%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_deq) 36%nat 0%nat).
Lemma rntf_deq : ltac:(sec_stmt2 constr:(SEC_T_rntf_deq) 37%nat 0%nat).
Proof using Type ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fr st g nx pv sc lo.
intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(pose_ceil; unfold RCTX in *).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (950384, 950384 + 928)]%Z m) as MU.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH.
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. clear CH.
rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (950384 + 80 + 8 * sc)) with (Z_to_bv 64 (950384 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
st1. clear RDA.
assert (EQmid : deq_mid (LActive sc) g st =
if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
{ unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }
st1. if_cases K; zify_cond K.
-
assert (HA : optr_eqb (active st sc) (Some g) = false).
{ destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
-
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. pose_ceil. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
rewrite HA, optr_eqb_refl in EQmid.
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH. st1.
pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (Z_to_bv 64 (950384 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
clear ACTS.
rraw_store_finish (950384 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
rewrite <- EQmid in MR3. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSn | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.
End SE.
#[using="Type"] Lemma land_mod_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_E "H':&Q=zr1%3221'6&Q?&Q<r4r3%3221&QA+2r2%3221%9251%:282%;283%;221%>3C41p0@1pT6E1pSFF1pS8G1").
Proof. intros a b n.
intros Hn. rewrite <- !Z.land_ones by lia.
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.
#[using="Type"] Lemma act_mask_le4 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_ntf_E "QH':'5&Q=zr3%3221&Q>&QA+2+Q0%3221%5271%;271+1%<21:%=2;5%?221'6&Q?%12?9&QBr4%2219%521=%73H51'2'RFy8%211%411&I&REyR0&Q<&>r6%211&RG%726A%2271%7241%:291%<11&Br5%I21Q0%=2;1%411%B11%Q03D71p0J1p0Q31p0Q81pV4QE1pV2QF1pSHQG1").
Proof. intros f y z.
intros Hf Hy Hz. apply le4_congr.
pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
{ split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
rewrite unsigned_lit, wz_unsigned by lia.
rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b29c) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.
Section SE.
Local Abbreviation SEC_T_rntf_postdeq := (forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool), let st1 := upd_meta g clr_links stm in
rmrep stm m -> mem_inv rsegs m -> meta_slot stm g -> 0 <= sc < 48 ->
(if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
(an = true -> forall a, active st1 sc = Some a ->
meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
/\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b238) fc None m (seg_rom rsegs))) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 27%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 28%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 29%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 30%nat 0%nat).
Variable fr : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 31%nat 0%nat).
Variable stm : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 32%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 33%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 34%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 35%nat 0%nat).
Variable an : ltac:(sec_ty2 constr:(SEC_T_rntf_postdeq) 36%nat 0%nat).
Lemma rntf_postdeq : ltac:(sec_stmt2 constr:(SEC_T_rntf_postdeq) 37%nat 0%nat).
Proof using Type ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fr stm g sc lo an.
intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
pose proof (rmeta_slot_bounds stm m g MR MSL) as GB. pose_ceil.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(pose_ceil; unfold RCTX in *).
pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.
rmeta_open (conc stm g) MUg WMg.
rmeta_chunk MR MSL CH.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st1 mX)
by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUg WMg CH
end.
assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono rsegs m m' ->
rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
{ intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).
st1. if_cases K; zify_cond K.
-
destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
cbn [pd_st].
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
-
destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
cbn [pd_st].
pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
replace (wa (950384 + 80 + 8 * sc)) with (Z_to_bv 64 (950384 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.
st1. destruct (active st1 sc) as [a|] eqn:HA1.
+ destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. pose_ceil. rewrite !Hconc in AB.
munch_grow MU (conc stm a, conc stm a + 40).
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.
st1.
destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
rewrite Hconc in RD8.
st1.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
{ rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
set (y := 2 ^ (g_active_idx gh + 1)).
st1. st1. rewrite negw_word.
clear CHa. rmeta_open (conc stm a) MUa WMa.
rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
st1. rewrite sx32_wz_sxv by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
{ apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
st1. st1. st1.
set (f := m_freed (get_meta_rec st1 a)) in *.
assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act_of st1 a = y - 1).
{ unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Y1 : 1 <= y <= 2^32).
{ unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
end.
{ unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
clear MUa WMa CHa.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
- eapply rfree_fp_meta; [exact MR | exact MSL | lia].
- eapply rfree_fp_meta; [exact MR | exact MSa | lia].
- eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR2.
+
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
End SE.
End CEIL_WRAP_1.
