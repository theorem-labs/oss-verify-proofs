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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocModel_B F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_ntf_C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_ntf_C.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5qa_facts"; "5qpath_st"]; ["6meta_slot"; "7cell"; "7cells_size"; "8evt"; "9mkR"; "9stk"; ":MS"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">active"; ">aptr"; ">conc"; ">get_meta_rec"; ">m_next"; ">m_prev"]; [">mstate"; ">optr"; "?rsegs"; "@rqpath_post"; "Armrep"; "Bseg_rom"; "Cadd"; "Cle"; "Clt"; "Csub"; "0a1"; "0a3"; "0a5"; "0a6"; "0a7"; "0fc"]; ["0fr"; "0g"; "0gp"; "0lo"; "0m"; "0q"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"]; ["0s7"; "0s8"; "0s9"; "0sc"; "0sp"; "0st"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"]; ["0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | tauto ]]);
clear MUq WMq CH end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a0 a2 a3 a5 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c448) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.
Section SE.
Local Abbreviation SEC_T_rconc_meta_inj := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_C "Q4'Q0'R7yR0%211'4y8%511%311p051&K&Q4v=r4r3%43321&@r5%2214r6%4216'6':&Lr7%221<%3229%63521%73B;9p021p0:1p0=1p0A1pS<G1pS4H1pS:J1pT<Q31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 2%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_rconc_meta_inj) 3%nat 0%nat).
Lemma rconc_meta_inj : ltac:(sec_stmt2 constr:(SEC_T_rconc_meta_inj) 4%nat 0%nat).
Proof using Type st m g q.
intros MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
- rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
- exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rntf_qpath := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_C "VE'R7yR0%211&<y5%2213yQ0%711'4y8%:11%311p0:1'2'A%211'Q0&K':&Q4v=r4r6%43321&G&Q2r7%3221&@r5%2281'5&Q7z%2215&Q8+Q@%2281%7241'9'6&Q1&Jr8%221F(0%11M%73631'7r9%821H(1r1%22Q41%>3=41%K263%I221qS<Q81%:2Q91%D2<1&8%:2Q<B%F3E<1%311&N&Mr:%221B%411%M3L1G&O%114%Q03O1J%Q:241p0;1&>%13:Q1K&Ir=&Q6&R8rQ:%22RA1-S0%5221r<%94QM821'3&B%11;uS0%QC3421&Er?rQ<%?2RN1%A21=%54R84O1&H%11R?r;%R5221&Q9rQ>%H2S71+S0%4221%R;2F1&C&Q3rQ@rQ?rQ=rQ9rQ8rQ7rQ2rQ1rQ0rOrNrMrLrKrJrIrQ;rQ4rQ3rHrGrFrErDrCr@rB&?r>%2341Q>rA%Q0Q2ONQ6MLKJIHGFEDCBA@Q??QL>=<;:987QO6Q@521&F&D&R6%R12T@Q2%R321QO%32TB1&L%12>QH%62TE1%72TF=rQ6+L%R;251%;2TJ1rQ5%>OQ?:QFQ=QOOR<Q<Q;7Q:6521NMQ9Q8Q7Q6Q5Q4Q3Q2Q1Q0LKJI+c`a<%?2TN1%SC1TN&Q5%11T9%E76N4M3K1%QH3T;G1p0QJ1p0R11p0R61p0R=1p0RC1p0RN1p0S11p0SA1p0T71p0T@1p0TD1p0TI1pS8TO1pT8U01pS4U21pT<U41pS2U61pS:U:1pS0U@1pHUC1pU0UG1pTNUH1pTLUI1pTJUJ1pSFUK1pSDUL1pT6UM1pT4UN1pT2UO1pT0V01pSNV11pSLV21pSJV31pSHV41pRNV51pRLV61pRJV71pRHV81pRFV91pSBV:1pS@V;1pTHV<1pTFV=1pTDV>1pU2V?1pS6V@1pT:VA1pS>VB1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 27%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 28%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 29%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 30%nat 0%nat).
Variable fr : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 31%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 32%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 33%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 34%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rntf_qpath) 35%nat 0%nat).
Lemma rntf_qpath : ltac:(sec_stmt2 constr:(SEC_T_rntf_qpath) 36%nat 0%nat).
Proof using Type ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fr st g sc lo.
intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
(pose_ceil; unfold RCTX in *).
st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
replace (Z_to_bv 64 (954560 + sc * 8 + 80)) with (wa (954560 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
st1. clear RDA.
st1. if_cases K; zify_cond K.
{
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. pose_ceil. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
unfold qpath_st. rewrite HA, optr_eqb_refl.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
assert (HA : active st sc <> Some g).
{ intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
destruct (GNP HA) as [GN GP].
assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
{ unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
rewrite QS. clear QS K.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
clear CH.
st1. destruct (active st sc) as [hd|] eqn:HD.
-
destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
assert (NEh : hd <> g) by congruence.
pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).
rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1. clear CHh.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
st1. clear CH. st1.
rmeta_open (conc st hd) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
-
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (954560, 954560 + 928)]%Z m) as MU.
st1.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.
pose proof MRb as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives stB) sc (Z_to_bv 64 (954560 + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
end.
assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3 SOK.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
pose proof (length_le8 (pw stB (Some g))) as L8;
apply (rw_cells_frame rsegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
apply (stk_write rsegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs) in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs) in HI;
[| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok rsegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
end;
remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
end.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.
End SE.
End CEIL_WRAP_1.
