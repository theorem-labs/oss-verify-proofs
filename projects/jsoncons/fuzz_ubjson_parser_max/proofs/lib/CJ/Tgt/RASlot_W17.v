(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W17.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RF_malloc_bigw RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W17 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W17."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "0G"; "4machine_state"; "5bvmap"; "0RUNp"; "6mm_ai"]; ["6mm_st4"; "7wz"; "8evt"; "9mkR"; "9munch"; "9wmono"; ":MS"; ";mem_inv"; "<c_mmap_counter"; "<ctx"; "<u32"; "=rsegs"; ">RCTX"; ">RMLOCK"; ">rmmap_entry"; ">rmrep"]; ["?seg_rom"; "@add"; "@sub"; "0a0"; "0a1"; "0a2"; "0a3"; "0a3'"; "0a4"; "0a4'"; "0a5"; "0a6"; "0a7"; "0c"; "0cnt"; "0fc"]; ["0gp"; "0m"; "0m'"; "0ms'"; "0mt"; "0nd"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"]; ["0s7"; "0s8"; "0s9"; "0sc"; "0size"; "0sp"; "0st2"; "AZ_to_bv"; "Abv"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"]; ["0tp"; "0xa"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rmm_call_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W17 "SA'R8yR0%211&=y5%2213yQ0%711'3y8%:11%311p0:1&B&K'<'7r1&F&C&R7+cd\H%22E1rQ2rQ1rQ0rOrNrMrLrKz%<2O1rA+3%?2Q21+Q2%A2Q41-1%C2Q61rDrCr@r?r>r=r<r;r:r9r8r7r6r5%Q3OQ0ONMLKJIHFECA?F>=?E<;:987654321r4&N%Q52QH1r3(0%11QJr2&Q0%11QA%Q>7:976431%QA3QBQ@1qS8QC1rJrIrHrGrFrErB%QGOQCQBQAQ@Q?Q>Q=Q<765432Q2Q11Q9Q0ONMLKJIHGFEC+cd[H%QH2R;1%QK73C1@AQL>%R13R0<1pS4R31pS0R91pFR<1pU0R@1pTNRA1pTLRB1pTJRC1pSFRD1pSDRE1pT6RF1pT4RG1pT2RH1pT0RI1pSNRJ1pSLRK1pSJRL1pSHRM1pRJRN1pRHRO1pRFS01pRBS11pR>S21pR<S31pR:S41pR8S51pSBS61pS@S71pTHS81pTFS91pTDS:1pU2S;1pS2S<1pT<S=1pS>S>1").
Proof.
intros. unfold rmmap_entry.
step. step. step. step. step. step. step. step.
apply evt_done. reflexivity.
Qed.
#[using="Type"] Lemma rmm_ret_fail_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W17 "S6'R8yR0%211&=y5%2213yQ0%711'3y8%:11%311p0:1&B&K'<'7r1&F&CrQ1rQ0rOrNrMrLrKrJrI&R7-1%22N1rHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5%Q1OQ0ONMLKJIHEDCBA@?>E=<;:987654321r4+cdf0%J2QF1r3(0%11QHr2&Q0%11Q?%Q<7:976431%Q?3Q@Q>1qS8QA1%Q>OQ<Q;Q:Q9Q8Q7Q6Q5Q1Q2Q0ONMLKJQ2IHGFEDCBA@?><+cd\H%Q62R21%QB73<19:QC7%QH3QG51pS4QJ1pS0R01pFR31pU0R71pTNR81pTLR91pTJR:1pSFR;1pSDR<1pT6R=1pT4R>1pT2R?1pT0R@1pSNRA1pSLRB1pSJRC1pRJRD1pRHRE1pRFRF1pRBRG1pR>RH1pR<RI1pR:RJ1pSBRK1pS@RL1pTHRM1pTFRN1pTDRO1pU2S01pS2S11pT<S21pS>S31").
Proof.
intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
apply evt_done. reflexivity.
Qed.
Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.
Section SE.
Local Abbreviation SEC_T_rmm_ret_ok_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W17 "U?'R8yR0%211&=y5%2213yQ0%711'3y8%:11%311p0:1&Ov>vR6r1%43321&G&Kr2%3221&B'<'8'6'7r4&F&CrQ0rOrNrMrLrKrJ&R7vR3%22Q61v;%42Q81vRA%62Q:1&Q2vQ>+1%3221%;2Q?1&?vR4%2261%?2QC1r3rErDrC-1%E2QI1&AvQE%211rBrA&M%L2R01r@%81A%91Gr?r>r=r<r;r:%Q>OQ=Q<Q;Q:Q9Q8Q7Q4Q2Q0KGFQGEDCA>=<:987654321r9+cd_@%Q92R=1r8(0%11R?&Q0%11R0%QH798653R41%QK3QNQJ1&D(1'5'9%2211(4&Q1+Q8%22QF1%4466QG1&L+<%6221+@%8241%:4<<31(2%11=%A3>31%B3?:1r7%E321RK&E%13RJ3RM%RL2RKRN&@vQD%23S2QE1%S53S41S2&H&I%114%311&JvQ=%M21R;%311%S13Q251%S32:1%S42?1%S52A1%S62D1%S72Q;1qS6SE1%S:2SF1qRDT11%S<2T21qR@T31%S>2T41qS8S@1rIrHrGrFr6%S@OS;S:S95432S6S4S2RGRFRER?R>R;R8RCR@R7R6R<R5R:R9R4R3R1QNQ31r5+cd\H%S;2T?1%SE7431SFR0RLQN%SL3SO;1p0SN1p0T31pS4T91pS0T?1pFTB1pU0TF1pTNTG1pTLTH1pTJTI1pSFTJ1pSDTK1pT2TL1pSNTM1pSLTN1pRJTO1pRHU01pRFU11pRBU21pR>U31pR<U41pR:U51pTHU61pTFU71pTDU81pU2U91pS2U:1pT<U;1pS>U<1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 6%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 7%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 13%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 14%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 15%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 22%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 24%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmm_ret_ok_walk) 25%nat 0%nat).
Lemma rmm_ret_ok_walk : ltac:(sec_stmt2 constr:(SEC_T_rmm_ret_ok_walk) 26%nat 0%nat).
Proof using SC CNT SZ ND NDA XA XA2 MST REC HC CR ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m.
intros MR MI.
pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). pose_ceil. fold G in Gpos, GC, GI, G4.
(pose_ceil; unfold RCTX, RMLOCK in *).
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
clear K.
step.
rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
rmeta_open G MUa WMa.
step.
step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
rewrite (divu_word 4080 size) by lia.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
set (d := 4080 / size) in *.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
step. rewrite (sx32_wz_sxv c) by lia.
step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
{ unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }
step_ref.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
[ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
| clear MUa WMa H ] end.
set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (954552 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
clear CX1.
st1.
rewrite le4_swrap_succ by lia.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
clear MR3.
rraw_store_finish0 (954560 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
{ unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
rewrite <- E4 in MR4.
assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
evt rsegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 954552) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d1f0) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (954560 + 12, 954560 + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 954552) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d1dc) fc None mX (seg_rom rsegs))) end.
{ intros a2v mn Hmn ->.
assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
replace (cnt + -1) with (cnt - 1) by lia.
assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
{ unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
destruct (Z.ltb_spec cnt d) as [LT|GE].
- replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec d 0) as [E0|NE0].
+ rewrite E0. reflexivity.
+ replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
= Z_to_bv 64 (mm_ai cnt size)).
{ rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
destruct (Z.eqb_spec mn 0) as [E0|NE0].
- rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
- rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
rewrite EA2.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
-
eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End SE.
End MMOK.
End CEIL_WRAP_1.
