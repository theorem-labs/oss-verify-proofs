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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1fst"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["3N"; "3Z"; "0F"; "0Fr"; "0G"; "4machine_state"; "5bvmap"; "0RUNp"; "6span_exit"; "7sxv"; "8mw_ok"; "9meta_slot"; "9meta_word"; "9wz"; ":evt"; ";mkR"]; [";munch"; ";wmono"; "<MS"; "=mem_inv"; "=sx32"; ">Unknown"; ">aptr"; ">cell_read"; ">cellval"; ">conc"; ">g_meta"; ">get_shadow"; ">m_avail"; ">m_next"; ">m_sizeclass"; ">mask_upto"]; [">meta"; ">optr"; ">set_active"; ">set_group_active_idx"; ">span_loop"; "?rsegs"; "@rt1_regs"; "ARCTX"; "ARMLOCK"; "ARSSP_GUARD"; "Armrep"; "Bseg_rom"; "Cadd"; "Cland"; "Cle"; "Clor"]; ["Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Cpow"; "Cshiftl"; "Cshiftr"; "Csub"; "0a0"; "0a1"; "0a1'"; "0a2"; "0a2'"; "0a3"; "0a3'"; "0a4"]; ["0a4'"; "0a5"; "0a5'"; "0a6"; "0a6'"; "0a7"; "0a7'"; "0ai0"; "0b"; "0c"; "0cnt2"; "0fc"; "0g"; "0gh"; "0gp"; "0gw"]; ["0h"; "0m"; "0m'"; "0mask"; "0mn"; "0mq"; "0mr"; "0ms'"; "0o"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"]; ["0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sc"; "0sc0"; "0size"; "0sp"; "0span"; "0st"; "0st5"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"]; ["0t0"; "0t0'"; "0t1"; "0t1'"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0v"; "0w"; "0wv"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_lw_slli52_srli58_sc := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "Q0'Q@&Jr1%211'='SNyR0%211&SM&R6&SO&R5&Q4&Lr2%211%82:1%511%82<1+QD%9221%=2?1%<2@1+QJ%?221%A2C1&Q>%11=%D2F1%I3F41p0K1pV<O1")) (only parsing).
Variable mq : ltac:(sec_ty2 constr:(SEC_T_lw_slli52_srli58_sc) 0%nat 0%nat).
Lemma lw_slli52_srli58_sc : ltac:(sec_stmt2 constr:(SEC_T_lw_slli52_srli58_sc) 1%nat 0%nat).
Proof using Type mq.
intros MWq. pose proof (meta_word_range _ MWq) as WR. pose proof MWq as (LI & FB & SCR & ML).
f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite swrap32_eq'.
unfold meta_word.
Z.div_mod_to_equations. nia.
Qed.
End SE.
Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.
#[using="RUNp mr MR MSL AV0"] Lemma ravz_pre_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "S6'SNyR0%211&Fy5%2213yQ0%711'='A&SOr3%22;1vD%63521&Q3&QEvS1%3221&N'Er1&Q2&QFvSGrOrNrMrLrKrJrIrHr6&Mz%211rFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7%NKMLKJIHGFEDA@?>=<;:987654321r5&SM+ccP@%22QH1r4(0%11QJ&QK%11Q>%Q97:9653Q>1%QH3Q<Q;1qV@Q=1rG%Q<KQ;Q9Q8Q7Q6Q5Q4Q31=NMLKJIHGFEDCBA@?Q2+ccP4%>2R41%Q@73<1QK:QE8%QD3QG61p0QF1p0QK1pUHR31pQ6R61pV0R:1pXBR;1pX@R<1pX>R=1pX<R>1pVLR?1pVJR@1pW<RA1pW:RB1pW0RC1pVNRD1pU<RE1pU8RF1pU4RG1pU0RH1pTLRI1pTHRJ1pTDRK1pVHRL1pX:RM1pX6RN1pX2RO1pXDS01pUNS11pWDS21pVDS31").
Proof.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
apply evt_done. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_ravz_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "U4'SNyR0%211&Fy5%2213yQ0%711'='A&SOr3%22;1vD%63521&Q3&QEvS1%3221&N'E'>'7y8%H11%311p0H1'<r8&Q2&QFvSGrQ6rQ5rQ4rQ3rQ2rQ1rQ0rOr=&M&IvS3%211%411r7r6r5r4r2rGrFrErDrCrBrAr@r?r>%OKNMLKJIHGFE@?>=<QB;:987654321r<&SM+ccT8%22R01r;(0%11R2r1&QK%11QG%Q;7;:76431%R13QEQ=1&Q0(3'9%12R4R4(8&QL+Q8%22R41%44R9R9R51&QG+k@%6221+l@%8241%:4R?R?31(6%11=%@3>31%A3?:1%C31R<H&Q1%13R?R>J%RA2R@K&QJvGvSL%3321O%R:251%R;271%R<2:1%R=2O1qV6R?1%RE2R@1qU>S91%RG2S:1qU:S;1%RI2S<1qU6S=1%RK2S>1qU2S?1%RM2S@1qTNSA1%RO2SB1qTJSC1%S12SD1qV@S31rNrMrLrKrJrIrHr:r9%S3KS29876543R>RAR=R<R;R:R9R8R7R6R5RIR3QO21S5RCRB+ccP@%R42T21%S773RC1SIR0SCQM%SB3SE>1p0SD1p0SI1pUHT11pQ6T41pV0T81pXBT91pX@T:1pX>T;1pX<T<1pVLT=1pVJT>1pW<T?1pW:T@1pW0TA1pVNTB1pU<TC1pU8TD1pU4TE1pU0TF1pTLTG1pTHTH1pTDTI1pVHTJ1pX:TK1pX6TL1pX2TM1pXDTN1pUNTO1pWDU01pVDU11")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 14%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 15%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 16%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 17%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 18%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 19%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 20%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 21%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 22%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 23%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 24%nat 0%nat).
Variable gw : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 25%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 26%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ravz_walk) 27%nat 0%nat).
Lemma ravz_walk : ltac:(sec_stmt2 constr:(SEC_T_ravz_walk) 28%nat 0%nat).
Proof using b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0 ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw F fc.
intros HG MI. unfold rt1_regs.
pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). pose_ceil. fold G in Gpos, GC, GI, G4, G24.
pose proof (meta_word_range _ MW) as MWR.
assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
{ apply amo_aligned_intro; [pose_ceil; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
clear G4 G24.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
step.
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
step.
step. step.
assert (W8M : bv_unsigned w8 mod 32 = ai).
{ unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
set (y := 2 ^ (ai + 1)).
step. step. rewrite negw_word.
pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
step. rewrite sx32_wz_sxv by lia.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
step. if_false.
amo_step AMO.
step. if_false.
step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.
step. rewrite addiw_m1_word.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
step.
assert (AI31 : Z.land ai 31 = ai).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
{ rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
clear MUa WMa.
step. if_cases K1; zify_cond K1.
2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
clear K1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HRW : ov_read_bytes rsegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read rsegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
step. step. step.
rewrite (lw_slli52_srli58_sc mr MW).
pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
set (sc := m_sizeclass mr) in *.
step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
-
assert (NR : (7 <=? sc) && (sc <? 39) = false).
{ destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
-
assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
rewrite Z.mod_small in K2 by lia.
assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
step.
pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (954560 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
pose proof (BNC (sc - 7)) as BR.
step. rewrite ?zxb_b8 by lia.
step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
+
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
+
step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
pose proof (u8arr_store_ok rsegs _ _ _ (sc - 7) (Z_to_bv 64 (954552 + (sc + -7) + 888)) X5
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
rraw_store_finish0 (954560 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|].
split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End SE.
End AVZ.
Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.
#[using="SZ"] Lemma rspan_loop_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "U6'5'A'SNyR0%211&Fy5%2213yQ0%711'7y8%:11%311p0:1&QNzrO%3221&R0&QLrQ0&R2vSH&R3rQ2%211+2%8221%7261%:291&R4+O%2261%?241+1%@2;1rQ3%>11%C231%E217'='2&HrQ4%231DF(;%63521&Q3&QEr6%3221&N'E'>r4&Q2&OrQ7rQ6rQ5r3r2rQ1rNrMrL&M&QDrQ:rQ9%QC21Q4rQ8%54421QB%711%81QDr1&SM+TP0%22R<1rKrJrIrHrGrFrErDrCrBrAr@r?r>%Q5OQ4Q3Q2QBQ1Q0R5OR9R=NMLDCB?>=<;:987654321r=+cdPH%D2RN1r<(0%11S0r;&QK%11QF%Q@7:976431%R03QDQB1qU:S61%QE2S71qX8S81%QG2S91qX4S:1%QI2S;1qV@QK1%Q>1R5%Q?1QF&R7%S02R8RM%221RB%QC11r:%QOORCROQIS37S7QHQGQFQ8Q7Q6Q56Q=2Q9Q4Q3Q2Q1Q0ONMLKIFC1r9+cdP4%Q>2SH1r8r7%R676532J1G%R;3R>?1p0R=1p0RB1p0RJ1p0S11p0SB1p0SC1pV4SH1pUHSN1pQ8T11pXBT51pX@T61pX>T71pX<T81pVLT91pVJT:1pW<T;1pW:T<1pW8T=1pW6T>1pW4T?1pW2T@1pW0TA1pVNTB1pTLTC1pTHTD1pTDTE1pTBTF1pVHTG1pVFTH1pX:TI1pX6TJ1pXDTK1pUNTL1pWDTM1pVDTN1pWFU21pUDU31pQ6U51").
Proof.
induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
cbn [span_exit] in EX. cbn [span_loop].
rewrite Nat2Z.inj_succ in SB, CB.
pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.
step. rewrite ?wz_unsigned by lia.
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
rewrite (Z.lxor_comm (span + size - 1) span).
step. if_cases K.
-
assert (LT : Z.lxor span (span + size - 1) < 4096).
{ unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
replace (c + 2) with (c + 1 + 1) by lia.
eapply (IH (c + 1) (span + size)); try assumption; try lia.
- assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
{ intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
#[using="Type"] Lemma ai_byte_land224 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "H'A&QNzr2%3221'=&QM&R1&QOr3+O%5221r4+W0%8221%7241+X0%:221%<218%>3C18p0@1p0A1pXFF1pXHG1").
Proof. intros w v.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace 224 with (Z.shiftl 7 5) by reflexivity.
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.
Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.
Ltac ract_prefix CH w8 :=
rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
step;
let RD8 := fresh "RD8" in let L8 := fresh "L8" in
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
let W8R := fresh "W8R" in
pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
step;
let W8M := fresh "W8M" in
assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.
#[using="RUNp b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "SI'SNyR0%211&Fy5%2213yQ0%711&?'='A&QMvS3&Q?vRG%211%5241z%93821%;11&Q3&QEvS1%3221&N'E'>r5&Q2&QFvSFrQ0rOrNrMrLrKrJrI&SMvD%22Q81r4r3r2r1rFrErDrCrBrAr@r?r>r=r<r;r:%NKMLKJIHGFEBA@?>=<;:987654321r9+ccP4%G2QM1r8(0%11QO&QK%11Q>%Q8798653Q>1%QL3Q<Q:1qU2R41%Q=2R51qTNR61%Q?2R71qTJR81%QA2R91qTFR:1%QC2R;1qV@QE1rHrG&M&I%11R7%311+2%Q?2RE1r7r6%QLKQKQEQDQC:9Q;Q:Q9Q@Q8Q753Q6Q5Q4Q3Q2Q1Q0OMJ21QN+cbnL%QD2RJ1%R073QB1QAKR6I%R53R8?1p0R71p0R<1pUHRI1pQ8RL1pXBS01pX@S11pX>S21pX<S31pVLS41pVJS51pW<S61pW:S71pW0S81pVNS91pU<S:1pU8S;1pU4S<1pTHS=1pTDS>1pVHS?1pX:S@1pX6SA1pX2SB1pXDSC1pUNSD1pWDSE1pVDSF1").
Proof.
intros until fc. intros NZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _). pose_ceil.
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
step. if_cases K; zify_cond K.
2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
rewrite ?wz_unsigned in K by (apply sxv_range).
first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
apply evt_done. do 4 eexists. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_ract_next_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "UJ'SNyR0%211&Fy5%2213yQ0%711&Q6'='A&QMvS3&Q?vRG%211%5241z%93821&QA&Q=vS6%211(1r2%22A1%A3741&?r3vRL%E3F21%411&KvSKr4%3221&Q3&QEvS1%3221&N'E'>'7y8%Q=11%311p0Q=1'<r6&Q2&QFvSFrQ5rQ4rQ3rQ2rQ1rQ0rOrN&SM&Q9r<%22O1%42R01r5rKrJrIrHrGrFrErDrCrBrAr@r?%MKLKJIHGFED?>Q>QDQH=<;:987654321r>+ccP4%F2RB1r=(0%11RDr1&QK%11QD%Q87:976431%RB3QBQ:1&Q0(3'9%12RERE(8&QL&QG+R@%3221&R2+8%221QC%7241%8213%:4S0S021(6%11=%@3>31%B31R8G&Q1%13R;R:I%R=2R<J&QJvG&QB%RN2S=QF%23R21RE%5341Q0%R8271%R9291%R:2<1%R;2Q01qV6R=1%RC2R>1qU2SL1%RE2SM1qTNSN1%RG2SO1qTJT01%RI2T11qTFT21%RK2T31qV@RM1rMrLvD%R=2T91&M&I%11T1%311+2%RC2T?1r;r:r9%S1KS0RIRH=<RAR@R?R>:R=R<64R;R:R9R8R7R6R5R3R0RE321r8+cbnL%RJ2TF1r7%S775421R3SCR0%SB3SED1p0SD1p0SI1p0SN1p0T41p0T=1pV:TH1pUHTJ1pQ8TM1pXBU11pX@U21pX>U31pX<U41pVLU51pVJU61pW<U71pW:U81pW0U91pVNU:1pU<U;1pU8U<1pU4U=1pTHU>1pTDU?1pVHU@1pX:UA1pX6UB1pX2UC1pXDUD1pUNUE1pWDUF1pVDUG1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 9%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 10%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 11%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 12%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 13%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 14%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 15%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 22%nat 0%nat).
Variable Fr : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 24%nat 0%nat).
Variable mn : ltac:(sec_ty2 constr:(SEC_T_ract_next_walk) 25%nat 0%nat).
Lemma ract_next_walk : ltac:(sec_stmt2 constr:(SEC_T_ract_next_walk) 26%nat 0%nat).
Proof using b MR MSL SC Hmem Hgh AI0 ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc mn.
intros ZR GN NEn MSn MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _). pose_ceil.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _). pose_ceil.
assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.
rewrite GN in CH. cbn [oconc] in CH.
step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (954560 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (954560 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
step.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End SE.
#[using="ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W3 "VG'SNyR0%211&Fy5%2213yQ0%711'A'<&QN+1r2%3221+Q0%5231%7231z%8216&R0+X0%2291%=241r1%>271+9%7231%B231'>'='Q8&Q7&Q;vSK&4'@vRH%332M1%6251&QL&:%136Q15r3%4221%=261(Q5%11G%B3A31qV2Q81%E2Q91p0G1pVBQ;1&QA&Q:vRM%211(1&Q6vRL%3221%O3851&Q<vS6%211%Q33QH1Q?&Q3&QEvS1%3221&N'E'7y8%R911%311p0R91r5&Q2&OrQ5rQ4rQ3rQ2rQ1rQ0rO&SMvSF%22RG1rNvD%52RJ1r4rMrLrKrJrIrH&QI%>2S31&QG+R@%R0221&R2+8%221C%R4241%F2S;1&QH%H2S=1%R8225%J2S?1rGrFrErDrCrBrAr@%Q;OQ:Q9Q8Q7Q6Q5Q4Q1Q0NMR?LS=KJIHGE=;987654321r?+ccP@%Q62SK1r>(0%11SM&QK%11QO%QE798653S;1%S63QMQG1&Q0(3'9%12SOSO(8&Q9%12S9S6%S421SB%44T4T421(6%117%:3831%<31R=SI&Q1%13R@R?SK%RB2RASL&QJvG&QC&R7r=%221T>%43SF1SI%7361T4%TC291%TD2;1%TE2>1%TF2L1qV6RE1%T52RF1qU2U01%T72U11qTJU21%T92U31qTFU41%T;2U51qV@S21%RC2U8Or7%RE2U:1r8%RG2U<1r<r;%S2ORLRKRGRCRBRAR@RHR?RE75R>3QOQNQMQLQKR<R4R2R0QJQIQHQFQCH21r:+cdQ8%RM2UB1r9%S875421QFSBQD%SA3SD>1p0SC1p0SH1p0SM1p0T71p0U51p0U<1pXJUE1pUFUF1pUHUH1pQ8UK1pXBUO1pX@V01pX>V11pX<V21pVLV31pVJV41pW<V51pW:V61pW0V71pVNV81pU<V91pU8V:1pU4V;1pTLV<1pVHV=1pX:V>1pX6V?1pX2V@1pXDVA1pUNVB1pWDVC1pVDVD1").
Proof.
intros until wv. intros C2R WVR UNK GM AV0 MI.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _). pose_ceil.
pose proof MR as (_ & _ & _ & _ & GR & _). destruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl rsegs m) as WMb.
step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
set (nbv := Z.lor _ _).
step. rewrite (le1_mod nbv). mem_after_store.
pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
lazymatch goal with H : rw_cells rsegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
[ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
| ] end.
{ rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
{ lazymatch goal with H : rw_cells rsegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
{ rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }
assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
rmchunk MR2 MS2 CH.
replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
rewrite AV0 in CH.
step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.
Section SE.
Local Abbreviation SEC_T_ract_span_walk := (forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc, Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 ->
mem_inv rsegs m ->
let sc' := m_sizeclass mr in
let cnt := ai0 + 2 in
let size := size_class sc' * UNIT in
let span := UNIT + size * cnt in
let cnt1 := span_loop 300 cnt span size in
let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
evt rsegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9cc10) fc None m' (seg_rom rsegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9cbdc) fc None m (seg_rom rsegs))) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 9%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 10%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 11%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 12%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 13%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 14%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 15%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 22%nat 0%nat).
Variable Fr : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ract_span_walk) 24%nat 0%nat).
Lemma ract_span_walk : ltac:(sec_stmt2 constr:(SEC_T_ract_span_walk) 25%nat 0%nat).
Proof using MR MSL Hmem Hgh AI0 ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc.
intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _). pose_ceil.
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
pose proof (size_class_range sc' ltac:(lia)) as SZR.
unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *.
ract_prefix CH w8.
pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.
rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
step.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.
assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
step.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ =>
pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
step. rewrite zx16_wz by lia. clear SCRD.
fold cnt.
assert (SZB : 16 <= size <= 131056) by (unfold size, UNIT; lia).
assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
assert (PR : 0 <= cnt * size <= 33 * 131056) by nia.
assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
clearbody size cnt span cnt1 cnt2.
step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.
step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
replace (span + size - 16 + 15) with (span + size - 1) by lia.
step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
step.
eapply evt_cut.
{ change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
intros ms' (t0' & t1' & a6' & ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
step.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
- replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
-
step.
replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End SE.
End ACT.
End CEIL_WRAP_1.
