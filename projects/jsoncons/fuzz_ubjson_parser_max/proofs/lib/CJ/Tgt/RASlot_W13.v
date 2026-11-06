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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W13 ASlot_W14.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W13 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W13."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1cons"; "1fst"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "0F"]; ["4machine_state"; "5bvmap"; "0P"; "0RUNp"; "6enf0_st"; "6pp"; "7mw_ok"; "8meta_slot"; "8ticks_ok"; "9evt"; ":mkR"; ":munch"; ":wmono"; ";MS"; "<mem_inv"; "=aptr"]; ["=c_mmap_counter"; "=conc"; "=ctx"; "=get_meta_rec"; "=ghdr"; "=m_set_maplen"; "=mstate"; "=put_meta"; "=region"; "=s_groups"; "=s_regions"; "=wr8"; "=zero_hdrs"; ">rsegs"; "?RMLOCK"; "?RSIZE_CLASSES"]; ["?rmrep"; "@seg_rom"; "Aadd"; "Aland"; "Ale"; "Alor"; "Alt"; "Amul"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0a0"; "0a1"; "0a1'"; "0a2"]; ["0a2'"; "0a3"; "0a3'"; "0a4"; "0a4'"; "0a5"; "0a5'"; "0a6"; "0a6'"; "0a7"; "0a7'"; "0b"; "0cnt"; "0fc"; "0g"; "0gp"]; ["0i"; "0idx"; "0j"; "0k"; "0m'"; "0m1"; "0mC"; "0mC0"; "0ms'"; "0mt"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"]; ["0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "CN_countable"; "CZ_countable"; "Cprod_countable"; "Dprod_eq_dec"]; ["Egmap"; "Feq_dec"; "Geq_dec"; "0stride"; "0stz"; "0szc"; "0t0"; "0t0'"; "0t1"; "0t1'"; "0t2"; "0t2'"; "0t3"; "0t3'"; "0t4"; "0t4'"]; ["0t5"; "0t5'"; "0t6"; "0t6'"; "0tp"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.
Section SE.
Local Abbreviation SEC_T_rnenf_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W13 "V6'S:yR0%211&Ay5%2213yQ0%711'9&QDz&Q0&Q2vS8%211%411%7261&QF&QI+2+Q0%3221%5271%?271&N&Q=vRE%3221&I'@';'5y8%Q111%311p0Q11':r@&M&J&S9+ccgH%22Q91rQ>rQ=rQ<r?r>r=rQ8rQ7vB%<2QC1r<r;r:r9r8r7r6&QB&Q?&QGvRB%221Q=%5241%J2R11rOrNrM&Q>%O2R61rLrK%Q22R9=rJrIr5r4r3r2%Q:OQ7Q6Q5Q4Q3Q2Q1Q0OMLKJIHGF?>=<:987654321rDrC(0%11RCr1&QA%11QO%QC787Q?6431%QF3QMQE1&K(1'7'>%2211(6&QJ+3%22Q@1%44661QA(4%117%;3831%=31R>B&L%13RAR@D%RC2RBE&Q@vC&DvR>vR;vRA%44S5321%7361M&H%113%S>231%S?2<1%S@2>1%SA2A1%SB2Q01qU:RH1%RN2RI1qX8SK1%S02SL1qX4SM1%S22SN1qX0SO1%S42T01qWLT11%S62T21qTFT31%S82T41qTBT51%S:2T61qT>T71%S<2T81qT:T91%S>2T:1qT6T;1%S@2T<1qT2T=1%SB2T>1qSNT?1%SD2T@1qWHTA1%SF2TB1qWDTC1%SH2TD1qW@TE1%SJ2TF1qUBSL1rHrG%SD2TKQ;rFrErBrA%SI2U0S2%SKORORNRMRJRIRGRF87654R@R?32SM1SDSCSBRKS=S<RHS;S:S9S8S7RE+ccf<%SL2U31%SO73RG1RFR@T;R=%T:3T==1p0T<1p0TA1pTLU21pQ0U51pX6U91pX2U:1pWNU;1pWJU<1pUNU=1pULU>1pV<U?1pV:U@1pV6UA1pV4UB1pV2UC1pTDUD1pT@UE1pT<UF1pT8UG1pT4UH1pT0UI1pSLUJ1pUJUK1pUHUL1pWFUM1pWBUN1pW>UO1pX:V01pU0V11pV@V21pUFV31")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 9%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 10%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 11%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 15%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 16%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 17%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 26%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 27%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rnenf_walk) 28%nat 0%nat).
Lemma rnenf_walk : ltac:(sec_stmt2 constr:(SEC_T_rnenf_walk) 29%nat 0%nat).
Proof using o r N MR UA J HA MSL MW SCg STR SO TK ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 F fc.
intros CTR MI.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
pose proof (size_class_range j J) as SZR.
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND.
pose proof (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
pose_ceil.
set (G := conc st g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
pose proof MW as (LI0 & FB0 & SCR0 & ML0).
pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
unfold RSIZE_CLASSES, RMLOCK, RCTX in *.
step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step.
pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (110048 + 2 * j) with (110048 + j * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
pose proof (rmrep_active_read st m1 j (wa (954560 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
replace (wa (954560 + 80 + 8 * j)) with (Z_to_bv 64 (954552 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.
step. rewrite sx32_wz_sxv by lia.
step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
step.
step.
eapply evt_mono.
{ eapply (renframe_walk (Z_to_bv 64 0x9cef8) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
(pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
| |- ov_read_bytes _ _ _ _ = _ => exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
| |- _ => idtac end.
all: try (rewrite (unsigned_lit G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
- exact (so_maplen _ _ _ _ _ _ SO). }
intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
replace (fold_off off0 0) with 0 in EM |- * by lia.
rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
replace (ret_pc (Z_to_bv 64 0x9cef8)) with (Z_to_bv 64 0x9cef8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
assert (S31n : stride - 4 - N < 2^31) by lia.
assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
rewrite Z.mul_0_r, Z.add_0_r in MRr.
change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
fold P in MRr, EM. rewrite <- EM in MRr.
destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
{ rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
assert (MU : munch [(P - 3, P)]%Z m1 m').
{ rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
assert (WM : wmono rsegs m1 m').
{ rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
do 14 eexists. exists m'.
split; [unfold P, G; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
End SE.
#[using="st g b idx j mr stride B P N"] Lemma lor_192 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W13 "D'>'9&QDzr1%3221&QF+Q0%2241%8241':&QEr2+V0%3221&QB%1243%73A31p091pSHC1").
Proof. intros a. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.
Section SE.
Local Abbreviation SEC_T_renfD_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W13 "VI'S:yR0%211&Ay5%2213yQ0%711&O'>'5y8%<11%311p0<1&GvS8r3%3221&F&Q3r4%2261%411'9&QD+1%2216+Q0%4281%6231&Q@vC&DvR>vR;vRA%44E321%7361A&H%113&N&Q=r6%3221&I'@';':r2&M&JrQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2&S9&Q1r;%22Q?1%42QO1vB%62R11&QBr:%221Q;%:2R51+<%5271%=2R81rOrNrMrLrKrJ%D2R?<rIrHrGrFrErDrCrBrAr@r?r>%Q:OQ9Q8Q7Q6Q5Q4Q3Q2MKGDCBA@?>=<;:987654321r=+cci0%Q42RO1r<(0%11S1r1&QA%11QL%QE7:976431%QH3QJQG1&K(1'7%12S3S3(6+Q8%Q<2Q@1%34S7S7QA1&QJ+3%22QB1+2%42QD1%94S=S=31(4%11<%?3=31%@3>:1r9%C321H&L%13RD3J%RF2REK&Q;'=&2%132SJS0&8%134SLS2+@&QGvSC%221S5%R7241%R8261-3%R:221%Q14=T5;1&QE&QC+O%22S>1+V0%5221&Q7&Q5z%T42T8RJ%3221%53RL1SE%K3=71%SM3SL1QH%SF12%T6221%T72Q01%T82Q21%T92Q51%T:2QJ1qU:TE1%SE2TF1qUBSG1rQ1rQ0%S;2THQ=%S=2U81r8%S?2U:1%SIOSFSESDSCSBSA653S:S2S1S0RORNRMRKRJ1RIRHRGRFRERDRCRBRAR@R>R;+ccgH%SB2U=1r7%SN74SB2S<R=1R:%T43T7<1p0T61p0T;1p0T>1p0TG1p0TO1p0U51pU>U:1pTJU@1pUDUB1pTLUD1pQ0UG1pX6UK1pX2UL1pWNUM1pWJUN1pUNUO1pULV01pV>V11pV<V21pV:V31pV8V41pV6V51pV4V61pV0V71pTDV81pT@V91pT<V:1pT8V;1pT4V<1pT0V=1pSLV>1pUHV?1pWFV@1pWBVA1pW>VB1pX:VC1pU0VD1pV@VE1pUFVF1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 14%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 27%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 28%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 29%nat 0%nat).
Variable mt : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 30%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 31%nat 0%nat).
Variable mC : ltac:(sec_ty2 constr:(SEC_T_renfD_walk) 32%nat 0%nat).
Lemma renfD_walk : ltac:(sec_stmt2 constr:(SEC_T_renfD_walk) 33%nat 0%nat).
Proof using m1 r j N MR J SO TK ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mt cnt mC.
intros MST MWT CR MRC TKC MIC.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). pose_ceil.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
set (st0' := enf0_st st g b idx) in *.
assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
pose proof (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _). pose_ceil.
change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
pose proof (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
pose proof MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
pose_ceil.
rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
rmeta_open (conc st mt) MUt WMt.
step.
step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
set (w := meta_word (get_meta_rec st mt)) in *.
rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
rewrite (meta_word_mod4096 st g b idx j _ MWT).
step.
lazymatch goal with H : rw_cells rsegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
[ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
| clear MUt WMt H ] end.
set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
pose proof (land31_range idx) as L31.
assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
{ change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
[| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
by (unfold wa; f_equal; unfold P; lia).
step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
step. rewrite (unsigned_lit cnt), swrap32_small by lia.
step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
pose proof MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
rewrite <- (lor_192 (Z.land idx 31)) by lia.
rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
step. rewrite ?(unsigned_lit P) by (unfold P; lia).
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
End SE.
Lemma rzero_loop_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W13 "X<'3'>'Q6'S:yR0%211'5y8%511%311p051&Ay5%2218yQ0%<11':&QHrQ4%211&QJ&QBrQ1+1%3221rQ3%6221%;3J81'9&QDz%221=rQ2%42?1%6231%62<A&QF+TP0%22D1%;281+@&QGrQ6%2231rQ5%4221%I261vSC%C221'S@'=&SA&S<'Q8%544321&Q:%11<vS8%311%Q;3531&O&S?&SB%24=<QN1&S>&S=%26@?>R141'Q4%C48521&Q9%11L%21>%QH3421&Q@vCrQ7%3321Q0&HrQ8%211&N&Q=%2217&K(1'7%12RERE(6vB+<%R5221rQ<%QC2QD1rQ;%QE221%R:251%R;21R9%:4S0S071(4%11=%@3>31rQ9%C321H&LrQ:%23H14&I'@';r2&M&J&S9rQ?%RN21RK%32S?1rQ0rOrNrMrL%92SE8rKrJrIrHrQ@%RF2RG1%@2SL1rFrErDrCrBrA%HOQ:OQ2QIQLRMRKSES>S7DDSACBA@?>=<;:7>654321r@+cd_@%J2T61r?(0%11T8r1&QA%11QO%Q37:976431%T23Q7Q51%S:2DQ2%SO2QJ1%T021SN%QO4TETEQL1%R33R11QDrQ=%R6321;%QC3R92<%R;2R:=&Q<&EvR>vR;vRA%44S8321rQArQBrQ>%954Q6321%RM3RL1H%RJ12%SA13%TI3SC1S?%S515%TK3S71S4rQC%T@21O%TA2Q0<%TC221&<&S;r3%22U?1%T;2T<8%T<21R8%U12RL1%U73UF41%811p0:1pU6UI1%91R>%H1R?%U=3UD21p041pX<UJ1%U42E1%U52H1%U62K1%U72M1%U82Q91%U92Q;1%U:2Q=1%U;2QE1qU:UN1%RM2UO1qUBRO1%UF2QCUD%UH21RK%RM2V91%U52U6Q:%U621RN%UK2SF1%S12V=1%S22V>QJrG%S42V@6%S6OS@T7T:U;U9V3ULUEUOS184S0RORNRMRKRJ3RIRH2RD1RCRBRAR@R?R=R:r>+cci0%S82VD1r=%S<75421R=SBR:%SA3T:A1p0SC1p0SG1p0T<1p0T@1p0TD1p0TI1p0U71p0UC1p0UM1p0V21p0V41p0V<1pTLVI1pQ0VL1pX6W51pX2W61pWNW71pWJW81pUNW91pULW:1pV>W;1pV:W<1pV8W=1pV6W>1pV4W?1pV0W@1pTDWA1pT@WB1pT<WC1pT8WD1pT4WE1pSJWF1pUJWG1pUHWH1pWFWI1pWBWJ1pW>WK1pX:WL1pU0WM1pV@WN1pUFWO1pU>WK1pU@WL1pW:X51pTJX71pW<X81pU2X91pU8X;1").
Proof using MR STR SO.
induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
{ exfalso. lia. }
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). pose_ceil.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
pose proof MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
specialize (MR2 Hr' Hk ltac:(lia)).
assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
{ intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & _ & GWF).
destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
assert (E3 : stride * idx = 16 * (stride / 16 * idx)) by (rewrite E2 at 1; ring).
clear - CONTRA GE E0 E1 E3 SZI FIT. lia. }
specialize (MR2 NOG ltac:(lia)). clear NOG.
replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
[ intros u Hu Hux;
rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
exfalso; lia
| apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
apply (wmono_write rsegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
[| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
end;
clear SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
end.
step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
step. rewrite ?unsigned_lit by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
eapply evt_mono.
{ (eapply (IH (i + 1) szc cnt);
[ lia | lia | exact SZC | exact CNT | exact FIT
| rewrite s_regions_wr8; exact RGz
| rewrite s_groups_wr8; exact GRz
| exact MR2
| apply ticks_ok_wr8; exact TKz
| assumption | exact MU | exact WM ]). }
cbv beta. intros ms' (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW).
eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
split; [exact X6|]. split; [exact X7|].
intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
-
assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
apply evt_done. eexists. split; [reflexivity|].
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.
End CEIL_WRAP_1.
