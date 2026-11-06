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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_ntf_F () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_F."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_ntf_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "0F"; "4bvmap"; "0RUNp"]; ["5fm_facts"; "6seq_st"; "7fm_st"; "8mw_ok"; "9meta_slot"; "9meta_word"; "9wz"; "9zeros"; ":C8"; ":cell"; ":cells_bytes"; ";evt"; "<mkR"; "<munch"; "<stk"; "<wmono"]; ["=MS"; ">mem_inv"; "?alloc_ceiling"; "@rw_cells"; "Aaptr"; "Ac_seq"; "Aconc"; "Actx"; "Aget_meta_rec"; "Aghdr"; "Am_maplen"; "Am_mem"; "Am_sizeclass"; "Ameta"; "Amstate"; "Aoptr"]; ["Arecord_seq"; "Aregion"; "As_groups"; "As_regions"; "As_shadow"; "Ashadow"; "Astep_seq"; "Brsegs"; "Crntf_frame"; "Drntf_ret_post"; "ERCTX"; "ERSSP_GUARD"; "Ermrep"; "Fseg_rom"; "Gadd"; "Gle"]; ["Glt"; "Gmul"; "Gsub"; "0a1"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0g"; "0gp"; "0junk"; "0lo"; "0m"; "0m0"]; ["0mr"; "0ns"; "0p"; "0ra"; "0raw"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2o"; "0s3"; "0s3o"; "0s4"; "0s5"]; ["0s6"; "0s7"; "0s8"; "0s9"; "0sc"; "0sp"; "0st"; "0st0"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "IN_countable"; "IZ_countable"; "Iprod_countable"; "Jprod_eq_dec"; "Kgmap"]; ["Leq_dec"; "Meq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rntf_seq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_F "XF'S9yR0%211&>y5%2213yQ0%711'5y8%:11%311p0:1'3%114'Q>&Q4'<'Q=&Q8r6r5%3221&QLv?r7r?%43321&Q1&QGr@%3221&Dr9r8%3221&Cr4%211'9&Q<%11D%33I81&Q?&Q;%11I(1r:%22Q01%:3641'8&QOz%221D&R0+X0%22G1%7241&@r>r=%3221rQ=&S8&QK%22R01%K3R041'S?';&S@&S;'QA%544321&QC%11Q<rA%311%Q63531'QE%<4;:91&QD%116rB%311%Q=3531&S>&SA%24CBR61&S=&S<%26FEDR941'Q9%I4R<521&QB%11<rC%311%QJ3531&M(2'7%12RDRD(6&R2&S:rQH%22S91+S0%5221%74RLRL13&QJ&QN+m0%2231%<4S1S141(4%11?%B3@31%C3A91rLrK%G3321&OrM%23RO15&Q3rQJ%G2SN1-S0%B221&QHrGrHrIrJ%57S?@4321?%;4S;=71&NrNrQK%Q42T;1%N21=%54SA4R31&Q2%11SH%RN21QOrQM%Q;2TB1%Q=21Q9%S22QF1&K&QIrOrQNrQLrQ@rQ?rQ>rQ<rQ;rQ:rQ9rQ4rQ3rDrQ2&B&ArErF%3321Q5%521Q7&Q6%12Q8Q:%S?2U=1&R1&Q:%11RB+TP0%4221%SE2UC1%NITMMLQ3KQ;QJQNQMJIHSGGFEDCBAQ?@:71&Q0&LrQO%RA2UHQ0%R;21QJ%SL2UJ1rQIrQG%B2QIQJ%T02UN1%T12UOG%T22V0IrQFrQErQDrQCrQB%T82V6RIrQArQ8rQ7rQ6rQ5%FOEBQKQCR2R?AS4@>=<;:98765QBQAQ@T?Q?Q>Q=Q<4321+c`l4%T@2V>1(0%11V?rQ1&QM%11UG%O78QC6QB431%R03UIQ11p0R21p0R71p0R;1p0RB1p0RO1p0S31p0SL1p0T:1p0TB1p0TN1p0U41p0U91p0UB1p0UJ1p0UO1p0V31p0V81p0V=1tU2VGVC1pTLVI1pU4VJ1pV:VK1pU6VM1pTFVN1pV>W01pV@W11pULW?1pUHW@1pUFWA1pU>WB1pU:WC1pTJW81pTNW;1pU0W<1pTDWB1pLWE1pWBWI1pW@WJ1pW>WK1pW<WL1pUDWM1pUBWN1pV8WO1pV6X01pV4X11pV2X21pV0X31pUNX41pUJX51pTBX61pT@X71pT>X81pT<X91pT:X:1pU@X;1pU<X<1pW:X=1pW8X>1pW6X?1pWDX@1pTHXA1pV<XB1pU8XC1").
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(pose_ceil; unfold RCTX, rntf_frame in *).
st1. rewrite ?(unsigned_lit sc) by lia. st1.
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
pose proof (rw_cells_store_ok_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (954560 + 912)) C6 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish (954560 + 912) [b8 ns] FR ST MU WM SOK.
set (st1 := upd_ctx (set_seq ns) st) in MR1.
st1.
assert (JOIN : forall m2 (a1' : word),
rmrep (seq_st ns sc st) m2 -> mem_inv rsegs m2 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (954560, 954560 + 928)] m0 m2 -> wmono rsegs m0 m2 ->
stk rsegs m2 lo (bv_unsigned sp + -96) -> rw_cells rsegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 (wz canary_val); C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 954560) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c39c) fc None m2 (seg_rom rsegs))).
{ intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
rmeta_chunk MR2 MS2 CH.
assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1. st1. clear CH.
rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
eapply evt_mono.
{ eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | pose_ceil; lia | lia | idtac].
unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
intros ms' PO. unfold rntf_ret_post in PO |- *.
destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
do 14 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans.
- apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
- eapply rpres_except_mono; [exact PE|]. intros a Ha.
eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
if_cases K; zify_cond K.
-
assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
- assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
st1.
pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_store_ok rsegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (954560 + (sc + -7) + 848)) US
ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
clear US.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish (954560 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
eapply JOIN; try eassumption.
unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
unfold upd_ctx. cbn. reflexivity.
Qed.
#[using="Type"] Lemma zeros32_cells : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_F "J'9'3'S9y8%211%411&J(2'I(H&S8yR0z%3221%511(4%118%:3931%;3:41%<3;51%=3<61%?11&GuQ0%211%I3D41").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rntf_top : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_ntf_F "Y3'S9yR0%211&>y5%2213yQ0%711'5y8%:11%311p0:1'3%114'Q>&Q4'<'Q=&Q8r5r4%3221&QLv?r6r>%43321&Q1&QGr?%3221&Dr8r7%3221&C%11@'9&Q<%11D%33H71&Q?&Q;%11C(1r9%22O1%:3641&:&Q:%11Az%?3Q421%511'8&QO&Q5&Q7r=%211%411%62:1&R0+X0%2241%;241&@%12Q:9rQ>&S8&QK%22R71%Q33R741'S?';&S@&S;'QA%544321&QCr@%211rA%411%Q?3631'QE%=4<;:1&QD%116rB%311%QF3531&S>&SA%24DCR>1&S=&S<%26GFERA41'Q9%J4RD521&QB%11<rC%311%R33531&M(2'7%12RLRL(6&R2&S:rQI%22SA1+S0%5221%74S4S413&QJ&QN+m0%2231%<4S9S941(4%11?%B3@31%C3A91rLrK%G3321&OrM%23S715&Q3rQK%G2T61-S0%B221&QHrGrHrIrJ%57SG@4321?%;4SC=71&NrNrQL%Q42TC1%N21=%54SI4QL1&Q2%11T0%S121QBrDrQN%Q<2TK1%Q>21Q:%S6241&K&QIrOrQOrQMrQ@rQ?rQ=rQ<rQ;rQ:rQ9rQ4rQ3rErQ2&B&Q@rF&QF%11Q6%4231%621Q9&Q6%12Q:Q<%SB2UG1&R1%T81Q0+TP0%3221%SG2UL1%NIU6MLQ3KQ<QKQOQNJISIHGFEDCBAQ@@961&Q0&LrR0%RB2V1Q0%R<21QK%SN2V31rQJrQH%A2QJQK%T22V71%T32V8H&F&E%11QB%311rQFrQErQDrQCrQB%T=2VBRMrQArQ8rQ7rQ6rQ5%IOHEQNQFR6RCDS8CA@<;:98765QEQDTDQCQBQAQ@Q?4321+c`i4%TE2VJ1(0%11VKrQ1&QM%11V3%Q278QF6QE431%R33V5Q41p0R51p0R;1p0R?1p0RF1p0S31p0S71p0T01p0T>1p0TF1p0U31p0U91p0U<1p0UI1p0V01p0V81p0V=1p0V@1p0VE1p0VJ1tU2W4W01pTLW61pV:W71pU6W91pTFW:1pV>W<1pV@W=1pULWK1pUHWL1pUFWM1pU>WN1pU:WO1pTJWD1pTNWG1pU0WH1pTDWN1pLX11pWBX51pW@X61pW>X71pW<X81pUDX91pUBX:1pV8X;1pV6X<1pV4X=1pV2X>1pV0X?1pUNX@1pUJXA1pTBXB1pT@XC1pT>XD1pT<XE1pT:XF1pT8XG1pU@XH1pU<XI1pW:XJ1pW8XK1pW6XL1pWDXM1pTHXN1pV<XO1pU8Y01").
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(pose_ceil; unfold RCTX, rntf_frame in *).
st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.
pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
st1. clear RDS. st1.
st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
-
st1.
replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | pose_ceil; lia].
-
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (rw_cells_of_u8arr rsegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
replace (954560 + 848) with 955408 in UB by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(954560 + 848, 954560 + 880)]%Z mX) as MUz; pose proof (wmono_refl rsegs mX) as WMz end.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UA' : u8arr rsegs mX (RCTX + 848) (zeros 32))
by (apply (u8arr_of_rw_cells rsegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
clear UB.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
{ eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }
st1. st1.
replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
replace (conc st p) with (conc stz p) by reflexivity.
change (get_meta_rec st g) with (get_meta_rec stz g).
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | pose_ceil; lia
| apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.
End CEIL_WRAP_1.
