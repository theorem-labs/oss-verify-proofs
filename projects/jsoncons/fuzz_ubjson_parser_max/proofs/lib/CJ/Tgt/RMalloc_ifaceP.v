(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMalloc_ifaceP () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMalloc_iface."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "1None"; "1Some"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3mul"; "4Forall"; "4map"; "4repeat"; "5N"; "5Z"; "0LB"; "0RUNp"; "6blk_addr"; "6blk_id"; "6blk_size"; "6blk_slot"; "6block"; "7MFACTS_g"; "8wz"; "9mem"]; [":u64arr"; ":u64s"; ";C1"; ";C8"; ";CB"; ";cell"; "<ivl"; "<munch"; "<wmono"; "=mem_inv"; ">alloc_ceiling"; ">canary_val"; "?rw_cells"; "@RKGroup"; "@aptr"; "@cptr"]; ["@mstate"; "@r_base"; "@r_kind"; "@r_len"; "@region"; "@rkind"; "@round_up_pg"; "@s_regions"; "@s_slots"; "APState"; "Abptr"; "Aps_init"; "AreservedZ"; "Brsegs"; "Crrepfoot"; "DRAUXV_CELL"]; ["DRCTX"; "DRGOT_SSP"; "DRLIBC"; "DRMLOCK"; "DRSSP_GUARD"; "Dref_reserved"; "Drmrep"; "ERHEAP"; "Erblock_range"; "Erclient_write_ok"; "FIn"; "FNoDup"; "Gadd"; "Gle"; "Glt"; "Gmodulo"]; ["0W"; "0a"; "0auxv"; "0b"; "0b1"; "0b2"; "0blk"; "0bs"; "0g"; "0idx"; "0k"; "0m"; "0m'"; "0n"; "0r"; "0rid"]; ["0s"; "0st"; "Hlookup"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "JN_countable"; "JZ_countable"; "Jprod_countable"; "Kprod_eq_dec"; "Lgmap"; "Lgmap_lookup"; "Meq_dec"; "Neq_dec"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma rregion_addr_facts : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "R;'Q@'S4yR0%211'8y8%511%311p051'D'QD&R6vGr4r3%43321'<%=17&S2'S:&S<&S6%34=21<&S;%14?43>&QGr5%211%:6CB64>1(2r2%22E1%@3?41';&R=+TP0&QA%11G%4231'E&R?%1246z%K3421&R<&QF&QC%11Q1%311%52<1&Q:%11Q7%B231&R>%12<6'?%D1Q;%;1Q<%=11%?231+RPP0%K221+mXP0%M217%9231p0;1%Q12>1%Q22H1%Q32N1p0Q51p0QG1pUNQM1pV0QO1pUHR11pV4R:1").
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rblock_inside := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "SN'Q@'5&L%211'S4yR0%211'8y8%511%311p051'M&R5r4r3%43321&R6vGr5%33215&R:%13D73'='QD&Q>'E';'<%F15&S2'D'S:&S<&S6%34421;&S;%14643=&4&Kr7%211%43;@1&QGr:%211%@6?F;941(2%12HQ1%E3D31'QE&QB%11Q5(Q=%J3421':%12ON%QB11&Q?&S9&S=%24NLQ31&S8&S7%26Q1ONQ641%Q14Q8419%N4Q952:&QH%11H%Q76;=43L1(9r2r1%34Q@Q?21%K2B1%Q?3B61&R=&QA%11QO&H%11Q8%5231&R<&J%11Q<%3251&QF&QC%11R9%311%82<1%?261z%A219+TP0%C21A&Q:%11R?%F281'?+RPP0%I2;1+mXP0%K21I%5231%R>271%R?2;1%R@2>1%RA2A1%RB2L1%RC2Q31%RD2QI1%RE2QO1qUDRG1%RK2RH1qUBRJ1%RM2RK1qUNRM1%RO2RN1p0S11p0S41p0S91pU>SH1pUHS@1pQ>SI1pV4SM1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rblock_inside) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_rblock_inside) 1%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rblock_inside) 2%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_rblock_inside) 3%nat 0%nat).
Lemma rblock_inside : ltac:(sec_stmt2 constr:(SEC_T_rblock_inside) 4%nat 0%nat).
Proof.
intros MF MR IN.
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
destruct BR as (r & Hr & Hk).
pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
pose proof (round_up_pg_ge (r_len r)) as RU.
rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Esnd in EA. pose_ceil.
assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.
End SE.
Lemma RHEAP_blocks_nodup_proof : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "E'QI'5&L%211&O&R7vGr3r2r1%544321'R;&QJ&B&I%24=318%5241p071pUH>1pQ>@1pV2D1").
Proof.
intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
inversion ND; subst. constructor; [|apply IH; assumption].
intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_RHEAP_block_range_proof := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "I'QI'5&L%211&O&R7vGr4r3r2%544321&R:%13:35&R8&H%117&J%119%53<31p071p0:1pU8C1pUHB1pQ>D1pV2H1")) (only parsing).
Variable s : ltac:(sec_ty2 constr:(SEC_T_RHEAP_block_range_proof) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_RHEAP_block_range_proof) 1%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_RHEAP_block_range_proof) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_RHEAP_block_range_proof) 3%nat 0%nat).
Lemma RHEAP_block_range_proof : ltac:(sec_stmt2 constr:(SEC_T_RHEAP_block_range_proof) 4%nat 0%nat).
Proof.
intros (st & LB0 & HP & _ & MR & [_ AR]) HIN.
pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
assert (32 <= round_up_pg (r_len r)) by nia.
unfold rblock_range. pose_ceil. split; [lia|]. split; [|lia].
rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.
End SE.
Lemma RHEAP_blocks_disjoint_proof : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "Q>'QI'5&L%211&O&R7vGr5r4r3%544321&R:%13:35r6%33<51&>'<&QJ&I%11<%21<%53421%711'?&R=&R<&H%11>&J%11@%5231%51H%8221%51J%9231%;218%=241p0?1p0H1p0K1p0N1pU<Q71pU:Q81pUHQ71pQ>Q91pV2Q=1").
Proof.
intros s LB m b1 b2 (st & LB0 & HP & _ & MR & [_ AR]) I1 I2 NE. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
- exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
+ exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
+ exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
- destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
+ exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
+ destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rrepfoot_where := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "R='Q@'S4yR0%211'8y8%511%311p051'E&R6vGr3r2%43321&QNr4%2214';&R>&Q:%11:%32:1'?&R=&R0%221>&R<+m0%2241%;2B1%=251&R3%921E+4%8231%A2H1%C241&R2%?21K+QH%>231%G2N1%I241&R1%E21Q1+8%D231%M2Q41%O241&R4%K21Q7%I226%Q22Q91%Q4231+RPP0%Q52Q<1+mXP0%Q221Q>+mVU4%Q421Q@%Q222K%Q;2QB1%Q=231%Q9261%Q:291%Q;2<1%Q<2B1%Q=2I1%Q>2Q01%Q?2Q71%QE2QA1p0QG1p0QK1pU4R11pUHR31pV4R<1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rrepfoot_where) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rrepfoot_where) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rrepfoot_where) 2%nat 0%nat).
Lemma rrepfoot_where : ltac:(sec_stmt2 constr:(SEC_T_rrepfoot_where) 3%nat 0%nat).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
(pose_ceil; unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *).
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose_ceil.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose_ceil.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose_ceil. lia.
- lia. - lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_RHEAP_frame_proof := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "Q@'QI'5&L%211&O'S4yR0%211'8y8%511%311p051&Q6%=11&R7vGr5r4r3%544321&Q7r2%23154&Q8&QM%23198'A':'E%2211&R9r7%22A1%7341@r9r8r6%G4F321p051p0>1p0B1p0F1pU2M1pUJQ01pUHQ91pQ>Q;1pV2Q?1")) (only parsing).
Variable s : ltac:(sec_ty2 constr:(SEC_T_RHEAP_frame_proof) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_RHEAP_frame_proof) 1%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_RHEAP_frame_proof) 2%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_RHEAP_frame_proof) 3%nat 0%nat).
Variable W : ltac:(sec_ty2 constr:(SEC_T_RHEAP_frame_proof) 4%nat 0%nat).
Lemma RHEAP_frame_proof : ltac:(sec_stmt2 constr:(SEC_T_RHEAP_frame_proof) 5%nat 0%nat).
Proof.
intros (st & LB0 & HP & Hst & MR & HI) MU WM FW.
exists st, LB0. split; [exact HP|]. split; [exact Hst|].
split; [|exact HI].
destruct HI as [_ AR]. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
eapply (rmrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (rrepfoot_where st m a MR RF) as [AC AW].
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
- pose_ceil. lia.
- (pose_ceil; unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD in *). lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
+ unfold RCTX in R1. lia.
+ unfold RMLOCK in R2. lia.
+ unfold RNEED_LOCKS in R3. lia.
+ unfold RPAGE_SIZE in R4'. lia.
+ destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
+ unfold RGOT_SSP in R8. lia.
+ unfold RSSP_GUARD in R9. lia.
Qed.
End SE.
Lemma reservedZ_ref : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP ";'<'5':'E%2211%411&QL&QM%211&R5%:3521").
Proof. vm_compute. reflexivity. Qed.
Lemma u64arr_of_rw_cells' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_ifaceP "QD'S4yR0%211'8y8%511%311p051'E'6'5%116&Q<&QMr5r4(3'Q5(Q4r3r2%3221(7%116%83731%=4<;:1'<&Q1&C&Nz%211%43N1<%611%83G?1&@u8%221B%<3MH1&Q0r8r7%>3Q8;K%44N321p061p0;1p0E1pUFQ61pU@Q51pULQ81p2Q:1pUHQ<1").
Proof.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.
End CEIL_WRAP_1.
Ltac rimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Section SE.
Variables (m : mem).
Variables (auxv : word).
Lemma RHEAP_init_proof : (forall a : word, 0xe90b8 <= bv_unsigned a < 0xe9460 -> m a = None) ->
(forall a : word, RVMLOCKC <= bv_unsigned a < RVMLOCKC + 4 -> m a = None) ->
rw_cells rsegs m 0xe8f43 [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m 0xe8f48 [C8 auxv] ->
rw_cells rsegs m 0xe8f70 [C8 (Z_to_bv 64 4096)] ->
rw_cells rsegs m 0xb5f18 [C8 (Z_to_bv 64 0xe8f20)] ->
rw_cells rsegs m 0xe8f20 [C8 (Z_to_bv 64 canary_val)] ->
mem_inv rsegs m ->
RHEAP (ps_init (reservedZ rsegs)) [] m
/\ rw_cells rsegs m RAUXV_CELL [C8 auxv].
Proof.
intros NONE NONEV NL AUXC PS GOT GUARD MI.
set (st0 := minit secret_val ref_reserved).
rimg_chunk NONE m 0xe90c0%Z (ctx_head_cells st0) CXH.
rimg_chunk NONE m (0xe90c0 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
rimg_chunk NONE m (0xe90c0 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
rimg_chunk NONE m (0xe90c0 + 848)%Z [CB 32 (zeros 32)] CXS.
rimg_chunk NONE m (0xe90c0 + 880)%Z [CB 32 (zeros 32)] CXB.
rimg_chunk NONE m (0xe90c0 + 912)%Z (ctx_tail_cells st0) CXT.
rimg_chunk NONE m 0xe90b8%Z [C4 (wz 0)] ML.
rimg_chunk NONEV m RVMLOCKC%Z [C4 (wz 0)] VML.
split.
2:{ unfold RAUXV_CELL. exact AUXC. }
exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
split.
2:{ unfold ps_init; cbn [ps_brk]. apply HINV_from_init. }
split; [|split; [|split; [|split; [|split]]]].
- split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
- unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
+ replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
+ replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
+ replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
+ replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
+ exact CXT.
- unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. split; [exact ML|]. split; [|split; [|split; [|split]]].
+ change (b8 0) with (Z_to_bv 8 0). exact NL.
+ change (wz 4096) with (Z_to_bv 64 4096). exact PS.
+ change (wz 954144) with (Z_to_bv 64 0xe8f20). exact GOT.
+ change (wz canary_val) with (Z_to_bv 64 canary_val). exact GUARD.
+ exact VML.
- intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.
End SE.
End CEIL_WRAP_2.
