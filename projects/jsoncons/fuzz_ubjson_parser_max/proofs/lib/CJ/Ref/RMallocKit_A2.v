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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMalloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RMallocKit_A2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "1None"; "1Some"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"]; ["3N"; "3Z"; "0L"; "4write_to_mem"; "0P"; "0RUNp"; "5agree_on"; "6lr_lo"; "6meta_cells"; "6pw"; "6ticks_ok"; "6wz"; "7optr_in"; "7ptrs_in"; "8u64arr"; "8u8arr"]; ["9C1"; "9C8"; "9cell"; "9cells_size"; ":bytes_at"; ":le4"; ":wa"; ":wr_at"; ";rw_cells"; "<rsegs"; "=RCTX"; "=RGOT_SSP"; "=RLIBC"; "=RMLOCK"; "=RSSP_GUARD"; "=rarea_rep"]; ["=rgroup_rep"; "=rmrep"; "=rmrep_ctx"; "=rregions_wf"; ">RKGroup"; ">aptr"; ">area"; ">conc"; ">get_meta_rec"; ">get_shadow"; ">ghdr"; ">meta"; ">mstate"; ">optr"; ">put_group"; ">r_base"]; [">r_kind"; ">r_len"; ">region"; ">rkind"; ">round_up_pg"; ">s_areas"; ">s_groups"; ">s_regions"; ">set_mmap_counter"; ">shadow"; ">upd_ctx"; "?add"; "?land"; "?le"; "?lt"; "?modulo"]; ["?mul"; "?of_nat"; "?pow"; "0a"; "0ai"; "0ar"; "0b"; "0bs"; "0cs"; "0g"; "0gh"; "0m"; "0m'"; "0n"; "0off"; "0p"]; ["0q"; "0r"; "0r0"; "0rid"; "0rq"; "0st"; "0st'"; "@delete"; "@insert"; "@lookup"; "Abv"; "Abv_unsigned"; "BN_countable"; "BZ_countable"; "Bprod_countable"; "Cprod_eq_dec"]; ["Dmap_delete"; "Dmap_insert"; "Egmap"; "Egmap_lookup"; "Egmap_partial_alter"; "Feq_dec"; "Geq_dec"; "0v"; "0w8"; "0ws"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.
Lemma rpw_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "B&QM&LvDr1%3221'='S:yR0%211&IvS6r2%3221vS5%5213%:3731p0<1pV0A1").
Proof. intros p. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.
Lemma rget_meta_rec_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 ";&QE'='QK&QHvS6r1%3221vS5%5213%83731pUD:1").
Proof. intros g. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.
Lemma rmeta_cells_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "?&QE'='6'Q2%211&HvS6&QHvS5r1%3221%6251%7242%<3921pUD>1").
Proof. intros g.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.
Lemma rmrep_ctx_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "A'S:yR0%211'8y8%511%311p051&QBvS5r1%3221vS6r2%6221p041pUH91").
Proof. intros m.
intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (E1 : ctx_head_cells st' = ctx_head_cells st).
{ unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.
Lemma rarea_rep_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q@'S:yR0%211'8y8%511%311p051&QE'QF'=%812&S9'SB&S?'@&SE'A&SF%544321&S>&S<&S=%36872651%;4@51?&SC%14B73Ar2&R5vS5%211%C6GF7541(2r1%22I1%I3H41&Q?r4r3%34:21<vS6r5%642154p041p091pU<Q41pU8Q61pUHQ81").
Proof. intros m a ar.
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.
Lemma rgroup_rep_extP : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q@'S:yR0%211'8y8%511%311p051&QE'QJ'=%812&S9'SB&S?'@&SE'A&SF%544321&S>&S<&S=%36872651%;4@51?&SC%14B73Ar2&R6vS5%211%C6GF7541(2r1%22I1%I3H41&Q@r4r3%34:21<vS6r5%642154p041p091pUFQ41pU>Q61pUHQ81").
Proof. intros m b gh.
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.
Lemma rbytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q0'S:yR0%211'8y8%511%311p051'A'6%115&Q4&Q9r4r2r1%544321&Fr5r3&RA&5%12A8%311%746;51%>4=7<6p021p0;1pU@B1p2E1pUJG1pUHH1").
Proof. intros m m' A bs.
intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Lemma rwr_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "J'S:yR0%211'8y8%511%311p051'A&Q7&Q9r4r2r1%544321&Fr5r3%342716%:49382p021p071pUL>1p2?1pUJA1pUHB1").
Proof. intros m m' A n.
intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.
Lemma rrw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q1'S:yR0%211'8y8%511%311p051'A'6'Q2%211&Q8&Q9r4r2r1%544321&Fr5r3&RA&Q3%118%311%746;51%>4=7<6p021p0;1pUBB1p2F1pUJH1pUHI1").
Proof. intros m m' A cs.
intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.
Lemma ru64arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q3'S:yR0%211'8y8%511%311p051'A'6%118&N&Q9r4r2r1%544321&Fr5r3&R@+8&RA&5%12F:%311%6251%:49>81%A4@:?9p021p0>1pWDE1p2H1pUJJ1pUHK1").
Proof. intros m m' A ws.
intros [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.
Lemma ru8arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q0'S:yR0%211'8y8%511%311p051'A'6%115&O&Q9r4r2r1%544321&Fr5r3&RA&5%12A8%311%746;51%>4=7<6p021p0;1pU@B1p2E1pUJG1pUHH1").
Proof. intros m m' A bs. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_agree := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "SG'QL'S:yR0%211'8y8%511%311p051&QAvEr3r2%43321&F&Q=+4%346521r4&Q<+R[8%743:21r5&Q;+8%;43721r6&Q>%>42614&QE'QF'=%L12&S9'SB&S?'@&SE'A&SF%544321&S>&S<&S=%36872651%;4@51?&SC%14B73A&R5r:%211%B6FE64Q71(2r1%22H1%H3G41r9&QGr;%221Q@+TP0%Q?4<521p071pU<Q11pU8Q31'QJ%QN11%Q14Q6KG2%F4Q7LH3&R6%11<%Q66Q:643QK1%D27C%Q:3721r<%B21R0+9%QO4CL21p051pUF>1pU>QC1'R2%R>11%QA4Q?Q>Q92%Q64Q@Q?Q:3&R7%11<%QF6QC643R;1%Q427Q3%QJ3721'R3&R0%11R@(QD%QO3421r=&QO%11RF&R4&R1%11RI%311%RH47L51p091p0?1pV4H1pV8R61%S23S1QAQCp021p0M1p0Q>1p0RC1p0RG1p0RL1p0S11p0S61pUJS<1pUHS=1pV<SF1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree) 2%nat 0%nat).
Lemma rmrep_agree : ltac:(sec_stmt2 constr:(SEC_T_rmrep_agree) 3%nat 0%nat).
Proof.
intros (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
End SE.
Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).
Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).
Lemma rnr_regions : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "E'='SB'@&SE&S<'R2%544321&R7vS6%211&S8&SA&SD%14;:98%34<981vS3vS2vS5%;11%97A>=5431%D3>;1").
Proof. reflexivity. Qed.
Lemma rnr_lookup_new : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "E'='8'R2%211&S9'@'SB&SE&S<%344217&SC%146439vS3&R7vS6%211%<6;>7541(2vS2%22A1%D3A41").
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "L'@&>'=r1vS3%33521%511'8'R2%211&S9'SB&SE&S<%34>216&SC%14@438r2&R7vS6%211%;6E=7541vS5%511%>6H@:871%G3@41p0D1pV2K1").
Proof. intros q. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q9'@'R2'='8%113&S9'SB&SE&S<%349218&SC%14;43:r2&R7vS6%211%;6@?7541(2r1%22B1%B3@41'?'<r3vS3%G3I21vS2%I3J?1%6231&>%115vS5%C11%L6Q1Q0HF:1%A2Q1F%Q13O21%>261%@291p0B1pV4Q61pV2Q81").
Proof. intros q r.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rnr_lookup_new in H. inversion H. auto.
- right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "E':'@'A%3221&>'=&4r1%23761vS3%53921%711&QGvS6r2%3221vS5%5213%=3@31p081pV2A1").
Proof. intros q. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "?'A'=&QGvS6(9'@vS3r1%443821%7261&R;vSJ%2215%<3=41pUN>1").
Proof. intros off. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 ";'@'='R9&QIvS6r1%3221vS5%5213%83731pV2:1").
Proof. intros q. reflexivity. Qed.
Lemma rnr_lr_lo_new : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "6&R=vSJ&GvS2%211%5241").
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.
Lemma rnr_old_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q:'@'R2'='8%113&S9'SB&SE&S<%349218&SC%14;43:r2&R7vS5%211%;6@?7541(2r1%22B1%B3@41'?&R=&R;vSJvB%3221&G%11@%7231&QO%11C&R4&R1%11F%311%=251%?21=%A291p0C1pV4Q71pV2Q91").
Proof. intros q r.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.
Lemma rnr_regions_wf : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "4&QCvEvS6%3221").
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RFimg : ranges_free ref_reserved x L = true).
{ apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
split; [exact RS|]. split; [|split; [|split]].
- intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+ unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
+ exact (WR q r H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists r. rewrite rnr_lookup_old by exact Pa. auto.
- intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.
Lemma rmrep_new_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "5&QAvEvS6vRL%43321").
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
{ intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
pose proof (round_up_pg_ge len) as LG. fold L in LG. pose_ceil.
assert (MR1 : rmrep st m').
{ eapply rmrep_agree; [exact MR| | | | | | |].
- intros a Ha. apply AG; unfold RMLOCK in *; lia.
- intros a Ha. apply AG; unfold RLIBC in *; lia.
- intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
- intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
- intros a ar Ha a0 Ha0.
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
pose_ceil. apply AG; lia.
- intros b gh Hb a0 Ha0.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). pose_ceil. apply AG; lia.
- intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). pose_ceil.
pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
- eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
- intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
- intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
- intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+
cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
split.
* split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
* intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
+ eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.
Lemma rticks_ok_new_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "6&JvS5%211vS6%411p031").
Proof. intros H. exact H. Qed.
Lemma rptrs_in_new_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "<'@!p021&Mr1vS5%3221r2vS6%6221p041pQ:91").
Proof. intros P. intros H. exact H. Qed.
End NEWREGION.
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
(RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x968 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).
Lemma rdr_regions : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "D'='SB'@&SE&S<'R2%544321&R7vS6%211&S7&S@&SD%14;:98%34<981vS3vS5%:11%85@<431%C3=:1").
Proof. reflexivity. Qed.
Lemma rdr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "Q4'@'R2'='8%113&S9'SB&SE&S<%349218&SC%14;43:r2&R7vS6%211%;6@?7541(2r1%22B1%B3@41'<&>r3vS3%G3I21%411vS5%?11%H6MLDB61%=2MB%M3K21%;261p0=1pV:Q11pV2Q31").
Proof. intros q rq.
intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "L'@&>'=r1vS3%33521%511'8'R2%211&S9'SB&SE&S<%34>216&SC%14@438r2&R7vS6%211%;6E=7541vS5%511%>6H@:871%G3@41p0D1pV2K1").
Proof. intros q. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "E':'@'A%3221&>'=&4r1%23761vS3%53921%711&QGvS6r2%3221vS5%5213%=3@31p081pV2A1").
Proof. intros q. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "A'@&>'=r1vS3%33521%511'R9&QIvS6r2%3221vS5%5213%<3731p091pV2@1").
Proof. intros q. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rmrep_drop_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "5&QAvEvS6vRL%43321").
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). pose_ceil.
assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
split; [|split; [|split; [|split; [|split]]]].
-
split; [exact RS|]. split; [|split; [|split]].
+ intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
+ intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
+ intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rdr_lookup_old by exact Pa. auto.
+ intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists rb. rewrite rdr_lookup_old by exact Pb. auto.
-
eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xaf000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xaf000 \/ 0xe9000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
assert (AGC : agree_on m m' RLIBC 0x968).
{ intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0xaf000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0xaf000 \/ 0xe9000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
+ eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
+ eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
+ eapply rrw_cells_agree; [exact G6|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
- intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose_ceil.
assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
assert (AGA : agree_on m m' (conc st a) 4096).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
+ intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
- intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). pose_ceil.
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
- intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
destruct (WR q rq H) as (Bq & _ & _ & BCq & _). pose_ceil.
pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
destruct (SH q rq H Hk) as [HWr HB]. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.
Lemma rticks_ok_drop_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "6&JvS5%211vS6%411p031").
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.
Lemma rmrep_put_group_new : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "T4'QL'S:yR0%211'8y8%511%311p051':'@'A%3221&QE'R2&QAvEr7r6%43321'='QJ%B11&S9'SB&S?&SE&SF%34B2A1&S>&S<&S=%36F62E51%94D51<&SC%14F73>&R6r8%211%@6KB64E1(1%11D%F3D31%Q71M%D4Q2B>N%;4Q3C?O&4%13Q5Q4N&R7r9%211%L6Q9Q57641(2r4%22Q81%Q33<41'R3&R0r5%211(QD%Q93521&R=z&;%13QGQF@%4231&R;r:%53QKQJ1+@%4221&R4&R1%11QI%311%>251&R?r;%?3R5R41%321:%QM3R61B&Q8&Q9r=&QGr>r<%3221(3'Q2(Q1&I%Q92R@?%2281%411(Q0%11QL(7%119%;3:31%<3;61%D4CB>1&R<&S;%12S4QH+O%4221%52N2%RI3S221&QN%QK2S2Kr@%34K2J1r?%S43S321p071p0?1p0Q51p0Q;1p0QF1p0QL1p0R31p0RA1p0S91pWBSG1pV4S@1pU:SD1pUDSC1pU>SE1pUHSJ1pV<T31").
Proof.
intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
pose proof WF as (RS & WR & DJ & WA & WG).
split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
- split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
+ rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
- intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
+ rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.
Lemma rmrep_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Ref_RMallocKit_A2 "QB'QL'S:yR0%211'8y8%511%311p051'A&QAvEr3r2%43321'<&R=z%2215&R>&RB+2+Q0%3221%52;1%:271&R:&R8%11@r5%4221&Cr4&Q6&R;&Q:+<%3221%511&Q5&K%11M%311%<3;51%Q23Q1>1p0D1p0Q01pW@Q61pUHQ81pV<QA1").
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le4 (wz v)) as L4.
pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
- left.
pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.
End CEIL_WRAP_1.
