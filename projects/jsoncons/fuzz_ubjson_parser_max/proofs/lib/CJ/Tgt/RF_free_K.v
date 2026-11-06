(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export F_free_K.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_free_K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_Bpres."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1fst"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "0LB"; "0RUNp"; "4hdr_st"]; ["5block"; "6ci_mptrs"; "7KINV"; "7ZINV"; "8actives"; "8ctx_head_cells"; "8ctx_tail_cells"; "8meta_cells"; "8pw"; "8ticks_ok"; "9optr_in"; "9ptrs_in"; ":cell"; ";Known"; ";RKGroup"; ";aptr"]; [";cell_read"; ";cellval"; ";conc"; ";get_meta_rec"; ";get_shadow"; ";ghdr"; ";meta"; ";mstate"; ";optr"; ";r_kind"; ";region"; ";rkind"; ";s_groups"; ";s_regions"; ";s_shadow"; ";shadow"]; ["<rfree_fp"; "=rmrep"; ">le"; ">sub"; "0a"; "0b"; "0c"; "0gh"; "0k"; "0lo"; "0m"; "0p"; "0pf"; "0q"; "0r"; "0rid"]; ["0rid'"; "0sp"; "0sp'"; "0st"; "0st'"; "0st2"; "?delete"; "?lookup"; "@bv"; "AN_countable"; "AZ_countable"; "Aprod_countable"; "Bprod_eq_dec"; "Cmap_delete"; "Dgmap"; "Dgmap_lookup"]; ["Dgmap_partial_alter"; "Eeq_dec"; "Feq_dec"; "0w"; "0x"]]).
Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rfree_fp_hdr_st := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "QK'Q7'5';'<%3221&Ir6%211'7&QB+1r1%3221+3%5231%7231'9'8'Q1&Q0&Q4r:&1r9%23FE1%5241&QC&6%13JI5r3%4221%<261(M%11F%A3@31qU8Q01%D2Q11p0F1pSBQ31r4r5%Q0221&Q@&?r8%22F1r7%542178%64K428p021p091p0=1p0Q=1pS:QB1pT6QC1pT4QD1pSDQE1pSJQE1pT8QJ1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 0%nat 0%nat).
Variable pf : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 1%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 3%nat 0%nat).
Variable sp' : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 4%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rfree_fp_hdr_st) 5%nat 0%nat).
Lemma rfree_fp_hdr_st : ltac:(sec_stmt2 constr:(SEC_T_rfree_fp_hdr_st) 6%nat 0%nat).
Proof using Type st pf lo sp sp' a.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
- right; left. exact H.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
exists rid, r, w. auto.
Qed.
End SE.
Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.
#[using="Type"] Lemma rdrop_regions : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "D'8'R>';&RA&R9'Q:%544321&Q=vR4%211&R6&R=&R@%14;:98%34<981vQOvR3%:11%85@<431%C3=:1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "D'8'R>';&RA&R9'Q?%544321&Q>vR4%211&R6&R=&R@%14;:98%34<981vQOvR3%:11%85@<431%C3=:1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "E'5';'<%3221&:'8&1r1%23761vQO%53921%711&Q2vR4r2%3221vR3%5213%=3@31p081pSLA1").
Proof. intros q. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "G&Q8&J';&:'8r1vQO%33521%511qU:71%9215'R8yR0%211&HvR4r2%3221vR3%5213%@3731p0;1pSHF1").
Proof. intros p. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "A';&:'8r1vQO%33521%511'Q?&Q4vR4r2%3221vR3%5213%<3731p091pT2@1").
Proof. intros rid'. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K ";&O'8'Q6&Q3vR4r1%3221vR3%5213%83731pSL:1"). Proof. intros q. reflexivity. Qed.
#[using="PTR"] Lemma rmeta_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "?&O'8'2'L%211&GvR4&Q3vR3r1%3221%6251%7242%<3921pSL>1").
Proof. intros q.
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma rctx_head_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K ":'8'2'L%211&EvR4%211vR3%411%93631").
Proof.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "<'8'2'R8yR0%211%411&DvR4%211vR3%411%;3631").
Proof.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K ":'8'2'L%211&FvR4%211vR3%411%93631").
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_drop_region := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "B'R8yR0%211'4y8%511%311p051&QAv>vR3r1%43321vR4r2%73621p041pSF:1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_drop_region) 0%nat 0%nat).
Lemma rmrep_drop_region : ltac:(sec_stmt2 constr:(SEC_T_rmrep_drop_region) 1%nat 0%nat).
Proof using PTR m.
intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [|split; [|split]].
+ intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
+ intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
+ intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
+ intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
- unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
- exact GL.
- intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
- intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
- intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End SE.
End DROP.
Section SE.
Local Abbreviation SEC_T_rptrs_in_norid := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_K "S6'Q7'2&@%211'<';'Q:'R8yR0%211'4y8%511%311p051'Br6r5r4%43321&Cr7(3&O%211%5241&QAv>r8r3%43321'8%F1J&R7'R>&RA&R9%34Q021O&R?%14Q243Q1&Q=r9%211%:6Q6Q564K1(0%12Q7L%?3>31'Q;&Q9%11Q1(N%D3421'5%12Q@QA'Q5%Q=11&R<&RB%24QEGQF1&R;&R:%26QHJIQI41%L4Q7418%I4Q8529r2&Q<r=%211%Q36?>6541r1%J2@1%Q83@31&:&1%13R5R6Q=r;%Q=3R721%511p071pS@I1pS<K1&Ar<%211&K%QF3R@@:%>11qU:RB1%421Fp061p0:1p0Q81p0Q>1p0QO1p0R51p0R<1pSFRB1pSNRK1pT0RM1pS>RO1pLS11pT<S51")) (only parsing).
Variable st2 : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 2%nat 0%nat).
Variable rid : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 4%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rptrs_in_norid) 5%nat 0%nat).
Lemma rptrs_in_norid : ltac:(sec_stmt2 constr:(SEC_T_rptrs_in_norid) 6%nat 0%nat).
Proof using Type st2 LB c rid r m.
intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
{ intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
{ intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
- apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
- apply NGr. exact M1.
- apply NGr. exact M2.
- apply NGr. exact M3.
- apply NGr. exact M4.
- intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
- destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
- intros g. split; [| split].
+ apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
+ apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
+ destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
- intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b gh Hb. split; [exact (NOG b gh Hb)|].
destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.
End SE.
End CEIL_WRAP_1.
