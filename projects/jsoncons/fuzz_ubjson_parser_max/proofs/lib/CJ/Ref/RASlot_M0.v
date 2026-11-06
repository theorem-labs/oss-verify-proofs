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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W18 ASlot_I ASlot_M0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_M0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W9."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["0A"; "0B"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2or"; "3N"; "3Z"; "0LB"; "0RUNp"; "4gmf"; "4taf"; "5block"; "6ISTF_g"]; ["6lmem"; "7mem"; "8cell"; "9alloc_ceiling"; ":rw_cells"; ";rsegs"; "<RCTX"; "<ref_reserved"; "<rmrep"; "=rauxv_ok"; "=rpres_except"; ">rmalloc_fp"; "?aptr"; "?get_meta_rec"; "?m_sizeclass"; "?mstate"]; ["?r_base"; "?r_len"; "?region"; "?round_up_pg"; "?s_regions"; "@add"; "@le"; "@lt"; "0a"; "0cs"; "0g"; "0lo"; "0m'"; "0m1"; "0mE"; "0r"]; ["0rid"; "0sc"; "0sp"; "0st"; "0st0"; "0stE"; "Alookup"; "Bbv"; "CN_countable"; "Dgmap"; "Dgmap_lookup"; "Eeq_dec"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rgmf_of_facts := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "Q9'O'3&>%211'9&L'?&Gr4r3%43321&@r5r2%3221'6&N&Mr6%221:%411%63A1='5&Q6z%221=&Q7+Q@%22@1%7241'<r8%231>Dp041p0=1p0E1p0J1pRFQ01pS4Q21pFQ41pS8Q81")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rgmf_of_facts) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_rgmf_of_facts) 1%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_rgmf_of_facts) 2%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rgmf_of_facts) 3%nat 0%nat).
Lemma rgmf_of_facts : ltac:(sec_stmt2 constr:(SEC_T_rgmf_of_facts) 4%nat 0%nat).
Proof.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
constructor.
- exact MSL.
- exact AVr.
- exact FRr.
- exact MW.
- exact SC48.
- exact GSC.
- exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
+ intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
exact (X Hmem Hgh S0).
+ intros o Ho. exact (GU b _ o Hgh Ho).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
- destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
exists n, p. split; reflexivity.
Qed.
End SE.
Lemma rtaf_of_facts : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "J'O'3&>%211'9'?&Gr3r2%43321'5&Q6z%2215&Q7+Q@%2281%7241'=r5%221=p041p0=1pS4C1pFE1pS8I1").
Proof. intros st LB sc.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
- intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.
Section SE.
Local Abbreviation SEC_T_rst0_region := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "QO'8'Q2'6'4%113&QF'QI&QK&QH%349218&QJ%14;43:r2&Q4vQD%211%;6@?7541(2r1%22B1%B3@41'5&Q6z&Q0%11=%4231&Q5&Q3&Q1%11B%311%5271&Cv;%211%>241'7+RPP0%A271+V\P0%C21@%5231%E2;3+elP0%G21D%9231%I2?3+fdP0%K21H%=231%M2C3+mTP0%O21L%A231%Q2251%Q32:1%Q42?1%Q52F1%Q62Q11p0Q81pS0QL1pS2QN1")) (only parsing).
Variable rid : ltac:(sec_ty2 constr:(SEC_T_rst0_region) 0%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rst0_region) 1%nat 0%nat).
Lemma rst0_region : ltac:(sec_stmt2 constr:(SEC_T_rst0_region) 2%nat 0%nat).
Proof.
intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. pose_ceil. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rmalloc_fp_cases_ER := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "Q7'O'QGyR0%211'4y8%511%311p051'9&Hv;r5r4%43321&KvQDr6r3r2%56943721'7'5&Q6%12<6&Q7%128=%5231&C%11B%52<1%:241p0<1p0C1pRBI1pS6J1pRHK1pRNM1pS<Q61")) (only parsing).
Variable stE : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases_ER) 0%nat 0%nat).
Variable mE : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases_ER) 1%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases_ER) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases_ER) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases_ER) 4%nat 0%nat).
Lemma rmalloc_fp_cases_ER : ltac:(sec_stmt2 constr:(SEC_T_rmalloc_fp_cases_ER) 5%nat 0%nat).
Proof.
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
pose_ceil.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
- right. pose_ceil. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rmalloc_fp_image_ER := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "QG'O'QGyR0%211'4y8%511%311p051'9&Hv;r5r4%43321&KvQDr6r3r2%56943721&Q6&C%11<%321<'5+RPP0%621>&Q7+mTP0%22A1%6241'7&F%=21F&Q5+m0%2241%:2J1%>251+hnmL%D21M+hnn0%?2O1%C231%=261p0?1p0G1p0L1p0Q31pRBQ91pS6Q:1pRHQ;1pRNQ=1pS<QF1")) (only parsing).
Variable stE : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image_ER) 0%nat 0%nat).
Variable mE : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image_ER) 1%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image_ER) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image_ER) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image_ER) 4%nat 0%nat).
Lemma rmalloc_fp_image_ER : ltac:(sec_stmt2 constr:(SEC_T_rmalloc_fp_image_ER) 5%nat 0%nat).
Proof.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
pose_ceil.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.
End SE.
Lemma rauxv_ok_malloc_fp_ER : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "Q>'O'QGyR0%211'4y8%511%311p051'9&A&Hv;r7r6%43321&Ir4r2%33721&J&KvQDr9%35<21;:r5%63219&Q6&C%11Ar8%4221%5227%A3EDCp021p041p0:1p0B1p0G1p4N1pRJN1pRLO1pS6Q11pRHQ21pRNQ41pS<Q=1").
Proof. intros stE mE lo sp m1 m' B.
intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
destruct AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). pose_ceil. lia.
- intros a Ha Hfp. unfold RAUXV_CELL in Ha.
destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.
Lemma rframe_keep_ER : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M0 "QC'O'QGyR0%211'4y8%511%311p051'9&A'3'B%211&Hv;r8r7%43321&J&KvQDr9r6%4593271r5r4%83321&D&Er3%342851&Q6%12A8&C%11D%421=%948ED>p021p061p091p0>1p0H1pRDN1p2Q31pRJQ31pRLQ41pS6Q61pRHQ71pRNQ91pS<QB1").
Proof. intros stE mE lo sp m1 m' A cs.
intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.
End CEIL_WRAP_1.
