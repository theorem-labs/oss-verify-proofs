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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_enframe.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocKit_B2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocKit_B2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocTree."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["0A"; "0C"; "1None"; "1Some"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"]; ["3N"; "3Z"; "4wview"; "0RUNp"; "5rdv"; "6agree_on"; "7mem"; "7pans_mem"; "8u64arr"; "8u8arr"; "9cell"; "9cells_size"; ":ivl"; ":munch"; ":outside"; ":stk"]; [";bytes_at"; ";wa"; ";wr_at"; "<rw_cells"; "=RKGroup"; "=Unknown"; "=cell_read"; "=cellval"; "=get_shadow"; "=mstate"; "=r_base"; "=r_kind"; "=r_len"; "=region"; "=rkind"; "=round_up_pg"]; ["=s_regions"; ">rsegs"; "?rrepfoot"; "@rgrp_region_addr"; "Armrep"; "Brpres_except"; "Cadd"; "Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"; "0W"; "0a"; "0bs"]; ["0cs"; "0h"; "0hi"; "0lo"; "0m"; "0m'"; "0mX"; "0n"; "0o"; "0q"; "0r"; "0st"; "Dlookup"; "Ebv"; "Ebv_unsigned"; "FN_countable"]; ["Ggmap"; "Ggmap_lookup"; "Heq_dec"; "0ws"; "0x"]]).
Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
(c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.
#[using="Type"] Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof.
intros H. unfold rd8. unfold rdv in H.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.
#[using="Type"] Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.
#[using="Type"] Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
rimplT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.
#[using="Type"] Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
(c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.
#[using="Type"] Lemma rrdv_range : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "R<&F'Q9'R=yR0%211'9y8%511%311p051':'@'A%3221'Q=&QDvCr4r3%43321'=%@17&R<'R@&RB&R?%34?21<&RA%14A43>&5%13CB<&Q@r5%211%<6GD8641(3r2%22G1%B3A41'Q>&Q;%11G(Q4%G3421'<&QGz&;%13Q5Q4@%4231&QH&Q?&Q<%11Q4%311%5271%<271&D&Gr9r8r6%55QN4321%B2A1+X0%?231%F231p0;1p0I1p0O1p0QC1pTFQI1pTDQK1pT:R01pTHR91pTBR;1").
Proof.
intros o st m q r MR Hr Hk Ho. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
- apply pans_mem_range.
Qed.
#[using="Type"] Lemma rrdv_cur : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "SB'R=yR0%211'9y8%511%311pU:51'Q9p073':'@'A%3221'Q=&QDvCr5r4%43321'=%B17&R<'R@&RB&R?%34?21<&RA%14A43>&5%13CB<&Q@r6%211%<6GD8641(3r3%22G1%B3A41'Q>&Q;%11G(Q4%G3421'<&QGz&;%13Q5Q4@%4231&QH&Q?&Q<%11Q4%311%5271%<271'Q7&Q6&Q8r:r8%Q13QCQB1%4231%A3QEQD3%7221(Q5r1%211%QA3<41r<&Q1&QF&Q:%11=r9%M3R1R01%5231%711%911%D12%QM3R;21p0=1pT4R71&Q0&QAr7%>11%@21H(4(8%11RF%33RGQL1%948B51&D&F&Gr;%4532L1G&R>%12S0>%RA3RI31p091p0D1p0Q@1p0QN1p0R41p0RH1pU:S71pTFRO1pTDS11pT>S61pTHS81pTBS:1").
Proof.
intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite (AG h eq_refl).
destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). pose_ceil.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.
#[using="Type"] Lemma rwview_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "I'R=yR0%211'9y8%511%311pU:51'=r2r1%211r3%113%63831&B&QA%23158r4%4331:%<3>31p071pSND1pT<@1pT:A1").
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.
#[using="Type"] Lemma rwr_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "J'R=yR0%211'9y8%511%311p051'A&Q2&QAr4r2r1%544321&Er5r3%342716%:49382p021p071pT@>1p2?1pT<A1pT:B1").
Proof.
intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.
#[using="Type"] Lemma rrw_cells_agree' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "Q1'R=yR0%211'9y8%511%311p051'A'7'J%211&Q3&QAr4r2r1%544321&Er5r3&QJ&K%118%311%746;51%>4=7<6p021p0;1pT2B1p2F1pT<H1pT:I1").
Proof.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.
#[using="Type"] Lemma ru64arr_agree' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "Q3'R=yR0%211'9y8%511%311p051'A'7%118&H&QAr4r2r1%544321&Er5r3&QI+8&QJ&6%12F:%311%6251%:49>81%A4@:?9p021p0>1pU8E1p2H1pT<J1pT:K1").
Proof.
intros m m' A ws [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.
#[using="Type"] Lemma ru8arr_agree' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "Q0'R=yR0%211'9y8%511%311p051'A'7%115&I&QAr4r2r1%544321&Er5r3&QJ&6%12A8%311%746;51%>4=7<6p021p0;1pT0B1p2E1pT<G1pT:H1").
Proof. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.
#[using="Type"] Lemma rstk_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "L'R=yR0%211'9y8%511%311p051'A&O&QAr4r2r1%544321&Er5r3&QL%1272%544931%<4;5:4p021p091pT6@1pT8A1pT<C1pT:D1").
Proof.
intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).
Section SE.
Local Abbreviation SEC_T_rmrep_transport_agree := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "R4'Q9'R=yR0%211'9y8%511%311p051pU:62&QDvCr3r2%43321'A'<&QGzr1%3221&QH&QK+2+R0%3221%5271%;271&QBr6%221A'=r5&Q1%11F%311%712%63N21p081p0<1pSNI1&QCr7%221N&>&B&QA%2315=(2%11Q;%C3Q;31%711r4%D11%938<1%H3Q@16%<11p061p0?1p0Q01pSNQ=1%QC3QBQ09p021p0G1p0QB1pT<QH1pT:QJ1pTHR31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_agree) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_agree) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_agree) 2%nat 0%nat).
Lemma rmrep_transport_agree : ltac:(sec_stmt2 constr:(SEC_T_rmrep_transport_agree) 3%nat 0%nat).
Proof using Type st m m'.
intros (WF & CX & GL & AR & GR & SH) AG WG.
pose proof WF as (Hres & WR & DJ & WA & WGr).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
+ apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
+ apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
+ apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
+ apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
+ apply TC; [exact G6 |]. intros a Ha. apply rrepfoot_vml. cbn in Ha. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
+ apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). pose_ceil.
split.
+ destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.
End SE.
#[using="Type"] Lemma rmrep_transport_agree' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "QC'Q9'R=yR0%211'9y8%511%311p051pU:62&QDvCr3r2%43321'A'<&QGzr1%3221&QH&QK+2+R0%3221%5271%;271'?&QBr6%221B&QC%123D%6231'=r5&Q1%11J%311%:12%63Q221p081p0@1pSNM1%Q33Q29Q1p021p0Q11pT<Q71pT:Q91pTHQB1").
Proof.
intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
- intros a Ha Hf. apply AG; auto.
- intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.
#[using="Type"] Lemma rpres_except_of_munch_nw : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "QA'A!pU:21'7&L%211'R=yR0%211'9y8%511%311p051&Mr3r2r1%43321'<&QGz%2215&QH&QK+2+R0%3221%52;1%:271&>r7%11@%311&N%124Dp031p081pSNQ61&QEr6r4%3321Kp051p0J1pT<Q01pT:Q11pSLQ:1p4Q>1").
Proof.
intros C W m m' MU HW a Ha Hc.
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.
#[using="Type"] Lemma rpres_except_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "Q?'A!p021&F&QEr5r4r3%43321&QGz%2214&QF%1276&QK+2+R0%3221%9251'<r6r1%=221&QH%<24C%2241%7241&>r:r2%211%411p061pSNQ11&Er8r7%3421AQ0p051p0E1p0M1p0Q11pT@Q:1p2Q;1pT<Q91pT:Q:1p4Q<1").
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.
#[using="Type"] Lemma ru64arr_pres : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "QB'A!p021&F'7'R=yR0%211%411&QEr5r4r3%43321&H&QAr2%342751'<&QGr1%22;1&QH&QF&QI+8&QJ&6%12EA%311%6251%82E1%:2<1%?2<1&>r9%11D%311p051pSNQ71r6%K4J1ONp031p0J1p0O1pU8Q51p2Q>1pT<Q<1pT:Q=1p4Q?1").
Proof.
intros C m m' A ws HP H HC. pose proof (u64arr_bound rsegs m A ws H).
eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.
#[using="Type"] Lemma ru8arr_pres : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B2 "Q?'A!p021&F'7'R=y8%211%411&QEr5r4r3%43321&I&QAr2%342751'<&QGr1%22;1&QH&QF&QJ&6%12C?%311%52B1%7291%<291&>r9%11A%311p051pSNQ41r6%H4G1LKp031p0G1p0L1pT0Q21p2Q;1pT<Q91pT:Q:1p4Q<1").
Proof.
intros C m m' A bs HP H HC. pose proof (u8arr_bound rsegs m A bs H).
eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.
End CEIL_WRAP_1.
