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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocKit_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMallocKit_B () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocTree."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0C"; "1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"; "2not"]; ["2or"; "3N"; "3Z"; "4le_bytes_to_word"; "5ov_read_bytes"; "0RUNp"; "6agree_on"; "6ivs_avoid"; "6ivs_covered"; "7actives"; "7b8"; "7bouncess"; "7ctx_head_cells"; "7ctx_tail_cells"; "7lr_lo"; "7meta_cells"]; ["7meta_slot"; "7pw"; "7unmap_seqs"; "7usages"; "7wz"; "8u64arr"; "8u8arr"; "9cell"; "9cells_size"; ":ivl"; ":munch"; ":wmono"; ";bytes_at"; ";le8"; ";wa"; "<alloc_ceiling"]; ["=rw_cells"; ">Known"; ">META_SIZE"; ">RKGroup"; ">active"; ">aptr"; ">area"; ">bounces"; ">c_free_meta_head"; ">c_seq"; ">cell_read"; ">cellval"; ">conc"; ">ctx"; ">del_group"; ">del_slots"]; [">g_active_idx"; ">get_shadow"; ">ghdr"; ">meta"; ">mstate"; ">put_meta"; ">r_base"; ">r_kind"; ">r_len"; ">region"; ">rkind"; ">round_up_pg"; ">s_areas"; ">s_groups"; ">s_metas"; ">s_regions"]; [">s_reserved"; ">s_shadow"; ">set_slots"; ">shadow"; ">usage"; "?rsegs"; "@rfree_fp"; "@rrepfoot"; "ARCTX"; "ARGOT_SSP"; "ARMLOCK"; "ARNEED_LOCKS"; "ARPAGE_SIZE"; "ARSSP_GUARD"; "Armrep"; "Armrep_ctx"]; ["Brpres_except"; "CIn"; "Dadd"; "Dge"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0W"; "0a"; "0ak"; "0ar"; "0b"]; ["0bs"; "0c"; "0cs"; "0g"; "0gh"; "0hi"; "0i"; "0lo"; "0m"; "0m'"; "0mr'"; "0n"; "0p"; "0q"; "0r"; "0rid"]; ["0s"; "0sc"; "0sp"; "0sp'"; "0st"; "0st'"; "Elookup"; "Fbv"; "Fbv_extract"; "Fbv_unsigned"; "GN_countable"; "GZ_countable"; "Gprod_countable"; "Hprod_eq_dec"; "Igmap"; "Igmap_lookup"]; ["Jeq_dec"; "Keq_dec"; "0v"; "0ws"; "0x"]]).
Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rrepfoot (st : mstate) (a : Z) : Prop :=
(RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
\/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RVMLOCKC <= a < RVMLOCKC + 4).
#[using="Type"] Lemma rrepfoot_ctx : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RHr1%3221&S5&S2+m0%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_mlock : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RJr1%3221&S5&S2+4%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_nl : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RKr1%3221&S5&S2+1%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_pgsz : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RLr1%3221&S5&S2+8%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_area : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QD'R4'B&QE'QF'<'8%113&T6'T>&T='A&T@&TA%4432<1&T<&T:&T;%36762@51%:4@51?&T?%14B73Ar2&R<r4%211%B6GF7541(2r1%22I1%I3G41';&S4&QLr5r3%3221%521=&S5&S2+TP0%2251%42B1%<261&RGr6%221<p041p0B1pVNQ=1pVLQ?1pVJQA1pX:QC1").
Proof. intros st a ak ar. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma rrepfoot_group : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QD'R4'B&QE'R2'<'8%113&T6'T>&T='A&T@&TA%4432<1&T<&T:&T;%36762@51%:4@51?&T?%14B73Ar2&R=r4%211%B6GF7541(2r1%22I1%I3G41';&S4&QLr5r3%3221%521=&S5&S2+9%2251%42B1%<261&RGr6%221<p041p0B1pW:Q=1pW0Q?1pVJQA1pX:QC1").
Proof. intros st a b gh. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma rrepfoot_known : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "R5'R4'B'A'R9'<'8%113&T6'T>&T@&T:%349218&T?%14;43:r3&R?r5%211%;6@?7541(2r2%22B1%B3@41'R:&R7%11;(QC%G3421';&S4&R6r4%211r6%5221&S5&S2&R;&R8%118%311%5291%7291%?291'QK&QJ&R1r8%221?&S:r7%E1Q3%3221%8251(QA%11H%QD3<31&RGr9%221<p041p0B1p0Q31p0Q91pY6QO1pWNQN1pX0R01pVJR21pX:R41").
Proof. intros st a rid r v. intros; do 6 right; left. exists rid, r, v. auto. Qed.
#[using="Type"] Lemma rrepfoot_got : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RIr1%3221&S5&S2+8%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; do 7 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_guard : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4&RMr1%3221&S5&S2+8%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; do 8 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_vml : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4+mVU4r1%3221&S5&S2+4%2261%4261%:261&RGr3r2%3221p051pVJA1pX:C1"). Proof. intros st a. intros; do 9 right; assumption. Qed.
#[using="Type"] Lemma rbytes_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q0'T7yR0%211'8y8%511%311p051'B'5%115&Q<&REr4r2r1%544321&Fr5r3&S8&4%12A8%311%746;51%>4=7<6p021p0;1pW2B1p2E1pWDG1pWBH1").
Proof.
intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
#[using="Type"] Lemma rrw_cells_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q5'T7yR0%211'8y8%511%311p051'B'5'Q7%211&Q@&REr4r2r1%544321&Fr5r3&S8&Q8%118%311%746;51&Q;r6%23?19%A4@2:?p021p061p0?1pW6F1p2J1pWDL1pWBM1").
Proof.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma ru64arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q7'T7yR0%211'8y8%511%311p051'B'5%118&Q5&REr4r2r1%544321&Fr5r3&S7+8&S8&4%12F:%311%6251%:49>81&Q;r6%23B1<%D4C2=Bp021p061p0B1pY8I1p2L1pWDN1pWBO1").
Proof.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.
#[using="Type"] Lemma ru8arr_agree : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q4'T7yR0%211'8y8%511%311p051'B'5%115&Q6&REr4r2r1%544321&Fr5r3&S8&4%12A8%311%746;51&Q;r6%23?19%A4@2:?p021p061p0?1pW2F1p2I1pWDK1pWBL1").
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_transport_unowned := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q8'R4'T7yR0%211'8y8%511%311p051'5&Q9%211&RNvEr4r3%43321&Q:r2%23154&Q;&REr5%33219&G&RGr7%211%42>1r8r6%C3B21p041p0:1p0?1p0C1pVHI1pWDM1pWBN1pX:Q71")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_unowned) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_unowned) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_unowned) 2%nat 0%nat).
Variable W : ltac:(sec_ty2 constr:(SEC_T_rmrep_transport_unowned) 3%nat 0%nat).
Lemma rmrep_transport_unowned : ltac:(sec_stmt2 constr:(SEC_T_rmrep_transport_unowned) 4%nat 0%nat).
Proof using Type st m m' W.
intros (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
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
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
pose proof Bt as (B0 & B1 & _). cbn in B1.
eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rmrep_put_meta_frame := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QM'R4'T7yR0%211'8y8%511%311p051&QE'R3&RNvEr5r4%43321&Q0r6r3%3221&Q:(3':'B%2211(9&QLr7%221>&S2&QB%2231%749941(7%11:%>3;31%@31CG&Q;&RE%231<F&Q@r9%@21I&O%123O%547B31&R5r:%23EO1r8%Q73Q621p061p0=1p0A1p0Q31p0Q81pWFQ>1pW8Q@1pWDQB1pWBQC1pX:QL1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_put_meta_frame) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_put_meta_frame) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_put_meta_frame) 2%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rmrep_put_meta_frame) 3%nat 0%nat).
Variable mr' : ltac:(sec_ty2 constr:(SEC_T_rmrep_put_meta_frame) 4%nat 0%nat).
Lemma rmrep_put_meta_frame : ltac:(sec_stmt2 constr:(SEC_T_rmrep_put_meta_frame) 5%nat 0%nat).
Proof using Type st m m' g mr'.
intros MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
pose proof (round_up_pg_ge (r_len ra)) as RU.
assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
assert (TC : forall A cs, rw_cells rsegs m A cs ->
(A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
split; [|split; [|split; [|split; [|split]]]].
- exact WF.
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. unfold RCTX in *.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 | cbn; lia].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
+ apply TC; [exact C6 | cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros a' ar' Ha'. cbn in Ha'.
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
destruct (decide (a' = a)) as [->|NEa].
+ rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k' Hk'. rewrite Hmc, get_meta_rec_put.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
* apply TC; [exact PD| cbn; lia].
+ assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
{ rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
- rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
eapply rarea_rep_ext; [exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
* apply TC; [exact HD| cbn; lia].
* intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
* apply TC; [exact PD| cbn; lia].
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [|exact I].
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.
End SE.
#[using="Type"] Lemma rmrep_ctx_frame' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "S:'R4'T7yR0%211'8y8%511%311p051&RNvEr4r2%43321&Q:(3':'B%2211(9&RH&S2+m0%2231%547741(7%118%<3931r3%?321A&Q;&RE%231E4'<'T>'A&T@&T:'R9%544321&R?r6%211r7%411%<3631&QE&T=&TA%24>=Q01&T<&T;%26A@?Q341'R3%D48521&R>%11=r8%311%J3531'QF%K4?<91&R<%116r9%311%Q13531'R2%Q24FC@1&R=%116r:%311%Q83531'RC%Q94Q8Q7Q61&RA%116r;%311%Q?3531'5%11R0&R@%116r<%311%QF3531&RO%124Br=%RB3RA1=p031p061p0>1p0F1p0N1p0Q61p0QE1p0R31p0R71p0RH1pWDRN1pWBRO1pX<S81pX:S91").
Proof.
intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
assert (TC : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
unfold RCTX in *.
split; [|split; [exact CX'|split; [|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split; [|split]]]]; (apply TC; [assumption | cbn; lia]).
- intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len ra)).
destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
+ apply TC; [exact A1| cbn; lia].
+ intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
+ apply TC; [exact A3| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len rb)).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.
#[using="Type"] Lemma rmrep_del_group : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "G'R4'T7yR0%211'8y8%511%311p051&QE&RNvEr3r2%43321&QNr4%2241%83716p051pWJ;1pWB=1pX:F1").
Proof.
intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.
#[using="Type"] Lemma rmrep_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q5'R4'T7yR0%211'8y8%511%311p051'T>&QE&T='A&T@'B&TA%544321&T<&T:&T;%36872651':%12<8%>4=731&RNvEr3r2%43321&RBr4%2241%83716p051pY6;1pWBK1pX:Q41").
Proof.
intros st m v (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.
#[using="Type"] Lemma rmrep_del_slots : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "L'R4'T7yR0%211'8y8%511%311p051&QE'B&RNvEr5r4%43321&QOr3r2r6%446321%:3918p071pW4=1pX2>1pWJ@1pWBB1pX:K1").
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.
#[using="Type"] Lemma rmrep_active_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QM'R4'T7yR0%211'8y8%511%311p051'B&RNvEr4r3%43321';&S4z%2215&S5+Q@%2281%7241'<&Q>&S2&RH+R@%3221&S7+8%221C%7241%911%;3OE1'5%11N%Q111&D&REr6u8%4432N1(2&Q=&Q1r7&QDr5%2231%5241%711%92@1%N3@;1p0D1p0Q11p0Q:1pVJQF1pX4QA1pWBQC1pX:QL1").
Proof.
intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.
#[using="Type"] Lemma rmrep_usage_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QM'R4'T7yR0%211'8y8%511%311p051'B&RNvEr4r3%43321';&S4z%2215&S5+Q@%2281%7241'<&Q>&S2&RH+^@%3221&S7+8%221C%7241%911%;3OE1'5%11N%Q111&D&REr6u8%4432N1(2&Q=&Q4&RDr7r5%3221%511%711%92@1%N3@;1p0D1p0Q11p0Q:1pVJQF1pX4QA1pWBQC1pX:QL1").
Proof.
intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.
#[using="Type"] Lemma rmrep_bounces_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QL'R4'T7yR0%211'8y8%511%311p051'B&RNvEr4r3%43321';&S4z%2215&S5+Q0%2281%7241'<&Q>&S2&RH+k@%3221%421A%611%83LB1'5%11K%N11&D&REr6u1%4432K1(2(3&J&QGr7r5%3221%511(7%11Q;%93Q<31%;2B1%M3B=1p0F1p0Q01p0Q91pVJQE1pW>Q@1pWBQB1pX:QK1").
Proof.
intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.
#[using="Type"] Lemma rmrep_seq_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QA'R4'T7yR0%211'8y8%511%311p051&RNvEr3r2%43321'<&Q>&S2&RH+l@%3221%511%73B91'5%11A%D11&D&REr4u1%4432B1(2(3&J&QI&QMr5%211%411%611(7%11Q2%:3Q331%<2C1%M3C>1p0G1p0Q01pVJQ;1pWBQ71pX:Q@1").
Proof.
intros st m a (_ & (_ & _ & _ & _ & _ & C6) & _) ->.
apply (rw_cells_read_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.
#[using="Type"] Lemma rmrep_fmh_read : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q?'R4'T7yR0%211'8y8%511%311p051&RNvEr3r2%43321'<&Q>&S2&RH+@%3221%511%73B91'5%11A%D11&D&REr4u8%4432B1(2&Q=&Q1r5&QH&QM%113%311%6251%811%:2A1%K3A<1p0E1p0N1pVJQ91pWBQ51pX:Q>1").
Proof.
intros st m a (_ & (C1 & _) & _) ->.
apply (rw_cells_read_at rsegs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); reflexivity.
Qed.
#[using="Type"] Lemma rbytes_at_cons : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q4'T7yR0%211'8y8%511%311p051'B'5%115&>&Q<&REr4r3(3r2r1%33>21%847651';(7%11B%83C71%=4<;:1&S2+1%22=1%A4@?1;%9251%D2;1pW2F1pW0L1pVJJ1pWBL1").
Proof.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app rsegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.
#[using="Type"] Lemma rmrep_group_word8 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "RI'R4'T7yR0%211'8y8%511%311p051&QE'R2&RNvEr4r3%43321'<%=17&T6'T>&T='A&T@'B&TA%544321&T<&T:&T;%36872651%;4E51D&T?%14G73F&R=r5%211%B6KJ64F1(2r2%22M1%H3G41'='5%11Q5';%Q912&D&REr6&Q>&S2&QLr7%221C+8%5221%711u8%<4;:21r1%G2A1%Q=3@31'6&4%12QJ5%QA3318&S6&T9&T8w&C%11<%44R63R61%62R71+Q0%9221&R0%11R0%QN3QG31%Q32>1%Q42C1qW2Q61%Q92Q71p0Q;1p0R51pW:R;1pW0R=1pWBR?1pX:RH1").
Proof.
intros st m b gh MR Hb. pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (GR b gh Hb) as (w8 & R & Hw8).
destruct (SH (fst b) r Hr Kr) as [HWr _].
pose proof WF as (_ & WR & _). destruct (WR (fst b) r Hr) as (_ & _ & _ & RC2 & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
pose_ceil. pose proof (round_up_pg_ge (r_len r)).
destruct (rwr_at_bytes_exist m (conc st b + 9) 7) as (bs & Lbs & Bbs).
{ eapply wr_at_sub; [exact HWr| rewrite Cb; lia | rewrite Cb; lia]. }
{ lia. }
{ rewrite Cb. lia. }
assert (B8 : bytes_at rsegs m (conc st b + 8) [w8]).
{ destruct R as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
replace (conc st b + Z.of_nat 8) with (conc st b + 8) in HB by lia.
first [ apply bytes_at_app in HB; destruct HB as [HB _]; exact HB | exact HB ]. }
assert (B : bytes_at rsegs m (conc st b + 8) (w8 :: bs)).
{ apply rbytes_at_cons. split; [exact B8|]. replace (conc st b + 8 + 1) with (conc st b + 9) by lia. exact Bbs. }
exists (w8 :: bs).
assert (L8 : length (w8 :: bs) = 8%nat) by (cbn; lia).
split; [|split; [exact L8|]].
- rewrite <- (Z.add_0_r (conc st b + 8)). rewrite (bytes_at_read rsegs m _ _ 0 8 B); [|lia|rewrite L8; cbn; lia].
cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite L8; lia). reflexivity.
- rewrite load8_le_val by exact L8. cbn [map le_val]. rewrite <- Hw8.
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
set (L := le_val (map bv_unsigned bs)). replace (256 * L) with ((8 * L) * 32) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rmeta_slot_bounds := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QJ'R4'T7yR0%211'8y8%511%311p051&QE&RNvEr3r2%43321&Q0r4%2214';&S5z&QLr5%221;%5241&S4&S2+Q8%2251&Q?%11C%6231'@+RPP0%9261+mXP0%;21=%5231'<'B&S6+4%22C1%5341G&S3+TP0%62G1+H%4221%O261%Q02=1%Q12D1%Q22L1p0Q41p0Q81pW8Q>1pWBQ@1pX:QI1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmeta_slot_bounds) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmeta_slot_bounds) 1%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rmeta_slot_bounds) 2%nat 0%nat).
Lemma rmeta_slot_bounds : ltac:(sec_stmt2 constr:(SEC_T_rmeta_slot_bounds) 3%nat 0%nat).
Proof using Type st m g.
intros MR (a & ar & k & Ha & Hk & Eg).
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
(pose_ceil; unfold AREA_HDR, META_SIZE, NSLOTS in *). pose proof (round_up_pg_ge (r_len ra)).
rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rgroup_bounds := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "R8'R4'T7yR0%211'8y8%511%311p051&QE'R2&RNvEr4r3%43321'<%=17&T6'T>&T='A&T@'B&TA%544321&T<&T:&T;%36872651%;4E51D&T?%14G73F&R=r5%211%B6KJ64F1(2r2%22M1%H3G41';&S4z&QLr6%221Q1%5241&S2+@%2241&Q?%11Q8%;231'@+RPP0%>261+mXP0%@21<%5231&S6%12?<%Q>3Q71C%F241%G2;1%H2B1p0J1p0QD1pW:QJ1pW0QL1pWBQN1pX:R71")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rgroup_bounds) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rgroup_bounds) 1%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_rgroup_bounds) 2%nat 0%nat).
Variable gh : ltac:(sec_ty2 constr:(SEC_T_rgroup_bounds) 3%nat 0%nat).
Lemma rgroup_bounds : ltac:(sec_stmt2 constr:(SEC_T_rgroup_bounds) 4%nat 0%nat).
Proof using Type st m b gh.
intros MR Hb.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
pose_ceil. pose proof (round_up_pg_ge (r_len r)).
rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.
End SE.
Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).
#[using="Type"] Lemma rfree_fp_stack : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "D'R4'B';&S4r3r1%3221&S5r2%2241%8241&RFr5r4%3421:6p051pVJ?1pX6@1pW@A1pX:C1").
Proof. intros st lo sp a. intros; left; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_ctx : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "H'R4'B';&S4&RHr1%3221&S5&S2+m0%2261%4261%:261&RFr5r4r3r2%544321p071pVJC1pX6D1pW@E1pX:G1").
Proof. intros st lo sp a. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_region : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QN'R4'B'A'R9'<'8%113&T6'T>&T@&T:%349218&T?%14;43:r2&R?r6%211%;6@?7541(2r1%22B1%B3@41&?'R:&R7%11<(QC%H3421%611';&S4&Nr3%211r5%5221&S5&S2&R6%117&R;&R8%11:%311%7251%92;1%A2;1&RFr9r8r7%44321Q4p061p0I1p0Q11pWNQE1pX0QG1pVJQI1pX6QJ1pW@QK1pX:QM1").
Proof. intros st lo sp a rid r. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma rfree_fp_group : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QH'R4'B&QE'R2'<'8%113&T6'T>&T='A&T@&TA%4432<1&T<&T:&T;%36762@51%:4@51?&T?%14B73Ar2&R=r6%211%B6GF7541(2r1%22I1%I3G41';&S4&QLr7r3%3221r4%6221&S5&S2+8%2261%4261%=261&RFr8r5%342>H1p051p0D1pW:Q?1pW0QA1pVJQC1pX6QD1pW@QE1pX:QG1").
Proof. intros st lo sp a b gh. intros; right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma rfree_fp_meta : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q='R4'T7yR0%211'8y8%511%311p051'B&QE&RNvEr6r5%43321&Q0r7r3%3221';&S4&QLr8r4%3221%5218&S5&S2+Q8%2251%42=1%<261&RFr9%241BF;p041p0B1p0G1pVJN1pWLN1pX6Q01pW@Q11pWBQ31pX:Q<1").
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="Type"] Lemma rfree_fp_mono : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "R7'R4'B'<'T>'A&T@&T:'R9%544321&R?r5%211r6%411%<3631'RC%=4<;:1&RA%116r7%311%C3531&QE'R2'8%112&T6&T=&TA%24IHL1&T<&T;%26LKJO41%N4;41:&T?%14=63<r2&R=r9%211%>6BA7541(2r1%22D1%Q:3C41r3r;%:11%F6JI?=31%82J=%Q@3I21p071pW:M1pW0O1&S4%12Q=Q;&RFr8%24D1Q>Q@%34=E2Q?p021p061p091p0Q:1p0QB1pVJR01pX8R11pX6R21pW@R31pX<R51pX:R61").
Proof.
intros st st' lo sp sp' a ER ES HG HS H.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
- right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.
#[using="Type"] Lemma rpres_except_of_munch' : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "QE'B!pY:21'5&Q9%211'T7yR0%211'8y8%511%311p051&Q:r3r2r1%43321&Q;&RE%23165&S1':%12HH(9%14JJ:9r7%63421';&S4r4%221?&S5%12AC%6231r;%11Ep031pY:Q71p0<1pW<Q91pW@Q:1&S0r5%23B1>p041p0J1p0N1pWDQ41pWBQ51pVHQ>1p4QB1").
Proof.
intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.
#[using="Type"] Lemma rpres_except_of_munch_cov : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q5'B!p021'5&Q9%211'T7yR0%211'8y8%511%311p051&Q:r3r2r1%43321&Q;&RE%23165&Hr6r5%3221&S0r7r4%33251p051p0:1p0>1pWDD1pWBE1pVHN1p4Q21").
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.
Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.
#[using="MU WIN"] Lemma rctxW_avoid : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "Q@'B'@&S4&S2r2r1%3221&RH%6221+m0%7231%9217%;241&S1':%12??(9%14AA=<vS;%63421r5r4%C221r3%F221%G2E5%I221p081pW<L1pW@M1%M2B1z%N219%N2<:&S9+2+R0%3221%Q4251&FvSHvSI%3421FEp051p0<1p0?1pWHQ>1p2Q?1").
Proof.
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; exact Hin.
+ destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.
#[using="m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMallocKit_B "T5'@&Q@&REvSI&RH&LvT5%211%746541';'<'5'Q7%211vT4%:11%63391'B&S1':%1233(9r2r1%347721vS;%83621&S4&S2+R@%22J1r3%5221%62;M%Q2221p091pW<C1pW@D1%M2F1%Q72O1&Q5&I%11Q4%34Q9Q8=1'T7yR0%211%Q411%71Q2%Q73271+^@%G2Q?1%I21E%J2OG%QF221p0M1pW<Q71pW@Q81%QA291%QK2@1&Q3%11QG%F4QLQK;1%31QA%QF3A31+j@%Q62QN1%Q821Q4%Q92Q>A%R5221p0Q<1pW<QF1pW@QG1%R0291%R:2<1&Q6&Q2%11R7%34R<R;<1y8%Q411%R611%61R4%R93261+k@%QI2RA1%QK21QG%QL2R1E%RH221p0QO1pW<R91pW@R:1%RC291%RM2?1&K%11RI%E4RNRM;1%31RC%RH3A31+l@%R82S01%R:21R6%R;2R@A%S7221p0R>1pW<RH1pW@RI1%S2291%S<2<1&M%11S8%S>4S=S<;1%31S2%S73S431+m0%RG2S?1%RI21RE%RJ2ROA%SF221p0RM1pW<S71pW@S81%SA291%SK2<1&RNvE%231SHSKp041p0D1p0Q41p0QH1p0R81p0RM1").
Proof.
intros H1 H2 H3 H4 H5 H6.
pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
assert (CX' : rmrep_ctx st' m').
{ unfold rmrep_ctx. split; [|split; [|split; [|split; [|split]]]].
- destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
- apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.
Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.
End CEIL_WRAP_1.
