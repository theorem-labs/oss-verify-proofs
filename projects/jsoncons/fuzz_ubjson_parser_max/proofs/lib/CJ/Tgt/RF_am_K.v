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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "1None"; "1Some"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "3N"]; ["3Z"; "0RUNp"; "4lr_lo"; "4meta_cells"; "4wz"; "4zeros"; "5C4"; "5C8"; "5CB"; "5cell"; "5cells_bytes"; "5cells_size"; "5cells_wf"; "6munch"; "6wmono"; "7bytes_at"]; ["7wr_at"; "8rw_cells"; "9AREA_HDR"; "9META_SIZE"; "9NSLOTS"; "9RKGroup"; "9a_check"; "9a_nslots"; "9aadd"; "9aptr"; "9area"; "9conc"; "9meta"; "9meta0"; "9mkArea"; "9mstate"]; ["9r_base"; "9r_kind"; "9r_len"; "9region"; "9rkind"; "9round_up_pg"; "9s_areas"; "9s_metas"; "9s_regions"; "9set_areas"; ":rsegs"; ";rrepfoot"; "<rmrep"; "=add"; "=le"; "=lt"]; ["=modulo"; "=mul"; "=of_nat"; "0a"; "0ar"; "0chk"; "0cs"; "0k"; "0m"; "0m'"; "0n"; "0off"; "0p"; "0r"; "0st"; ">insert"]; [">is_Some"; ">lookup"; "?bv"; "@N_countable"; "@Z_countable"; "@prod_countable"; "Aprod_eq_dec"; "Bmap_insert"; "Cgmap"; "Cgmap_lookup"; "Cgmap_partial_alter"; "Deq_dec"; "Eeq_dec"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma rbytes_at_zeros_sub : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_K "Q8'RByR0%211'8y8%511%311p051'@'6&O&QJr5r4&Er3%211%746541&QNz%2215&QM&R2%118%32;1%31=%8221r8r7%821A%@1A%E4D421p061p0=1p0A1pT@J1pTHL1pTFL1p2N1pTBQ01").
Proof. intros m A n off k.
intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.
Lemma rrw_cells_of_zeros : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_K "QO'RByR0%211'8y8%511%311p051'@'6'5'I%211&O&QJr5r4&Er3%211%746541&Q0r6&R2%118%44;3:1&L%119'=%C1H&J%11?&K%11A%A11%73641&QNz%221@&QMr7%91C%C11%4231r8%F11%:231&Q1r;r:%;216%44Q531;p061p0?1p0C1p0L1p0O1p0Q51pT>Q>1pTHQC1pTFQC1p2QE1pTBQG1").
Proof. intros m A n off cs.
intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
- rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
- eapply wr_at_sub; [exact HW| lia| lia].
Qed.
Section SE.
Local Abbreviation SEC_T_rmrep_set_area_next := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_K "T3'Q?'RByR0%211'8y8%511%311p051&Q9'Q:':'?'@%3221&QLvAr6r5%43321'=%A1;&RA'RH&RF&RK&RL%34?2>1&RE&RC&RD%36C62B51%94G51F&RI%14I73Hr4&QFr7%211%A6NM7541(2r3%22Q01%G3F41&R@'QC%G4Q2EA1%>4Q3FB2&4%13Q5Q48&QHr8%211%O6Q987641%:291&M(3%Q>2Q<Q<(9&QM&Q;r9%221Q=+8%5221+@%7241%94QFQF31(7%11<%>3=31%@31DQ2&N&QJ%231=G&Q1r;%A21J'I(G&D&Q6%11Q=%311%511%I29R4%611%811(F&Q7%11QE%;11%411z%>11%711%L1B%Q93C21%Q:3D61%Q;3E<1%Q<3F@1%J4LQ8H1&QI&R?&RG&RJ%14S1R?R;S0%34S2S1R;1(Q>%L1QJ%R62S0R9%F1QL%43321r<%R>11%<7S:S9RC8QF31%>213r:%S73S621p0B1p0Q>1p0QB1p0R41p0R@1p0S91pTJS?1pT:SD1pT8SF1pTDSH1pTBSI1pTNT21")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_area_next) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_area_next) 1%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_set_area_next) 2%nat 0%nat).
Lemma rmrep_set_area_next : ltac:(sec_stmt2 constr:(SEC_T_rmrep_set_area_next) 3%nat 0%nat).
Proof.
intros a ar p MR Ha Hp MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil.
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
assert (AG : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells rsegs m' A cs).
{ intros A cs H HD. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
change (ctx_tail_cells st') with (ctx_tail_cells st).
split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
apply AG; [exact C6| cbn; unfold RCTX; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. split; [apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia]|]. apply AG; [exact G6| cbn; lia].
- intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
* apply AG; [exact A3| cbn; lia].
+ rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
- rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. lia.
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
change (pw st' (a_next ar')) with (pw st (a_next ar')).
split; [apply AG; [exact A1| cbn; lia]|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
* apply AG; [exact A3| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
+ eapply wr_at_transport; [exact HWr| exact WM].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); pose_ceil; pose proof (round_up_pg_ge (r_len r)); lia).
assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.
End SE.
Lemma rmrep_new_area : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_K "V0'Q?'RByR0%211'8y8%511%311p051&Q9'QC'@&QLvAr5r4%43321'='Q:%?11&RA'RH&RF'?&RK&RL%4432?1&RE&RC&RD%36762C51%:4F51=&RI%14H73?&QFr6%211%A6LC64F1(1%11E%G3E31%Q51O%E4CB>Q0%;4DC?Q1&4%13FQ2O&QHr7%211%M6JQ77641(2%12Q9Q4%Q33;31&>'QD&QA%11Q:(Q5%Q93421%611&QNz&;%13Q8QD@%4231&QMr8%53Q<QH1+TP0%4221&QE&QB%11I%311%>251&R0r9%?3QFR21%321:%QN3R41B&B%115&Q@%117r:%G3QNR:1%E231%K261'<r1%N2M1&QO&Q4%2241%6241'Q<%RL11%R<4RHR7R32%R24RIR8R43&Q8r=&Q2&R1&Q3r2%3221%Q9251%8271&QGr?%211%RK6S6@>=41%R:1A%S03A21p0D1pT@S81&Q1&QJ&Q;r>r<%3221(3'I(G&D%11Q:%311%31R3%511(F%61Q7%211%315(7%11<%>3=31%?3>51%@3?91%A3@<1%H4GQ8C1r@rA%I21Q2%R?21Q;%R@21Q8&C&Q=%2261%Q14Q0841p0QH1pT@T<1%Q22;Q1+So0%RI221(HuQ0&E%112%4231%Q63Q51I%Q=4Q<QD71&QI&R?&RG&RJ%14TMT<T8TD%34TNTET81(Q>%T31U0%23R61R>%T91M%97U3TJT=5QO21%;21O%U23U11Q1p0>1p0I1p0Q51p0QO1p0RL1p0S51p0S;1p0SF1p0SL1p0T41p0TA1p0U:1pT<U@1pTLUB1pTJUD1pTBUF1pTNUO1").
Proof.
intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
+ exists r. repeat split; assumption.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
- exact CX.
- exact GL.
- intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
destruct (decide (a' = p)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
split; [exact HDR|]. split; [| exact PAD].
intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
- exact GR.
- exact SH.
Qed.
Section SE.
Local Abbreviation SEC_T_rfresh_page_avoids := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_K "SF'Q?'RByR0%211'8y8%511%311p051&Q9'QC'@&QLvAr5r4%43321'=%>18&RA'?'RH&RK&RC%34421>&RI%14643@&4%138A=&QHr6%211%=6<F8641(2r3%22I1%C3B41&>'QD&QA%11I(Q5%I3421%611&QNz&;%13KQ4A%4231&QMr7%53OQ81+TP0%4221&QE&QB%11J%311%>251&R0r8%?3Q9QB1%321:%Q>3QD1B&B%115&Q@%117r9%G3QAQJ1%E231%K261'Q:%R511&RF&RL%24QHQFR11&RE&RD%26QKQIQHR441%QK4R7418%QH4R8529r:&QFr<%211%R36R=>6541(1%11@%R83@31'<&Q;r=r;%3221%QC21K&QO%Q@23Q=%22N1%9241&QKr>%221D%R211p051p0@1p0Q31p0Q<1p0QB1p0QM1p0R31p0R;1p0S01pT8S61pTLS81pTJS:1pTBS<1pTNSE1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rfresh_page_avoids) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rfresh_page_avoids) 1%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rfresh_page_avoids) 2%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rfresh_page_avoids) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rfresh_page_avoids) 4%nat 0%nat).
Lemma rfresh_page_avoids : ltac:(sec_stmt2 constr:(SEC_T_rfresh_page_avoids) 5%nat 0%nat).
Proof.
intros MR Hr NK S0 S1 SAL SLR ANone Ha.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). pose_ceil.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
+ rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
assert (NEo : snd ak <> snd p).
{ intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
Z.div_mod_to_equations. lia.
+ pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.
End SE.
End CEIL_WRAP_1.
