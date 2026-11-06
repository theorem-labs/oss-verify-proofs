(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K F_am_K2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A2 RF_am_K.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_am_K2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_am_K2.A2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1bool"; "1fst"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3N"; "3Z"; "0P"; "0RUNp"; "4actives"]; ["4bouncess"; "4lr_lo"; "4unmap_seqs"; "4usages"; "5mem"; "5ptrs_in"; "6u64arr"; "6u8arr"; "7rsegs"; "8agree_on"; "9RCTX"; "9RGOT_SSP"; "9RLIBC"; "9RMLOCK"; "9RSSP_GUARD"; "9ref_reserved"]; ["9rmrep"; "9rmrep_ctx"; "9rregions_wf"; ":RKGroup"; ":active"; ":aptr"; ":area"; ":bounces"; ":conc"; ":ctx"; ":ghdr"; ":live_ranges"; ":mctx"; ":meta"; ":mkRegion"; ":mstate"]; [":optr"; ":r_base"; ":r_kind"; ":r_len"; ":ranges_free"; ":region"; ":rkind"; ":round_up_pg"; ":s_areas"; ":s_groups"; ":s_metas"; ":s_regions"; ":s_reserved"; ":s_shadow"; ":shadow"; ":unmap_seq"]; [":upd_region"; ":usage"; ";add"; ";le"; ";lt"; "0a"; "0ar"; "0b"; "0gh"; "0i"; "0lo"; "0m"; "0m'"; "0n"; "0off"; "0q"]; ["0r"; "0r'"; "0rg"; "0rid"; "0rq"; "0sc"; "0st"; "0st'"; "<insert"; "<lookup"; "=bv"; ">N_countable"; ">Z_countable"; ">prod_countable"; "?prod_eq_dec"; "@map_insert"]; ["Agmap"; "Agmap_lookup"; "Agmap_partial_alter"; "Beq_dec"; "Ceq_dec"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_rmrep_agree_but_ctx := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "U9'Q?'RJyR0%211'4y8%511%311p051&D&Q0v>r4r2%43321'8'S0';&S3&RK'QE%544321&QK%11;r5%311%;3531&Q5&RN'<&S4%34>=21&RM&RL%26A@?541'Q=%D49521&QJ%11>r6%311%J3531'Q6%K4@<91&QH%116r7%311%Q13531'Q:%Q24GC@1&QI%116r8%311%Q83531'QN%Q94Q8Q7Q61&QM%116r9%311%Q?3531'3'5%12Q4Q4%311&QL%118r:%311%QH3531&I&M+4%34?F21&L+S8%649B21r;&K+8%:43=21r<&N%=42614r=+mRRD%@4251>%RE1Q?&RI&S1%14R1QMQJQBrB%QB11%56R4QEQD3RB1(0r1%22QH1%RD3:41rAr@&Q8rCr3%3221+TP0%Q347621p091pT>R31pT<RC1%S;1QN%E4RERAR>QO%QN1:%H6RGR1R02S51%C2R2B%S53521rD%@21>+9%Q@4KD21p051pTBR91pT@S01%SH1S8%Q24S<S;S:S9%S819%Q56S>S;S:2SB1%Q02S<O%SB3521'QF&QB%11SG(Q3%SG3421&QA%11Q0&QG&QC%11Q3%311%R54HQ651p081p0>1pU2SL1pU8T01&Q1%12QFQ>%T:3T9Q=Q@p021p051p0L1p0Q:1p0R11p0R51p0R91p0R>1p0RB1p0RG1p0S11p0S91p0SA1p0SI1p0T91p0TF1pTJTL1pTHTN1pU@U71pU>U81")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree_but_ctx) 0%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree_but_ctx) 1%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree_but_ctx) 2%nat 0%nat).
Variable m' : ltac:(sec_ty2 constr:(SEC_T_rmrep_agree_but_ctx) 3%nat 0%nat).
Lemma rmrep_agree_but_ctx : ltac:(sec_stmt2 constr:(SEC_T_rmrep_agree_but_ctx) 4%nat 0%nat).
Proof.
intros (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGV AGA AGG AGR CX'.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [exact CX'|split; [|split; [|split]]]].
- destruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G6|]. eapply A2.agree_on_sub; [exact AGV| lia| cbn; lia].
- intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
unfold rarea_rep. rewrite !Hconc.
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
rewrite PW. split; [|split].
+ eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
+ eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
+ eapply RA2.rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.
End SE.
Lemma rmrep_ctx_mid_agree : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "S6'Q?'RJyR0%211'4y8%511%311p051&D&Q0v>r4r2%43321':'8'Q<&Q9%117r5%311%63531'7'<&Q@&Q4r1%2281r6%4213%?3631pU<81&R1%12>7%2268%D3<21pU<=1&QO%12C<%22;=%I3A21pTDB1&Q7%12HA%22@B%N3F21pTDG1%I261%J2<1%K2B1%Q42M1'S0';&S3&RK'QE%544321&QK%11Q7%21O%Q=3421&I&R2&J+R@%3221+j0%64Q@QH21&F&H&?r7%211%544QF81+^@%=2<1&C%116%:49QK31&G+j@%C2B1&B%11<%54?R131+k@%H2G1&@%11A%:4DR631%R4261%R52=1%R62C1p0J1p0Q21p0Q=1p0RC1pTJRI1pTHRK1pU@S41pU>S51").
Proof.
intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
assert (E3 : usages st' = usages st).
{ unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st).
{ unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
assert (E5 : bouncess st' = bouncess st).
{ unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
rewrite E2, E3, E4, E5.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RCTX in *.
split; [|split; [|split]].
- eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.
Lemma rarea_in_live : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "R@'Q?'5';'<%3221'Q6'QE&Q2v>r5%3221'8'4%118&RI'S0&Q5&RN&S3&S4%34B2A1&RM&RK&RL%36F62E51%:4951D&S1%14;73F&QHr6%211%A6KJ64F1(0r4%22M1%H3F41%H1N%F4Q3C?O%<4Q4D@Q0&2%13Q6Q5;&QKr7%211%N6Q:Q67641%=2Q7<%Q33:21'7&R3&Q8r8%2219%421C&R4&R2+TP0%2251%42H1%;261&A%11O%=21QD&QA%11Q2&QG&QC%11Q5%311%>251%@2QL1%G291p0=1p0J1p0Q61p0R01pV<R81pU2R61pT>R81pT<R:1pU>R?1").
Proof.
intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.
Lemma rgroup_in_live : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "R@'Q?'5';'<%3221'Q:'QE&Q2v>r5%3221'8'4%118&RI'S0&Q5&RN&S3&S4%34B2A1&RM&RK&RL%36F62E51%:4951D&S1%14;73F&QIr6%211%A6KJ64F1(0r4%22M1%H3F41%H1N%F4Q3C?O%<4Q4D@Q0&2%13Q6Q5;&QKr7%211%N6Q:Q67641%=2Q7<%Q33:21'7&R3&Q8r8%2219%421C&R4&R2+9%2251%42H1%;261&A%11O%=21QD&QA%11Q2&QG&QC%11Q5%311%>251%@2QL1%G291p0=1p0J1p0Q61p0R01pV<R81pU2R61pTBR81pT@R:1pU>R?1").
Proof.
intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.
Lemma rimage_clear_of_ranges_free : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "Q<'Q?'<'8'3'5%1244%311&QLr4%211&O%93521'1&QD&Q;r5%211r3%532:1(6%B3821'7&R3+RPP0%2217&R4+mTP0%22:1%7241&9r6%921G&R2%123B%92J1%>241%711p091p0B1p0L1pV<Q71pTLQ81pTFQ91pU>Q;1").
Proof. intros st lo n x.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.
Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.
Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.
Lemma rgr_eq : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "E'8'Q?&R0vRC'QE(Q>&QBr1%211&QA%113&R2vR>+TP0%3221%:3751qU6<1vRF%@3?21vRG%D3C21").
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rgr_regions : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "E'8'S0';&S3&RK'QE%544321&QKvRG%211&RH&RO&S2%14;:98%34<981vRCvRAvRF%;11%97A>=5431%D3>;1").
Proof. reflexivity. Qed.
Lemma rgr_lookup_inv : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "Q9';'QE'8'4%113&RI'S0&S3&RK%349218&S1%14;43:r2&QKvRG%211%;6@?7541(0r1%22B1%B3@41':'7r3vRC%G3I21vRA%I3J?1%6231&9%115vRF%C11%L6Q1Q0HF:1%A2Q1F%Q13O21%>261%@291p0B1pU:Q61pU0Q81").
Proof. intros q rq.
rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma rgr_lookup_old : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "L';&9'8r1vRC%33521%511'4'QE%211&RI'S0&S3&RK%34>216&S1%14@438r2&QKvRG%211%;6E=7541vRF%511%>6H@:871%G3@41p0D1pU0K1").
Proof. intros q. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rgr_lookup_new : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "E'8'4'QE%211&RI';'S0&S3&RK%344217&S1%146439vRC&QKvRG%211%<6;>7541(0vRA%22A1%D3A41").
Proof. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma rgr_conc : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 ";&Q5'8'<&Q8vRGr1%3221vRF%5213%83731pU0:1").
Proof. intros q.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, rgr_lookup_new, Hr. reflexivity.
- rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Lemma rgr_ru : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 ";'8'<&QG&R2vR>+TP0%3221%511%614%6214%:3931").
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.
Lemma rgr_regions_wf : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "4&Q2v>vRG%3221").
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
split; [exact RS|]. split; [|split; [|split]].
- intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
apply ranges_free_intro. intros b n HI.
pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
- intros q1 r1 q2 r2 H1 H2 NE.
assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
{ intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
- left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
- right. exact D. }
destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ exact (OLD q2 r2 H2' NE2).
+ destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
destruct (decide (fst a = rid)) as [E|NE].
+ exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
rewrite LEN in A1. repeat split; try assumption; lia.
+ exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
- intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.
Lemma rmrep_grow_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "5&Q0v>vRGvR;%43321").
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
replace (ctx_tail_cells st') with (ctx_tail_cells st).
2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
- intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
- intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
exists w8. rewrite rgr_conc, PW. split; assumption.
- intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
+ exfalso. apply NK. exact Hk.
+ exact (SH q rq H Hk).
Qed.
Lemma rptrs_in_grow : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_K2 "<';!p021&Er1vRF%3221r2vRG%6221p041pL91").
Proof. intros P. intros H. exact H. Qed.
End GROW.
Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl rsegs (at_node rsegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.
End CEIL_WRAP_1.
