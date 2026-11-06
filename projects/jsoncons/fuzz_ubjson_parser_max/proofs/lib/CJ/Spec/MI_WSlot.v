(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WSlot () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Pres3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_TF2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WAMeta."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WSlot.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WTry2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1andb"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "0L"]; ["0LS"; "0LS'"; "0LS4"; "0RUNp"; "4mled"; "5INVL"; "5MR"; "5blk"; "5cnt_of"; "5extras"; "5hosts"; "5mkX"; "5sstart"; "5x_idle"; "6xidle"; "7geom_kept"]; ["8AM_frame"; "9GP"; "9X_as"; "9geo_of"; ":TA_frame"; ";LActive"; ";active"; ";aptr"; ";c_bounces"; ";c_mmap_counter"; ";c_seq"; ";get_head"; ";get_stride"; ";ghdr"; ";lhead"; ";m_avail"]; [";m_freed"; ";m_maplen"; ";m_set_avail"; ";m_set_freed"; ";mask_upto"; ";meta"; ";meta0"; ";mkMeta"; ";mstate"; ";optr"; ";put_meta"; ";region"; ";s_ctx"; ";s_groups"; ";s_metas"; ";s_next_rid"]; [";s_regions"; ";s_secret"; ";s_shadow"; ";s_slots"; ";s_tick"; ";shadow"; ";upd_meta"; ";usage"; "<In"; "=ldiff"; "=le"; "=leb"; "=sub"; "=testbit"; "0X"; "0a"]; ["0ai"; "0b"; "0c"; "0h"; "0i"; "0idle"; "0idle'"; "0last"; "0m"; "0ml"; "0r"; "0r'"; "0s0"; "0sc"; "0st"; "0st'"]; ["0st2"; "0st3"; "0st4"; ">lookup"; "?N_countable"; "?Z_countable"; "?prod_countable"; "@prod_eq_dec"; "Agmap"; "Agmap_lookup"; "Beq_dec"; "Ceq_dec"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.
Definition GP (st st' : mstate) : Prop :=
(forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
/\ s_secret st' = s_secret st.
Lemma GP_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "5'QH&Q1r1%2211pUN41"). Proof. intros st. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "<'QH&Q1r3r2%3221r5%5214p031p041pU691pU4:1pU0;1").
Proof. intros a b c. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "K'QH';'S8'=&S:&S4'QK%544321&R0r1%211r2%411%<3631'>&R1%115r3%311%B3531&Q1r4%2215p041p0;1pV0I1pUNJ1").
Proof. intros st st'. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot ";'QH'Q0r2r1%3221&Q1r3%2215p041pV091pUN:1").
Proof. intros st st'. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot ">'QH'>'Q4r3r2r1%43321&Q1r4%2216p041pUL:1pV0<1pUN=1").
Proof. intros st st' sc. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.
Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).
Lemma geo_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "Q8'QE';'9&QI'>%3221%4212%5213&Q3r1%211r2%411%<3631':&Lr3%2218r4%421:%C3@31pU:A1&H%11<%218%H3E21&QA%11@%21<%L3I21&Q<%11D%21@%Q03M21%D251%E2:1%F2?1p0H1pUHQ61pUFQ71").
Proof. intros r r'.
unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.
Lemma geom_kept_geo : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "QH'QH&Q7'Q=';'8%113&S3'S8&S7'=&S:'>&S;%544321&S6&S4&S5%36872651%;4A51@&S9%14C73Br2&QMr4%211%C6HG7541(2r1%22J1%J3H41r3%I6NM=;17%62N;%N3L21p051pU8Q11pU4Q31'9&QI%221L%321M%421N&Q3&F%12>A%311%32GC%511%Q=3731pVJQ@1&O%12LEp031p0A1pV0QF1pUNQG1").
Proof. intros st st'.
intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.
Lemma INVL_idle_sub : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "Q7'I'6&Q7%211'QH'D&G%611'Q>p016&R8r1r6%33;21r2&Mr8%211%83@41p061pVJB1&EvCr7r5r4r3%6654321=&N%12=6%9681B654p041p0<1pQ2H1p2K1pQ0N1pUNQ01pU>Q21pTNQ61").
Proof. intros X idle' st L BL LS.
intros SUB (IR & IA & IM & IL & IG & IS & ISH).
split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
split.
{ destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.
Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).
Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "M';'8'QE%211&S3&Q7'S8&S7'=&S:'>&S;%544321&S6&S4&S5%36872651%;4<51?&S9%14>73AvRH&QNvRN%211%D6CF7541(2&QF%22I1%L3I41").
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "8';'QH&QJvRH&QFvRN%43321%73612").
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.
Lemma free_idle_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "S1':&EvC&Q2vRE%211vROv?v0vA%96854321';'S8'=&S:&S4'R5%544321&R2%11=vRN%311%;3531&R4%11B%215%?3=21&Q7&S7'>&S;%34BA21&S6&S5%26EDC541'Q=%H49521&QM%11Q0%21C%M3421'9%12?=%O4@<91&R3%11Q7%21J%Q43421'QK%Q54Q4Q3Q21&R0%11Q=%21Q0%Q:3421&QO%11QA%21Q4%Q>3Q<21&QI&Q6r1%22QG1%32Q:2%QD3521pULQ31&R7%12QL6%22Q?7%QI3Q721pULQ81&Q9&QL%11R2%311%31QF%511%R13Q?31%R14Q@Q?Q<Q@&Q8%117%216%R63421&Q:%11;%21:%R:3QH21%RF251%RG2;1%RH2C1%RI2I1%RJ2Q11%RK2Q61%RL2Q=1%RM2QE1%RN2R41%RO2R91%S02RF1").
Proof.
pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
unfold st', fm_st. rewrite fi_put.
pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.
Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.
Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).
Lemma fin_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "5&JvS0vRAvRH%43321"). Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "<';'6&Q7%211v@(Q5vRM%211%411(7%118%;3831").
Proof.
pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.
Lemma mask_upto_pred : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "A'>&R:zr1%3221';&R<&QDr2%211+1%5221&R9%1243%93>31p0;1pU0@1").
Proof. intros a.
intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
destruct (Z.eq_dec i 0) as [->|NZ].
- cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma testbit_avail' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "H'>&R:zr1%3221';'4&R=&R<&QDvR@%211+1%5221r2%8221&3&R;%1264%2259%4221%@3?61p0B1pU:G1").
Proof. intros i.
intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.
Lemma st3_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "H';'QHvS1&R6vRH'QE&QB&R<&QDvR@%211+1%5221&QCvRG%711%9216r1%5221%=271qUF?1vS0%C3B21%G3FE1").
Proof.
unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.
Lemma fin_INV3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "E&EvC(KvRE(7&Q7%211(2vRL%2241(1'=%211vRH%7291%=5<9631vS1v?v0v@%D6C54321").
Proof.
rewrite st3_eq.
pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
- rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
split; [exact M4|]. split; [| exact M6].
intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
- rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
rewrite <- Em in P5.
destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
rewrite testbit_avail' by lia.
destruct (Z.eq_dec i 0) as [->|NZ].
+ assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
* cbn. discriminate.
* intros F. exact (M5 0 ltac:(lia) A0 F).
* unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
+ destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
* assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
-- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
-- intros F. exact (M5 i ltac:(lia) A F).
-- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
* assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
-- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
-- exact F.
-- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
- right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
- intros NF. exfalso. apply NF. reflexivity.
- intros NF. exfalso. apply NF. reflexivity.
- intros NF. exfalso. apply NF. reflexivity.
Qed.
Lemma fin_MR3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "J';'QE&FvS1vRH%3221(QG(1&Q7%211(2vRA%2241&R<&QDvR@%211+1%5221vRG%611%8215vRMvRI%B9??<635721%I3HD1").
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "A&Q7&<';r1vRH%33521%511'QE&FvS1r2%3221vS0%5213%<3731p091pVJ@1").
Proof. intros x. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.
Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.
Lemma fin_head3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "<';&QI&Q;vS1(Q5vRM%211%5241(1&Q7%211%;3:41").
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.
Lemma fin_INV4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "E&EvC(KvRE(7&Q7%211(2vRL%2241(1'=%211vRH%7291%=5<9631vS2v?v0vB%D6C54321").
Proof.
apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
- rewrite fin_MR3. reflexivity.
- unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
- cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.
Lemma fin_LS4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "?';'6&Q7%211vB(Q5vRM%211%411(5vRH(7%11:%43;31%>3;61").
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.
Lemma fin_MR4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "L':';'9&QI'>%3221%4212%5213&Q3&FvS2vRH%3221%511vS1%6214%811%@3:41&Q?%117%215%D3A21&Q@%11;%219%H3E21%J251%K2:1").
Proof.
pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.
Lemma fin_geo : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot "C&Q7';'9&QI'>%3221%4212%5213&Q3&FvS2r1%3221%511vS0%6214%811%@3:41pVJB1").
Proof. intros x.
pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
destruct (aptr_eq_dec x m) as [->|NE].
- rewrite fin_MR3, Em. reflexivity.
- rewrite (fin_MR3_other x NE). reflexivity.
Qed.
Theorem slot_finish_ok :
exists LS',
queue (LActive sc) m st3 k bail = k st4
/\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
/\ TF2 st4
/\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
/\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
/\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
/\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2.
Proof.
exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, FC.
pose proof fin_INV4 as INV4.
assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
split; [exact fin_queue_eq|].
split.
{
apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
intros b' ai' Hb'. rewrite G4 in Hb'.
assert (Eb : b' = b /\ ai' = ai).
{ pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
destruct Eb as [-> ->].
assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
rewrite Esc. split; [| split; [| split]].
- intros _. rewrite fin_LS4. left. reflexivity.
- intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
- intros sc0 Hin Hh. exfalso.
pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
- intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
split.
{ apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.
End CEIL_WRAP_1.
