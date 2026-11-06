(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Shadow MI_WFree2 MI_WGroup.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_TF2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_TF2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "3map"; "4N"; "4Z"; "0P"; "0P'"; "5MR"]; ["5hosts"; "5sstart"; "6PS"; "6TF0"; "6TF2"; "6TW"; "6geom_kept"; "7TF"; "7TKS"; "7wrs"; "8IB"; "8aptr"; "8get_shadow"; "8ghdr"; "8hdr_havoc"; "8meta"]; ["8mstate"; "8r_cells"; "8s_groups"; "8s_shadow"; "8s_tick"; "8set_tick"; "8shadow"; "8wr8"; "9In"; ":lt"; ";add"; ";le"; ";lt"; ";modulo"; ";sub"; "0a"]; ["0b"; "0bg"; "0c"; "0g"; "0h"; "0i"; "0idx"; "0l"; "0m"; "0o"; "0p"; "0q"; "0rid"; "0st"; "0st'"; "<lookup"]; ["=N_countable"; "=Z_countable"; "=prod_countable"; ">prod_eq_dec"; "?gmap"; "?gmap_lookup"; "@eq_dec"; "Aeq_dec"; "0t"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).
Definition TF0 (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.
Definition PS (st : mstate) (q : aptr) : Prop :=
exists b m, hosts st b m /\ fst b = fst q /\
((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
\/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).
Definition TF2 (st : mstate) : Prop := TW st (PS st).
Lemma TF0_TW : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "='Q0&K!p021&Cr2%211&Er3%2214p041pL81pSL<1").
Proof. intros st P. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "9'Q0&Cr1%211&Dr2%211p041pSL81"). Proof. intros st. apply TF0_TW. Qed.
Lemma TF0_TF : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "9'Q0&Cr1%211&Gr2%211p041pSL81").
Proof. intros st. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TW_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "E'Q0&K!p021r3r1%211r2%411p031pSH91&Er4%2219r5%421;p031p071pN?1pL@1pSLD1").
Proof. intros st P P'. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.
Lemma TW_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "Q0'Q0&K!p021'8'R4';&R6&R0'Q6%544321&Q3r2%211r3%411%<3631&Q4%114r4%311%A3?31&Er5%221:%3226p021p061p0<1pLJ1pSNN1pSLO1").
Proof. intros st st' P. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.
Lemma TF0_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "K'Q0'8'R4';&R6&R0'Q6%544321&Q3r1%211r2%411%<3631&Q4%114r3%311%A3?31&Cr4%211p011p051p0;1pSNI1pSLJ1").
Proof. intros st st'. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.
Lemma TF0_tick_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "D'Q0';&Hr2&Q4%112%4231&Q9r3%511%3217&C&Q5r4%2261%411p061p0;1pTBA1pSLC1").
Proof. intros st t.
intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.
Lemma TF0_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "<'Q0&K&Cr2%211&Nr3%2241%611p051pS291pSL;1").
Proof. intros st b.
intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
change (s_tick (hdr_havoc b st)) with (s_tick st).
destruct (N.eq_dec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
+ eapply H; eassumption.
+ rewrite lookup_empty in Hc. discriminate.
- rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.
Lemma TW_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "A'Q0&K!p021&Er3r1%3221&Nr4%2251r2%8221p061pL;1pS2>1pSL@1").
Proof. intros st b P.
intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
destruct (N.eq_dec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
+ eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
+ rewrite lookup_empty in Hc. discriminate.
- rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.
Lemma TW_wr8' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "G'Q0&K'<!p031&Er4r1%3221r2%114&Q7r5r6%33281r3%;221p071p0:1pL?1pTDB1pSHD1pSLF1").
Proof. intros st q v P.
intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
unfold wr8, upd_shadow in Hs. cbn in Hs.
destruct (N.eq_dec rid (fst q)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
destruct (Z.eq_dec o (snd q)) as [->|NEo].
+ replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
+ rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
- rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.
Lemma TW_wrs : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "Q1'2'5&K'<%3221%511'Q0!p061&Er2r1%3221&Q8&:&1%12>=r5%44>@21%63A81r4%11;p031pSHE1&I%1285r3%B221p051p0A1pLF1pSLI1pS@K1").
Proof. intros l.
induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
apply IH.
- apply TW_wr8'; [exact H| apply HP; left; reflexivity].
- intros q' Hq'. apply HP. right. exact Hq'.
Qed.
Definition geom_kept (st st' : mstate) : Prop :=
forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
/\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).
Lemma geom_kept_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "5'Q0&Fr1%2211pSL41").
Proof. intros st. intros b m H. auto. Qed.
Lemma geom_kept_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "<'Q0&Fr3r2%3221r5%5214p031p041pS691pS2:1pS0;1").
Proof. intros a b c.
intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.
Lemma PS_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "?'Q0&K&Fr3r2%3221&Br4%2214%3226p021p061pSH;1pSN=1pSL>1").
Proof. intros st st' q.
intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
exists b, m. split; [exact Hm'|]. split; [exact Hf|].
destruct ALT as [(i & Hi & E)|(Z0 & R0)].
- left. exists i. rewrite C, S. auto.
- right. rewrite ML. auto.
Qed.
Lemma TF2_kept : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "O'Q0'8'R4';&R6&R0'Q6%544321&Q3r1%211r2%411%<3631&Q4%114r3%311%A3?31&Fr4%2215&Dr5%211p011p051p091p0?1pSNM1pSLN1").
Proof. intros st st'.
intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.
Lemma geom_kept_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "QG'Q0&K'M'8'3%113&QO'R4&R3';&R6'<&R7%544321&R2&R0&R1%36872651%;4A51@&R5%14C73Br2&Q2r4%211%C6HG7541(0r1%22J1%J3H41r3%I6NM=;17%62N;%N3L21p051pS:Q11pS2Q31&@r5%231B<'O&?%124Er6%321G%Q:3531p071pSBQ>1pS2Q?1&F%12KDp031p0@1pSNQE1pSLQF1").
Proof. intros st st'.
intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
rewrite (HM _ _ Hm). auto.
Qed.
Lemma wr8_cells_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "Q<'Q0'5';'<%3221&9'8(4r2r1%348721r4%63821%811'3%>2<=%211&QO'R4&R7&R1%34B216&R5%14D438&Q1&L&Q7r5r6%332B1r3%6221%811%@6NB<:I1%9264%;11%C6Q1E?=L1%O3E41p0I1pSDQ41pSJQ61pTDQ61pSHQ61pSLQ;1").
Proof. intros st q v rid o.
intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.
Lemma wrs_cells_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "QB'2'5';'<%3221%4212%611'Q0&9&Q8(4r2r1%34;:21&:&1%12<=r4%44=>21%:3?61%<11'8'3%F2DE%211&QO'R4&R7&R1%34J216&R5%14L438&Q1&L&Ir5%221Cr3%5221%711%?6Q5A;9M1%82H4%:11%B6Q8D><Q01%G3D41p0I1pSDQ;1pSJQ=1pSLQ91pS@Q;1").
Proof. intros l.
induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.
Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Lemma sstart_res : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "H&K'<&@vQMr3r2%43321'8&Q=&Q>&A&?%1298%3218&J%6221+@%9221+<%<3B21p0>1pS<D1pTFF1pS2G1").
Proof. intros b x i.
intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Section SE.
Local Abbreviation SEC_T_PS_not_interior := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "Q9&K&BvQMr1%3221'8';&1'<r2%33421vQA%53641%83731&9'7&Q;&A&?vQC%22B1vQF%5221&6r3%23CA1%:241&Q<&Q>&Q:+1%22:1%?2<1&J%6221%82:1%E2:1%G11p0I1p0Q31pSHQ81")) (only parsing).
Variable q : ltac:(sec_ty2 constr:(SEC_T_PS_not_interior) 0%nat 0%nat).
Lemma PS_not_interior : ltac:(sec_stmt2 constr:(SEC_T_PS_not_interior) 1%nat 0%nat).
Proof.
intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)].
- destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
+
assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
destruct (aptr_eq_dec m g) as [->|NEm].
* pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
* destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
+ assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
destruct (aptr_eq_dec m g) as [->|NEm].
* destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
* destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
-
destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
destruct LVp as [bp Hp].
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
assert (NE : p <> g \/ ip <> idx).
{ destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.
End SE.
Lemma TF2_interior_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "QO&DvQM%211'<';'8'3'5%1254%311&QO'R4&R7&R1%34;216&R5%14=438r3&Q1&L&1vQA%23BC1%42F1%611%?6FA;981(0(4r2r1%34KJ21%52G1%K3G71'7&Q;&A&?vQC%22Q51vQF%5221r4%8221&Q<&Q>&Q:+1%2281%=2:1&J%6221%82:1%C2:1&Q9&Q4%11QF%32Q71p051p0J1pTBQG1pTDQI1pSDQJ1p0QL1").
Proof.
intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.
Section SE.
Variables (p : aptr).
Lemma TF2_ghdr_old : TF2 st -> snd p mod 16 = 0 ->
forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
- pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
- destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End SE.
Lemma TF2_TF : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_TF2 "6&DvQM%211&G%113p031").
Proof.
intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
- pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
- destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.
End CEIL_WRAP_1.
