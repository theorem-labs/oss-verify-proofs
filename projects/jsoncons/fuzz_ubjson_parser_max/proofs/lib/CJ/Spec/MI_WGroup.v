(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
MI_WFree MI_WFree2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WGroup () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Ext."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Kit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Pres2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup.CEIL_WRAP_1.NL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1Some"; "1app"; "1cons"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2iff"; "2not"]; ["2or"; "3map"; "4N"; "4Z"; "0L"; "0LS"; "0RUNp"; "5mled"; "6ctrl_eq"; "7INVL"; "7MR"; "7blk"; "7extras"; "7gbase"; "7hosts"; "7known"]; ["7sstart"; "8sh_ticks"; "9inT"; ":DOMS"; ";nl_list"; ":TF"; ":TKS"; ":wrs"; ":zlist"; "<Known"; "<RKGroup"; "<UNIT"; "<aadd"; "<aptr"; "<cell_read"; "<cellval"]; ["<get_shadow"; "<hdr_havoc"; "<lhead"; "<mstate"; "<r_cells"; "<r_kind"; "<region"; "<rkind"; "<s_regions"; "<s_shadow"; "<s_tick"; "<set_tick"; "<shadow"; "<slot_start'"; "<wr8"; "<zero_hdrs"]; ["=In"; ">le"; ">lt"; "?add"; "?land"; "?le"; "?lor"; "?lt"; "?modulo"; "?mul"; "?of_nat"; "?shiftr"; "?sub"; "0T"; "0X"; "0a"]; ["0b"; "0bg"; "0c"; "0cnt"; "0d"; "0g"; "0i"; "0idx"; "0k"; "0k'"; "0l"; "0l1"; "0l2"; "0n"; "0o"; "0p"]; ["0q"; "0r"; "0rid"; "0sh"; "0size"; "0st"; "0st'"; "0st0"; "@lookup"; "AN_countable"; "AZ_countable"; "Bgmap"; "Bgmap_lookup"; "Ceq_dec"; "Deq_dec"; "0t"]; ["0v"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition TF (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.
Definition TKS (st : mstate) (T : N) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh ->
(forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.
Lemma TKS_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "L'L'QC'G'5&K%211'QB&Q=%511p031&IvFr5r4r3r2r1%76654321&Q6&QJ%118%3291p051pQ<>1p2C1pQ:G1pV<I1pTNK1").
Proof. intros X st L BL LS. intros INV. exact (ish_ticks _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
Lemma DOMS_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "J'L'QC'G'5&K%211'QB&Q=%511p031&IvFr5r4r3r2r1%76654321&Q3%1277p031pQ<<1p2A1pQ:E1pV<G1pTNI1").
Proof. intros X st L BL LS. intros INV. exact (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
Lemma TF_tick_new : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "D'QC'B&Q6r2&QJ%112%4231&R2r3%511%3217&Q5&QKr4%2261%411p061p0;1pW0A1pV<C1").
Proof. intros st t.
intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. lia.
Qed.
Lemma get_shadow_cells_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QF'QC'B'C'9%1223'<'7%113&S8'S;&S>&S:%34:218&S<%14<43:r2&QD&Q@r4r3%3221%511%>6DB:871(1r1%22E1%E3C41'='QL';%H12&S=&S9%H4Q0215%E4Q1326r5&QIr6%211%O6Q6;6541%A2<@%Q43;21%J1B%Q36Q9Q7OMI1%E2Q8I%Q83Q621%A251qV8C1%E2D1p0G1pU6Q>1pUNQA1pV6QC1pV<QE1").
Proof. intros st rid o c.
unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn; [intros H; exists sh; auto|]. rewrite lookup_empty. discriminate.
Qed.
Lemma TF_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "J'QC'9'B'C%3221&Q5r3%211&R5+<&R8&:%13:96+@%4221%7261&QNr4r5%332=1%?11p061p0?1pW2D1pV2D1pV<I1").
Proof. intros st q v.
intros H Hq rid sh o w t. rewrite (wr8_shadow_lookup st q v rid). destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
intros E. inversion E. subst sh. cbn. destruct (Z.eq_dec o (snd q)) as [->|NEo].
- rewrite lookup_insert_eq. intros _ _. exact Hq.
- rewrite lookup_insert_ne by congruence. intros Ho Et. destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
Qed.
Lemma TF_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "<'QC&Q=&Q5r2%211&QAr3%2241%611p051pU291pV<;1").
Proof. intros st b.
intros H rid sh o w t. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn. intros Ho Et.
destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
- rewrite lookup_insert_ne by congruence. apply H.
Qed.
Lemma TF_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "K'QC'<'S;'B&S=&S9'QL%544321&QIr1%211r2%411%<3631&QJ%114r3%311%A3?31&Q5r4%211p011p051p0;1pV>I1pV<J1").
Proof. intros st st'. intros E1 E2 H rid sh o v t. rewrite E1, E2. apply H. Qed.
Section SE.
Local Abbreviation SEC_T_TKS_hdr_havoc := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "?'QC&Q=&Q6r2&QJ%112%4231&QAr3%2261%612%9221p061pU2<1pV<>1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_TKS_hdr_havoc) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_TKS_hdr_havoc) 1%nat 0%nat).
Lemma TKS_hdr_havoc : ltac:(sec_stmt2 constr:(SEC_T_TKS_hdr_havoc) 2%nat 0%nat).
Proof.
intros TK rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn.
assert (G : forall P : shadow -> Prop, (forall sh, s_shadow st !! fst b = Some sh -> P sh) -> P shadow0 -> P (get_shadow st (fst b))).
{ intros P H1 H0. unfold get_shadow. destruct (s_shadow st !! fst b) eqn:Es; [apply H1; reflexivity| exact H0]. }
split; [| split].
- apply (G (fun sh => forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (TK _ _ Hsh))| intros o w t Ho; cbn in Ho; rewrite lookup_empty in Ho; discriminate].
- intros u hl ch. destruct (Z.eq_dec u (snd b / 16)) as [->|NEu].
+ rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. intros [<-|Hin]; [cbn; lia|].
apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
* intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
* cbn. rewrite lookup_empty. cbn. tauto.
+ rewrite lookup_insert_ne by congruence.
apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
cbn. rewrite lookup_empty. discriminate.
- apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed.
End SE.
Lemma DOMS_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QB'QC'9'B'C%3221&Q3r4r3%3221'='QF';'<'7%114&S8'S;&S=&S9%34A219&S<%14C43;&4%13EDA&QHr6%211%<6IA8641(1r1%22D1%C3A41'QG&QE%115(Q:%H3421%J261qV4L1%N2M1&QNr5%23Q4Q31%Q62B1p051p0Q51pW2Q;1pV2Q;1pV<Q@1pV@QA1").
Proof. intros st0 st q v. intros D Hq. unfold DOMS. apply (wr8_dom st q v (fun rid => exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup) D Hq). Qed.
Lemma DOMS_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QA'QC'9'B'C%3221&Q3r3r2%3221'='QF';'<'7%114&S8'S;&S=&S9%34A219&S<%14C43;&4%13EDA&QHr5%211%<6IA8641(1r1%22D1%C3A41'QG&QE%115(Q:%H3421%J261qV4L1%N2M1&QAr4%22Q41%Q62B1p051p0Q51pU2Q:1pV<Q?1pV@Q@1").
Proof. intros st0 st b.
intros D Hb rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [intros _; exact Hb|].
rewrite lookup_insert_ne by congruence. apply D.
Qed.
Lemma TKS_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "I'QC&Q='C'B&R1&QJr4%211r1%5221&Q6r5r2%3221&QNr6%235:1r3%8221p061p0;1pTLB1pW2D1pV2F1pV<H1").
Proof. intros st q v T. intros LE TK. exact (wr8_tks st q v T LE TK). Qed.
Lemma sh_ticks_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "@'QC'B&Q6r2&QJ%112%4231&Q1&Q@r3%2217%712%5221p071pV6=1pV<?1").
Proof. intros st rid.
intros TK. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
- destruct (TK _ _ E) as (_ & A & B). split; [exact A| exact B].
- split; [intros u hl ch H; rewrite lookup_empty in H; discriminate| intros pg t H; rewrite lookup_empty in H; discriminate].
Qed.
Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.
Lemma wrs_app : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "E'5'9&Q='C%3221%511'QC'<&Q7&2r3r2%33821r1%6221%7252%8251%:3;31pV<<1pUJ>1pUH?1").
Proof. intros l1 l2 st. revert st. induction l1 as [|[q v] l1 IH]; intros st; cbn; [reflexivity| apply IH]. Qed.
Section WRS.
Lemma wrs_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "G'5'9&Q='C%3221%511'QC';'Hr1&Q7r2%2213%5241'<'B&QJ%115%219%53421%=271pV<?1pUFA1").
Proof. intros l st.
revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.
Lemma wrs_read_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "Q6'5'9&Q='C%3221%511'QC&?&R0r1&A&4%12:9r3%44:<21%73=61%911'<'Q?&Q>&Q@&Q7r4%221:'Br2%?32G1%7241&:%135J4%;231%;2B5%=213%@3?31p0B1pV2Q11pV<N1pUFQ01").
Proof. intros l st q.
revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.
Lemma wrs_TKS : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "K'5'9&Q='C%3221%511'QC'B&R1&QJr2%211r1%5221&Q6r3%2216&Q7r5r4%3221%7216p061p0:1pTLA1pV<C1pUFE1").
Proof. intros l st T.
revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.
Lemma wrs_DOMS : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QL'5'9'B'C%3221%4212%611'QC&Q3r2r1%3221&R0&A&4%12;<r5%44<=21%63>81'='QF';'<'7%114&S8'S;&S=&S9%34K219&S<%14M43;r3%C3ON1&QHr6%211%<6Q3A8641(1%12CM%B3@31'QG&QE%11Q1(Q:%G3421%I261qV4K1%M2L1p0O1pV2Q>1r4&Q7%12Q5E%Q>231p051p0Q=1pV<QB1pV@QC1pUFQE1").
Proof. intros l st0 st.
revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.
Lemma wrs_TF : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "Q5'5'9'B'C%3221%4212%611'QC&Q5r1%211&R0&A&4%12:;r4%44;<21%63=81&R5+<&R8&:r2%23ED1+@%5221%8271p0:1pV2H1&Q7r3%22@1%H11p051p0H1pV<L1pUFN1").
Proof. intros l st.
revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.
Lemma wrs_read_last : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QH'5'9&Q='C%3221%511'QC&?&R0r4&A&4%12:9r2%44:<21%73=61%911&Q6&QJ%116%3271'<'Q?&Q>&Q@&Q7&2r7(3(8r6r5%34NM21%53M1H%83N71r3%;221'B%K31Q38%?231&:%134Q6;%C231(Q9&R4+WO%22?1%411%K3J61p0M1p0Q21pV<Q=1pUJQ?1pW2QB1pV2QD1pUHQB1").
Proof. intros l1 q v l2 st.
intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
destruct (wrs_ctrl l1 st) as [C T].
apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. apply wrs_TKS; [lia| exact TK].
Qed.
End WRS.
Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.
Lemma zero_hdrs_wrs : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "F&Q='C'6'QC'<&QOr5r4r3r2r1%6554321&Q7&Q8%148765%3215%<3=51pV<>1pUL@1pU>B1pV:C1pV0E1").
Proof. intros p size i n st. revert i st. induction n as [|n IH]; intros; cbn; [reflexivity| apply IH]. Qed.
Lemma in_zlist : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "QC&Q='C'6&>&R0r3&A'9%1287&4%12:9&Q8r5r4r1r2%544321%;49A71%>3B=1'=';&R5%1278&R7&R3&R:%11E%32<1%52>1%9271'<&Q<r6&R<&Q;&R9%12FH%=231+4%6221%9281%;3Q9L1%F2=1qUBQ:1%I2Q;1%Q:2K1pU>Q=1pULQ=1pV2Q@1pV:Q@1pV0QB1").
Proof. intros p size q.
induction n as [|n IH]; intros i; cbn.
- split; [tauto| intros (k & Hk & _); lia].
- rewrite IH. split.
+ intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
+ intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed.
Lemma zlist_split : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "RA&Q='C'6';&R5r3r1%3221&R7&R3&R:r2%211%4281%6281%<281'='5'9%12CB%311'<&Q8r8r7r6r5%544321&2(3(8&Q<&R<&Q;&R9r4%221<%L241+4%7221%92A1z%<4Q:Q921%>3H1Q5%@3IQ11%H3IB1&R0&A&4%12QAQ@%34OQB1Q7%53QCQ=1%Q<2LQ>r9%Q<1O%Q>221%Q@2QB1%QF251r;r:%J2QF1%QD2L1%N21H%Q0251%Q;3R0QK1%QN281qUDR11%QC2R21p0A1pV2R51%R32I1qUJQC1%QH2QD1qUHQE1%QJ2QF1p0QL1pUBR;1pULR;1pU>R=1pV:R>1pV0R@1").
Proof. intros p size i n k.
revert i. induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
cbn. destruct (Z.eq_dec k i) as [->|NE].
- exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
- destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed.
Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.
Definition nl_list : list (aptr * Z) :=
[(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
(aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).
Lemma g_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "5&NvS5vRAvRE%43321"). Proof. exists aig. exact Hg. Qed.
Lemma p_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup ";'<&Q=&QM&JvS5vRE%3221vRG%6221vRO%:3921"). Proof. unfold p. apply (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ g_hosts). Qed.
Lemma bg_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup ":'<&Q=&M&JvS5vRE%3221%511vRA%93821"). Proof. apply (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ g_hosts). Qed.
Lemma nl_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "8'<'QCvS6&Q7&Q4vS5%3221%73651").
Proof.
unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
rewrite p_eq. unfold set_size.
replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed.
Lemma p_mod16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup ";'<'C&R8&:'BvRO%33251+@%6221z%:3921").
Proof.
unfold p. cbn. unfold sstart. rewrite bg_gbase.
pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
apply Z_mod_mult.
Qed.
Lemma res16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "@'C'<&R8r2+@%3221z%63721&R3r3%2217%9217%;3<17p061pU:>1pU0?1").
Proof. intros a d. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_nl_residues := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "H&Q=&R0r1&A'9'C%2261&4%1283&Q4%744:21%:3;91&R5+<&R8&:'Br2%332=1+@%6221%9281p0;1pV4G1")) (only parsing).
Variable r : ltac:(sec_ty2 constr:(SEC_T_nl_residues) 0%nat 0%nat).
Lemma nl_residues : ltac:(sec_stmt2 constr:(SEC_T_nl_residues) 1%nat 0%nat).
Proof.
pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
- destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); cbn; lia.
- apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [cbn; lia|].
rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_nl_in_T := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "Q:&Q=&R0r1&A'9'C%2261&4%1283&Q4%744:21%:3;91'@&Q2'BvRA%932;1&R<&Q0&JvS5vRE%3221vRG%6221+3%9221&R3+1%2261%<281+4%?221r2%E4B821'<(8%14GQ0E5%33Q651%K251p0M1pV4Q91")) (only parsing).
Variable r : ltac:(sec_ty2 constr:(SEC_T_nl_in_T) 0%nat 0%nat).
Lemma nl_in_T : ltac:(sec_stmt2 constr:(SEC_T_nl_in_T) 1%nat 0%nat).
Proof.
unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
- left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
- apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
+ right. unfold aadd. cbn [fst snd]. f_equal. lia.
+ left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed.
End SE.
Lemma nl_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "E&Q=&R0r1&A'9'C%2261&4%1283&Q4%744:21%:3;91'<'Br2%832:1vRA%:34<1%63531p081pV4D1").
Proof. intros r. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.
Theorem nest_layout_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WGroup "S<';&IvFvR>vS6vDv0vE%76654321&Q5%116'HvS5%2219'<'B&QJ%11=%216%53421&O&Q<vRO-3%3221&R4&R6vRG+O%4221+V0%5221+WO%8221%>3N:1-2%?2>1vS0%=216%C3Q331+1%D251&R;+8%2271%D21=%J3Q:51'C&R5zr1%3221vRC%5231%QF231&R<&R3&Q;&R9r2vS4%3221%6251+4%9221%Q<2Q;1%Q>3QN1Ap0=1pUBE1&Q=&?&Q2&4vRA%23QKK1&Q0&JvRE%22R21%421QD+3%J221%J2QGQ:%8251%M21E%>4;41Q3%@11'Q?&Q>&Q@%B3R;Q;O%22RG1&:%13R>Q>Q2%6231%62RC5%8213%RC3:31p0<1pV4N1%S42Q01%S52QG1%S62QO1%S72R51%S82RE1%S92RL1%S:2S01%S;2S31").
Proof.
rewrite nl_eq. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (wrs_ctrl nl_list st) as [CE TK].
pose proof (TKS_of _ _ _ _ _ INV) as TK0. pose proof (DOMS_of _ _ _ _ _ INV) as DM0.
assert (RD : forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
cell_read (get_shadow (wrs nl_list st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
{ intros r Hr. destruct (in_dec aptr_eq_dec r (map fst nl_list)) as [Hin|Hn]; [| apply wrs_read_other; exact Hn].
destruct (nl_in_T r Hin) as [HT| ->]; [exfalso; exact (Hr HT)|].
pose proof (ish_hdr0 _ _ ISH bg g (idx + 1) g_hosts ltac:(unfold cnt_of; lia)) as K0. unfold known, SHd, IB in K0. cbn [fst snd] in K0 |- *. rewrite K0.
assert (E : (fst bg, sstart (MR st g) (idx + 1) - 4) = aadd p (UNIT + cnt * size - 4) /\ UNIT + cnt * size = get_stride (MR st g)).
{ unfold nl_list in Hin. rewrite map_app in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
- exfalso. cbn [map fst In] in Hin. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold p, aadd in E; cbn [fst snd] in E; rewrite sstart_succ in E; unfold UNIT in *; lia.
- apply in_zlist in Hin as (k & Hk & Ek). rewrite Z2Nat.id in Hk by lia. apply (f_equal snd) in Ek. unfold p, aadd in Ek. cbn [fst snd] in Ek.
rewrite sstart_succ in Ek. destruct (Z.eq_dec k cnt) as [->|NEk].
+ split; [unfold p, aadd; cbn [fst snd]; rewrite sstart_succ; f_equal; unfold UNIT in *; lia| unfold UNIT in *; lia].
+ exfalso. assert (k * size <= (cnt - 1) * size) by nia. unfold UNIT in *. lia. }
destruct E as [E1 E2]. apply (f_equal snd) in E1. cbn [snd] in E1. rewrite E1.
destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) cnt ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & EZ & Hl2).
change (cell_read (get_shadow (wrs nl_list st) (fst (aadd p (UNIT + cnt * size - 4)))) (snd (aadd p (UNIT + cnt * size - 4))) = Known (Z.land 0 255)).
unfold nl_list. rewrite EZ.
rewrite (app_assoc _ l1) || rewrite app_assoc.
apply wrs_read_last; [| exact TK0].
intros Hin2. destruct (Hl2 _ Hin2) as (k' & Hk' & _). rewrite Z2Nat.id in Hk' by lia. lia. }
pose proof (is_part _ _ _ IS _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite p_eq, HP in P5. unfold one5 in P5.
assert (NH : s_groups st !! p = None).
{ destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
assert (NB : forall k, In k BL -> bslot k <> p).
{ intros k Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk. }
assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hg).
split; [| split; [| split; [exact CE| split; [exact TK|]]]].
- split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
apply (inv_SH_write_T X st (wrs nl_list st) BL LS IM IG IS ISH g bg idx g_hosts Hidx NH NB CE TK RD).
+ apply wrs_DOMS; [exact DM0|]. intros r Hr. rewrite (nl_regions r Hr). exact REG.
+ apply wrs_TKS; [lia| exact TK0].
- apply wrs_TF; [exact HTF| apply nl_residues].
-
assert (KN : forall l1 r v l2, nl_list = l1 ++ (r, v) :: l2 -> ~ In r (map fst l2) -> known (wrs nl_list st) r (Z.land v 255)).
{ intros l1 r v l2 E Hn. unfold known, SHd. rewrite E. apply wrs_read_last; [exact Hn| exact TK0]. }
pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
assert (ZL : forall r, In r (map fst (zlist p size 0 (Z.to_nat (cnt + 1)))) -> snd p + 12 <= snd r).
{ intros r Hr. apply in_zlist in Hr as (k & Hk & ->). cbn. unfold UNIT. nia. }
split; [| split; [| split; [| split; [| exact RD]]]].
+ apply (KN [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5)] (aadd p (-3)) _ (zlist p size 0 (Z.to_nat (cnt + 1))) eq_refl).
intros Hin. pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ rewrite <- (Z.land_assoc q 255 255 : Z.land (Z.land q 255) 255 = Z.land q (Z.land 255 255)) || idtac.
replace (Z.land q 255) with (Z.land (Z.land q 255) 255) by (rewrite <- Z.land_assoc; reflexivity).
replace (Z.land (Z.land q 255) 255) with (Z.land q 255) by (rewrite <- Z.land_assoc; reflexivity).
apply (KN [] (aadd p (-2)) q _ eq_refl).
cbn [map fst app]. intros [E|[E|[E|[E|Hin]]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ apply (KN [(aadd p (-2), q)] (aadd (aadd p (-2)) 1) (Z.shiftr q 8) _ eq_refl).
cbn [map fst app]. intros [E|[E|[E|Hin]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ intros k Hk. destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) k ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & E & Hl2).
change (known (wrs nl_list st) (aadd p (UNIT + k * size - 4)) (Z.land 0 255)).
apply (KN ([(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5); (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ l1) _ 0 l2).
* unfold nl_list. rewrite E. rewrite <- app_assoc. reflexivity.
* intros Hin. destruct (Hl2 _ Hin) as (k' & Hk' & E'). unfold aadd in E'. apply (f_equal snd) in E'. cbn in E'. unfold UNIT in E'. nia.
Qed.
End NL.
End CEIL_WRAP_1.
