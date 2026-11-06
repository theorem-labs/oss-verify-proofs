(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WEnframe () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Cnt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Ext."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WEnframe.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WEnframe.CEIL_WRAP_1.EF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."], [["0BL"; "1Some"; "1bool"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "0L"]; ["0LS"; "0RUNp"; "4mled"; "5zrange"; "6ctrl_eq"; "7INVL"; "7blk"; "7extras"; "9ef_list"; "8fold_f"; ":DOMS"; ":TKS"; ":wrs"; ";Known"; ";RKGroup"; ";UNIT"]; [";aadd"; ";aptr"; ";cell_read"; ";cellval"; ";enframe_at"; ";fold_off"; ";get_shadow"; ";havoc"; ";lhead"; ";mstate"; ";r_kind"; ";region"; ";rkind"; ";s_regions"; ";s_shadow"; ";s_tick"]; [";shadow"; "<forallb"; "=land"; "=le"; "=lt"; "=modulo"; "=mul"; "0X"; "0a"; "0c"; "0g"; "0idx"; "0n"; "0off"; "0p"; "0p0"]; ["0q"; "0r"; "0slack"; "0st"; "0st0"; ">insert"; ">lookup"; "?N_countable"; "@map_insert"; "Agmap"; "Agmap_lookup"; "Agmap_partial_alter"; "Beq_dec"; "0v"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
Lemma fold_all : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "<';'2&QA'>&I&Cz+X0%3221%73651(9%;3:21"). Proof. vm_compute. reflexivity. Qed.
Lemma fold_off_le : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "E'>':&QCzr2%3221&QD+X0%2241%8241&Q5r4r3%3221%<2;1%=223%?221p0<1p091pT6C1pSLD1").
Proof. intros off slack.
intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
- pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
- unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.
Lemma s_shadow_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "Q4&Q1'>'Q9&QDzr2%3221';'R9'=&R<&R7'Q@%544321&Q>&Q7r4r3%3321=%511&R5&R8&R;%14>=<;%34?<;1&3%13AI:&Q6%12:2%?1H%:7EBA6421%H3B<1p0J1pT8O1pSJQ11pSNQ31").
Proof. intros p n st.
intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.
Lemma TKS_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "Q1'7'='>%3221'Q9';&QE&8r3%23871+@%5221z%83;21&QD%1237&K&Q?%11:%32;1&Q7r6r5r4%43321%812%:221p081p0=1p0@1pT8J1pSJM1pSNM1").
Proof. intros p n st.
intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
- exact (proj1 (TK _ _ E0)).
- intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.
Lemma DOMS_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "QG'Q9'7'='>%3221&QDzr2%3221&Jr5%2214'<'Q;':';'5%114&R6'R9&R<&R7%34D219&R:%14F43;&3r6%23IH1&Q=r7%211%=6MB9741(1r1%22E1%D3B41'Q<&Q:%115(N%I3421%K261qT4M1%O2N1&Q7r4%23DQ41%Q62B1p051p0Q61p0Q:1pT8QC1pSJQA1pSNQA1pT:QF1").
Proof. intros st0 p n st.
intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.
Lemma havoc_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "E&Q1'>'Q9':'Dr1&Q7r3r2%33214%6251';'=&Q?%115%21:%53421%>271pT8@1pSJB1pSND1").
Proof. intros p n st. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.
Lemma set_size_wrs p e n b3 st :
set_size p e n b3 st =
wrs ((if negb (snd e - snd p - n =? 0) then [(aadd e (- (snd e - snd p - n)), 0)] else [])
++ (if 5 <=? snd e - snd p - n then [(aadd e (-4), snd e - snd p - n); (aadd (aadd e (-4)) 1, Z.shiftr (snd e - snd p - n) 8); (aadd (aadd e (-4)) 2, Z.shiftr (snd e - snd p - n) 16); (aadd (aadd e (-4)) 3, Z.shiftr (snd e - snd p - n) 24); (aadd e (-5), 0)] else [])
++ [(aadd p (-3), Z.land b3 31 + Z.shiftl (if 5 <=? snd e - snd p - n then 5 else snd e - snd p - n) 5)]) st.
Proof.
unfold set_size. generalize (snd e - snd p - n). intros r.
destruct (r =? 0); destruct (5 <=? r); reflexivity.
Qed.
Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.
Definition ef_list : list (aptr * Z) :=
(if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].
Lemma enframe_at_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "C';'7'Q9&Q1%3221&Q4vR3vQJvQKvQLvQM%6554321(6&L&H%2219vQO%54?>21%B3>71").
Proof.
unfold enframe_at, ef_list, q, res, p0, e, c, gm, stride, mr.
generalize (get_meta_rec st g); intros MR. generalize (get_stride MR); intros STR. generalize (default (0%N, 0) (m_mem MR)); intros GM.
destruct (off =? 0); cbn beta iota delta [negb]; rewrite set_size_wrs; unfold wr16; cbn beta iota delta [wrs app]; reflexivity.
Qed.
Lemma p0_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe ";';&Q1vQO&Q0vQI&QF&OvQM%3221%6251%:3981").
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.
Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
match l with
| [] => acc
| (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
end.
Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.
Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
destruct (aptr_eqb_spec a r) as [<-|NE].
- rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
- destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.
Lemma known_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe "QE'G'Q9'B'4&F%211'Q8&Q1%511p031'7'='>%3221&EvAr7r6r5r4r3%76654321';'Q3&Q2&Q6&3%13@?7%32<1&8%13CB:%7231(Mr2%211%=3<41':&QCz%221C&QD+X0%22F1%7241p091p0H1pTLQ21pT2Q21pQ2Q71p2Q<1pQ0Q@1pT8QB1pS@QD1").
Proof. intros X st L BL LS q v.
intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.
Lemma havoc_0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe ";&Q1'Q9';&Q7r2zr1%43321%63712pT881pSN:1").
Proof. intros p st. reflexivity. Qed.
Lemma land255_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe ">'>':&QCz&QBr1+WO%3221%6251&QD+X0%2241%;241pSB=1").
Proof. intros a.
split; [apply Z.land_nonneg; right; lia|].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
End CEIL_WRAP_1.
