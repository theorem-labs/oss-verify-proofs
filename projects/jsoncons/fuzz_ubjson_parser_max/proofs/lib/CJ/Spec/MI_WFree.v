(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Shadow MI_Read MI_Pres1 MI_Pres2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WFree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WFree.CEIL_WRAP_1.BLOCK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.STree."; "Stdlib.ZArith.BinInt.Z."], [["1Some"; "1fst"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2or"; "3N"; "3Z"; "4MR"; "4gbase"; "4sstart"; "5blk_facts"]; ["6M"; "6UNIT"; "6aadd"; "6aptr"; "6area"; "6ev"; "6free_hdr"; "6mstate"; "6size_class"; "6wr16"; "6wr8"; "7SRet"; "0S"; "8add"; "8div"; "8le"]; ["8lt"; "8modulo"; "8mul"; "8pow"; "8sub"; "0a"; "0ai"; "0ar"; "0bm"; "0c"; "0d"; "0e"; "0ea"; "0i"; "0ka"; "0last"]; ["0m"; "0maplen"; "0n"; "0off"; "0p"; "0q"; "0res"; "0sc"; "0st"; "0stride"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma guard_true {R} tag (c : bool) (k bail : M R) : c = true -> guard tag c k bail = k.
Proof. intros ->. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_size_class_28 := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "A';'6&O+Lr1%3221&Q0+Q@%2241%8241+Y4&Hr2%211%<241p061pS@@1")) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_size_class_28) 0%nat 0%nat).
Lemma size_class_28 : ltac:(sec_stmt2 constr:(SEC_T_size_class_28) 1%nat 0%nat).
Proof.
intros H. unfold size_class.
assert (E : exists n, Z.to_nat sc = (28 + n)%nat /\ (n < 20)%nat) by (exists (Z.to_nat sc - 28)%nat; lia).
destruct E as (n & -> & Hn).
do 20 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.
End SE.
Lemma guard16_arith : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "R7';&O+1r7%3221'7&Q2+@r3%3221&Mr6%6291r5%8271%5231%;3@71%;2:6%8215&Q4r8+4%3221%F251z%H21>'6%J237+WO%L291%4231r:%O281%Q022F%8221'9r<r=%Q02O1%Q23Q731%Q33Q8Q5@%6221r>%Q52Q41%Q;271+Y4%Q=214%<231r?%Q;21<%QA21C&Q0%Q:2?QB%Q?251%32G1%M251p091p0@1p0H1p0M1p0Q31p0Q61p0Q>1p0QK1pS0R01pS<R11pS6R21pS8R31pRLR41pSDR51pQJR61").
Proof. intros S stride i off n q last.
intros HS Hq Hfit Hn Hoff Hi A B.
destruct A as [E|L0].
- subst stride. assert (q = S * i + off) by lia. subst q. nia.
- assert (i = 0) by lia. subst i. assert (q = off) by lia. subst q. lia.
Qed.
Lemma guard17_arith : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "QK';&O+@r7%3221'7&Q2r4%2261&Mr8%5218r6%72;1%5231%:3?71%:2>=%8215&Q4r9+4%3221%E251z%G21E%H226'6r;%K251%L22J%4221r=+1%H2G1%L231%J2Q11+TP0%O2Q21%Q5231r:&N%Q32O5%221Q8%I21;%Q;251p071p0@1p0F1p0H1p0K1p0Q31p0Q?1pS4QD1pS0QE1pS<QF1pS6QG1pS8QH1pRLQI1pSDQJ1").
Proof. intros stride i off n q last maplen.
intros. replace (maplen * 4096 / 16) with (maplen * 256) by (rewrite <- (Z.div_mul (maplen * 256) 16) by lia; f_equal; lia).
assert (stride * i + stride <= stride * (last + 1)) by nia. lia.
Qed.
Section BLOCK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (c : cptr) (off n : Z).
Hypothesis Hk : In ((c, off), n) BL.
Local Notation R := (MR st).
Record blk_facts (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) : Prop := mkBF {
bf_slot : s_slots st !! c = Some (m, i);
bf_hosts : s_groups st !! bm = Some (mkGhdr (Some m) ai);
bf_mem : m_mem (R m) = Some bm;
bf_c : c = (fst bm, sstart (R m) i);
bf_i : 0 <= i <= m_last_idx (R m);
bf_li : m_last_idx (R m) <= 31;
bf_ai : 0 <= ai <= m_last_idx (R m);
bf_off : 0 <= off <= 255;
bf_n : 0 <= n;
bf_fit : UNIT * off + n <= get_stride (R m) - IB;
bf_stride : UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0;
bf_b16 : 0 <= snd bm /\ snd bm mod UNIT = 0;
bf_notA : tbit (m_avail (R m)) i = false;
bf_notF : tbit (m_freed (R m)) i = false;
bf_notH : s_groups st !! c = None;
bf_sc : (0 <= m_sizeclass (R m) < 48 /\ (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
/\ (get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) \/ (m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0)))
\/ m_sizeclass (R m) = 63;
bf_top : m_maplen (R m) <> 0 -> snd bm = 0 /\ gend (R m) <= m_maplen (R m) * 4096;
bf_maplen : 0 <= m_maplen (R m);
bf_area : s_areas st !! a = Some ar /\ a_check ar = c_secret (s_ctx st) /\ snd a mod PGSZ = 0 /\ 0 <= ka < NSLOTS /\ m = mslot a ka;
bf_shadow : blk_shadow_ok st ((c, off), n) m i;
bf_hdr0 : known st (fst bm, sstart (R m) (i + 1) - IB) 0;
bf_bytes : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256
}.
Lemma block_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "K'8&C';'D'?r7r6r5r4r3r2r1%877654321qRN;1%>2<1qR@<1%@2=1qR<@1%B2A1qR>A1%D2B1qRLC1%F2D1qRBF1%H2G1qS2H1%J2I1").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Hoff & Hn & Hfit). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec).
pose proof Hm as [ai Hm'].
pose proof (ig_ok _ _ _ IG _ _ _ Hm') as GO.
pose proof (hosts_mem _ _ _ IM _ _ Hm) as Hmem.
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! m) as [mr|] eqn:Em; [| congruence].
destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
exists m, bm, i, ai, a, ar, ka.
pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec in P.
assert (U : In c (map bslot BL)) by (change c with (bslot ((c, off), n)); apply in_map; exact Hk).
unfold one5 in P.
constructor; auto.
- pose proof (g_li _ _ _ _ _ _ GO). lia.
- exact (g_ai _ _ _ _ _ _ GO).
- exact (stride_ge _ _ _ IG _ _ Hm).
- exact (g_align _ _ _ _ _ _ GO).
- destruct (tbit (m_avail (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
- destruct (tbit (m_freed (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
- destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. tauto.
- destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc Hml]|(Hsc & Hli & Hml & _)]; [left| right; exact Hsc].
destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
split; [exact Hsc|]. split; [exact S1|].
unfold get_stride. destruct (m_last_idx (R m) =? 0) eqn:E0; destruct (m_maplen (R m) =? 0) eqn:EM; cbn [andb negb];
first [left; reflexivity | right; split; [apply Z.eqb_eq; exact E0| apply Z.eqb_neq; exact EM]].
- intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r' & _ & _ & _ & Hge). auto.
- exact (g_maplen _ _ _ _ _ _ GO).
- exact (ish_blk _ _ ISH _ m i Hk Hs).
- apply (ish_hdr0 _ _ ISH _ _ _ Hm). unfold cnt_of. lia.
- intros q v Hq. eapply known_byte; [| exact Hq]. intros sh o' v' t Hsh Hc. exact (proj1 (proj1 (ish_ticks _ _ ISH _ _ Hsh) o' v' t Hc)).
Qed.
End BLOCK.
Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let e : Z := snd c + stride - IB.
Let res : Z := e - snd p - n.
Let q : Z := (snd p - snd bm - UNIT) / UNIT.
Lemma p_snd : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "D'7';&5':vQD%33241&M&>&<vQHvQ@%3221vQ=%6221&Q2&AvQC%3221%<251%C3B>1").
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma p_fst : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "9'7':&1';vQD%33421vQ8%53641%83731").
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma gbase_bm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree ":'7&C&=&<vQHvQ@%3221%511vQ8%93821").
Proof. unfold gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma c_snd : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree ">'7';&5':vQ9%33241&>&<vQHvQ@%3221vQ=%6221%=3<81").
Proof. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma q16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "J'6'7';&Q2&AvQE%3221&MvQIvQ=%7221vQC%9281%6231%=3<81&Oz%221<&Q0&Q3+2+@%3221%52B1%H271%I2;1").
Proof.
destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (_ & _ & _ & _ & Q & _). cbn [bslot boff fst snd] in Q.
rewrite gbase_bm in Q. subst q p. cbn [snd aadd] in *. rewrite c_snd in *. unfold sstart in *. rewrite gbase_bm in *.
destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. subst stride.
replace (snd bm + UNIT + get_stride (R m) * i + UNIT * off - snd bm - UNIT) with (get_stride (R m) * i + UNIT * off) in Q |- * by lia.
split; [| exact Q].
unfold UNIT in *. pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). rewrite S2 in H.
replace (get_stride (R m) * i + 16 * off) with ((get_stride (R m) / 16 * i + off) * 16) by lia.
rewrite Z.div_mul by lia. lia.
Qed.
Let SH := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.
Lemma p_mod16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree ";'7';&Q1&5':vQD%33251+@%6221z%:3921").
Proof.
rewrite p_snd. unfold sstart. rewrite gbase_bm.
destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. destruct (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2]. unfold UNIT in *.
pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
rewrite S2 in H. rewrite B2 in H0.
replace (snd bm + 16 + get_stride (R m) * i + 16 * off) with ((snd bm / 16 + 1 + get_stride (R m) / 16 * i + off) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma res_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "4&OzvQF%3221").
Proof.
subst res e p stride. cbn [snd aadd]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. lia.
Qed.
Lemma get_meta_eq {T} (k : aptr -> Z -> Z -> M T) bail : get_meta st p k bail = k m q i.
Proof.
pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
unfold get_meta.
rewrite (guard_true 10) by (apply Z.eqb_eq; exact p_mod16).
unfold rd16.
rewrite (rd8_known st (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [exact K2| cbn; lia| reflexivity]).
rewrite (rd8_known st (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [exact K1| cbn; lia| reflexivity]).
rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| cbn; lia| reflexivity]).
rewrite (rd8_known st (aadd p (-4)) 0) by (eapply known_at; [exact K4| cbn; lia| reflexivity]).
cbn [Z.eqb negb].
rewrite (u16_bytes q Q).
assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bm).
{ pose proof q16 as [Q1 _]. pose proof p_snd as PS. pose proof p_fst as PF. unfold sstart in PS. rewrite gbase_bm in PS.
subst stride. unfold aadd. destruct bm as [br bo]. cbn [fst snd] in *. f_equal; [exact PF| lia]. }
rewrite Ebase. unfold get_group. rewrite (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). cbn [g_meta].
rewrite (land31_idx i (Z.min res 5)) by lia. fold (MR st m).
rewrite (guard_true 11) by (rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF); apply optr_eqb_refl).
rewrite (guard_true 12) by (apply Z.leb_le; lia).
rewrite (guard_true 13) by (unfold testbit; rewrite (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
rewrite (guard_true 14) by (unfold testbit; rewrite (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
rewrite (guard_true 15) by (rewrite Em, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; exact Hck).
pose proof q16 as [Q1 _]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. fold stride in FIT.
unfold UNIT, IB in Q1, FIT. fold stride in FIT.
rewrite (guard_true 16).
2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
- fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
pose proof (size_class_bound _ Hsc) as SB.
assert (A : stride = 16 * size_class (m_sizeclass (R m)) \/ m_last_idx (R m) = 0) by tauto.
assert (B : stride <= 16 * size_class (m_sizeclass (R m)) \/ 292 <= size_class (m_sizeclass (R m))).
{ destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
clearbody p stride e res q. clear SH Hle Hst.
pose proof (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B) as [G1 G2].
destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [|lia].
apply Bool.andb_true_iff. split; [apply Z.leb_le; exact G1| apply Z.ltb_lt; exact G2].
- clearbody p stride e res q. clear SH. destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [lia|]. apply Z.eqb_eq. exact E63. }
rewrite (guard_true 17).
2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
destruct (Z.eqb_spec (m_maplen (R m)) 0) as [|NM]; cbn [negb]; [reflexivity|].
destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE]. apply Z.leb_le.
unfold gend, cnt_of, sstart in GE. rewrite gbase_bm, B0 in GE. fold stride in GE. unfold UNIT in GE.
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _]. fold stride in S1. unfold UNIT in S1.
clearbody p stride e res q. clear SH.
eapply (guard17_arith stride i off n q); try eassumption; lia. }
reflexivity.
Qed.
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).
Lemma ea_fst : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "9'7':&1';vQ<%33421vQ8%53641%83731"). Proof. reflexivity. Qed.
Lemma ea_snd : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "8'7';&5':vQ<%33241vQ;%73621").
Proof. subst ea e stride. cbn [snd aadd]. rewrite c_snd. unfold sstart. rewrite gbase_bm. lia. Qed.
Lemma ea_off : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree ">';'7&5':&BvQ<r1%3221%63581&MvQ;%2215%;3<41pRF=1").
Proof. intros d. pose proof ea_snd as EA. unfold aadd at 1. cbn [snd]. rewrite <- EA. reflexivity. Qed.
Lemma get_nominal_size_eq {T} (k : Z -> M T) bail : get_nominal_size st p ea k bail = k n.
Proof.
pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
pose proof ea_snd as EA. pose proof p_fst as PF. pose proof c_snd as CS.
assert (CF : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
assert (Hres : res = e - snd p - n) by reflexivity.
assert (He : e = snd c + stride - IB) by reflexivity.
assert (Hst : stride = get_stride (R m)) by reflexivity.
assert (Hp2 : snd p = snd c + UNIT * off) by reflexivity.
pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ, <- CS, <- Hst in H0.
assert (OFF : forall d, snd (aadd ea d) = snd c + get_stride (R m) - IB + d) by (intros d; rewrite ea_off, He, Hst; reflexivity).
clearbody q. clear SH.
unfold get_nominal_size.
rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
cbv beta. rewrite (shiftr5_res i (Z.min res 5)) by lia. cbv zeta.
destruct (Z.leb_spec 5 (Z.min res 5)) as [R5|R5].
-
destruct (K5 ltac:(lia)) as (B0 & B1 & B2 & B3 & B5 & R32).
rewrite (guard_true 20) by (apply Z.eqb_eq; lia).
unfold rd32.
rewrite (rd8_known st (aadd ea (-4)) (byte_of res 0)) by (eapply known_at; [exact B0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (rd8_known st (aadd (aadd ea (-4)) 1) (byte_of res 1)) by (eapply known_at; [exact B1| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (rd8_known st (aadd (aadd ea (-4)) 2) (byte_of res 2)) by (eapply known_at; [exact B2| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (rd8_known st (aadd (aadd ea (-4)) 3) (byte_of res 3)) by (eapply known_at; [exact B3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (u32_bytes res) by lia.
rewrite (guard_true 21) by (apply Z.leb_le; lia).
rewrite (rd8_known st (aadd ea (-5)) 0) by (eapply known_at; [exact B5| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (guard_true 25) by reflexivity.
rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [apply Kr; lia| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (guard_true 23) by reflexivity.
rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (guard_true 24) by reflexivity.
f_equal. rewrite EA. lia.
-
replace (Z.min res 5) with res by lia.
rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
assert (Kr0 : known st (fst c, snd c + get_stride (R m) - IB - res) 0).
{ destruct (Z.eq_dec res 0) as [E0|NE]; [| apply Kr; lia]. rewrite E0, Z.sub_0_r, CF, <- Hst. exact H0. }
rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [exact Kr0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (guard_true 23) by reflexivity.
rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
rewrite (guard_true 24) by reflexivity.
f_equal. rewrite EA. lia.
Qed.
Lemma free_hdr_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree "Q5'7&@'2'4'G&C%3221';%5221%711%911&FvQHvQD%3221(K'E(0(3&I&B-2%2291z&J-3%62=1+WO%4321@%:3761vQ@%=4KJ21vQ=%?4KJ21%A2J1%D4CLJ1%Q43JF1").
Proof.
unfold free_hdr. rewrite get_meta_eq. cbv beta zeta.
unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
match goal with |- get_nominal_size st p ?e ?k ?b = _ => change (get_nominal_size st p e k b) with (get_nominal_size st p ea k b) end.
rewrite get_nominal_size_eq. reflexivity.
Qed.
End HDR.
End CEIL_WRAP_1.
