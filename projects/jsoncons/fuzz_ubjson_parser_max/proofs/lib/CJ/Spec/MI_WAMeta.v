(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
MI_WFree2 MI_Ledger.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WAMeta () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WAMeta.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WAMeta.CEIL_WRAP_1.CARVE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3N"; "3Z"; "0F"; "0L"; "0L'"; "0LS"; "0RUNp"; "4alloc_ceiling"; "5BPDead"; "5BPLive"; "5LEN_MAX"; "5MAPF"; "5brk_phase"; "5event_pre"; "5ld_brk"]; ["5ld_brkreg"; "5ld_groups"; "5ld_metas"; "5ld_resv"; "5mled"; "6INVL"; "6blk"; "6extras"; "6frontier"; "6inv_R"; "6inv_SH"; "6mslot"; "7AM_frame"; "8cr_areas"; "8cr_head"; "7L_frame"]; ["9AREA_HDR"; "9BrkDead"; "9EBrk"; "9EMmap"; "9EMprotect"; "9META_SIZE"; "9NSLOTS"; "9PGSZ"; "9PROT_NONE"; "9PROT_RW"; "9RKBrk"; "9RKGroup"; "9RKMeta"; "9aadd"; "9aptr"; "9area"]; ["9brk_pages_ok"; "9brkstate"; "9c_active"; "9c_avail_meta"; "9c_avail_meta_area_count"; "9c_avail_meta_areas"; "9c_avail_meta_count"; "9c_bounces"; "9c_brk"; "9c_free_meta_head"; "9c_init_done"; "9c_meta_alloc_shift"; "9c_meta_area_head"; "9c_meta_area_tail"; "9c_mmap_counter"; "9c_secret"]; ["9c_seq"; "9c_unmap_seq"; "9c_usage"; "9ctx"; "9ghdr"; "9lhead"; "9live_ranges"; "9meta"; "9mkRegion"; "9mstate"; "9optr"; "9r_base"; "9r_kind"; "9r_len"; "9ranges_free"; "9region"]; ["9rkind"; "9round_up_pg"; "9s_areas"; "9s_ctx"; "9s_groups"; "9s_metas"; "9s_next_rid"; "9s_regions"; "9s_reserved"; "9s_secret"; "9s_shadow"; "9s_slots"; "9s_tick"; "9set_brk"; "9shadow"; "9upd_ctx"]; [":filter"; ";Permutation"; "<add"; "<le"; "<lt"; "<modulo"; "<mul"; "<pow"; "<sub"; "0X"; "0a"; "0b"; "0base"; "0c"; "0k"; "0len"]; ["0lo"; "0n"; "0off"; "0old"; "0p"; "0q"; "0r"; "0r'"; "0rid"; "0rq"; "0s"; "0s'"; "0st"; "0st'"; "0st2"; "0st3"]; ["=insert"; "=lookup"; ">N_countable"; ">Z_countable"; ">prod_countable"; "?prod_eq_dec"; "@map_insert"; "@map_to_list"; "Agmap"; "Agmap_fold"; "Agmap_lookup"; "Agmap_partial_alter"; "Beq_dec"; "Ceq_dec"; "0tl"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Record AM_frame (st st1 : mstate) : Prop := mkAMF {
amf_groups : s_groups st1 = s_groups st;
amf_slots : s_slots st1 = s_slots st;
amf_shadow : s_shadow st1 = s_shadow st;
amf_tick : s_tick st1 = s_tick st;
amf_active : forall sc, active st1 sc = active st sc;
amf_usage : forall sc, usage st1 sc = usage st sc;
amf_bounces : c_bounces (s_ctx st1) = c_bounces (s_ctx st);
amf_seq : c_seq (s_ctx st1) = c_seq (s_ctx st);
amf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
amf_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st1 !! rid = Some r;
amf_next_rid : (s_next_rid st <= s_next_rid st1)%N;
amf_ssec : s_secret st1 = s_secret st
}.
Lemma amf_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "5'RI'Q<r1%2211pXJ41").
Proof. intros st. constructor; auto; first [reflexivity| lia]. Qed.
Lemma amf_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "<'RI'Q<r3r2%3221r5%5214p031p041pWL91pWH:1pWF;1").
Proof. intros a b c.
intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11]; constructor; try congruence.
- intros rid r H K. apply B10; [| exact K]. apply A10; assumption.
- clear -A11 B11. eapply N.le_trans; eassumption.
Qed.
Record L_frame (L L1 : mled) : Prop := mkLF {
lf_groups : ld_groups L1 = ld_groups L;
lf_live : ld_live L1 = ld_live L;
lf_resv : ld_resv L1 = ld_resv L
}.
Lemma lf_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "5'Q4'Q?r1%2211pQ:41"). Proof. intros L. constructor; reflexivity. Qed.
Lemma lf_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "<'Q4'Q?r3r2%3221r5%5214p031p041pWL91pWH:1pWF;1").
Proof. intros a b c. intros [] []; constructor; congruence. Qed.
Lemma inv_SH_view' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "RN'RI'6&Q6%211'='TH'A&TL&TB'S>%544321&S:r2%211r3%411%<3631&S<%114r4%311%A3?31'RO'7%112&TA%E4DCB4&TJ%14FED6&S7r7%211%76J:64D1(2r1%22=1%Q03<41'S0&RL%11K(QK%Q53421r8%>11%C6Q6FB@I1%<2GO%Q:3F21p061p0<1pX>K1pXBQ<1&QN&TE'B&TM%34QAQ@21&TD&TC%26QDQCQB541'RD%QG49521&S4r5%211r6%411%QN3631'9%12A?%R04B>;1&S;%117%21Q:%R53421'RG%R64HDA1&S5%11Q?%21Q4%R;3421'Q:r9%221QD%322Q9p021p061p0=1p0E1p0Q61p0R41p0R:1p2RH1pXLRL1pXJRM1").
Proof. intros st st' BL.
intros SH TK HR HG HS HM I.
pose proof (inv_SH_view st (set_regions (s_regions st) st') BL SH TK eq_refl HG HS) as V.
assert (ME : forall x, MR (set_regions (s_regions st) st') x = MR st x) by (intros; apply MR_ext; exact HM).
specialize (V ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) I).
destruct V as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros rid sh H. destruct (D1 rid sh H) as (r & Hr & K). exists r. split; [apply HR; assumption| exact K].
Qed.
Lemma mslot_succ : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "A&QN'B'=&QM&Q;r2r1%3221&QE%6221&SB+1%2261%9281%<3>51pWN>1pWF@1").
Proof. intros a k. unfold mslot, aadd, META_SIZE. cbn. f_equal. lia. Qed.
Section TAKE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HC : 0 < c_avail_meta_count (s_ctx st).
Lemma am_take_ok {T} (k : mstate -> optr -> M T) bail :
exists m st2, am_take st k bail = k st2 (Some m) /\ INVL (xidle X (m :: x_idle X)) st2 L BL LS /\ AM_frame st st2 /\ ~ In m (x_idle X).
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (ia_avail _ IA) as [A1 A2]. destruct (A2 HC) as (a & Ht & Eam & FREE).
set (k0 := NSLOTS - c_avail_meta_count (s_ctx st)) in *.
exists (mslot a k0).
unfold am_take, ctx. rewrite Eam.
set (st1 := upd_ctx _ st). set (st2 := upd_meta (mslot a k0) _ st1).
exists st2. split; [reflexivity|].
assert (ABS : s_metas st !! mslot a k0 = None) by (apply FREE; lia).
assert (MRm : MR st (mslot a k0) = meta0) by (unfold MR, get_meta_rec; rewrite ABS; reflexivity).
assert (M2 : s_metas st2 = <[mslot a k0 := meta0]> (s_metas st)).
{ unfold st2, st1. rewrite s_metas_upd_meta. cbn. f_equal. rewrite get_meta_rec_upd_ctx. fold (MR st (mslot a k0)). rewrite MRm. reflexivity. }
assert (MR2 : forall x, MR st2 x = MR st x).
{ intros x. unfold MR, get_meta_rec. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
- rewrite lookup_insert_eq, ABS. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity. }
assert (DE : forall x, data_of (MR st2 x) = data_of (MR st x)) by (intros x; rewrite MR2; reflexivity).
assert (KEYS : forall x, s_metas st2 !! x <> None <-> s_metas st !! x <> None \/ x = mslot a k0).
{ intros x. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
- rewrite lookup_insert_eq. split; [auto| discriminate].
- rewrite lookup_insert_ne by congruence. tauto. }
assert (Ha : s_areas st !! a <> None) by (apply (ia_tail _ IA); exact Ht).
assert (NLm : forall h, ~ In (mslot a k0) (LS h)).
{ intros h Hin. apply (listed_present _ _ _ _ _ (conj IR (conj IA (conj IM (conj IL (conj IG (conj IS ISH)))))) _ _ Hin). exact ABS. }
split.
-
split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct IR; constructor; try assumption.
+ destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
assert (CT2 : c_meta_area_tail (s_ctx st2) = c_meta_area_tail (ctx st)) by reflexivity.
assert (CC2 : c_avail_meta_count (s_ctx st2) = c_avail_meta_count (s_ctx st) - 1) by reflexivity.
assert (CA2 : c_avail_meta (s_ctx st2) = Some (mslot a (k0 + 1))) by (rewrite <- mslot_succ; reflexivity).
destruct IA; constructor.
* exact ia_ctx.
* exact ia_secret.
* exact ia_areas.
* exact ia_head.
* exact ia_tail.
* cbn. intros Hn. exfalso. unfold ctx in Ht. rewrite Ht in Hn. discriminate.
* intros m mr Hm. rewrite M2 in Hm. destruct (aptr_eq_dec m (mslot a k0)) as [->|NE].
-- exists a, ar, k0. split; [exact Ea|]. split; [unfold k0; lia| reflexivity].
-- rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
* rewrite CT2, CA2, CC2. split; [lia|]. intros Hc. exists a. split; [exact Ht|]. split; [unfold k0; f_equal; f_equal; lia|].
intros k1 Hk1. rewrite M2, lookup_insert_ne; [apply FREE; lia|]. unfold mslot, aadd. intros E. inversion E. unfold META_SIZE in *. lia.
* rewrite CA2. intros q Hq. inversion Hq. subst q. unfold mslot, aadd. cbn [fst].
destruct (ia_areas _ _ Ea) as ((r & Hr & K & _) & _). exists r. auto.
* intros sc Hsc. unfold usage, ctx. cbn. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry.
apply (gcnt_ext_groups st st2 eq_refl). intros b h m _ _. rewrite MR2. auto.
* exact ia_usage_keys.
* exact ia_active_keys.
+ destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn [x_idle x_zomb x_pend x_orph x_fresh xidle].
* intros m Hm. rewrite !MR2 in *. exact (Q1 m Hm).
* intros m b Hm. rewrite MR2 in Hm. exact (Q2 m b Hm).
* intros b h Hb. destruct (Q3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !MR2. auto.
* intros m [<-|Hm].
-- split; [rewrite M2, lookup_insert_eq; reflexivity|]. intros [h Hin]. exact (NLm h Hin).
-- destruct (Q4 m Hm) as [E NI]. split; [| exact NI]. rewrite M2, lookup_insert_ne; [exact E|]. intros Emm. congruence.
* intros z Hz. rewrite !MR2. exact (Q5 z Hz).
+ destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
all: try (intros h; destruct h; cbn; apply L1).
* intros h. pose proof (L2 h) as D. destruct (LS h) as [|x l]; [exact I|]. cbn [dll] in D |- *. eapply linked_ext; [| | exact D]; intros; rewrite MR2; reflexivity.
* intros m. rewrite !MR2. apply L5.
* intros m Hm. rewrite !MR2. apply L6. exact Hm.
* intros sc m Hm. rewrite MR2. exact (L7 sc m Hm).
+ destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
* intros m b ai Hb. pose proof (G1 m b ai Hb) as GO. destruct GO; constructor; rewrite ?MR2; try assumption.
-- apply KEYS. left. exact g_present.
-- intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !MR2. auto 10.
* intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MR2. eapply G3; eassumption.
* intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite MR2. auto.
+ destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
* intros s m i Hs. rewrite !MR2. exact (S1 s m i Hs).
* intros b m i Hb Hi. rewrite MR2 in Hi |- *. exact (S2 b m i Hb Hi).
* intros b m ai i Hb Hi. rewrite MR2 in Hi. rewrite !MR2. exact (S3 b m ai i Hb Hi).
* intros kk Hk. destruct (S6 kk Hk) as (m & i & ? & ?). exists m, i. rewrite MR2. auto.
+ apply (inv_SH_view st st2); try reflexivity; try (intros; rewrite MR2; reflexivity). exact ISH.
- split; [constructor; cbn; auto; first [reflexivity| lia]|].
intros Hin. pose proof (proj1 (im_idle _ _ _ IM _ Hin)) as E. rewrite ABS in E. discriminate.
Qed.
End TAKE.
Definition adv (st : mstate) (p : aptr) : mstate :=
upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st.
Definition carve_rest (s : mstate) (p : aptr) : mstate :=
let st2 := match c_meta_area_tail (ctx s) with
| Some tl => set_areas (<[tl := match (s_areas s) !! tl with
| Some a => mkArea (a_check a) (Some p) (a_nslots a)
| None => mkArea 0 (Some p) 0 end]> (s_areas s)) s
| None => upd_ctx (set_meta_area_head (Some p)) s
end in
let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4.
Lemma am_carve_eq {T} st p (k : mstate -> optr -> M T) bail : am_carve st p k bail = am_take (carve_rest (adv st p) p) k bail.
Proof. reflexivity. Qed.
Section CARVE.
Variables (X : extras) (s : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (p : aptr).
Hypothesis INV : INVL X s L BL LS.
Hypothesis HP : c_avail_meta_areas (s_ctx s) = Some (aadd p 4096).
Hypothesis NA : s_areas s !! p = None.
Hypothesis NM : forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None.
Hypothesis PG : PGSZ <= snd p.
Hypothesis PM : snd p mod PGSZ = 0.
Hypothesis INIT : c_init_done (s_ctx s) = 1.
Let s' := carve_rest s p.
Definition cr_areas : gmap aptr area :=
match c_meta_area_tail (ctx s) with
| Some tl => <[p := mkArea (c_secret (ctx s)) None NSLOTS]>
(<[tl := match (s_areas s) !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
| None => <[p := mkArea (c_secret (ctx s)) None NSLOTS]> (s_areas s)
end.
Definition cr_head : optr := match c_meta_area_tail (ctx s) with Some _ => c_meta_area_head (ctx s) | None => Some p end.
Lemma tail_not_p : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "C&QN'=&RJ&R=&RCvT:%211%411(2r1%22:1%:3941&?r2vT4%>3?21%411p061pYNB1").
Proof. intros tl. intros Ht ->. apply (ia_tail _ (proj1 (proj2 INV)) p Ht). exact NA. Qed.
Lemma cr_shape : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "UB'<'='TH&QN&TE'A&TL'B&TM%544321&TD&TB&TC%36872651'QO%=4<621&S2vT;%211&Q=%C3521&RJ&R<&S3%117%311&Q>%J3621&R=%115(2vT4%22M1%Q03<41&R3%11;&QM&Q@%2271%92Q41%Q73C51&R6%11B&QF%Q;3Q521'RO%Q<4Q9Q8Q31&S7%11OvT:%311%QB3531'RG%QC4QBQ<Q81&S5%11Q6%217%QH3421'RD%QI4QHQBQ>1&S4%11Q<%21=%QN3421'9%12QNQJ%R04QOQIQE1&S;%11QC%21D%R53421'S>%R64R3R2QM1&S:%11QI%21J%R;3421&S<%11QM%21N%R?3R;21&S6%11R1%21Q2%RC3R?21&S9%11R5%21Q6%RG3RA21'6%J2RCRC%211&S8%11R<%21Q=%RN3421&R5%11R9%R;1QA%311%S33R?31&R4%11R>%215%S73S121&R?%11RB%219%S;3S521&R:%11RF%21=%S?3S921%S?4S:S9S5S>&R2%11RK%21B%SD3421%SD4S?S>S:S?&RB%11S0%21G%SI3421&R9%11S4%21K%SM3S921&R;%11S8%21O%T13SK21'R1&R8%11S=%21Q4%T63421&R>%11SA%21Q8%T:3T421&R@%11SE%21Q<%T>3T821&R7%11SI%21Q@%TB3M21&RA%11SM%21QD%TF3Q121%TH251%TI2:1%TJ2?1%TK2D1%TL2J1%TM2O1%TN2Q41%TO2Q:1%U02Q@1%U12QE1%U22QJ1%U32QO1%U42R51%U52R=1%U62RB1%U72RG1%U82RL1%U92S31%U:2S;1%U;2SB1%U<2SI1%U=2T11%U>2T61%U?2T>1%U@2TE1%UA2TM1").
Proof.
unfold s', carve_rest, cr_areas, cr_head, ctx. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET; cbn -[lookup insert NSLOTS AREA_HDR].
- rewrite lookup_insert_ne by (intros E; exact (tail_not_p tl ET (eq_sym E)) || exact (tail_not_p tl ET E)). rewrite NA. cbn. repeat split; reflexivity.
- rewrite NA. cbn. repeat split; reflexivity.
Qed.
Lemma cr_areas_lookup a : cr_areas !! a =
if aptr_eqb a p then Some (mkArea (c_secret (ctx s)) None NSLOTS)
else match c_meta_area_tail (ctx s) with
| Some tl => if aptr_eqb a tl then Some (match (s_areas s) !! tl with Some ar => mkArea (a_check ar) (Some p) (a_nslots ar) | None => mkArea 0 (Some p) 0 end)
else s_areas s !! a
| None => s_areas s !! a
end.
Proof.
unfold cr_areas. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ET.
- destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence.
destruct (aptr_eqb_spec a tl) as [->|NE2]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
- destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma mslot0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "<'=&QN&QMvT4&Q@%3221&Q;&SH&QF%2211%4271%;3:61").
Proof. unfold mslot, aadd. f_equal. Qed.
Theorem INVL_carve : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "E'<&Q5vGvSIvT;vDv0vF%76654321'Q<vT:%2217&SDz&R6&S3%11<%311%6251%C281%D2<1").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct cr_shape as (EA & EH & ET & EAM & EAC & ER & EM & EG & ESL & ESH & ETK & EN & ESE & ERS & ECA & ECC & EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7 & EC8 & EC9 & EC10 & EC11).
assert (FR : forall rid r, frontier s' rid r = frontier s rid r) by (intros; unfold frontier; rewrite ECA; reflexivity).
assert (MRE : forall x, MR s' x = MR s x) by (intros; unfold MR, get_meta_rec; rewrite EM; reflexivity).
destruct (ir_cursor _ _ _ IR) as (CU1 & CU2 & CU3). destruct (CU3 _ _ HP) as (rp & Hrp & Kp & _ & _ & Ep & _). cbn in Hrp, Ep.
assert (HE : forall h, get_head s' h = get_head s h) by (intros [sc|]; cbn [get_head]; unfold active, ctx; rewrite ?EC3, ?EC5; reflexivity).
split; [| split].
- split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct IR; constructor; rewrite ?ER, ?EN, ?ERS, ?EG, ?ECA, ?ECC, ?EC6, ?EC7; try assumption.
* eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
* intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
* intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
+ destruct IA; constructor; rewrite ?ER, ?EA, ?EH, ?ET, ?EAM, ?EAC, ?EM, ?ESE, ?EC1, ?EC2, ?EC3, ?EC4, ?EC8, ?EC9, ?EC10, ?EC11; try assumption.
* destruct ia_secret as [S0 [[I0 _]|S1]]; [exfalso; rewrite INIT in I0; discriminate|]. split; [exact S0| right; exact S1].
* intros a ar. rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp].
-- intros E. inversion E. subst ar. cbn. split; [| split; [reflexivity| split; [reflexivity| intros a' H; discriminate]]].
exists rp. rewrite FR. unfold frontier. rewrite HP. cbn. rewrite N.eqb_refl. split; [exact Hrp|]. split; [exact Kp|]. split; [exact PM|]. split; [exact PG|]. unfold PGSZ. lia.
-- assert (OLD : forall ar0, s_areas s !! a = Some ar0 -> (exists r, s_regions s !! fst a = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a /\ snd a + PGSZ <= frontier s' (fst a) r)
/\ a_check ar0 = c_secret (s_ctx s) /\ a_nslots ar0 = NSLOTS /\ (forall a', a_next ar0 = Some a' -> cr_areas !! a' <> None)).
{ intros ar0 H0. destruct (ia_areas a ar0 H0) as ((r & Hr & K & M & P & F) & C & NS & NX). split; [exists r; rewrite FR; auto 10|]. split; [exact C|]. split; [exact NS|].
intros a' Ha'. rewrite cr_areas_lookup. destruct (aptr_eqb a' p); [discriminate|].
destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a' tl); [discriminate|]|]; exact (NX a' Ha'). }
destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
++ destruct (aptr_eqb_spec a tl) as [->|NEt].
** destruct (s_areas s !! tl) as [ar0|] eqn:E0; [| exfalso; exact (ia_tail tl ETL E0)].
intros E. inversion E. subst ar. cbn. destruct (OLD ar0 E0) as (R1 & C & NS & _). split; [exact R1|]. split; [exact C|]. split; [exact NS|].
intros a' Ha'. inversion Ha'. subst a'. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
** intros H0. exact (OLD ar H0).
++ intros H0. exact (OLD ar H0).
* intros h Hh. rewrite cr_areas_lookup. destruct (aptr_eqb_spec h p) as [->|NEhp]; [discriminate|].
unfold cr_head in Hh. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
-- destruct (aptr_eqb h tl); [discriminate|]. exact (ia_head h Hh).
-- inversion Hh. congruence.
* intros t Ht. inversion Ht. subst t. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
* intros H. discriminate.
* intros m mr Hm. destruct (ia_metas m mr Hm) as (a & ar & k & Ha & Hk & Em). exists a.
rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp]; [rewrite NA in Ha; discriminate|].
destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a tl); [eexists _, k; eauto| exists ar, k; auto]| exists ar, k; auto].
* split; [unfold NSLOTS; lia|]. intros _. exists p. split; [reflexivity|]. split; [rewrite mslot0; reflexivity|].
intros k Hk. apply NM. unfold NSLOTS in *. lia.
* intros q Hq. inversion Hq. subst q. cbn. exists rp. auto.
* intros sc Hsc. unfold usage, ctx. rewrite EC4. fold (ctx s). fold (usage s sc). rewrite (ia_usage sc Hsc). symmetry.
apply (gcnt_ext s s'); [exact EG| exact EM].
+ apply (inv_M_ext X s s'); [exact EM| exact EG| exact IM].
+ apply (inv_L_ext s s'); [exact EM| exact EG| exact HE| exact IL].
+ destruct IG as [G1 G2 G3 G4 G5]; constructor; rewrite ?EG, ?ER.
* intros m b ai Hb. apply (group_ok_ext X s s'); [exact EM| exact ESL| intros; rewrite ER; assumption| exact (G1 m b ai Hb)].
* exact G2.
* intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MRE. eapply G3; eassumption.
* intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (hosts_ext s s' EG), MRE. auto.
* exact G5.
+ apply (inv_S_ext X s s' BL); [exact EM| exact EG| exact ESL| exact IS].
+ apply (inv_SH_view s s'); auto; intros; rewrite MRE; reflexivity.
- constructor; rewrite ?EG, ?ESL, ?ESH, ?ETK, ?EC8, ?EC9, ?EC10, ?EN; auto; try reflexivity.
+ intros sc. unfold active, ctx. rewrite EC3. reflexivity.
+ intros sc. unfold usage, ctx. rewrite EC4. reflexivity.
+ intros rid r H _. rewrite ER. exact H.
- rewrite EAC. unfold NSLOTS. lia.
Qed.
End CARVE.
Lemma above_frontier : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "S5'Q7'RI'Q4'6&Q6%211'RE&QN%511p031'A'RO&Q5vGr8r7r6r5r4%76654321'='7%11;&TA'TH&TL&TB%34A21@&TJ%14C43B&S7%11A%96FE53>1(2r3%22H1%@3>41&5'B%23M15%D3N1G&SC&Q8r:%231LK&:%13Q48L%6231'<'QO%M11&TE&TM%24Q;L?1&TD&TC%26Q>ONB41%Q14QB418%N4QC529&S2r;%211%Q76QG=54Q=1(1%11?%Q=3?31zr1%K221&SD&QF%2241%H241'RG%QE11%QC4R4FC2%Q@4R5GD3&Q;r2%22R01&S5r=%211%QL6R<:8741%E1;%R13;21p0>1pWNQA1%Q82G1p0Q:1p0QB1p0QG1p0R91pX:RF1pX>RC1pXBRE1pQ>RG1p2RL1pQ:S01pXJS21pWDS41").
Proof. intros X st L BL LS rid r p.
intros INV Hr Hf Hfr. pose proof (proj1 (proj2 INV)) as IA. split.
- destruct (s_areas st !! p) as [ar|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _ & _ & _ & F) & _). rewrite Hf, Hr in Hr'. inversion Hr'. subst r'. rewrite Hf in F. unfold PGSZ in F. lia.
- intros k Hk. destruct (s_metas st !! mslot p k) as [mr|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em).
destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _).
unfold mslot, aadd in Em. inversion Em. rewrite Hf in H0. rewrite <- H0, Hr in Hr'. inversion Hr'. subst r'. rewrite <- H0 in F.
unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. lia.
Qed.
Section META_ADV.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcur : c_avail_meta_areas (s_ctx st) = Some (rid, off).
Hypothesis Hcnt : 0 < c_avail_meta_area_count (s_ctx st).
Let p : aptr := (rid, off).
Let a : Z := conc st p.
Let st' := adv st p.
Let L' := KInv.set_metas (map (bump_meta a) (ld_metas L)) L.
Lemma ma_region : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "R4'>'RO'<'='7%114&TA'A'TH&TL&TB%34421:&TJ%14643<vT8&S7vT<%211%<6;A7541(2r1%22D1%C3A41'S0&RL%115(QL%H3421&SC&QGvT2%3221'B&SE%1245z%Q13421&SB&SF&R4&S3%11I%311%521>%72>1&RM%11J%Q<3?31%?22C%Q>3A1>&SD&RK%11Q0%32B1%A228&HvG%211%N241%QI261%QJ2;1%QK2>1%QL2J1%QM2Q01%QN2Q51%QO2Q;1qX>R11%R32R21").
Proof.
destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3). destruct (C3 _ _ Hcur) as (r & Hr & K & P1 & P2 & P3 & P4).
pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 K) as [S7 S8].
exists r. repeat split; auto.
pose proof (round_up_ge (r_len r)). lia.
Qed.
Lemma ma_frontier q rq : frontier st q rq = if (rid =? q)%N then off else r_len rq.
Proof. unfold frontier. rewrite Hcur. reflexivity. Qed.
Lemma ma_frontier' q rq : frontier st' q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st', adv. cbn. reflexivity. Qed.
Lemma ma_event_pre : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "8&NvD(QDvSJ&QG&QI%43321%7261").
Proof.
destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|].
exists (r_base r), (r_len r), (frontier st rid r / PGSZ - 1).
split.
- pose proof (ir_metas _ _ _ (proj1 INV)) as P. eapply Permutation_in; [apply Permutation_sym; exact P|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [apply In_map_to_list_regions; exact Hr| cbn; rewrite K; reflexivity].
- rewrite ma_frontier, N.eqb_refl. unfold a, conc, get_region, p. cbn [fst snd]. rewrite Hr.
unfold PGSZ in *. pose proof (round_up_ge (r_len r)).
pose proof (Z.div_mod off 4096 ltac:(lia)) as DM. rewrite P2 in DM. set (q := off / 4096) in *. clearbody q. nia.
Qed.
Theorem INVL_meta_adv : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "RK'<&Q5vGvSIvT=vEv0vF%76654321'=&RJ&R5&S3%119%311(2&QN&QMvT4+TP0%3221%6251%=3<81'7'QO%211&TA'TH&TE'A&TL'B&TM%544321&TD&TB&TC%36872651%;4F51>&TJ%14H73@&S2%11Q6%A6KC53I1(1%11E%Q53E31&SCzr1%3221&SD&QF%2241%QF241'RG%Q111%N4Q9HD2%C4Q:IE3&Q;r2%22Q;1&S5%11QK%Q66Q@97631%E1:%QI3:21p0=1pWNQ51&QG&:%13Q:Q8QE%I231&SE%1235%R23Q<1K&R:%11R0vT<%R311%411%R83QB41'Q<%125R?%RD231%RE2:1%RF2>1%RG2C1%RH2Q:1%RI2R31%RJ2RB1").
Proof.
destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
destruct (above_frontier X st L BL LS rid r p INV Hr eq_refl ltac:(rewrite ma_frontier, N.eqb_refl; cbn; lia)) as [NA NM].
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [cbn; lia| split; [exact P2| split; [reflexivity|]]]]]]].
2:{ constructor; cbn; auto; first [reflexivity| lia]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- assert (Rg : s_regions st' = s_regions st) by reflexivity. assert (Rn : s_next_rid st' = s_next_rid st) by reflexivity.
assert (Rv : s_reserved st' = s_reserved st) by reflexivity. assert (Rgr : s_groups st' = s_groups st) by reflexivity.
assert (Csh : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) by reflexivity.
assert (Cbrk : c_brk (s_ctx st') = c_brk (s_ctx st)) by reflexivity.
assert (Cam : c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)) by reflexivity.
assert (Cac : c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) - 1) by reflexivity.
unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_metas];
rewrite ?Rg, ?Rn, ?Rv, ?Rgr, ?Csh, ?Cbrk, ?Cam, ?Cac; try assumption.
+
eapply Permutation_trans; [apply Permutation_map; exact ir_metas|]. rewrite map_map.
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. cbn in Hk |- *.
apply In_map_to_list_regions in Hin. destruct (r_kind rq) eqn:Ekq; try discriminate.
rewrite ma_frontier.
pose proof (ir_shape q rq Hin) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(right; exact Ekq)) as [S7 S8].
destruct (N.eqb_spec rid q) as [<-|NE].
* rewrite Hr in Hin. inversion Hin. subst rq.
replace (r_base r + (1 + (off / PGSZ - 1)) * PGSZ) with a.
2:{ unfold a, conc, get_region, p. cbn. rewrite Hr. unfold PGSZ in *. pose proof (Z.div_mod off 4096 ltac:(lia)). lia. }
rewrite Z.eqb_refl. f_equal. unfold PGSZ in *.
pose proof (Z.div_mod off 4096 ltac:(lia)). rewrite P2 in H.
replace (off + 4096) with ((off / 4096 + 1) * 4096) by lia. rewrite Z.div_mul by lia. lia.
* destruct (Z.eqb_spec (r_base rq + (1 + (r_len rq / PGSZ - 1)) * PGSZ) a) as [E|NE2]; [| reflexivity]. exfalso.
unfold a, conc, get_region, p in E. cbn in E. rewrite Hr in E.
pose proof (Z.div_mod (r_len rq) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite S7 in DM.
pose proof (ir_disj q rid rq r Hin Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ekq, K in D.
pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). unfold PGSZ in *. nia.
+ intros q rq Hq Kq. rewrite ma_frontier'. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite ma_frontier in F1, F2.
split; [exact J|]. destruct (N.eqb_spec rid q) as [<-|NE]; [| auto].
rewrite Hr in Hq. inversion Hq. subst rq. unfold PGSZ in *. split; [lia|].
rewrite <- Zplus_mod_idemp_l, P2. reflexivity.
+ intros q rq Hq Kq. rewrite ma_frontier'. destruct (N.eqb_spec rid q) as [<-|NE]; [rewrite Hr in Hq; inversion Hq; subst rq; rewrite Kq in K; discriminate|].
pose proof (ir_brkfront q rq Hq Kq) as F. rewrite ma_frontier in F. destruct (N.eqb_spec rid q); [congruence| exact F].
+ split; [lia|]. split; [intros _; discriminate|]. intros q o E. inversion E. subst q o. exists r.
split; [exact Hr|]. split; [right; exact K|]. split; [lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, P2; reflexivity|].
split; [unfold PGSZ in *; lia| intros _; exact K].
- destruct IA; constructor; cbn -[frontier PGSZ]; try assumption.
intros a0 ar Ha. destruct (ia_areas a0 ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
exists rq. split; [exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
rewrite ma_frontier'. rewrite ma_frontier in F. destruct (N.eqb_spec rid (fst a0)); lia.
- apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
- apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
- apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End META_ADV.
Lemma frontier_full : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "QA'Q7'RI'Q4'A'RO'Q9vGr5r4r3%544321'='B&R4&S3%118%311z%73621'7%11@&TA'TH&TL&TB%34F21E&TJ%14H43G&S7r6%211%:6LK64G1(2%12MH%G3>31&Q8r7%231NM&RM%11O%M3L31p071p0H1p0Q11pX>Q81pXBQ:1pQ:Q<1pXJQ>1pWDQ@1").
Proof. intros X st L rid r.
intros IR Hc Hr. unfold frontier. destruct (c_avail_meta_areas (s_ctx st)) as [[q off]|] eqn:E; [| reflexivity].
destruct (N.eqb_spec q rid) as [->|NE]; [| reflexivity].
destruct (ir_cursor _ _ _ IR) as (_ & _ & C3). destruct (C3 _ _ E) as (r' & Hr' & _ & _ & _ & Eq & _).
rewrite Hr in Hr'. inversion Hr'. subst r'. rewrite Hc in Eq. lia.
Qed.
Section NEW_META.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKMeta r len st).
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
(set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Let L' := KInv.set_metas ((r, len, 0) :: ld_metas L) L.
Lemma nm_n : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "C'<'='BvT1&SG+2&SB&R;&S3vT<%211%411+1%7221%:291%>3=<1&SC%12<>%B231").
Proof.
pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0. unfold n. rewrite Z.shiftl_mul_pow2 by exact S0.
rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. split; [lia|].
pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (s_ctx st))). lia.
Qed.
Lemma nm_len : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "8'<&SDzvSO%3221&K%5231%7231").
Proof.
destruct nm_n as [En N2]. unfold len. split; [unfold PGSZ; lia|].
destruct (ir_shift _ _ _ (proj1 INV)) as [S0 [S1|(q & rq & Hq & K & E)]].
- unfold n. rewrite S1. change (Z.shiftl 2 0 * PGSZ) with 8192. unfold LEN_MAX. lia.
- pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hq) as (A1 & _ & _ & _ & A5 & _). pose proof (round_up_ge (r_len rq)).
rewrite En. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite E in *. (pose_ceil; unfold LEN_MAX, PGSZ in *). nia.
Qed.
Lemma nm_fresh : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "D'='7'RO%211&TA'A'TH&TL&TB%344217&TJ%146439vT8&S7vT<%211%<6;>7541(1%11@%C3@31").
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma nm_lookup q : s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKMeta r len) else s_regions st !! q.
Proof. unfold st2, st1. cbn -[new_region]. apply lookup_new_region. Qed.
Lemma nm_keep : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "N'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41r3vT>%:11%C6HG?=31%82H=%H3F21p071pXDK1pX<M1").
Proof. intros q rq. intros H. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite nm_fresh in H; discriminate| exact H]. Qed.
Lemma nm_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "Q='A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT>%211%;6@?7541(2r1%22B1%B3@41'@'<r3vT8%G3I21(RH(QLvT6vSO%43321%M3NC1%:271&?%119vT<%G11%Q06Q5Q4LJ>1%E2Q5J%Q53Q321%B261%D291p0F1pXDQ:1pX<Q<1").
Proof. intros q rq. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma nm_frontier q rq : frontier st2 q rq = if (rid =? q)%N then PGSZ else r_len rq.
Proof. reflexivity. Qed.
Lemma nm_frontier_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "O'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41'B&Q8r3%23:1<&RM%11>%I3631p081pXDL1pX<N1").
Proof. intros q rq. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.
Lemma nm_event_pre : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "9&NvD(QCzvSO&QH&L%544321%8271").
Proof. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| exact nm_len]. Qed.
Theorem INVL_new_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "M'<&Q5vGvSIvT>vEv0vF%76654321&SDz&R4&S3%119%311%6251'='B&R:%116vT<%911%411%73641'Q<%125E%J231%K2<1%L2D1").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
destruct nm_n as [En N2]. pose proof nm_len as [L0 L1].
assert (LPG : len mod PGSZ = 0) by (unfold len; apply Z_mod_mult).
assert (RU : round_up_pg len = len).
{ unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
rewrite Z.mod_opp_l_z; [lia| lia| ]. change (2 ^ 12) with 4096. exact LPG. }
split; [| split; [cbn; lia| split; [reflexivity| constructor; cbn; auto; try reflexivity; [intros q rq H _; apply nm_keep; exact H| unfold rid; lia]]]].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_metas].
+ intros q rq Hq. unfold st2, st1. cbn -[new_region]. rewrite s_next_rid_new_region. apply nm_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
+ intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
rewrite RU. rewrite RU in RCEIL. split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros _. split; [exact LPG|]. unfold len, PGSZ in *. nia.
+ intros q1 q2 r1 r2 H1 H2 NE.
apply nm_some in H1 as [[-> ->]|[N1 H1]]; apply nm_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn. rewrite RU in RFREE |- *. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
* pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D. rewrite RU in D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
+ exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|].
change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
cbn. apply Permutation_refl.
+ eapply Permutation_trans; [apply perm_skip; exact ir_metas|].
change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
cbn -[frontier PGSZ Z.div Z.sub]. rewrite nm_frontier, N.eqb_refl. replace (PGSZ / PGSZ - 1) with 0 by reflexivity. apply perm_skip.
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn.
rewrite (nm_frontier_old q rq Hin). destruct (N.eqb_spec rid q) as [<-|]; [rewrite nm_fresh in Hin; discriminate| reflexivity].
+ intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]].
* rewrite N.eqb_refl. cbn. split; [exists (c_meta_alloc_shift (s_ctx st) + 1); split; [pose proof (proj1 ir_shift); lia| unfold len; rewrite En; reflexivity]|].
unfold len, PGSZ in *. split; [nia| reflexivity].
* destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (nm_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence| reflexivity].
+ cbn. split; [pose proof (proj1 ir_shift); lia|]. right. exists rid, (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|].
split; [reflexivity|]. cbn. unfold len. rewrite En. reflexivity.
+ intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
* split; [apply nm_keep; exact Hq| auto].
* apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
+ intros q1 q2 r1 r2 H1 H2 K1 K2. apply nm_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply nm_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
+ revert ir_brk. change (c_brk (s_ctx st2)) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
* destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
* exact IBK.
* destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply nm_keep; exact Hq| auto].
+ cbn. split; [lia|]. split; [intros _; discriminate|]. intros q off E. inversion E. subst q off.
exists (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|]. cbn. split; [right; reflexivity|].
split; [lia|]. split; [reflexivity|]. split; [unfold len; lia| reflexivity].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & K & NG). exists rq. split; [apply nm_keep; exact Hrq| auto].
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite nm_frontier. split; [apply nm_keep; exact Hq|]. split; [exact K|]. split; [exact M|]. split; [exact P|].
rewrite (nm_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E|]; [| exact F]. exfalso. rewrite <- E, nm_fresh in Hq. discriminate.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
- apply (inv_M_ext X st st2); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st2); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X st st2); [reflexivity| reflexivity| intros q rq Hq K E; apply nm_keep; exact Hq| exact (G1 m b ai Hb)].
+ exact G2.
+ exact G3.
+ intros q rq Hq K Ho. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq K Ho).
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply nm_keep; exact Hq| exact K].
- apply (inv_S_ext X st st2 BL); [reflexivity| reflexivity| reflexivity| exact IS].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
Qed.
End NEW_META.
Lemma INVL_brk_dead : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "R;'Q7'RI'Q4'6&Q6%211'RE&QN%511p031&Q5vGr6r5r4r2r1%76654321'='9'B%2211%C11&Q3%11:%21<%83421&Q1%11?%21A%<3821%<2:;%M11&Q2%11Fr7%311%C3531'7%11B&Q0%116r8%311%J3531'M&O%115(I%O3421'<r<&S?&S=(QA%211r;%5221r9%QA6Q@821AH'Q<%1254%<231p0>1p0D1p0L1p0Q41p0Q91p0QC1pQ>QL1p2R11pQ<R51pQ:R61pXJR81pWDR:1").
Proof. intros X st L L' BL LS.
intros INV E1 E2 E3 E4 E5. destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
set (st' := upd_ctx (set_brk BrkDead) st).
assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by reflexivity.
split; [| constructor; cbn; auto; first [reflexivity| lia]].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; cbn -[frontier]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
all: try reflexivity.
all: try (intros q rq H1 H2; rewrite FR; first [exact (ir_metalen q rq H1 H2)| exact (ir_brkfront q rq H1 H2)]).
all: try (eapply Permutation_trans; [exact ir_metas|]; erewrite map_ext; [apply Permutation_refl|]; intros [q rq]; cbn -[frontier]; rewrite FR; reflexivity).
- destruct IA; constructor; cbn -[frontier]; try assumption.
- apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
- apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
- apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
Lemma round_up_pg_mod : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta ";'B'=&SE&S1r1%211&QG%5221z%83921pZ0:1").
Proof. intros x.
unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod (-x) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as B.
replace (x + (- x) mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z_mod_mult.
Qed.
Lemma round_up_pg_id : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta ">'B'=&SEr1&QG%3221z%63721&S1r2%211%:3;12p051pZ0=1").
Proof. intros x.
intros H. unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H in D.
replace (- x) with ((- (x / 4096)) * 4096) by lia. rewrite Z_mod_mult. lia.
Qed.
Lemma brk_pages_ok_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "Q2'RI'B'='3&R0vGr3r2r1%544321(;%93821'<&SDz%2219&SC&SB%12<;&H%11?%5231&RN&RFr4%211%431DC%I3H1A%@271%A2>1p0C1pX0N1pX2O1pXJQ11").
Proof. intros st lo len.
unfold brk_pages_ok. intros H. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. auto.
Qed.
Lemma regions_update_perm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "QO'RI'A'RO'9%1232'3p021'='7%117&TA'TH&TL&TB%34=21<&TJ%14?43>r4&S7r5%211%;6DC7541(2r3%22F1%B3@41r2(8%14KJ9;%311(4%H3J21r6%64Q0O1@%;11%L3N15'SA&S@&TG&TI%14Q7LKQ6r8%H11%55Q:Q9M31%73Q8K1&T@&TF&TK%14Q?Q4Q3Q>%34Q@Q?Q31r7%67QBQAQ521Q09%>5QCQBQ6<1%@3QAQ41%B3QB:1p0D1p0I1p0Q01pQ8QD1pX@QI1pX>QJ1pXBQL1pXJQN1").
Proof. intros st rid r r' F.
intros H F1 F2.
eapply Permutation_trans; [apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ H)|].
eapply Permutation_trans; [| apply perm_filter; apply (map_to_list_delete _ rid r'); rewrite lookup_insert_eq; reflexivity].
cbn. rewrite F1, F2. rewrite delete_insert_eq. apply Permutation_refl.
Qed.
Section BRK_GROW.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let old : Z := conc st (rid, off).
Hypothesis HOK : brk_pages_ok st old PGSZ = true.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).
Lemma bg_region : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "R?'>'RO'<'='7%114&TA'A'TH&TL&TB%34421:&TJ%14643<vT8&S7vT<%211%<6;A7541(2r1%22D1%C3A41'S0&RL%115(QJ%H3421'B&RM%11:vT2%M3421'M&OvD%211(J%Q33521'9%12<<%Q511&Q0%118(8&RK%11J%34CC1@%M281%Q>3861&SDz%2216&SE&QG%2291%QE3L15%42J3%QG3N17&SC&SF+2%2218%421Q0vT3&SB%12DQ3%R03Q731%R2251%R32;1%R42>1%R52C1%R62G1%R72Q31%R82Q:1%R92Q@1%R:2QF1qX>R<1%R>2R=1").
Proof.
pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [BP (r & Hr & K & E)].
pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(left; exact K)) as [S7 S8].
exists r. split; [exact Hr|]. split; [exact K|]. split; [exact E|]. split; [exact BP|].
split; [rewrite <- E; apply (proj2 (ir_brkreg _ _ _ (proj1 INV) (r_base r) (r_len r))); exists rid, r; auto|].
split; [exact S1|]. split; [exact S2|]. split; [rewrite <- E; exact S7|]. split; [rewrite <- E; exact S8|].
unfold old, conc, get_region. rewrite Hr. reflexivity.
Qed.
Let L' := KInv.set_brkreg (Some (old - off, off + PGSZ)) L.
Lemma bg_lookup q : s_regions st3 !! q = if (q =? rid)%N then option_map (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) (s_regions st !! rid) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[upd_region]. apply lookup_upd_region. Qed.
Lemma bg_frontier q rq : frontier st3 q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st3, adv. cbn. reflexivity. Qed.
Lemma bg_frontier_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "O'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41'B&Q8r3%23:1<&RM%11>%I3631p081pXDL1pX<N1").
Proof. intros q rq. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.
Lemma bg_event_pre : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "9&NvD(QB&SBvT3&QG%3221%511%8271").
Proof.
destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
right. right. exists (r_base r), off. split; [exact BP|]. split; [exact BR|]. lia.
Qed.
Theorem INVL_brk_grow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "RN'<&Q5vGvSIvT?vEv0vF%76654321'=&RJ&R5&S3%119%311(2&QN&QM(8'A'BvT8vT2%544321+TP0%8221%;2:1%B3A=1'7'QO%211&TA'9%12>='TH&TE&TL&TM%34C2B1&TD&TB&TC%36G62F51%94K51>&TJ%14M73@&S2%11Q;%A6?C53I1(1%11E%Q:3E31&SCzr1%3221&SD&QF%2241%QK241'RG%Q111%L4Q>HD2%C4Q?IE3&Q;r2%22Q;1&S5%11R0%Q66QE97631%E1:%QN3:21p0=1pWNQE1&QG%G21QE&SE%12QG3%R53QJ1I&R:%11R3vT<%R611%411%R;3R041'Q<%125RB%RG231%RH2:1%RI2>1%RJ2A1%RK2Q81%RL2R11%RM2RE1").
Proof.
destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF).
destruct (above_frontier X st L BL LS rid r (rid, off) INV Hr eq_refl ltac:(rewrite (bg_frontier_old _ _ Hr); cbn; lia)) as [NA NM].
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
set (r' := mkRegion RKBrk (r_base r) (off + PGSZ)).
assert (LK : forall q, s_regions st3 !! q = if (q =? rid)%N then Some r' else s_regions st !! q).
{ intros q. rewrite bg_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite Hr; cbn; rewrite K; reflexivity| reflexivity]. }
assert (KEEP : forall q rq, s_regions st !! q = Some rq -> q <> rid -> s_regions st3 !! q = Some rq).
{ intros q rq Hq NE. rewrite LK. destruct (N.eqb_spec q rid); [congruence| exact Hq]. }
assert (SOME : forall q rq, s_regions st3 !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq)).
{ intros q rq. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. }
assert (KEEPG : forall q rq, s_regions st !! q = Some rq -> r_kind rq = RKGroup -> s_regions st3 !! q = Some rq).
{ intros q rq Hq Kq. apply KEEP; [exact Hq|]. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
assert (KEEPM : forall q rq, s_regions st !! q = Some rq -> is_metakind rq -> exists rq', s_regions st3 !! q = Some rq' /\ is_metakind rq').
{ intros q rq Hq Kq. destruct (N.eq_dec q rid) as [->|NE]; [exists r'; rewrite LK, N.eqb_refl; split; [reflexivity| left; reflexivity]|].
exists rq. split; [apply KEEP; assumption| exact Kq]. }
assert (RU : round_up_pg (off + PGSZ) = off + PGSZ) by (apply round_up_pg_id; unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity).
assert (RUo : round_up_pg off = off) by (apply round_up_pg_id; exact OM).
assert (F3 : s_metas st3 = s_metas st /\ s_areas st3 = s_areas st /\ s_groups st3 = s_groups st /\ s_slots st3 = s_slots st
/\ s_shadow st3 = s_shadow st /\ s_tick st3 = s_tick st /\ s_next_rid st3 = s_next_rid st /\ s_secret st3 = s_secret st
/\ s_reserved st3 = s_reserved st /\ (forall h, get_head st3 h = get_head st h)
/\ c_usage (s_ctx st3) = c_usage (s_ctx st) /\ c_bounces (s_ctx st3) = c_bounces (s_ctx st) /\ c_seq (s_ctx st3) = c_seq (s_ctx st)
/\ c_mmap_counter (s_ctx st3) = c_mmap_counter (s_ctx st) /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st3) = c_meta_alloc_shift (s_ctx st) /\ c_secret (s_ctx st3) = c_secret (s_ctx st)
/\ c_avail_meta (s_ctx st3) = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st)
/\ c_meta_area_head (s_ctx st3) = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st3) = c_meta_area_tail (s_ctx st)
/\ c_free_meta_head (s_ctx st3) = c_free_meta_head (s_ctx st) /\ c_unmap_seq (s_ctx st3) = c_unmap_seq (s_ctx st)).
{ unfold st3, adv, st2, st1, upd_region, get_region. rewrite Hr. repeat split; try reflexivity. all: intros h; destruct h; reflexivity. }
destruct F3 as (FM & FA & FG & FS & FSH & FT & FN & FSE & FRS & FH & FU & FB & FQ & FMC & FI & FSF & FSC & FAM & FAC & FMH & FMT & FFH & FUS).
split; [| split; [reflexivity| split; [rewrite FA; exact NA| split; [rewrite FM; exact NM| split; [clear -O2; unfold PGSZ in *; lia| split; [exact OM| split; [exact FI|]]]]]]].
2:{ constructor; rewrite ?FG, ?FS, ?FSH, ?FT, ?FB, ?FQ, ?FMC, ?FN; auto; try reflexivity; try lia.
- intros sc. exact (FH (LActive sc)).
- intros sc. unfold usage, ctx. rewrite FU. reflexivity. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_brkreg].
+ intros q rq Hq. rewrite FN.
apply SOME in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids _ _ Hq)].
+ intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
pose proof (ir_shape _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6).
split; [lia|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [(pose_ceil; unfold LEN_MAX, PGSZ in *); lia|]. split; [unfold PGSZ in *; lia|].
intros _. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity| lia].
+ intros q1 q2 r1 r2 H1 H2 NE.
assert (GROW : forall q rq, s_regions st !! q = Some rq -> q <> rid ->
let '(b2, l2) := region_live_range rq in r_base r + PGSZ + (round_up_pg (off + PGSZ) - PGSZ) <= b2 \/ b2 + l2 <= r_base r + PGSZ).
{ intros q rq Hq NEq. pose proof (ir_disj rid q r rq Hr Hq ltac:(congruence)) as D. unfold region_live_range in D at 1. rewrite K, E, RUo in D.
pose proof (ranges_free_regions st _ _ q rq PF Hq) as D2. rewrite Eold in D2.
pose proof (ir_shape q rq Hq) as (T1 & _ & T3 & _). pose proof (round_up_ge (r_len rq)) as T4.
assert (NB : r_kind rq <> RKBrk) by (intros Kq; apply NEq; exact (ir_brk1 q rid rq r Hq Hr Kq K)).
unfold region_live_range in *. destruct (r_kind rq); [congruence| |]; rewrite RU; unfold PGSZ in *; lia. }
apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn. pose proof (GROW q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
* pose proof (GROW q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn. lia.
+ rewrite FRS. exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|]. apply Permutation_map.
change (s_regions st3) with (s_regions st1). unfold st1, upd_region, get_region. rewrite Hr. cbn -[map_to_list].
apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity.
+ eapply Permutation_trans; [exact ir_metas|].
eapply Permutation_trans; [| apply Permutation_map; change (s_regions st3) with (s_regions st1); unfold st1, upd_region, get_region; rewrite Hr; cbn -[map_to_list];
apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity].
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. apply In_map_to_list_regions in Hin. cbn in Hk. cbn [fst snd].
rewrite (bg_frontier_old q rq Hin), bg_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite Hr in Hin; inversion Hin; subst rq; rewrite K in Hk; discriminate| reflexivity].
+ intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite (bg_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|].
exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
+ rewrite FSF. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
exists q, rq. split; [apply KEEP; [exact Hq| intros ->; rewrite Hr in Hq; inversion Hq; subst; congruence]| auto].
+ intros b l. split.
* intros Eb. inversion Eb. subst b l. exists rid, r'. split; [rewrite LK, N.eqb_refl; reflexivity|]. cbn. repeat split; auto. lia.
* intros (q & rq & Hq & Kq & Eb & El). apply SOME in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; f_equal; f_equal; lia|].
exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
+ intros q1 q2 r1 r2 H1 H2 K1 K2.
apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
* exfalso. apply N2. exact (ir_brk1 q2 rid r2 r H2 Hr K2 K).
* exfalso. apply N1. exact (ir_brk1 q1 rid r1 r H1 Hr K1 K).
* exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
+ change (c_brk (s_ctx st3)) with (BrkLive rid (off + PGSZ)). split; [exact BP|]. exists r'. rewrite LK, N.eqb_refl. cbn. auto.
+ change (c_avail_meta_area_count (s_ctx st3)) with (1 - 1). change (c_avail_meta_areas (s_ctx st3)) with (Some (aadd (rid, off) 4096)).
split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists r'. rewrite LK, N.eqb_refl.
split; [reflexivity|]. split; [left; reflexivity|]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity|].
cbn. split; [unfold PGSZ; lia| intros; lia].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply KEEPG; assumption|]. split; [exact Kq|]. rewrite FG. exact NG.
- destruct IA; constructor; rewrite ?FA, ?FM, ?FSE, ?FU, ?FB, ?FQ, ?FMC, ?FI, ?FSC, ?FAM, ?FAC, ?FMH, ?FMT, ?FUS; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
destruct (KEEPM _ _ Hq Kq) as (rq' & Hq' & Kq'). exists rq'. rewrite bg_frontier. split; [exact Hq'|]. split; [exact Kq'|]. split; [exact M|]. split; [exact P|].
rewrite (bg_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|NE1].
* rewrite <- E1, Hr in Hq. inversion Hq. subst rq. lia.
* rewrite LK in Hq'. destruct (N.eqb_spec (fst a) rid); [congruence|]. rewrite Hq in Hq'. inversion Hq'. subst. lia.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). destruct (KEEPM _ _ Hrq Kq) as (rq' & Hq' & Kq'). exists rq'. auto.
+ intros sc Hsc. unfold usage, ctx. rewrite FU. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply (gcnt_ext st st3 FG FM).
+ intros sc g. unfold active, ctx in FH. rewrite <- !get_head_active, (FH (LActive sc)). apply ia_active_keys.
- apply (inv_M_ext X st st3); [exact FM| exact FG| exact IM].
- apply (inv_L_ext st st3); [exact FM| exact FG| exact FH| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor; rewrite ?FG.
+ intros m b ai Hb. apply (group_ok_ext X st st3); [exact FM| exact FS| intros q rq Hq Kq _; apply KEEPG; assumption| exact (G1 m b ai Hb)].
+ exact G2.
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !(MR_ext st st3 FM). eapply G3; eassumption.
+ intros q rq Hq Kq Ho. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m.
rewrite (hosts_ext st st3 FG), (MR_ext st st3 FM). auto.
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply KEEPG; assumption| exact Kq].
- apply (inv_S_ext X st st3 BL); [exact FM| exact FG| exact FS| exact IS].
- apply (inv_SH_view' st st3 BL FSH FT KEEPG FG FS FM ISH).
Qed.
End BRK_GROW.
Section BRK_FIRST.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis Hcur : brk0_answer_ok cur = true.
Let base : Z := round_up_pg cur.
Hypothesis HOK : brk_pages_ok st base (2 * PGSZ) = true.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).
Variable L0 : mled.
Hypothesis HL0 : ld_resv L0 = ld_resv L /\ ld_groups L0 = ld_groups L /\ ld_metas L0 = ld_metas L.
Let L' := KInv.set_brkph BPLive (KInv.set_brkreg (Some (base, 2 * PGSZ)) L0).
Lemma bf_base : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "Q0'<&SDzvSL%3221'='B&SE&QG%2261%53418&SC&SB&SF+2%2217%42=1&HvG%211%9241'3&RN&RFvT<%211%431G;(;%G3721%M291%N2D1%O2K1").
Proof.
destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF). split; [exact P0|]. split; [apply round_up_pg_mod|]. auto.
Qed.
Lemma bf_fresh : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "D'='7'RO%211&TA'A'TH&TL&TB%344217&TJ%146439vT8&S7vT<%211%<6;>7541(1%11@%C3@31").
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma bf_nobrk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "O'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41&?'S0&RL%11<(QJ%H3421%611p081pXDL1pX<N1").
Proof. intros q rq. pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [_ NB]. apply NB. Qed.
Lemma bf_lookup q : s_regions st3 !! q = if (q =? rid)%N then Some (mkRegion RKBrk base (2 * PGSZ)) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[new_region Z.mul]. apply lookup_new_region. Qed.
Lemma bf_keep : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "N'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41r3vT?%:11%C6HG?=31%82H=%H3F21p071pXDK1pX<M1").
Proof. intros q rq. intros H. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite bf_fresh in H; discriminate| exact H]. Qed.
Lemma bf_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "Q@'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT?%211%;6@?7541(2r1%22B1%B3@41'@'<r3vT8%G3I21(RH(QJvSL&SF+2&QG%3221%73651%Q03Q1F1%=2:1&?%11<vT<%J11%Q36Q8Q7OMA1%H2Q8M%Q83Q621%E261%G291p0I1pXDQ=1pX<Q?1").
Proof. intros q rq. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma bf_frontier q rq : frontier st3 q rq = if (rid =? q)%N then PGSZ + 4096 else r_len rq.
Proof. reflexivity. Qed.
Lemma bf_frontier_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "O'A'RO'='7%113&TA'TH&TL&TB%349218&TJ%14;43:r2&S7vT<%211%;6@?7541(2r1%22B1%B3@41'B&Q8r3%23:1<&RM%11>%I3631p081pXDL1pX<N1").
Proof. intros q rq. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.
Theorem INVL_brk_first : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WAMeta "RM'<&Q5vGvSIvT?vEv0vF%76654321'=&RJ&R5&S3%119%311(2&QN&QM(8'A'BvT8&QG%544321+TP0%8221%;2:1%B3A=1'7'QO%211&TA'9%12>='TH&TE&TL&TM%34C2B1&TD&TB&TC%36G62F51%94K51>&TJ%14M73@&S2%11Q;%A6?C53I1(1%11E%Q:3E31&SCzr1%3221&SD&QF%2241%QK241'RG%Q111%L4Q>HD2%C4Q?IE3&Q;r2%22Q;1&S5%11R0%Q66QE97631%E1:%QN3:21p0=1pWNQE1%F2QDQD&SE%12QFQF%R43QI1H&R:%11R2vT<%R511%411%R:3QO41'Q<%125RA%RF231%RG2:1%RH2>1%RI2@1%RJ2Q71%RK2R01%RL2RD1").
Proof.
destruct bf_base as (B0 & BM & BC & BF). destruct HL0 as (HL1 & HL2 & HL3).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (NA : s_areas st !! (rid, PGSZ) = None).
{ destruct (s_areas st !! (rid, PGSZ)) as [ar|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _) & _). cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
assert (NM : forall k, 0 <= k < NSLOTS -> s_metas st !! mslot (rid, PGSZ) k = None).
{ intros k Hk. destruct (s_metas st !! mslot (rid, PGSZ) k) as [mr|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em). destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _) & _).
unfold mslot, aadd in Em. inversion Em. rewrite <- H0 in Hr'. cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
assert (RU : round_up_pg (2 * PGSZ) = 2 * PGSZ) by reflexivity.
split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [lia| split; [reflexivity| split; [reflexivity|]]]]]]].
2:{ constructor; cbn -[Z.mul]; auto; try reflexivity; [intros q rq H _; apply bf_keep; exact H| unfold rid; lia]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_brkreg KInv.set_brkph]; rewrite ?HL1, ?HL2, ?HL3.
+ intros q rq Hq. change (s_next_rid st3) with (N.succ (s_next_rid st)). apply bf_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
+ intros q rq Hq. apply bf_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn -[Z.mul]. rewrite RU.
split; [exact B0|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold PGSZ, LEN_MAX; lia|]. split; [exact BC|]. intros _. split; [apply Z_mod_mult| lia].
+ intros q1 q2 r1 r2 H1 H2 NE.
apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn -[Z.mul]. rewrite RU. pose proof (ranges_free_regions st _ _ q2 r2 BF H2) as D. destruct (region_live_range r2) as [b2 l2]. unfold PGSZ in *. lia.
* pose proof (ranges_free_regions st _ _ q1 r1 BF H1) as D. destruct (region_live_range r1) as [b1 l1]. cbn -[Z.mul]. rewrite RU. unfold PGSZ in *. lia.
+ exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|].
change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
cbn -[Z.mul map_to_list]. apply Permutation_refl.
+ eapply Permutation_trans; [exact ir_metas|].
change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
cbn -[frontier PGSZ Z.div Z.sub Z.mul map_to_list].
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn [fst snd].
rewrite (bf_frontier_old q rq Hin), bf_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite bf_fresh in Hin; discriminate| reflexivity].
+ intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (bf_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq K).
+ cbn. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
exists q, rq. split; [apply bf_keep; exact Hq| auto].
+ intros b l. split.
* intros Eb. inversion Eb. subst b l. exists rid, (mkRegion RKBrk base (2 * PGSZ)). split; [rewrite bf_lookup, N.eqb_refl; reflexivity|]. cbn. auto.
* intros (q & rq & Hq & Kq & Eb & El). apply bf_some in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq Kq).
+ intros q1 q2 r1 r2 H1 H2 K1 K2.
apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
* exfalso. exact (bf_nobrk q2 r2 H2 K2).
* exfalso. exact (bf_nobrk q1 r1 H1 K1).
* exfalso. exact (bf_nobrk q1 r1 H1 K1).
+ cbn -[Z.mul]. split; [reflexivity|]. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl. cbn. auto.
+ cbn -[Z.mul]. split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl.
split; [reflexivity|]. split; [left; reflexivity|]. cbn -[Z.mul]. unfold PGSZ. split; [lia|]. split; [reflexivity|]. split; [lia| intros; lia].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply bf_keep; exact Hrq| auto].
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite bf_frontier. split; [apply bf_keep; exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
rewrite (bf_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|]; [| exact F]. exfalso. rewrite <- E1, bf_fresh in Hq. discriminate.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
- apply (inv_M_ext X st st3); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st3); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X st st3); [reflexivity| reflexivity| intros q rq Hq Kq E; apply bf_keep; exact Hq| exact (G1 m b ai Hb)].
+ exact G2.
+ exact G3.
+ intros q rq Hq Kq Ho. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq Kq Ho).
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply bf_keep; exact Hq| exact Kq].
- apply (inv_S_ext X st st3 BL); [reflexivity| reflexivity| reflexivity| exact IS].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
Qed.
End BRK_FIRST.
End CEIL_WRAP_1.
