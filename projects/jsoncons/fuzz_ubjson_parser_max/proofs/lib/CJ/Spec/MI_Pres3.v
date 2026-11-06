(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Pres3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Pres3.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "0L"; "0LS"; "0RUNp"; "4mled"; "5INVL"]; ["5MR"; "5blk"; "5cnt_of"; "5extras"; "5gcnt"; "5inv_A"; "6ctx_scalars_eq"; "6rem"; "7account_bounce"; "7aptr"; "7bounces"; "7c_bounces"; "7c_mmap_counter"; "7c_seq"; "7c_unmap_seq"; "7decay_bounces"]; ["7g_meta"; "7ghdr"; "7lhead"; "7m_mem"; "7m_next"; "7m_sizeclass"; "7mctx"; "7meta"; "7mstate"; "7optr"; "7record_seq"; "7s_ctx"; "7s_groups"; "7s_metas"; "7set_bounce"; "7set_mmap_counter"]; ["7step_seq"; "7u32"; "7upd_ctx"; "8In"; "9add"; "9le"; "9lt"; "9pow"; "0X"; "0X'"; "0b"; "0c"; "0g"; "0h"; "0i"; "0l"]; ["0m"; "0sc"; "0st"; "0st'"; ":lookup"; ";N_countable"; ";Z_countable"; ";prod_countable"; "<prod_eq_dec"; "=gmap"; "=gmap_lookup"; ">eq_dec"; "?eq_dec"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
cs_secret : c_secret c' = c_secret c;
cs_init : c_init_done c' = c_init_done c;
cs_fmh : c_free_meta_head c' = c_free_meta_head c;
cs_am : c_avail_meta c' = c_avail_meta c;
cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
cs_mah : c_meta_area_head c' = c_meta_area_head c;
cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
cs_active : c_active c' = c_active c;
cs_usage : c_usage c' = c_usage c;
cs_brk : c_brk c' = c_brk c;
cs_mc : 0 <= c_mmap_counter c' < 2^32;
cs_seq : 0 <= c_seq c' < 256;
cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.
Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.
Theorem INVL_ctx_scalars : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "8&?v=vQHvR3v;v0v<%76654321").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
+ intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
- destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
+ split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
+ intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
- apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
- apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
- apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.
Lemma ctx_scalars_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "R2'Q6'5&QEz&Lr1%211%5241&QF&QG+2+Q0%3221%5271%=271&Mr2%211%@2?1+X0%<231%D231':'6'4%113&R4'R9&R<&R6%348218&R:%14:43:&Kr5%211%:6>>64D1(2%12@Q1%@3>31r3%Q72Q61%Q222O%Q:221%Q:2Q9L%Q52MJ%Q=221%Q>241p091pTLK1pSNL1&Nr6%211%L6Q0Q0HFQ61%Q03N1Ap019pTLQ31pSNQ41'F%12JJp031p0<1p0Q:1p0QB1pSHR11").
Proof. intros c. intros; constructor; auto. Qed.
Lemma ia_ctx_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "R4'Q8'Er1%211'5&QEz&L&Q;r2%211%411%7261&QF&QG+2+Q0%3221%5271%?271&M%11;%A2@1+X0%;231%E231':'6'4%113&R4'R9&R<&R6%348218&R:%14:43:&Kr4%O11%311%;6??75Q01(2%12AQ9%A3?31r3%Q92Q81%Q222O%Q<221%Q<2Q;Q8%Q52Q9K%Q?221%Q@241p091pTLL1pSNM1&N%11B%L6Q0Q0HFQA1%Q03N1@p018pTLQ31pSNQ41%QK281%QL2Q71%QM2Q>1p0QO1pT6R31").
Proof. intros st. intros IA. exact (ia_ctx _ IA). Qed.
Lemma INVL_step_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "L'C'Q8'>'3&A%211'Q2&I%511p031&?v=r5r4r3r2r1%76654321r6&Q@%118%;6:31876p051pJ>1p2C1pHG1pT6I1pSBK1").
Proof. intros X st L BL LS.
intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
- intros i v H. rewrite lookup_empty in H. discriminate.
- unfold ctx in NE. lia.
Qed.
Lemma INVL_record_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "N'C'Q8'>'3&A%211'Q2&I%511p031':&?v=r6r5r4r3r2%76654321r7&Q:%1248%;6:31876p051pT4>1pJ@1p2E1pHI1pT6K1pSBM1").
Proof. intros X st L BL LS sc.
intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
apply INVL_ctx_scalars; auto; constructor; cbn; auto.
unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
- rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
- rewrite lookup_insert_ne by congruence. apply C4.
Qed.
Lemma INVL_set_bounce : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "Q>'C'Q8'>'3&A%211'Q2&I%511p031':&?v=r7r6r5r4r3%76654321'5&QEz%2215&QF+Q0%2281%7241+X0%52;1%:271r:&Q>r9%23BA1r8%H6G521FEp071p0;1p0D1pTLM1pSNN1pJQ01p2Q51pHQ91pT6Q;1pSBQ=1").
Proof. intros X st L BL LS i v.
intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
intros j w. destruct (Z.eq_dec j i) as [->|NE].
- rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
- rewrite lookup_insert_ne by congruence. apply C3.
Qed.
Lemma bounces_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "C'Q8':'Er2%211'5&QEz&Jr3%2217%5241&QF+X0%2241%:241p0<1pSN@1pT6B1").
Proof. intros st i.
intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.
Lemma INVL_account_bounce : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "N'C'Q8'>'3&A%211'Q2&I%511p031':&?v=r6r5r4r3r2%76654321r7&H%1248%;6:31876p051pT4>1pJ@1p2E1pHI1pT6K1pSBM1").
Proof. intros X st L BL LS sc.
intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
destruct (negb _ && _); [| exact INV].
pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.
Lemma INVL_decay_bounces : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "N'C'Q8'>'3&A%211'Q2&I%511p031':&?v=r6r5r4r3r2%76654321r7&O%1248%;6:31876p051pT4>1pJ@1p2E1pHI1pT6K1pSBM1").
Proof. intros X st L BL LS sc.
intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
apply INVL_set_bounce; auto; lia.
Qed.
Lemma INVL_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "Q7'C'Q8'>'3&A%211'Q2&I%511p031&?v=r5r4r3r2r1%76654321r6&QB'Q6&Q?&QA&QD&L%119+1%4221%611%821=qSH:1%<21C%F6E>1CBAp0@1pJI1p2N1pHQ21pT6Q41pSBQ61").
Proof. intros X st L BL LS.
intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.
Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).
Lemma in_rem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "F&I'3%112&7&QCr3&Gr2r1%3221%63:51'5%83<74&8'6%13?:8%311%6251%?281pT0A1pSJD1pTNE1").
Proof. intros x g l. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.
Lemma present_of_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "Q='Q8&I'6&Q9&Q3&@r3r2%3221%511(2r1%22;1%;3:41&8'4'Q7%211&R4'R9&R8'9&R;':&R<%544321&R7&R5&R6%36872651%;4M51>&R:%14O73@&Q=r4%211%B6Q3D64N1(1%11F%Q53F31%J11p0L1pSFQ91pT2Q:1pT6Q<1").
Proof. intros st m b. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma present_of_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "Q='Q8&I'6&Q9&Q4&@r3r2%3221%511(2r1%22;1%;3:41&8'4'Q7%211&R4'R9&R8'9&R;':&R<%544321&R7&R5&R6%36872651%;4M51>&R:%14O73@&Q=r4%211%B6Q3D64N1(1%11F%Q53F31%J11p0L1pTNQ91pT2Q:1pT6Q<1").
Proof. intros st m x. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma gcnt_ext_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "R6'Q8'6'R9&I&R8'9&R;':&R<%544321&R7&R5&R6%36872651'Q1%=4<621&Q<r1%211r2%411%D3631'4%119&R4&R:%14GA=<r3r6%=11%66K@?431(2%12B=%Q03:31&Q9&Q0%119%62Q2B%Q53421'5&Q5&@r7%221@%411r8%521C%711%Q?3Q941&B%117%215%QC3Q=21%>251p0@1p0F1pT2QE1pSLQ;1pSFQG1&Dr4%221Q<r5%421Q>%QO3QI31pT4QJ1p081p0Q>1pT8R41pT6R51").
Proof. intros st st'.
intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.
Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.
Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
Lemma uz_R_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "A&I&8'6r1vQL%33521%511'Q7&@vR3r2%3221vR2%5213%<3731p091pTN@1").
Proof. intros x. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.
Theorem INVL_unzombie : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres3 "8&?v=vQIvR3v;v0v<%76654321").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (im_zomb _ _ _ IM g Hz) as (NIg & Ng & Pg & bg & Mg & NGg).
assert (NLg : forall b, ~ hosts st b g).
{ intros b [ai Hb]. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hm & _). cbn in Em. inversion Em. subst m. rewrite Mg in Hm. inversion Hm. subst. rewrite Hb in NGg. discriminate. }
assert (RG : forall b m, hosts st b m -> MR st' m = MR st m).
{ intros b m Hm. apply uz_R_other. intros ->. exact (NLg b Hm). }
assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
{ intros x. unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
split; [intros _; exact (present_of_mem st g bg Mg)| intros _; discriminate]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- apply (inv_R_X X); [reflexivity|]. destruct IR; constructor; try assumption.
- destruct IA; constructor; try assumption.
+ intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
+ intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
- destruct IM as [M1 M2 M3 M4 M5]; constructor.
+ intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
+ intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
+ intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
rewrite (uz_R_other m NE). auto.
+ intros m Hm. cbn in Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
+ intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
- destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
+ intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros x Hx; rewrite uz_R_other; try reflexivity; intros ->; apply NIg; exists h; rewrite E.
* apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
* apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
+ intros m. destruct (aptr_eqb_spec m g) as [->|NE].
* rewrite uz_R, aptr_eqb_refl. cbn. split; [| reflexivity]. split; [intros H; exfalso; exact (NIg H)| intros H; exfalso; apply H; reflexivity].
* rewrite (uz_R_other m NE). apply L5.
+ intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists LFree; exact Hm|]. rewrite (uz_R_other m NE). apply L6. exact Hm.
+ intros sc m Hm. destruct (L7 sc m Hm) as (A1 & A2 & A3).
destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists (LActive sc); exact Hm|]. rewrite (uz_R_other m NE). auto.
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
+ intros m b ai Hb. pose proof (G1 m b ai Hb) as GO.
assert (NE : m <> g) by (intros ->; exact (NLg b (ex_intro _ ai Hb))).
destruct GO; constructor; rewrite ?(uz_R_other m NE); try assumption.
* apply KEYS. exact g_present.
* intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hst).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _).
assert (NEp : p <> g) by (intros ->; exact (NLg bp Hp)).
exists p, i. rewrite (uz_R_other p NEp). auto 10.
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2.
rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply G3; eassumption.
+ intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (RG _ _ Hm). auto.
- destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
+ intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
+ intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
+ intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
+ intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
+ intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
+ intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
+ intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.
End CEIL_WRAP_1.
