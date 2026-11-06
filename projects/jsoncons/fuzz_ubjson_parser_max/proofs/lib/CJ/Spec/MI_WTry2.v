(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WTry.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WTry2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WTry2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1Some"; "1bool"; "1cons"; "1list"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "0L"; "0LS"; "0LS'"]; ["0RUNp"; "4INVL"; "4MR"; "4head_of"; "4sstart"; "5GOODH"; "5TA_frame"; "6LActive"; "6active"; "6aptr"; "6decay_bounces"; "6dequeue"; "6get_stride"; "6ghdr"; "6lhead"; "6m_avail"]; ["6m_freed"; "6m_last_idx"; "6m_next"; "6m_set_avail"; "6m_sizeclass"; "6mask_upto"; "6meta"; "6mkGhdr"; "6mstate"; "6optr"; "6s_groups"; "6set_active"; "6upd_meta"; "7In"; "8land"; "8le"]; ["8lt"; "8testbit"; "0X"; "0a"; "0ai"; "0b"; "0c"; "0f"; "0i"; "0m"; "0m1"; "0mn"; "0n"; "0r"; "0rest"; "0sc"]; ["0sc0"; "0st"; "9lookup"; ":N_countable"; ":Z_countable"; ":prod_countable"; ";prod_eq_dec"; "<gmap"; "<gmap_lookup"; "=eq_dec"; ">eq_dec"; "0v"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Record TA_frame (st st1 : mstate) (sc : Z) : Prop := mkTAF {
taf_regions : s_regions st1 = s_regions st;
taf_shadow : s_shadow st1 = s_shadow st;
taf_tick : s_tick st1 = s_tick st;
taf_slots : s_slots st1 = s_slots st;
taf_areas : s_areas st1 = s_areas st;
taf_next_rid : s_next_rid st1 = s_next_rid st;
taf_heads : forall h, h <> LActive sc -> get_head st1 h = get_head st h;
taf_usage : forall sc', usage st1 sc' = usage st sc';
taf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
taf_ssec : s_secret st1 = s_secret st;
taf_secret : c_secret (s_ctx st1) = c_secret (s_ctx st) /\ c_init_done (s_ctx st1) = c_init_done (s_ctx st)
}.
Lemma taf_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "8'Q8'<'Fr2r1%33221pT051pT471"). Proof. intros st sc. constructor; auto. Qed.
Lemma taf_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "A'Q8'<'Fr4r3r1%43321r2%63541r6%83176p031p061pT0<1pS>>1pS<?1pS8@1").
Proof. intros a b c sc.
intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
all: try (intros sc'; rewrite (B8 sc'); apply A8).
all: split; congruence.
Qed.
Lemma taf_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "A'Q8&I'Q6p011'<'Fr4&Q<r3r2%33214r1%73621pT091pS@;1pSD>1pT4@1").
Proof. intros st m f sc. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "='Q8'<&Q9'Fr3&Q;r2r1%33214%63513pTH81pT0:1pT4<1").
Proof. intros st sc v.
constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "<'Q8'<'Fr3&Jr1%2213r2%63521pT281pT091pT4;1").
Proof. intros st sc sc0. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "?'Q8'<&I'Fr3&K(Gr2%211r1%53216%83714pSD:1pT0<1pT4>1").
Proof. intros st sc m.
destruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). destruct FC.
constructor; auto.
all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
all: try (split; assumption).
Qed.
Section HEADFACTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HA : active st sc = Some m.
Lemma hd_list : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "A'9'4&I%211'8v>(GvQO%211%411(3vQIr1%33;21%:3;51qSN<1%@2=1").
Proof.
pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
Lemma hd_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "9&Q=&IvQIv>(GvQO%211%411%83761").
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
Lemma hd_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "QF'7&Q?zvQO%3221&Q@+Q@%2241%8241'8'<&Q4&BvR1vQI%3221%511%8371>'9&I'5'M%211&R2'R7&R6';&R9&R:%4432C1&R5&R3&R4%36762G51%:4?51=&R8%14A73?r2&Q:%11J%A6EC6431(1(Q7%22HMr1%3221%52I1%Q63I71qS:Q61%O2Q71qS<O1%Q12Q01%QD2Q31%QE2Q=1").
Proof.
destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C). split; [exact A|]. split; [exact C|]. exists b, ai. exact Hb.
Qed.
Lemma hd_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 ">'8&Q9&Cv>(GvQO%211%411%611(1&IvQI%3221%=3<51").
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
Lemma hd_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "I'9&I'7'8&Q9&Q2&BvR1vQI%3221%511(1r1%22<1%;3:41&Q=v>(GvQO%211%411%63D91%D281qSHF1%H2G1").
Proof.
destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _). exists y. auto.
Qed.
End HEADFACTS.
Definition GOODH (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr) : Prop :=
INVL X st L BL LS /\ active st sc = Some m /\ m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0.
Section STEPS.
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.
Lemma rotate_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "Q8'Q8'N'4&I%211p041&EvQBr4v=v0r3vQOr2%877654321'8&Q9&Q2&Br5%2219%411(1%12D:%93831'9&Q;%52HCr7%33A21r1%I7H2FE1CGqQ0K1%82L1p0:1p0E1pSHQ11pSDQ21pNQ11pT4Q71").
Proof. intros st LS m mn.
intros (INV & HA & AV & FR) Hn.
destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
assert (INV' : INVL X (set_head (LActive sc) (Some mn) st) L BL (fupd LS (LActive sc) (rest ++ [m]))).
{ apply (INVL_rotate X st L BL LS sc m mn rest INV HL Hn). intros _ _. auto. }
exists (fupd LS (LActive sc) (rest ++ [m])). split; [exact INV'|].
split; [unfold active, set_active, ctx; cbn; rewrite lookup_insert_eq; reflexivity|].
change (MR (set_active sc (Some mn) st) mn) with (MR st mn).
pose proof (next_listed X st L BL LS INV (LActive sc) m mn (hd_in X st L BL LS sc m INV HA) Hn) as Hin.
destruct (aptr_eq_dec mn m) as [->|NE]; [auto|].
destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin) as (_ & [bb [aa Hbb]] & _).
apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
rewrite (hd_head X st L BL LS sc m INV HA). congruence.
Qed.
Section SE.
Local Abbreviation SEC_T_dequeue_exhausted_ok := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "RC'Q8'N'4&I%211p041&Av@vQBr3v=v0r2%76654321'8&Q9&Hr4vQO%3221(1%12B9%83731'<&O&Br5%221B%411z%@3721&Q0r6%821@%311%E3<16'9'7&K(G%11Fr7r9%53321%Q66Q5Q41Q2Q1Q0r8%116(3r1%23Q>81%Q43Q>41%Q328Q1&C%115%Q83Q731%31Q;%Q42QE8%Q;3Q:21r;%Q221Q?%Q411%Q?3Q61Q0&:%Q014%QB3Q91Q3%311%M251p0:1pSFR11%Q02?1%Q12D1%Q22K1qSNR41%Q52R51qQ0R51%Q72R61p0Q91p0Q?1p0QH1p0R21pSDR=1pNR<1pT4RB1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_dequeue_exhausted_ok) 0%nat 0%nat).
Variable LS : ltac:(sec_ty2 constr:(SEC_T_dequeue_exhausted_ok) 1%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_dequeue_exhausted_ok) 2%nat 0%nat).
Lemma dequeue_exhausted_ok : ltac:(sec_stmt2 constr:(SEC_T_dequeue_exhausted_ok) 3%nat 0%nat).
Proof.
intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
{ apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl). intros bb aix Hbb.
destruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _). rewrite G5 in Hbb.
pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ (ex_intro _ aix Hbb) (ex_intro _ ai Hb)) as ->. rewrite Hb in Hbb. inversion Hbb. subst aix.
pose proof (dequeue_data (LActive sc) m st m) as D. destruct (data_same _ _ 0 D) as (_ & El & Ea & Ef & Es & _).
rewrite El, Ea, Ef, Es. split; [| split; [intros; auto| split; [| intros; auto]]].
- intros Hlt. exfalso. pose proof (g_masks _ _ _ _ _ _ GO) as (_ & _ & _ & _ & _ & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
specialize (M6 (m_last_idx (MR st m)) ltac:(lia)). unfold tbit in M6. rewrite FR, Z.bits_0 in M6. discriminate.
- intros sc0 Hin. exfalso. cbn in Hin.
apply (m_out X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)). exists (LActive sc0). exact Hin. }
replace (xfresh (xfresh X (Some m)) None) with X in INV2 by (destruct X; cbn in HF |- *; subst; reflexivity).
exists (fupd LS (LActive sc) ([] ++ rest)), rest. split; [exact INV2|]. split; [exact HL|]. split.
- change (active (dequeue (LActive sc) m st) sc) with (get_head (dequeue (LActive sc) m st) (LActive sc)). rewrite dequeue_head.
rewrite decide_True by reflexivity. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. rewrite HL in HH. cbn in HH.
destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
destruct (optr_eqb_spec (Some mn) (Some m)) as [E|NE].
+ inversion E. subst mn. pose proof (proj1 (lists_singleton st LS (old_lists _ _ _ _ _ INV) (LActive sc) m rest HL) Hn) as ER. rewrite ER. reflexivity.
+ change (get_head st (LActive sc)) with (active st sc). rewrite HA, optr_eqb_refl. rewrite HL in Hin. destruct Hin as [->|Hin]; [congruence|].
destruct rest as [|a rest']; [destruct Hin|]. cbn.
pose proof (il_dll _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as D. rewrite HL in D. cbn [dll app] in D. destruct D as (D1 & _). rewrite Hn in D1. exact D1.
- intros m1 Hm1. destruct rest as [|a rest']; cbn in Hm1; [discriminate|]. inversion Hm1. subst a.
assert (Hin : In m1 (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin) as (_ & [bb [aa Hbb]] & _).
apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
rewrite HL. cbn. intros E. inversion E. subst m1.
pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left.
Qed.
End SE.
End STEPS.
Lemma land_mask_upto_all : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "O'<&Q?zr2%3221r1%5241'8'2&QAr6%2218(6%63521r3%>215p031p0;1pSBB1&Q>r5&Q5r4%211%5241%B3I15p081p0G1p0H1pSJM1pS@N1").
Proof. intros f n.
intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.
Lemma land_mask_upto_zero_above : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "O'<&Q?zr2%3221'8&Q>r4&Q5r3%211%5241%73<1:r1%=2<1'2&QAr7%221?(6%?3521&Q@%125=p031p0:1pSBI1p0>1p0G1p0H1pSJM1pS@N1").
Proof. intros f n.
intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
rewrite H, Z.bits_0 in T. discriminate.
Qed.
Section TRY.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.
Definition TA_POST (st st1 : mstate) (first : Z) (LS1 : lhead -> list aptr) : Prop :=
TA_frame st st1 sc /\
((first = 0 /\ active st1 sc = None /\ INVL X st1 L BL LS1)
\/ (exists g bg ai idx, first <> 0 /\ 0 <= first /\ ctz32 first = idx /\ active st1 sc = Some g
/\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ 0 <= idx <= m_last_idx (MR st1 g)
/\ m_sizeclass (MR st1 g) = sc /\ UNIT * size_class sc <= get_stride (MR st1 g)
/\ INVL (xpend X (Some (fst bg, sstart (MR st1 g) idx))) st1 L BL LS1)).
Lemma set_avail_views : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WTry2 "Q0'<'Q6'7'8&Q1&Q3r2r1%3221%511%613%83;21&Q4%115%217%<3?21&L%119%21;%@3C21&Dr3%A21@%321@%42BA%F3I21pSBJ1%I281%J2=1%K2B1pSLM1pTHO1").
Proof. intros v r. destruct r; repeat split; reflexivity. Qed.
Lemma fin_ok st0 st LS m (mask : Z) :
INVL X st L BL LS -> TA_frame st0 st sc -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST st0 st1 first LS1.
Proof.
intros INV TF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
right. exists m, bm, ai, (ctz32 (lowbit mask)).
assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.
Section SE.
Local Abbreviation SEC_T_try_avail_ok := (forall st LS, INVL X st L BL LS ->
exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST st st1 first LS1) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_try_avail_ok) 0%nat 0%nat).
Variable LS : ltac:(sec_ty2 constr:(SEC_T_try_avail_ok) 1%nat 0%nat).
Theorem try_avail_ok : ltac:(sec_stmt2 constr:(SEC_T_try_avail_ok) 2%nat 0%nat).
Proof.
intros INV. unfold try_avail.
destruct (active st sc) as [m|] eqn:HA.
2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
assert (STEP1 : exists st1 m1 LS1,
(if m_freed (MR st m) =? 0
then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
/\ GOODH X st1 L BL LS1 sc m1 /\ TA_frame st st1 sc
\/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
{ destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
- destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
rewrite HA1. destruct rest as [|m1 rest']; cbn.
+ exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
+ exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| apply taf_dequeue].
destruct (NXT m1 eq_refl) as [A1 F1].
assert (NE : m1 <> m).
{ intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
- destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| apply taf_set_active]. }
destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]).
2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [apply taf_dequeue| left; auto]. }
rewrite E1. clear E1.
assert (STEP2 : exists st2 m2 LS2,
(let mr := get_meta_rec st1 m1 in
if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
/\ GOODH X st2 L BL LS2 sc m2 /\ TA_frame st st2 sc).
{ cbn zeta. fold (MR st1 m1). destruct (_ && _).
- pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| eapply taf_trans; [exact TF1| apply taf_set_active]].
- exists st1, m1, LS1. auto. }
destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & TF2). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
cbn iota. fold (MR st2 m2).
destruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
assert (GAI : group_active_idx st2 b2 = ai2).
{ unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
rewrite GAI.
assert (STEP3 : exists st3 m3 LS3 b3 ai3,
(if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
else (let cnt := ai2 + 2 in
let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
let span := UNIT + size * cnt in
let cnt := span_loop 300 cnt span size in
let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
(set_group_active_idx b2 (cnt - 1) st2, m2))
else (st2, m2)) = (st3, m3)
/\ GOODH X st3 L BL LS3 sc m3 /\ TA_frame st st3 sc
/\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
{ destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
-
pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
assert (PART : ai2 < m_last_idx (MR st2 m2)).
{ destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
+
set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
set (st3 := Malloc.set_groups _ st2).
assert (INV3 : INVL X st3 L BL LS2).
{ apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
split; [split; [exact INV3| split; [exact HA2| auto]]|].
split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
change (MR st3 m2) with (MR st2 m2). intros E0.
assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
{ rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
rewrite E0, Z.bits_0 in Tb. discriminate.
+
destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
assert (NEm : mn <> m2) by congruence.
destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
assert (FULL : ai3 = m_last_idx (MR st2 mn)).
{ pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
split; [eapply taf_trans; [exact TF2| apply taf_set_active]|]. split; [exact Hb3|].
change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
destruct G3 as (_ & _ & _ & F3). exact F3.
- exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & TF3 & Hb3 & ACT).
match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
cbn iota. clear E3.
destruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
set (st4 := upd_meta m3 _ st3) in INV4 |- *.
rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
set (st5 := decay_bounces _ st4) in INV5 |- *.
assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
{ transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
destruct (fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
- eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
- exact HA5.
- rewrite MR5. reflexivity.
- exact ACT.
- exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End SE.
End TRY.
End CEIL_WRAP_1.
