(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Ext~~~~~~07ctrl_eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~k76mstate37Corelib7Numbers7BinNumsoe1Zk74aptrk73wr8k74wr1637Corelib4Init5Logicrf2eqoe1N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~tc2MRk74metak77s_metas35stdpp7numbers1Nhj06eq_dec35stdpp7numbers1Zhkb6eq_dec25stdpp9countablehm6bN_countablehm6bZ_countablehm6eprod_countable25stdpp9decidablehq7bprod_eq_dec25stdpp4gmaphs74gmaptc5hostsk78s_groupsrf3iffk74ghdrtcalive_grouptc8frontierk7h2c_avail_meta_areask75s_ctxk74optrk76regiontc4gcntk78get_headk75lheadk74mctxk77c_usagek75usagetc5knownk78s_shadowk76shadowtc7unknowntc6linked37Corelib4Init9Datatypesiq34listtc3dlltc5inv_Rtc5inv_Atc5inv_Mtc5inv_Ltc8group_oktc5inv_Gtc5inv_Stc6inv_SHtc3blkk76s_tickk78set_tick46Stdlib6NArith6BinNat1Nji72letc5gbasek7aget_stridek7am_last_idxk78m_maplenk79s_regionsk77s_slotsiq34prod" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ctrl_eq (st st' : mstate) : Prop := mkCE {
  ce_ctx : s_ctx st' = s_ctx st;
  ce_regions : s_regions st' = s_regions st;
  ce_next_rid : s_next_rid st' = s_next_rid st;
  ce_metas : s_metas st' = s_metas st;
  ce_areas : s_areas st' = s_areas st;
  ce_groups : s_groups st' = s_groups st;
  ce_slots : s_slots st' = s_slots st;
  ce_secret : s_secret st' = s_secret st;
  ce_reserved : s_reserved st' = s_reserved st
}.

Lemma ctrl_eq_refl : ltac2:(zQ "20!je!o5>2st$1@2$0^1^1").
Proof. intros st. constructor; reflexivity. Qed.
Lemma ctrl_eq_trans : ltac2:(zQ "20!je!o5>1a$1>1b$1>1c$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros a b c. intros [] []; constructor; congruence. Qed.

(* [comment removed for export] *)
Lemma ctrl_eq_wr8 : ltac2:(zQ "50!q7!je!qb!o5!r2>2st$3>1p$2>1v$0@2$1^3@3$4^2^1^3"). Proof. intros st p v. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr16 : ltac2:(zQ "50!q7!je!qb!o5!r8>2st$3>1p$2>1v$0@2$1^3@3$4^2^1^3"). Proof. intros st p v. constructor; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VIEWS.
Variables st st' : mstate.

Lemma MR_ext : ltac2:(zQ "e0!t3!t8!q7!hha!qb!hhf!hi6!hk1!hlc!hn7!ho6!hp5!hr8!ht3>0@3$0@4$d$4@4$c$1$7$2$8@6$b$1$7$9$2$8$a$5@1$6?3st'@1$6?2st>1x$4@3$0$5@2$3?3st'^1@2$3?2st^1").
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
Lemma hosts_ext : ltac2:(zQ "f0!qb!t8!q7!htb!hu3!hk1!hlc!t3!hue!hv4!hn7!ho6!hp5!hr8!ht3>0@3$7@4$e$0@4$d$1$5$2$6@6$c$1$5$a$2$6$b$9@1$4?3st'@1$4?2st>1b$0>1m$0@2$8@3$3?3st'^2^1@3$3?2st^2^1").
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
Lemma live_group_ext : ltac2:(zQ "f0!t8!q7!hvb!qb!hu3!hk1!hlc!t3!hue!hv4!hn7!ho6!hp5!hr8!ht3>0@3$7@4$e$3@4$d$0$5$1$6@6$c$0$5$a$1$6$b$9@1$4?3st'@1$4?2st>1m$3@2$8@2$2?3st'^1@2$2?2st^1").
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
Lemma frontier_ext : ltac2:(zQ "80!t3!ig8!ih3!ii9!t8!q7!ij1!ij8>0@3$0$6@1$2@1$3?3st'@1$2@1$3?2st>3rid$4>1r$7@3$0$5@3$1?3st'^2^1@3$1?2st^2^1").
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
Lemma gcnt_ext : ltac2:(zQ "h00!q7!t8!hk1!hlc!t3!ik1!qb!hu3!hi6!hn7!ho6!hp5!hr8!ht3!hv4!hhf>0@3$4@4$d$6@4$c$1$2$0$3@6$b$1$2$9$0$3$a$e@1$7?3st'@1$7?2st>0@3$4@4$d$6@4$c$1$2$0$3@6$b$1$2$9$0$3$a$f@1$8?3st'@1$8?2st>2sc$0@3$4$0@2$5?3st'^1@2$5?2st^1").
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
Lemma get_head_ext : ltac2:(zQ "60!t3!ik8!ii9!il3!ilb!ij1>0@3$0$4@1$2?3st'@1$2?2st>1h$3@3$0$5@2$1?3st'^1@2$1?2st^1").
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.
Lemma usage_ext : ltac2:(zQ "80!q7!t3!im2!ii9!imc!ho6!ht3!hlc>0@3$1@4$6$0$7$5$0@1$2@1$3?3st'@1$2@1$3?2st>2sc$0@3$1$0@2$4?3st'^1@2$4?2st^1").
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.
Lemma known_ext : ltac2:(zQ "b0!in4!inc!t3!hue!t8!q7!qb!io7!hn7!ht3!hk1>0@3$2@4$9$4$a$8$7@1$1?3st'@1$1?2st>1p$6>1v$5@2$3@3$0?3st'^2^1@3$0?2st^2^1").
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma unknown_ext : ltac2:(zQ "a0!ip0!inc!t3!hue!t8!qb!io7!hn7!ht3!hk1>0@3$2@4$8$4$9$7$6@1$1?3st'@1$1?2st>1p$5@2$3@2$0?3st'^1@2$0?2st^1").
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma linked_ext_metas : ltac2:(zQ "f0!t8!q7!ipa!qb!hi6!hk1!hlc!irb!t3!hhf!hn7!ho6!hp5!hr8!ht3>0@3$8@4$e$3@4$d$0$5$1$6@6$c$0$5$a$1$6$b$9@1$4?3st'@1$4?2st>1l@1$7$3>0@2$2?2st^1@2$2?3st'^2").
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
Lemma dll_ext_metas : ltac2:(zQ "f0!t8!q7!is3!qb!hi6!hk1!hlc!irb!t3!hhf!hn7!ho6!hp5!hr8!ht3>0@3$8@4$e$3@4$d$0$5$1$6@6$c$0$5$a$1$6$b$9@1$4?3st'@1$4?2st>1l@1$7$3>0@2$2?2st^1@2$2?3st'^2").
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ltac2:(zQ "10!je@2$0?2st?3st'").

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE.

Lemma inv_R_ctrl : ltac2:(zQ "10!is9>0@3$0?1X?2st?1L@3$0?1X?3st'?1L").
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HC, ?HG, ?HA; try assumption.
  - (* [comment removed for export] *)
    eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r q H1 H2 H3 H4 H5. rewrite FR in H4. eauto.
Qed.

Lemma inv_A_ctrl : ltac2:(zQ "10!it1>0@1$0?2st@1$0?3st'").
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
  destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
  - intros a ar H. destruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
  - intros sc Hsc. rewrite US, GC. auto.
Qed.

Lemma inv_M_ctrl : ltac2:(zQ "10!it9>0@3$0?1X?2st?2LS@3$0?1X?3st'?2LS").
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5 M6]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
  - intros m Hm. rewrite HM in Hm. rewrite (live_group_ext st st' HG). apply M6. exact Hm.
Qed.

Lemma inv_L_ctrl : ltac2:(zQ "10!iu1>0@2$0?2st?2LS@2$0?3st'?2LS").
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (get_head_ext st st' HC) as HE.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ctrl : ltac2:(zQ "30!iu9!qb!q7>1m$1>1b$1>2ai$2>0@6$0?1X?2st?2LS^3^2^1@6$0?1X?3st'?2LS^4^3^2").
Proof. intros m b ai.
  intros I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_G_ctrl : ltac2:(zQ "10!iv4>0@3$0?1X?2st?2LS@3$0?1X?3st'?2LS").
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [G1 G2 G3 G4 G5 G6]; constructor.
  - intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
  - intros b ai H. rewrite HG in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
  - intros rid r H1 H2 H3. rewrite HR in H1. destruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
  - intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G6; eassumption.
Qed.

Lemma inv_S_ctrl : ltac2:(zQ "10!ivc>0@3$0?1X?2st?2BL@3$0?1X?3st'?2BL").
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6 S7]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
  - intros k m i Hk H1 H2. rewrite HS in H1. rewrite ME in H2. rewrite HR. eapply S7; eassumption.
Qed.
End CTRL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_SH_set_tick : ltac2:(zQ "80!jg4!irb!t8!jgd!o5!jh3!jhc!jjf>2st$4>2BL@1$1$3>1t$2>0@2$7@1$5^3^1>0@2$0^4^3@2$0@2$6^3^5^4").
Proof. intros st BL t.
  intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
  intros rid sh H. destruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
  - intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
  - intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
  - intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma inv_SH_view : ltac2:(zQ "hd0!t3!q7!hha!qb!t8!hk1!hn7!ht3!hlc!jk5!jg4!jkd!jla!jm7!o5!hu3!jn2!inc!jne!jh3!ho6!hp5!hr8!irb!jo8!jgd!hv4!ij8!io7>2st$e>3st'$e>2BL@1$h7$h9>0@3$0@4$7$4$5$6$hc@1$h1^2@1$h1^3>0@3$0$4@1$h3^3@1$h3^4>0@3$0@4$7$4$5$6$hb@1$h0^4@1$h0^5>0@3$0@4$7$3@4$h6$4$5$1$8@6$h5$4$5$6$1$8$h4$ha@1$f^5@1$f^6>0@3$0@4$7$3@4$h6$4$5$1$8@6$h5$4$5$6$1$8$h4@2$h8$3$1@1$h2^6@1$h2^7>0>1x$3@3$0$3@1$9@2$2^8^1@1$9@2$2^9^1>0>1x$3@3$0$1@1$b@2$2^9^1@1$b@2$2^a^1>0>1x$3@3$0$1@1$c@2$2^a^1@1$c@2$2^b^1>0>1x$3@3$0$1@1$d@2$2^b^1@1$d@2$2^c^1>0@2$a^c^a@2$a^c^b").
Proof. intros st st' BL.
  intros SH TK HR HG HS VB VS VL VM I.
  assert (VSS : forall x i, sstart (MR st' x) i = sstart (MR st x) i) by (intros; unfold sstart; rewrite VB, VS; reflexivity).
  assert (VC : forall x, cnt_of (MR st' x) = cnt_of (MR st x)) by (intros; unfold cnt_of; rewrite VL; reflexivity).
  pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
  destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
  - intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
  - intros b m i Hb Hi. rewrite VC in Hi. rewrite VSS. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
  - intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
  - intros b m p i Hb Hml Hs. rewrite VM in Hml. rewrite HS in Hs. rewrite !VB.
    destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !VS, !VB.
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
