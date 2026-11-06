(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~k42MR46Stdlib6ZArith6BinInt1Zo72le37Corelib4Init5Logicq43andq42eq37Corelib7Numbers7BinNumss31Zk45hosts0am_last_idx0bslot_start'37Corelib4Init9Datatypeshg14listk43blkk46extrask45inv_S06mstateq43notk44one504meta0bm_set_avail0bm_set_freed08upd_meta05m_mem04optr06m_prev06m_next0bm_sizeclass08m_maplen0aget_stridek45gbasek46sstartk46cnt_ofk44INVL04ghdrs31N35stdpp7numbers1Nhu26eq_dec35stdpp7numbers1Zhvd6eq_dechg14Some25stdpp9countableii0bN_countableii0bZ_countableii0eprod_countable25stdpp9decidableim1bprod_eq_dechg16option06mkGhdr08s_groups25stdpp4baseipd6lookup25stdpp4gmapir34gmapir3bgmap_lookuphg14boolhg14truek44tbitq45Falseo72lthg14None37Corelib5Lists7ListDefjg23mapk45bslot04cptr36Stdlib5Lists4Listjie2Inq42exk46x_pendq42or07LActivek47head_ofk47x_freshk47in_list04UNIT0asize_classo73mulk47allfree09mask_uptoo73lor" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma slot_key_inj : ltac2:(zQ "e0!je!o2!pf!r8!re!tc!u0!u8!v4!hh9!hi1!hi7!hj0!hj8>1X$b>2st$d>2BL@1$9$a>2IS@3$c^3^2^1>2b1$0>2m1$0>2b2$0>2m2$0>2i1$5>2i2$5>0@3$6^9^6^5>0@3$6^a^5^4>0@2$3@2$2Z^4@2$2^4@1$7@2$1^b^7>0@2$3@2$2Z^4@2$2^4@1$7@2$1^c^6>0@3$4$0@2$8@2$1^d^9^6@2$8@2$1^d^7^5@2$3@3$4$0^a^8@3$4$5^7^6").
Proof. intros X st BL IS b1 m1 b2 m2 i1 i2.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

(* [comment removed for export] *)
Lemma one5_E_irrel : ltac2:(zQ "20!hk0!hk6>1AP>1BP>1CP>1DP>1EP>2E'P>0@5$1^6^5^4^3^2>0@1$0^3>0@1$0^3@5$1^9^8^7^6^4").
Proof. intros A B C D E E'.
  unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : ltac2:(zQ "10!ht1@5$0?1X?2st?1L?2BL?2LS").
Hypothesis Hg : ltac2:(zQ "h20!ht8!hte!tc!je!hv3!ige!ih8!ij1!ik0!ikf!in2!io1!re!iob!ip3!iq9!irf!is7@3$c@1$b$0@6$f$3$0@4$h0$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0@4$h1$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0?1b@1$e?2st@2$6$0@2$d@2$6$3?1g?2ai").

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : ltac2:(zQ "b0!pf!r8!it6!ite!re!iu6!tc!o2!u8!iud!iv5@2$1@2$0Z?2A'@2$1@2$0Z?2F'@2$1>1i$6>0@2$0Z^1>0@3$4$2@2$5?2A'^2$3@2$0^3?2ai@2$1>1i$6>0@2$0Z^1>0@3$4$2@2$5?2F'^2$3@2$0^3@1$8@2$7?2st?1g@2$1>1i$6>0@2$0Z^1>0@3$4$2@2$5?2A'^2$3>0@3$4$2@2$5?2F'^3$3$9>1i$6>0@2$1@2$a?2ai^1@2$0^1@1$8@2$7?2st?1g@3$4$2@2$5?2F'^2$3").
Hypothesis C_part : ltac2:(zQ "i10!je!tc!ht8!re!hte!hv3!ige!it6!io1!ite!o2!iu6!pf!ij1!ik0!ikf!in2!iva!ih8!r8!hk0!jh9!hi1!ji0!hk6!ji8!u8!ip3!v4!jk1!iq9!irf!is7>1i$1>0@2$h3@2$cZ^1@2$c^1@1$ha@2$a?2st?1g=1s$0@2$hc@2$a?2st?1g^2@5$h8@3$3$7@2$b?2A'^3$9@3$3$7@2$b?2F'^3$9@3$hd$0^1@4$h5$h6$h9$h7?2BL@1$h4@3$3@1$8$2@6$he$0$2@4$hf$0@4$h0$4$5$1$6@6$f$4$5$d$1$6$e$2@4$i0$0@4$h0$4$5$1$6@6$f$4$5$d$1$6$e$2^1@1$hb?2st@1$h1$2@3$3@1$8$0?5pend'@2$h2$0^1").
(* [comment removed for export] *)
Hypothesis C_pend : ltac2:(zQ "d5!je!r8!re!tc!o2!pf!io1!ih8!jk7!jkc!u8!v4!jl5&@2$1@2$5Z^1@2$5^1@1$a@2$4?2st?1g&@3$2$0^3@2$b@2$4?2st?1g^1&@2$1~0~1&\1i$3~2&@2$8$3~3@2$c@3$2@1$6$0?5pend'@1$9?1X@2$1>1s$0>0@3$2@1$6$0@1$9?1X@2$7$0^1~4>1s$0>0@3$2@1$6$0?5pend'@2$7$0^1~4").
Hypothesis C_rest : ltac2:(zQ "b0!je!re!hk0!tc!ih8!io1!jla!r8!jm3!jmd!jk1>0@1$2@3$1@1$5$0@1$9?1X@2$4$0?1g>2sc$3>0@3$a$0?1g@1?2LS@1$6^1>0@1$2@3$1@1$5$0@2$4$0?1g@1$8@1?2LS@1$6^2@2$7@3$1$3?2A'Z@1$2@3$1$3?2F'Z").
Hypothesis C_unlisted : ltac2:(zQ "c0!re!hk0!tc!je!ih8!io1!r8!o2!jn7!jmd!hp4!iv5>0@1$1@3$0@1$5$3@1$9?1X@2$4$3?1g>0@2$b@1$a@2$7?2st?1g+j0>0@1$1@2$8?2LS?1g@2$6@3$0$2?2A'Z@3$0$2?2F'Z").
Hypothesis C_under : ltac2:(zQ "f0!re!o2!tc!je!hp4!iv5!ih8!io1!r8!hk0!jmd!jo1!hqb!jo7!jp3>0@1$9@3$0@1$7$3@1$a?1X@2$6$3?1g>0@2$5@1$4@2$1?2st?1g+j0>0@2$5@1$c@2$1?2st?1g@2$e$b@1$d@1$4@2$1?2st?1g@2$8@3$0$2?2A'Z@3$0$2?2F'Z").
(* [comment removed for export] *)
Hypothesis C_big : ltac2:(zQ "50!re!tc!r8!o2!hp4>0@3$0$1@1$4@2$3?2st?1g+jf@2$2@3$0$1?2A'Z@3$0$1?2F'Z").
Hypothesis C_empty : ltac2:(zQ "ha0!tc!je!o2!ht8!re!hte!hv3!ige!hp4!ih8!hk0!ij1!ik0!ikf!in2!io1!jp9!u8!jq3!iob!ip3!jqe!iv5!iq9!irf!is7>0@3$4$0@2$h5?2A'?2F'@1$h2@1$h1@2$2?2st?1g>0@2$h6@1$8@2$2?2st?1g+j0>2m2$1>2b2$1>3ai2$0>0@3$4@1$f$3@6$h7$1$3@4$h8$1@4$e$5$6$0$7@6$d$5$6$b$0$7$c$3@4$h9$1@4$e$5$6$0$7@6$d$5$6$b$0$7$c$3^2@1$h4?2st@2$9$3@2$h3@2$9$1^3^1>0@1$a@3$4$1^4?1g>0@3$4$0@1$8@2$2?2st^5@1$8@2$2?2st?1g@1$a@1$h0@2$2?2st^6").

Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
Lemma R'_other : ltac2:(zQ "80!re!o2!je!hkd!hk0!hl3!hm0!hmd>1x$2>0@1$4@3$0$2^1?1g@3$0$3@2$1@3$7?1g\1r$3@2$5?2A'@2$6?2F'^1?2st^2@2$1?2st^2").
Proof. intros x. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma R'_mem : ltac2:(zQ "90!o2!hn7!re!je!hl3!hm0!hkd!hne!hmd>1x$3@3$2$7@1$1@2$0@3$8?1g\1r$6@2$4?2A'@2$5?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev : ltac2:(zQ "90!o2!ho4!re!je!hl3!hm0!hkd!hne!hmd>1x$3@3$2$7@1$1@2$0@3$8?1g\1r$6@2$4?2A'@2$5?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next : ltac2:(zQ "90!o2!hoc!re!je!hl3!hm0!hkd!hne!hmd>1x$3@3$2$7@1$1@2$0@3$8?1g\1r$6@2$4?2A'@2$5?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last : ltac2:(zQ "90!o2!u8!re!tc!je!hl3!hm0!hkd!hmd>1x$4@3$2$3@1$1@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc : ltac2:(zQ "90!o2!hp4!re!tc!je!hl3!hm0!hkd!hmd>1x$4@3$2$3@1$1@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_maplen : ltac2:(zQ "90!o2!hq1!re!tc!je!hl3!hm0!hkd!hmd>1x$4@3$2$3@1$1@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_stride : ltac2:(zQ "90!o2!hqb!re!tc!je!hl3!hm0!hkd!hmd>1x$4@3$2$3@1$1@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase : ltac2:(zQ "80!o2!hr7!je!re!hl3!hm0!hkd!hmd>1x$2@3$3$2@1$1@2$0@3$7?1g\1r$6@2$4?2A'@2$5?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sstart : ltac2:(zQ "90!tc!o2!hrf!re!je!hl3!hm0!hkd!hmd>1x$4>1i$0@3$3$0@2$2@2$1@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^2^1@2$2@2$1?2st^2^1"). Proof. intros x i. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_slot_start' : ltac2:(zQ "90!o2!je!v4!re!tc!hl3!hm0!hkd!hmd>1x$1>1i$4@3$3$1@2$2@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^2^1@2$2@2$0?2st^2^1"). Proof. intros x i. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_cnt : ltac2:(zQ "90!o2!hs8!re!tc!je!hl3!hm0!hkd!hmd>1x$4@3$2$3@1$1@2$0@3$8?1g\1r$7@2$5?2A'@2$6?2F'^1?2st^1@1$1@2$0?2st^1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.

Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
    + intros a ar k Ha Hk Ht. apply keys'. left. exact (ia_carved a ar k Ha Hk Ht).
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5 M6]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
    + intros m Hm. apply keys' in Hm. rewrite live'. destruct Hm as [Hm| ->]; [apply M6; exact Hm| left; exists b; exact g_hosts].
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5 G6]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      * (* [comment removed for export] *)
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: try exact C_big.
        all: match goal with |- ?g => idtac "REMAINS-G" g end.
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-O" g end.
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
    + (* [comment removed for export] *)
      intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. unfold allfree. rewrite ?R'_sc, ?R'_eq.
      destruct (aptr_eqb_spec m1 g) as [->|NE1]; destruct (aptr_eqb_spec m2 g) as [->|NE2].
      * intros; reflexivity.
      * rewrite fR_avail, fR_freed, fR_last. intros Hsc E AF1 AF2. exfalso. exact (C_empty AF1 Hsc m2 b2 ai2 H2 NE2 E AF2).
      * rewrite fR_avail, fR_freed, fR_last. intros Hsc E AF1 AF2. exfalso.
        apply (C_empty AF2 ltac:(rewrite E; exact Hsc) m1 b1 ai1 H1 NE1 (eq_sym E) AF1).
      * intros Hsc E AF1 AF2. exact (G6 m1 m2 b1 b2 ai1 ai2 H1 H2 Hsc E AF1 AF2).
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6 S7]; constructor.
    + intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      * (* [comment removed for export] *)
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
    + intros k m i Hk H1 H2. rewrite st'_slots in H1. rewrite R'_sc in H2. rewrite st'_regions. eapply S7; eassumption.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.
(* [comment removed for export] *)
