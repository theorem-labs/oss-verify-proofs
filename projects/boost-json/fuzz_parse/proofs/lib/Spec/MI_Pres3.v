(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~j65s_ctx46Stdlib6ZArith6BinInt1Znc2lenc2lt25stdpp9countablepebZ_countable35stdpp7numbers1Zrd6eq_dec37Corelib4Init9Datatypest74Somet76optionhc2eqj6ec_mmap_counterj65c_seq25stdpp4basehhd6lookup25stdpp4gmaphj34gmaphj3bgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hl65inv_Aj69c_bouncesj6bc_unmap_seqj66mstatenc3powt74listhl64INVL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~ht54mledhl63blkhl66extrasj64aptrj65lheadj68step_seqj6arecord_seqj6aset_bouncej67bouncesj6eaccount_bouncej6ddecay_bouncesj64mctxj6h0set_mmap_counterj63u32j67upd_ctxnc3add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Kit~~~~~~irabaptr_eq_dec36Stdlib5Lists4Listjg76removehl63mkXhl67x_freshhl66x_idlehl66x_orphhl66x_pendhl66x_zombjg72Inhc3iffhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres3~~~~~~jn03remt74consj64meta01N35stdpp7numbers1Njs86eq_decpebN_countablepeeprod_countable25stdpp9decidablekg2bprod_eq_dect74Nonehl62MRj65m_memj64optrj67s_metasj66m_nextj64ghdrj68s_groupshl66cnt_ofhl64gcntj6bm_sizeclassj66g_metajn0ectx_scalars_eq" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  cs_mc : 0 <= c_mmap_counter c' < 2^32;
  cs_seq : 0 <= c_seq c' < 256;
  cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
  cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : ltac2:(zQ "10!hsd@5$0?1X?2st?1L?2BL?2LS").
Hypothesis CS : ltac2:(zQ "20!n4!koc@2$1@1$0?2st@1?1f@1$0?2st").
Let st' := upd_ctx f st.

Theorem INVL_ctx_scalars : INVL X st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
  assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
  assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
    + intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
    + intros rid r q H1 H2 H3 H4. rewrite FR in H4. exact (ir_pages rid r q H1 H2 H3 H4).
  - destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
    + split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
    + intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5 GOE]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| apply blk_regions_kept_refl; reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.

Lemma ia_ctx_facts : ltac2:(zQ "h41!h9!j0!n4!p4!p9!qf!se!uf!v6!vf!hg4!hh5!hi9!hjf!hk7!hp4!hpd!hq9!hr7!hs0&@2$1@2$1@2$3Z^3@2$4^3+i0@2$1@2$3Z^2@2$4^2+hg0>2st$h2>0@1$f^1@2$1@2$1@2$3Z@1$a@1$2^2@2$4@1$a@1$2^2@2$h3+2+i0@2$1@2$1@2$3Z@1$b@1$2^2@2$4@1$b@1$2^2+hg0@2$1>1i$0>1v$0>0@3$9@1$8$0@6$c$0$0@4$d$0$6$5$0@4$e$0$6$5$0^2@1$h0@1$2^4@2$7$0^1~0>1i$0>1v$0>0@3$9@1$8$0@6$c$0$0@4$d$0$6$5$0@4$e$0$6$5$0^2@1$h1@1$2^4@2$7$0^1~0").
Proof. intros st. intros IA. exact (ia_ctx _ IA). Qed.

Lemma INVL_step_seq : ltac2:(zQ "90!hs6!hsd!ih1!ih9!ii0!iia!ij1!hr7!ij9>1X$4>2st$7>1L$2>2BL@1$0$3>2LS>0$6@1$0$5>0@5$1^5^4^3^2^1@5$1^6@1$8^5^4^3^2").
Proof. intros X st L BL LS.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
  - intros i v H. rewrite lookup_empty in H. discriminate.
  - unfold ctx in NE. lia.
Qed.

Lemma INVL_record_seq : ltac2:(zQ "a0!hs6!hsd!h9!ih1!ih9!ii0!iia!ij1!hr7!ik4>1X$5>2st$8>1L$3>2BL@1$0$4>2LS>0$7@1$0$6>2sc$2>0@5$1^6^5^4^3^2@5$1^7@2$9^2^6^5^4^3").
Proof. intros X st L BL LS sc.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C4.
Qed.

Lemma INVL_set_bounce : ltac2:(zQ "d0!hs6!j0!h9!hsd!p4!p9!ih1!ih9!ii0!iia!ij1!hr7!il1>1X$8>2st$b>1L$6>2BL@1$0$7>2LS>0$a@1$0$9>1i$2>1v$2>0@5$3^7^6^5^4^3>0@2$1@2$4Z^3@2$5^3+i0>0@2$1@2$4Z^3@2$5^3+hg0@5$3^a@3$c^5^4^9^8^7^6").
Proof. intros X st L BL LS i v.
  intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  intros j w. destruct (Z.eq_dec j i) as [->|NE].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C3.
Qed.

Lemma bounces_range : ltac2:(zQ "70!ile!j0!h9!hp4!hr7!p4!p9>2st$4>1i$2>0@1$3^2@2$1@2$5Z@2$0^3^2@2$6@2$0^3^2+hg0").
Proof. intros st i.
  intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
  destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.

Lemma INVL_account_bounce : ltac2:(zQ "a0!hs6!hsd!h9!ih1!ih9!ii0!im8!iia!ij1!hr7>1X$5>2st$9>1L$3>2BL@1$0$4>2LS>0$8@1$0$7>2sc$2>0@5$1^6^5^4^3^2@5$1^7@2$6^2^6^5^4^3").
Proof. intros X st L BL LS sc.
  intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (negb _ && _); [| exact INV].
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_decay_bounces : ltac2:(zQ "a0!hs6!hsd!h9!ih1!ih9!ii0!iia!in9!ij1!hr7>1X$5>2st$9>1L$3>2BL@1$0$4>2LS>0$8@1$0$6>2sc$2>0@5$1^6^5^4^3^2@5$1^7@2$7^2^6^5^4^3").
Proof. intros X st L BL LS sc.
  intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
  apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_mmap_counter : ltac2:(zQ "e0!hs6!hsd!ih1!ih9!ii0!iia!hg4!ij1!io9!hr7!ip0!iq4!iqa!ir4>1X$4>2st$9>1L$2>2BL@1$0$3>2LS>0$7@1$0$5>0@5$1^5^4^3^2^1@5$1^6@2$c\1c$8@2$a@1$b@2$d@1$6^1+1^1^5^4^3^2").
Proof. intros X st L BL LS.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rem : ltac2:(zQ "20!iia!hs6>1g$0>1l@1$1$0@1$1$0") := ltac2:(zQ "40!iia!hs6!iv8!jha\1g$0\1l@1$1$0@4$3$0\1x$0\1y$0@2$2^2^1^2^1").
Definition xzomb : ltac2:(zQ "30!ii0!hs6!iia>1X$0>1l@1$1$2$0") := ltac2:(zQ "80!hs6!ii0!ji4!jib!jj6!jk0!jka!iia\1X$1\1l@1$0$7@5$2@1$4^2^1@1$6^2@1$5^2@1$3^2").
Definition xidle : ltac2:(zQ "30!ii0!hs6!iia>1X$0>1l@1$1$2$0") := ltac2:(zQ "80!hs6!ii0!ji4!jib!jk0!jka!jl4!iia\1X$1\1l@1$0$7@5$2^1@1$6^2@1$5^2@1$4^2@1$3^2").

Lemma in_rem : ltac2:(zQ "80!iia!jle!hs6!j0!vf!jm4!jma!jr0>1x$0>1g$0>1l@1$2$0@2$5@3$1$0^3@2$7^2^1@2$3@3$1$0^3^1@1$6@3$4$0^3^2").
Proof. intros x g l. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.
(* [comment removed for export] *)
Lemma rem_notin' : ltac2:(zQ "60!iia!hs6!vf!jma!jr0!jle>1g$0>1l@1$1$0>0@1$3@3$5$0^2^1@3$2@1$1$0@2$4^3^2^2").
Proof. intros g l.
  induction l as [|x l IH]; cbn; [reflexivity|]. intros H.
  unfold rem. cbn. destruct (aptr_eq_dec g x) as [->|NE]; [exfalso; apply H; left; reflexivity|].
  cbn. f_equal. apply IH. tauto.
Qed.
Lemma rem_cons_self : ltac2:(zQ "70!iia!hs6!jr7!vf!jma!jr0!jle>1g$0>1l@1$1$0>0@1$4@3$6$0^2^1@3$3@1$1$0@2$5^3@3$2$0^3^2^2").
Proof. intros g l. intros H. unfold rem. cbn. destruct (aptr_eq_dec g g) as [_|NE]; [| congruence]. apply rem_notin'. exact H. Qed.

(* [comment removed for export] *)
Lemma present_of_mem : ltac2:(zQ "h70!iia!jre!js5!h9!jt9!se!vf!ju3!qf!jv1!kh3!ki2!uf!v6!jma!ki9!kif!hr7!kj7!kje!hi9!hjf!hk7>2st$h1>1m$0>1b$0>0@3$6$h2@1$h0@2$f^3^2@2$c$0^1@1$e@3$6@1$d$1@6$h4$0$1@4$h5$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@4$h6$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1^3@1$h3^4@1$b$1").
Proof. intros st m b. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma present_of_next : ltac2:(zQ "h70!iia!jre!js5!h9!jt9!se!vf!ju3!qf!jv1!kh3!ki2!uf!v6!jma!ki9!kk8!hr7!kj7!kje!hi9!hjf!hk7>2st$h1>1m$0>1x$0>0@3$6$h2@1$h0@2$f^3^2@2$c$0^1@1$e@3$6@1$d$1@6$h4$0$1@4$h5$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@4$h6$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1^3@1$h3^4@1$b$1").
Proof. intros st m x. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.

Lemma gcnt_ext_groups : ltac2:(zQ "h91!h9!iia!kl1!vf!js5!jt9!se!ki9!kl8!ju3!qf!jv1!kh3!uf!km3!kmd!kn5!hr7!hjf!v6!j0!ko3!kj7!hi9!hk7&@4$h2$1@4$c$4$5$0$6@6$b$4$5$9$0$6$a$2>2st$h1>3st'$h1>0@3$3~0@1$8^1@1$8^2>0>1b$1>1h$2>1m$1>0@3$3@1$h3$2@6$h7$1$2~0@4$h8$1@4$c$4$5$0$6@6$b$4$5$9$0$6$a$2^3@1$8^6@2$d$2^2>0@3$3$h6@1$h5^3@2$d$1^2@2$h4@3$3$0@1$h0@2$7^7^3@1$h0@2$7^8^3@3$3$0@1$e@2$7^7^3@1$e@2$7^8^3>2sc$0@3$3$0@2$f^4^1@2$f^5^1").
Proof. intros st st'.
  intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
  destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : ltac2:(zQ "10!hsd@5$0?1X?2st?1L?2BL?2LS").
Hypothesis Hz : ltac2:(zQ "30!jl4!iia!jle@3$2$1?1g@1$0?1X").
(* [comment removed for export] *)
Let X' := xidle (xzomb X (rem g (x_zomb X))) (g :: x_idle X).
Let st' := put_meta g meta0 st.

Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
Lemma uz_R_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.

Theorem INVL_unzombie : INVL X' st' L BL LS.
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
  - apply (inv_R_X X); [reflexivity| reflexivity|]. destruct IR; constructor; try assumption.
  - destruct IA; constructor; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
      intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
      rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
    + intros a ar k Ha Hk Ht. apply KEYS. exact (ia_carved a ar k Ha Hk Ht).
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5 MAL]; constructor.
    + intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
    + intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
      destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
    + intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
      assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
      rewrite (uz_R_other m NE). auto.
    + intros m Hm. cbn in Hm. destruct Hm as [<-|Hm].
      { split; [| exact NIg]. unfold st'. rewrite lookup_metas_put, aptr_eqb_refl. reflexivity. }
      destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
    + intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
      rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
    + intros m Hm. apply KEYS in Hm. cbn [x_idle x_zomb X' xidle xzomb].
      destruct (aptr_eqb_spec m g) as [->|NE]; [right; right; left; left; reflexivity|].
      destruct (MAL m Hm) as [H|[H|[H|H]]]; [left; exact H| right; left; exact H| right; right; left; right; exact H|].
      right; right; right. apply in_rem. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
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
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5 GOE]; constructor; try assumption.
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
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2.
      rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
      rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply GOE; eassumption.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6 SBG]; constructor; try assumption.
    + intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
    + intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
    + intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
      destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
    + intros k m i Hk Hs Hsc. destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb) in Hsc. exact (SBG k m i Hk Hs Hsc).
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
    + intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
    + intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.
(* [comment removed for export] *)
