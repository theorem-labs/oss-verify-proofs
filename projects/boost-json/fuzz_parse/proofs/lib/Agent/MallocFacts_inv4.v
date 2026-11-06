(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Read MI_WFree
  MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WNtf2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_Cnt MI_WTry2 MI_WGroup MI_TF2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Sim MI_Contracts MI_Fuel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_B MallocFacts_AM MallocNat MallocFacts_AS
  MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~k44lmem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~p2alive_group05lhead05strip36Stdlib5Lists4Listub2In37Corelib4Init9Datatypeshg34Some37Corelib4Init5Logichi32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~hjd5hostsp22MR05m_mem04optrhg34Nonehi33not07LActive06m_next0bm_sizeclassk4afact_listsk4dfact_freelistk47fact_mwk4h0fact_host_stridek4afact_linksk4dfact_sc0_fullk4ffact_bit_stridek46LFACTSk4dfact_ghdr_unk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~ike8MFACTS_gk46ISTF_g06region37Corelib7Numbers7BinNumsir11N25stdpp9countableisfbN_countable35stdpp7numbers1Niuf6eq_dechg36optionir11Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AM~~~~~~jh9bfresh_abovep28frontier09s_regions46Stdlib6ZArith6BinInt1Zjo52le25stdpp4basejq36lookup25stdpp4gmapjr94gmapjr9bgmap_lookupjh97AMpre_ghg34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentfMallocFacts_inv~~~~~~juf4CORR06mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~kk75block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~kp54mledp24INVLp23blkp26extras79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WSlot~~~~~~kuf2GPhg34prodhi33andhi32ex69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~lka7hsecretkp57ld_resv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_TF2~~~~~~lpd3TF0kuf4X_as08s_secretjq35NoDup89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0MallocFacts_inv43HCW~~~~~~lvd5JINVikk7bAREACH_fromlvd4JINV06s_tick08set_tick46Stdlib6NArith6BinNat1Nmnd2ltk47ta_fail06activejo52lthg34conshg34pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~ms32bSms32kS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~nh17leaf_ofnh13mem0aalloc_metak43IST37Corelib4Init3Natnn83addhg36lengthhg33natk46req_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WSlot2~~~~~~nqb9SLOT_POST0aalloc_slot08full_layk47nest_oklvdh0nest_facts_proofhg33nilp26x_zombp27x_fresh" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section GF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!kt9@5$0?1X?2st?1L?2BL?2LS").
Hypothesis ZB : ltac2:(zQ "50!je!ju7!oie!hj7!oj5@3$3@1$1$0@1$4?1X@1$2$0").
Hypothesis NFR : ltac2:(zQ "50!je!hpe!jga!hj7!oje@3$3@1$2$0@1$4?1X@1$1$0").

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma lmem_listed : ltac2:(zQ "60!je!ob!t0!td!u4!ve>1m$0>1h$3>0@3$5$0^2@1?2LS^1>0@2$2?2st^3@2$1@1$4?2st^4").
Proof. intros m h.
  intros Hin [b Hb]. unfold lmem. rewrite !get_meta_rec_strip. fold (MR st m).
  split; [rewrite (hosts_mem _ _ _ IM _ _ Hb); discriminate|].
  split; [exact (listed_next _ _ _ _ _ INV m h Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) h m Hin) as (y & _ & E & _). rewrite E. discriminate.
Qed.
(* [comment removed for export] *)
Lemma mem_live : ltac2:(zQ "70!je!hhb!hj7!ho3!hoc!hp1!hp8>1g$0>1b$0>0@3$2$6@1$5@2$4?2st^2@2$1$0^1@3$3?2st^2^3").
Proof. intros g b. intros H. exact (mem_hosts X st L BL LS INV ZB g b H). Qed.

Lemma linked_group_listed : ltac2:(zQ "c0!je!hoc!hj7!hp8!hpe!hhb!hq6!hqd!hp1!hr6!hre!ve>1g$0>1b$0>0@3$2$3@1$8@2$1?2st^2@2$5$0^1>0@1$6@3$2$3@1$9@2$1?2st^3@1$4$0@3$b$0^4@1?2LS@1$7@1$a@2$1?2st^4").
Proof. intros g b.
  intros Hb Hn. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
  destruct h as [sc|].
  - destruct (il_active _ _ IL sc g Hh) as (_ & _ & <-). exact Hh.
  - exfalso. apply (free_not_live _ _ _ _ _ INV g Hh). exists b. exact (mem_live _ _ Hb).
Qed.

Lemma l_lists : ltac2:(zQ "20!hsb!u4@1$0@1$1?2st").
Proof.
  split; [| split].
  - intros sc g H. rewrite active_strip in H. pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
    destruct (il_active _ _ IL sc g Hin) as (_ & Hl & _). exact (lmem_listed _ _ Hin Hl).
  - intros g n Hm Hn. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st n) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Hn; discriminate)) as Hg.
    pose proof (next_listed _ _ _ _ _ INV _ g n Hg Hn) as Hn'.
    destruct (il_active _ _ IL _ n Hn') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hn' Hl)| exact Esc].
  - intros g p Hm Hp. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st p) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    destruct (m_next (MR st g)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL g) Ex) as P; rewrite Hp in P; discriminate].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Ex; discriminate)) as Hg.
    pose proof (prev_listed _ _ _ _ _ INV _ g p Hg Hp) as Hp'.
    destruct (il_active _ _ IL _ p Hp') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hp' Hl)| exact Esc].
Qed.

Lemma l_freelist : ltac2:(zQ "20!ht8!u4@1$0@1$1?2st").
Proof.
  intros h Hh. rewrite ctx_strip in Hh. rewrite !get_meta_rec_strip. fold (MR st h).
  pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
  assert (MS : forall m, In m (LS LFree) -> meta_slot (strip st) m).
  { intros m Hm. ndestruct (listed_meta_slot X st L BL LS INV m LFree Hm) as (a & ar & k & Ha & Hk & E). nexists a, ar, k. auto. }
  split; [exact (MS h Hin)|].
  pose proof (il_free _ _ IL h Hin) as E. split; [rewrite E; reflexivity|].
  split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) LFree h Hin) as (p & Hp & Ep & Np).
  exists p. split; [exact Ep|]. split; [exact (MS p Hp)|]. rewrite !get_meta_rec_strip. fold (MR st p).
  pose proof (il_free _ _ IL p Hp) as Ep'. split; [rewrite Ep'; reflexivity|]. rewrite Np. discriminate.
Qed.
Lemma l_mw : ltac2:(zQ "20!hu8!u4@1$0@1$1?2st").
Proof.
  intros g. rewrite !get_meta_rec_strip. fold (MR st g).
  destruct (m_mem (MR st g)) as [b|] eqn:Hb.
  - destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
    pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
    pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
    assert (AV : m_avail (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
    assert (FR : m_freed (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
    assert (MLB : m_maplen (MR st g) < 2 ^ 52).
    { destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
      destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r & Hr & _ & E & _).
      destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & LT & _). pose proof (round_up_pg_spec (r_len r)). unfold LEN_MAX in LT. lia. }
    split; [| lia]. unfold mw_ok. split; [exact LI|]. split; [rewrite (g_freeable _ _ _ _ _ _ GO); lia|].
    split; [| lia]. destruct (g_sc _ _ _ _ _ _ GO) as [[S1 _]|(S1 & _)]; lia.
  - rewrite (im_zero _ _ _ IM g Hb). cbn. unfold mw_ok. cbn. lia.
Qed.

Lemma l_host_stride : ltac2:(zQ "20!hv2!u4@1$0@1$1?2st").
Proof.
  intros g b Hb Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
  unfold get_stride in *. destruct (m_last_idx (MR st g) =? 0) eqn:E0; [| reflexivity].
  destruct (m_maplen (MR st g) =? 0) eqn:EM; cbn [andb negb] in *; [reflexivity|].
  apply Z.eqb_eq in E0. apply Z.eqb_neq in EM. destruct (S2 E0) as [_ S27].
  assert (Esc : m_sizeclass (MR st g) = 27) by lia. rewrite Esc in *. change (size_class 27) with 255 in *.
  destruct S1 as [S1|S1]; [| lia].
  pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT in *. lia.
Qed.

Lemma l_links : ltac2:(zQ "20!ig6!u4@1$0@1$1?2st").
Proof.
  intros g Hg. unfold lmem in Hg. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. ndestruct Hg as (Hm & Hn & Hp).
  destruct (c_links X st L BL LS INV) as [CN CP _ _].
  split.
  - intros n E. rewrite get_meta_rec_strip. exact (proj1 (CN g n E)).
  - intros p E. rewrite get_meta_rec_strip. exact (proj1 (CP g p E)).
Qed.

Lemma l_sc0_full : ltac2:(zQ "20!ih3!u4@1$0@1$1?2st").
Proof.
  intros g b gh Hb Hgh Hsc. rewrite s_groups_strip in Hgh. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_live _ _ Hb) as Hh. destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai & Hg & GO).
  rewrite Hg in Hgh. inversion Hgh; subst gh. cbn. exact (g_full0 _ _ _ _ _ _ GO Hsc).
Qed.

Lemma l_bit_stride : ltac2:(zQ "20!ii3!u4@1$0@1$1?2st").
Proof.
  intros g b i Hb Hi Hbits Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| exact GE].
  exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 F0].
  rewrite A0, F0, !Z.bits_0 in Hbits. discriminate Hbits.
Qed.

Lemma inv_lfacts : ltac2:(zQ "20!ij5!u4@1$0@1$1?2st").
Proof. constructor; [exact l_lists| exact l_freelist| exact l_mw| exact l_host_stride| exact l_links| exact l_sc0_full| exact l_bit_stride]. Qed.

Lemma inv_ghdr_unk : ltac2:(zQ "10!ije@1$0?2st").
Proof.
  intros b gh o Hb Ho. destruct (hdr_hosts X st L BL LS INV b gh Hb) as [m Hm].
  exact (ish_ghdr _ _ ISH b m o Hm ltac:(lia)).
Qed.

(* [comment removed for export] *)
Variable resv : ltac2:(zQ "30!jh4!ju7!lj5@1$1@2$2$0$0").
Variable LB : ltac2:(zQ "20!ju7!koc@1$0$1").
Hypothesis CR : ltac2:(zQ "10!kj7@3$0?2st?2LB?2BL").
Hypothesis RESV : ltac2:(zQ "50!jh4!ju7!lj5!hj7!lp2@3$3@1$1@2$2$0$0@1$4?1L?4resv").

Local Ltac inst f :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV ZB) | exact (f _ _ _ _ _ INV ZB NFR)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV ZB _ CR) | exact (f _ _ _ _ _ INV ZB NFR _ CR) ].

Lemma inv_mfacts : ltac2:(zQ "10!ip4@3$0?4resv?2st?2LB").
Proof.
  constructor.
  - inst LB_blocks_ok.
  - inst LB_nodup.
  - inst f_ticks.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx.
  - inst f_active.
  - inst f_gmeta.
  - inst f_avail_clear.
  - inst f_hdr0.
  - inst f_free_clear.
  - inst f_hdr_clear.
  - inst f_usage.
  - inst f_masks.
  - inst f_maplen.
  - inst f_slots.
  - inst f_slots_complete.
  - inst f_ptrs.
  - inst f_blk_unknown.
  - inst f_blocks_disjoint.
  - inst f_cell_ticks.
Qed.

Lemma inv_istf : ltac2:(zQ "10!iq0@3$0?4resv?2st?2LB").
Proof. constructor; [exact inv_mfacts| exact inv_lfacts| exact inv_ghdr_unk]. Qed.

(* [comment removed for export] *)
Lemma frontier_fresh : ltac2:(zQ "f0!iq9!isa!iu0!jg0!hhb!jga!hj7!jh4!jm0!jmf!jna!jpd!jqf!js5!jsd>3rid$1>1r$0>1o$7>0@3$6@1$5$0@6$c$1$0@4$d$1$3$2$0@4$e$1$3$2$0^3@1$a?2st@2$4$0^2>0@2$b@3$9?2st^4^3^2@3$8?2st^5^3").
Proof. intros rid r o.
  intros Hr Ho q Hq Hoq. split.
  - exact (proj1 (above_frontier X st L BL LS rid r q INV Hr Hq ltac:(lia))).
  - destruct (s_metas st !! q) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & Em).
    pose proof (proj2 (above_frontier X st L BL LS rid r a INV Hr ltac:(rewrite Em in Hq; exact Hq)
                  ltac:(rewrite Em in Hoq; unfold mslot, aadd in Hoq; cbn in Hoq; unfold AREA_HDR, META_SIZE, NSLOTS in *;
                        destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _);
                        rewrite Em in Hq; unfold mslot, aadd in Hq; cbn in Hq; rewrite Hq, Hr in Hr'; inversion Hr'; subst r'; rewrite Hq in F; unfold PGSZ in F; lia)) k Hk) as N.
    rewrite <- Em, E in N. discriminate N.
Qed.

Hypothesis SEC : ltac2:(zQ "40!hj7!jh4!lo7!lua@3$0$1@1$3?2st@1$2?4HSEC").

Lemma inv_ampre : ltac2:(zQ "10!jtc@3$0?4HSEC?4resv?2st").
Proof.
  pose proof (ia_secret _ IA) as [S0 SD]. pose proof (ia_avail _ IA) as [AC AV]. pose proof (ir_cursor _ _ _ IR) as (C1 & C2 & C3).
  assert (RB : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r < 2 ^ 47).
  { intros rid r Hr. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _). pose proof (round_up_ge (r_len r)). unfold alloc_ceiling in CE. lia. }
  constructor.
  - (* [comment removed for export] *) unfold ctx. destruct SD as [(_ & E & _)|[_ E]]; rewrite E; lia.
  - unfold ctx. destruct SD as [(E & _)|[E _]]; rewrite E; auto.
  - exact SEC.
  - unfold ctx. exact AC.
  - unfold ctx. split; [exact C1|]. destruct (Z.eq_dec (c_avail_meta_area_count (s_ctx st)) 0) as [E|NE]; [rewrite E; lia|].
    destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    ndestruct (C3 rid off eq_refl) as (r & Hr & _ & P1 & _ & E & _). pose proof (RB _ _ Hr). unfold PGSZ in *. nia.
  - unfold ctx. destruct (ir_shift _ _ _ IR) as [SH0 [E|(rid & r & Hr & _ & E)]]; [lia|].
    pose proof (RB _ _ Hr) as [_ LT]. rewrite E in LT. unfold PGSZ in LT. change 4096 with (2 ^ 12) in LT.
    split; [exact SH0|]. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 38) as [|GT]; [assumption|]. exfalso.
    assert (2 ^ 39 <= 2 ^ c_meta_alloc_shift (s_ctx st)) by (apply Z.pow_le_mono_r; lia). nia.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - exact (c_links X st L BL LS INV).
  - intros h Hh. exact (ch_free _ (c_heads X st L BL LS INV) h Hh).
  - intros g Hm Hn. fold (MR st g) in *. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
    destruct h as [sc|].
    { exfalso. destruct (il_active _ _ IL sc g Hh) as (_ & [b Hb] & _). rewrite (hosts_mem _ _ _ IM _ _ Hb) in Hm. discriminate Hm. }
    pose proof (il_free _ _ IL g Hh) as E. split; [rewrite E; reflexivity|]. split.
    + intros nx Hnx. fold (MR st nx). pose proof (il_free _ _ IL nx (next_listed _ _ _ _ _ INV LFree g nx Hh Hnx)) as E'. rewrite E'. reflexivity.
    + intros pv Hpv. fold (MR st pv). pose proof (il_free _ _ IL pv (prev_listed _ _ _ _ _ INV LFree g pv Hh Hpv)) as E'. rewrite E'. reflexivity.
  - intros q mr Hq. destruct (ia_metas _ IA _ _ Hq) as (a & ar & k & Ha & Hk & Em). nexists a, ar, k. auto.
  - unfold ctx. intros NE. ndestruct (AV ltac:(lia)) as (a & Ht & Hav & FR).
    pose proof (ia_tail _ IA a Ht) as Ha. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
    nexists a, ar, (NSLOTS - c_avail_meta_count (s_ctx st)). split; [exact Ea|]. split; [exact Hav|]. split; [lia|]. split; [lia|].
    apply FR. lia.
  - unfold ctx. intros tl Ht. pose proof (ia_tail _ IA tl Ht) as Ha. destruct (s_areas st !! tl) as [ar|]; [eexists; reflexivity| congruence].
  - unfold ctx. intros NE. destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    ndestruct (C3 rid off eq_refl) as (r & Hr & MK & P1 & P2 & E & _).
    exists (rid, off), r. cbn [fst snd]. split; [reflexivity|]. split; [exact Hr|].
    split; [destruct MK as [K|K]; rewrite K; discriminate|]. split; [exact P2|]. split; [unfold PGSZ in P1; lia|].
    split; [unfold lr_lo; destruct (r_kind r); unfold PGSZ in P1; lia|].
    split; [pose proof (round_up_ge (r_len r)); lia|].
    apply (frontier_fresh rid r off Hr). unfold frontier. rewrite EC, N.eqb_refl. lia.
  - intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). exact L0.
  - pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (Malloc.c_brk (s_ctx st)) as [| |rid off]; [exact I| exact I|].
    destruct BR as [_ (r & Hr & K & Elen)]. exists r. split; [exact Hr|]. split; [exact K|]. split; [exact Elen|].
    destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & _ & _ & MK). destruct (MK ltac:(left; exact K)) as [M1 M2].
    split; [rewrite <- Elen; exact M1|]. split; [rewrite <- Elen; unfold PGSZ in *; lia|].
    split; [apply (frontier_fresh rid r off Hr); rewrite (ir_brkfront _ _ _ IR _ _ Hr K); lia|].
    intros q rq Hq Kq. exact (ir_brk1 _ _ _ IR _ _ _ _ Hq Hr Kq K).
  - exact (f_ptrs X st L BL LS INV ZB).
Qed.
End GF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma CORR_GP : ltac2:(zQ "b0!ju7!kj7!kjf!koc!kt1!kt9!ku0!ku6!lif!je!td>1X$7>2st$2>3st'$2>1L$4>2BL@1$0$6>2LS>0$a@1$0$9>2LB@1$0$3>0@5$5^7^6^4^3^2>0@2$8^7^6>0@3$1^8^3^5@3$1^8^4^6").
Proof. intros X st st' L BL LS LB.
  intros INV [GPR _] CR. eapply Forall2_impl_in; [exact CR|]. (intros b k Hb Hk nd_i1; ndestruct nd_i1 as (C1 & C2 & C3)).
  split; [exact C1|]. split; [exact C2|]. rewrite C3. rewrite (conc_same st st' (bslot k)); [reflexivity|].
  destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

(* [comment removed for export] *)
Definition JINVi : ltac2:(zQ "60!ju7!jh4!lj5!koc!je!kjf>4resv@1$0@2$2$1$1>4idle@1$0$4>2st$5>2LB@1$0$3P") := ltac2:(zQ "h40!ju7!ljd!jh4!je!lk4!lj5!hj7!kt1!ku0!td!koc!kj7!lo7!lp2!kt9!ltb!lu2!kjf!lua!lv4\4resv@1$0@2$5$2$2\4idle@1$0$3\2st$h1\2LB@1$0$a@2$4$7\1L$7@2$4>0$9@1$0$3\2LS>0$9@1$0$3@2$4@1$0$8\2BL@1$0$8@2$1@5$e@1$h0^6^5^3^1^2@2$1@2$h3$3^6@2$1@1$f^5@2$1@3$6@1$0@2$5$2$2@1$d^3^7@2$1@3$6$2@1$h2^5@1$c?4HSEC@3$b^5^4^1").
Definition JINV : ltac2:(zQ "50!ju7!jh4!lj5!koc!kjf>4resv@1$0@2$2$1$1>2st$4>2LB@1$0$3P") := ltac2:(zQ "80!ju7!jh4!je!lj5!lk4!koc!mkb!kjf\4resv@1$0@2$3$1$1\2st$7\2LB@1$0$5@2$4@1$0$2\4idle@1$0$2@4$6^4^1^3^2").

Lemma jinv_top : ltac2:(zQ "b0!ju7!jh4!lj5!isa!ml4!koc!mm3!kjf!mmb!mn3!mp5>4resv@1$0@2$2$1$1>3st0$7>2LB@1$0$5>1t$3>0@4$4?4HSEC^4^3^2>0@2$a@1$8^4^2@3$6^6@2$9^3^5^4").
Proof. intros resv st0 LB t.
  intros AR Ht. ndestruct (areach_inv resv st0 LB AR) as (L & LS & BL & INV & _ & RESV & SEC & CR).
  nexists [], L, LS, BL. split; [apply INVL_set_tick; [lia| exact INV]|].
  split; [apply NoDup_nil; exact I|| constructor|]. split; [apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| exact Ht]|].
  split; [exact RESV|]. split; [exact SEC|]. exact CR.
Qed.

(* [comment removed for export] *)
Lemma jinv_ta : ltac2:(zQ "f0!ju7!jh4!ljd!mkb!je!kjf!hpe!lj5!hj7!koc!mpb!mq5!hp8!jpd!mqd>4resv@1$0@2$7$1$1>4idle@1$0$4>2st$5>2LB@1$0$9>2sc$1>3st1$5>0@4$3^6^5^4^3>0@2$2@2$dZ^3@2$e^3+j0>0@3$a^4^6^3@2$2@4$3^9^8^4^6@3$8$c@2$b^4^5@1$6$4").
Proof. intros resv idle st LB sc st1.
  (intros nd_i2 Hsc TA; ndestruct nd_i2 as (L & LS & BL & INV & ND & TF & RESV & SEC & CR)).
  ndestruct (try_avail_ok (option (mstate * Z)) (X_as idle) L BL sc kS bS eq_refl eq_refl Hsc st LS INV) as (st1' & first & LS1 & E & TAF & RES).
  unfold ta_fail in TA. rewrite E in TA. unfold kS in TA. inversion TA. subst st1' first.
  destruct RES as [(_ & HA & INV1)|(g & bg & ai & idx & NZ & _)]; [| exfalso; exact (NZ eq_refl)].
  split; [| exact HA]. nexists L, LS1, BL. split; [exact INV1|]. split; [exact ND|].
  split; [exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF)|]. split; [exact RESV|].
  split; [rewrite (taf_ssec _ _ _ TAF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_taf _ _ _ TAF) CR).
Qed.

(* [comment removed for export] *)
Lemma jinv_am : ltac2:(zQ "h10!kjf!je!lj5!jga!hp8!ju7!hhb!jh4!mkb!mr3!mrb!koc!ng5!ngb!nl4!nlf!nm6>4resv@1$5@2$2$7$7>4idle@1$5$1>3st1$0>2LB@1$5$b>1o$f>3st2$0>1m$1>0@4$8^7^6^5^4>0@4$e@1$3@2$2$0$4^4@4$h0@1$3@2$2$0$4^6@2$d$0$4@1$c@2$2$0$4@2$6@2$2$0@1$3$1@4$a$0@1$3$1^3@2$6$1^2@4$8^9@3$9$1^3^8^4^6").
Proof. intros resv idle st1 LB o st2 m.
  (intros nd_i3 nd_i4; ndestruct nd_i3 as (L & LS & BL & INV & ND & TF & RESV & SEC & CR); ndestruct nd_i4 as (ans & o' & FL)).
  set (Post := fun (L' : mled) (r : option (mstate * optr)) =>
     match r with
     | Some (s2, Some m') => exists LS', INVL (X_as (m' :: idle)) s2 L' BL LS' /\ ~ In m' idle /\ AM_frame st1 s2 /\ L_frame L L'
     | _ => True
     end).
  assert (FT : ftree L (alloc_meta st1 kS bS) Post).
  { apply (alloc_meta_ft _ BL Post kS bS (X_as idle) st1 L (length idle)) with (LS := LS); [reflexivity| cbn; lia| reflexivity| reflexivity| | | exact INV| apply amf_refl| apply lf_refl| apply AREAS_refl].
    - intros s1 L1 LS1 _ _ _ _. exact I.
    - intros s1 L1 LS1 m' INV1 NI AF LF _. cbn. exists LS1. split; [exact INV1|]. split; [exact NI|]. split; [exact AF| exact LF]. }
  pose proof (ftree_prun pans_mem pupd_mem pans_mem_range (alloc_meta st1 kS bS) L Post o FT) as PT.
  unfold mrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L' & CP & POST). cbn in POST.
  ndestruct POST as (LS' & INV2 & NI & AF & LF).
  nexists L', LS', BL. split; [exact INV2|].
  split; [apply NoDup_cons; split; [intros Hin; apply NI; apply list_elem_of_In; exact Hin| exact ND]|].
  split; [exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF)|].
  split; [rewrite (lf_resv _ _ LF); exact RESV|].
  split; [rewrite (amf_ssec _ _ AF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_amf _ _ AF) CR).
Qed.

Lemma ist_jinv : ltac2:(zQ "80!ju7!jh4!kjf!lj5!ml4!koc!nn2!mm3>4resv@1$0@2$3$1$1>3st0$2>2LB@1$0$5>2st$2>0@4$4?4HSEC^4^3^2>0@2$6^4^2@3$7^6^3^4").
Proof. intros resv st0 LB st.
  intros AR. induction 1 as [t Ht|o st sc st1 st2 m _ IH Hsc TA AM].
  - exact (jinv_top resv st0 LB t AR Ht).
  - destruct IH as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. exists (m :: idle). exact (jinv_am _ _ _ _ _ _ _ J1 AM).
Qed.

(* [comment removed for export] *)
Lemma jinv_slot : ltac2:(zQ "i30!jh4!ju7!kjf!lj5!je!ljd!lk4!kt1!td!jga!hj7!noa!ku0!hhb!np1!npb!mrb!koc!nq2!kj7!mkb!ng5!ngb!nl4!nlf!lo7!lp2!kt9!lu2!nuc!nv9!og5!lua!jpd!mqd>4resv@1$1@2$3$0$0>4idle@1$1$4>2st$2>2LB@1$1$h1>1o$h8>1f$f>2sc$0>3req$0>3st3$2>3idx$0>0@4$h4^a^9^8^7>0@2$5@2$i1Z^5@2$i2^5+j0>0@2$h2^6^5>0@4$h7@1$9@2$3$2$0^9@8$he@1$9@2$3$2$0$hf^8^b^7^6@2$h6$2$0@1$h5@2$3$2$0@2$d@2$3$2$0@4$h0$2$0^5^4@2$6$7\1L$7@2$6>0$8@1$1$4\2LS>0$8@1$1$4@2$6@1$1$c\2BL@1$1$c@2$6$7\2L3$7@2$6>0$8@1$1$4\3LS3>0$8@1$1$4@2$5@5$hb@1$hc^h2^h1^5^3^4@2$5@b$hd@2$b@2$e$4^h2@2$b^eNj1^h2^d^c^h1^5^3^b^a^2^1@2$5@3$a@1$1@2$3$0$0@1$ha^2^h3@2$5@3$a$0@1$i0^b@1$h9?4HSEC@3$h3^b^h0^3").
Proof. intros resv idle st LB o f sc req st3 idx.
  (intros nd_i5 Hsc [Hreq Hfit] nd_i6; ndestruct nd_i5 as (L & LS & BL & INV & ND & TF & RESV & SEC & CR); ndestruct nd_i6 as (ans & o' & FL)).
  unfold mrun in FL. apply (@alloc_slot_follow_mono _ pans_mem pupd_mem full_lay f (f + 49)) in FL; [| lia].
  set (Post := fun (L' : mled) (r : option (mstate * Z)) =>
     match r with Some (s3, i) => exists LS3, SLOT_POST (length idle + (f + 49))%nat idle sc req st L BL s3 i L' LS3 | None => True end).
  assert (FT : ftree L (alloc_slot full_lay (f + 49) st sc req kS bS) Post).
  { apply (alloc_slot_ft _ Post (f + 49)%nat (length idle + (f + 49))%nat sc idle st L BL LS req kS bS ltac:(lia) INV TF ND ltac:(lia) Hsc Hreq Hfit).
    intros st1 i L1 LS1 SP. cbn. exists LS1. exact SP. }
  pose proof (ftree_prun pans_mem pupd_mem pans_mem_range _ L Post o FT) as PT.
  destruct (ptree_follow _ L _ ans PT FL) as (L3 & CP & POST). cbn in POST. destruct POST as [LS3 SP].
  nexists L, LS, BL, L3, LS3. split; [exact INV|]. split; [exact SP|].
  split; [rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  ndestruct SP as (_ & _ & GP3 & _). split; [rewrite (proj2 GP3); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV GP3 CR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ist_facts_proof : forall {resv} st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB.
Proof.
  intros resv st0 LB st AR H. ndestruct (ist_jinv resv st0 LB st AR H) as (idle & L & LS & BL & INV & ND & TF & RESV & SEC & CR).
  exact (inv_istf (X_as idle) st L BL LS INV eq_refl eq_refl resv LB CR RESV).
Qed.

Theorem istr_facts_proof : forall {resv} st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB.
Proof.
  (intros resv st0 LB st3 AR nd_i7; ndestruct nd_i7 as (o & st & f & sc & req & idx & H & Hsc & RQ & LF)).
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  ndestruct (jinv_slot resv idle st LB o f sc req st3 idx J Hsc RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & RESV & SEC & CR).
  ndestruct SP as (_ & _ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (inv_istf (X_as idle) st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
  - exact (inv_istf _ st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
Qed.

Theorem nest_facts_proof : forall {resv} st0 LB st sc st1 o st2 m f j req o' st3 idx,
  AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
  leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
  0 <= j < 48 -> req_ok j req ->
  leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
  nest_ok m st3.
Proof.
  intros resv st0 LB st sc st1 o st2 m f j req o' st3 idx AR H Hsc TA AM Hj RQ LF.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. pose proof (jinv_am _ _ _ _ _ _ _ J1 AM) as J2.
  ndestruct (jinv_slot resv (m :: idle) st2 LB o' f j req st3 idx J2 Hj RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & _).
  assert (K : forall X3, INVL X3 st3 L3 BL LS3 -> x_idle X3 = m :: idle -> nest_ok m st3).
  { intros X3 INV3 XI. destruct (im_idle _ _ _ (proj1 (proj2 (proj2 INV3))) m ltac:(rewrite XI; left; reflexivity)) as [Em NI].
    split; [unfold get_meta_rec; rewrite Em; reflexivity|].
    intros h Hh. pose proof (head_listed _ _ _ _ _ INV3 LFree h Hh) as Hin. split.
    - intros ->. apply NI. exists LFree. exact Hin.
    - intros Hp. apply NI. exists LFree. exact (prev_listed _ _ _ _ _ INV3 LFree h m Hin Hp). }
  ndestruct SP as (_ & _ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (K _ INV3 eq_refl).
  - exact (K _ INV3 eq_refl).
Qed.

Theorem areach_ampre_proof : forall {resv} st LB, AREACH_from resv st LB -> @AMpre_g _ resv st.
Proof.
  intros resv st LB AR. ndestruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & RESV & SEC & _).
  exact (inv_ampre x0 st L BL LS INV eq_refl resv RESV SEC).
Qed.

Theorem ist_ampre_proof : forall {resv}, AMP_AS_g resv (am_pre_g resv).
Proof.
  intros resv st0 LB st sc st1 AR H Hsc TA.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [(L & LS & BL & INV & _ & _ & RESV & SEC & _) _].
  exact (inv_ampre (X_as idle) st1 L BL LS INV eq_refl resv RESV SEC).
Qed.


(* [comment removed for export] *)
Local Definition g3 : ltac2:(zQ "ha0!kjf!jh4!lj5!jga!je!hp8!hhb!ju7!mrb!ljd!ng5!ngb!nl4!nlf!jpd!mqd!npb!ml4!koc!nn2!ogf!nq2!mpb!nm6!nv9!og5>4resv@1$7@2$2$1$1>3st0$0>2LB@1$7$h2>2st$0>2sc$1>3st1$0>1o$d>3st2$0>1m$4>1f$h0>1j$1>3req$1>2o'$d>3st3$0>3idx$1>0@4$h1?4HSEC^f^e^d>0@2$h3^f^d>0@2$9@2$eZ^d@2$f^d+j0>0@3$h6^e^f^d>0@4$c@1$3@2$2$0$5^d@4$h7@1$3@2$2$0$5^e@2$b$0$5@1$a@2$2$0$5@2$6@2$2$0@1$3$4@4$8$0@1$3$4^c@2$6$4^b>0@2$9@2$eZ^a@2$f^a+j0>0@2$h5^b^a>0@4$c@1$3@2$2$0$1^a@8$h8@1$3@2$2$0$1$h9^d^f^c^b@2$b$0$1@1$a@2$2$0$1@2$6@2$2$0$1@4$8$0$1^9^8@2$h4^f^a") := ltac2:(zQ "10!oh9$0").

End HCW.

(* [comment removed for export] *)
