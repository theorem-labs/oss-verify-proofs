(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_WFree
  MI_Pres4 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_inv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc2le37Corelib4Init9Datatypesj96lengthj94list37Corelib4Init5Logicm13and36Stdlib5Lists4Listnb2Innb5NoDuphc2lthc6of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~q94zsumhc3mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~v44aptrj94Somem12eqq92MRq95hostsv45m_memv44optrv44ghdr01N35stdpp7numbers1Nhmb6eq_dec35stdpp7numbers1Zho66eq_dec25stdpp9countablehq1bN_countablehq1bZ_countablehq1eprod_countable25stdpp9decidablehu2bprod_eq_decj96optionm12exq98group_okv46mkGhdrv48s_groups25stdpp4baseiif6lookup25stdpp4gmapik54gmapik5bgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~im89sstart_ofq96sstartv44metav46regionj93fstj93sndq94gendv47RKGroupv46r_kindv45r_lenv45rkindv4bround_up_pgv49s_regionsv44concv46r_basehc3addim88fact_ctxv45stripim8bfact_activeim8afact_masksim8bfact_maplenim8afact_slotsim8h3fact_slots_completeim8ffact_cell_ticksim8afact_gmetaj94prodj94boolj94pairj94truehc7testbitj94Nonem13notm12or37Corelib5Lists7ListDefjv93mapq93blkq95bslotv44cptrv47m_availv47m_freedv4am_last_idx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~kkd5blockkkd8blk_addrkkd8blk_sizekkd8blk_slotv44UNITv42IBv4aget_stridehc3subim8ffact_free_clearim8h0fact_avail_clearim8efact_hdr_clearim8h0fact_blk_unknownim8h4fact_blocks_disjointjv96Forallim88block_okv4as_next_rid46Stdlib6NArith6BinNat1Nlm92ltv44areav47s_areasv47s_metasv45meta0v45lheadv4dalloc_ceiling25stdpp8fin_mapsls2bmap_to_listik59gmap_foldq94gcnthc3powim8afact_usageq94INVLj93nilq96x_zombq97x_fresh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentfMallocFacts_inv~~~~~~mi94CORR" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros Hinj ND; cbn; [constructor|].
  inversion ND; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. ndestruct Hin as (y & Ey & Hy).
    rewrite (Hinj a y ltac:(now left) ltac:(now right) (eq_sym Ey)) in H1. exact (H1 Hy).
  - apply IH; [| assumption]. intros x y Hx Hy. apply Hinj; now right.
Qed.

Lemma NoDup_Z_length : ltac2:(zQ "90!h9!j4!l1!la!n5!oe!p3!pb!q0>1l@1$3$0>1N$0>0@2$1Z^1>0@2$6$0^3>0>1x$0>0@3$5$0^1^5@2$4@2$1Z^2@2$7^2^5@2$1@1$8@2$2$0^5^4").
Proof. intros l N.
  intros Hn ND HB.
  assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
  { intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (HB x Hx). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length ND INCL) as Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

Lemma zsum_bound : ltac2:(zQ "90!h9!j4!n5!u7!l1!la!oe!ue!q0>1l@1$5$0>1K$0>0>1x$0>0@3$6$0^1^3@2$2@2$1Z^2@2$1^2^3@2$2@2$1Z@1$3^3@2$1@1$3^3@2$7^2@1$8@2$4$0^3").
Proof. intros l K.
  induction l as [|a l IH]; intros HB; cbn -[Z.of_nat]; [lia|].
  pose proof (HB a ltac:(now left)). specialize (IH ltac:(intros x Hx; apply HB; now right)).
  unfold zsum in IH. rewrite Nat2Z.inj_succ. lia.
Qed.

Section MF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!mg9@5$0?1X?2st?1L?2BL?2LS").
Hypothesis ZB : ltac2:(zQ "50!hj2!la!mh0!hk0!mh6@3$3@1$1$0@1$4?1X@1$2$0").
Hypothesis NFR : ltac2:(zQ "50!hj2!ju7!ig2!hk0!mhf@3$3@1$2$0@1$4?1X@1$1$0").

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma mem_hosts : ltac2:(zQ "70!hj2!hj9!hk0!hk5!hka!hl2!hla>1g$0>1b$0>0@3$2$6@1$5@2$3?2st^2@2$1$0^1@3$4?2st^2^3").
Proof. intros g b. intros H. destruct (im_group _ _ _ IM g b H) as [Hh|Hz]; [exact Hh|]. rewrite ZB in Hz. destruct Hz. Qed.

Lemma hosts_GO : ltac2:(zQ "h60!h9!hj2!hm1!hm8!hnc!hp7!hj9!hr2!hs1!ht0!hv3!ig2!n5!hk0!igb!ih0!hka!ihb!ii4!ijb!il1!il9>1b$1>1g$1>0@3$h0?2st^2^1@2$e$0\2ai$0@2$c@3$d@1$b$2@6$h3$1$2@4$h4$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2@4$h5$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2^4@1$h2?2st@2$6$2@2$h1@2$6$1^3^1@6$f?1X?2st?2LS^3^4^1").
Proof. intros b g. intros H. exact (hosts_ok _ _ _ IG _ _ H). Qed.

Lemma sstart_of_eq : ltac2:(zQ "50!h9!hk0!iqe!irb!is4>1r$4>1i$0@3$1$0@2$2^2^1@2$3^2^1").
Proof. intros r i. reflexivity. Qed.

(* [comment removed for export] *)
Lemma group_in_region : ltac2:(zQ "ha0!isb!hm8!n5!hk0!h9!hj2!j4!hr2!hnc!hj9!it4!ig2!ita!igb!hk5!iu0!hka!iu7!iv1!iva!jg2!jga!jh8!ijb!il1!il9>1b$5>1m$5>0@3$h0?2st^2^1@2$d$0\1r$0@2$2@3$3@1$b$0@6$h7$1$0@4$h8$1$8$7$0@4$h9$1$8$7$0@3$a$1$4^4@1$h6?2st@2$9$0^1@2$2@3$3$h4@1$h2^1$h1@2$2@2$6Z@3$c$1$4^4@2$6@1$f@2$e?2st^3@1$h5@1$h3^1").
Proof. intros b m.
  intros Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ].
  - destruct (top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & i & c & bt & Ha & Ht & Htl & Hf).
    destruct (anc_box _ _ _ _ IM IG IS m t i c b Ha Hm) as (B1 & B2 & B3).
    destruct (anc_facts _ _ _ _ IM IG IS m t i c Ha) as (bm & bp & Hm' & Hp' & _ & Hi & _).
    pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hp'); subst bp.
    destruct (hosts_GO _ _ Ht) as (ait & Hbt & GOt).
    destruct (g_top _ _ _ _ _ _ GOt Htl) as (S0 & r & Hr & Kr & ML & GE).
    rewrite <- Hf. exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|].
    pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st t) + 1) Ht ltac:(lia)) as SM. rewrite <- gend_eq in SM. lia.
  - destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE). exists r. repeat split; auto. lia.
Qed.

Lemma conc_group : ltac2:(zQ "hb0!isb!hm8!n5!hk0!h9!ji4!jib!jj4!hj2!j4!hr2!hnc!hj9!it4!ig2!ita!igb!hka!iu7!iv1!iva!jg2!jga!jh8!ijb!il1!il9>1b$8>1m$8>0@3$h1?2st^2^1@2$h0$0\1r$0@2$2@3$3@1$e$0@6$h8$1$0@4$h9$1$b$a$0@4$ha$1$b$a$0@3$d$1$4^4@1$h7?2st@2$c$0^1@2$2@3$3$h5@1$h3^1$h2@2$2@3$3$4@2$5?2st^4@2$7@1$6^1@3$f$1$4^4@2$2@2$9@1$6^1@2$5?2st^4@2$9@2$7@2$5?2st^4+i0@2$7@1$6^1@1$h6@1$h4^1").
Proof. intros b m.
  intros Hm. destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). pose proof (gend_ge _ _ _ IM IG _ _ Hm) as G32.
  exists r. unfold conc, get_region. rewrite Hr. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma f_ctx : ltac2:(zQ "20!jja!jk6@1$0@1$1?2st").
Proof.
  pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
  unfold fact_ctx. rewrite ctx_strip. unfold ctx.
  split; [exact C1|]. split; [destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia|].
  split; [destruct S2 as [(E & _)|[E _]]; rewrite E; auto|]. split; [exact C2|].
  split.
  - intros i. unfold bounces, ctx. cbn. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)).
  - intros i. unfold unmap_seq, ctx. cbn. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)).
Qed.

Lemma f_active : ltac2:(zQ "20!jke!jk6@1$0@1$1?2st").
Proof.
  intros sc g H. rewrite active_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
  destruct (il_active _ _ IL sc g Hin) as (Hsc & [b Hb] & Esc). split; [exact Hsc|]. split; [exact Esc|].
  rewrite (hosts_mem _ _ _ IM _ _ Hb). discriminate.
Qed.

Lemma f_masks : ltac2:(zQ "20!jld!jk6@1$0@1$1?2st").
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  destruct (hosts_GO _ _ (mem_hosts _ _ H)) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  split; [intros i Hi Ha; pose proof (M3 i Hi Ha); lia|]. split; [exact M4|].
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.testbit (m_avail (MR st g)) i) eqn:Ea; destruct (Z.testbit (m_freed (MR st g)) i) eqn:Ef; try reflexivity.
  exfalso. exact (M5 i Hi Ea Ef).
Qed.

Lemma f_maplen : ltac2:(zQ "20!jmb!jk6@1$0@1$1?2st").
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
  destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE).
  destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). unfold alloc_ceiling in CEIL. lia.
Qed.

Lemma f_slots : ltac2:(zQ "20!jna!jk6@1$0@1$1?2st").
Proof.
  intros p g idx H. rewrite s_slots_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  destruct (is_valid _ _ _ IS _ _ _ H) as ([b Hb] & Hi & Ep). exists b. split; [exact (hosts_mem _ _ _ IM _ _ Hb)|].
  rewrite (slot_start'_eq _ _ _ IM _ _ idx Hb) in Ep. rewrite Ep. cbn. rewrite sstart_of_eq. auto.
Qed.

Lemma f_slots_complete : ltac2:(zQ "20!jo8!jk6@1$0@1$1?2st").
Proof.
  intros g b i H Hi. rewrite s_slots_strip. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. rewrite sstart_of_eq, <- (slot_start'_eq _ _ _ IM _ _ i Hm). exact (is_total _ _ _ IS _ _ _ Hm Hi).
Qed.

Lemma f_hdr0 : fact_hdr0 st.
Proof.
  intros g b i H Hi. fold (MR st g) in *. rewrite sstart_of_eq. exact (ish_hdr0 _ _ ISH b g i (mem_hosts _ _ H) ltac:(unfold cnt_of; lia)).
Qed.

Lemma f_cell_ticks : ltac2:(zQ "10!jq0@1$0?2st").
Proof. intros rid sh o v t Hs Hc. exact (proj2 (proj1 (ish_ticks _ _ ISH rid sh Hs) o v t Hc)). Qed.

Lemma f_ticks : ticks_ok st.
Proof.
  split.
  - intros rid sh u hl ch Hs Hu Hin. exact (proj1 (proj2 (ish_ticks _ _ ISH rid sh Hs)) u hl ch Hu Hin).
  - intros rid sh pg t Hs Hp. exact (proj2 (proj2 (ish_ticks _ _ ISH rid sh Hs)) pg t Hp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma f_gmeta : ltac2:(zQ "20!jr3!jk6@1$0@1$1?2st").
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  assert (AV : m_avail (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
  assert (FR : m_freed (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
  split.
  { (* [comment removed for export] *) pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
    destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). nexists a, ar, ka. rewrite s_areas_strip. split; [exact Ha|]. split; [exact Hka|]. exact Emk. }
  split; [lia|]. split; [lia|]. split; [exact LI|]. split; [exact (g_freeable _ _ _ _ _ _ GO)|].
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
  split. { destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia]. }
  split; [exact ML|].
  split. { exists ai. rewrite s_groups_strip. split; [exact Hb|]. split; [exact AI|]. exact M3. }
  split. { destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). exists r. rewrite s_regions_strip.
           pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|]. rewrite sstart_of_eq. rewrite gend_eq in GE. exact GE. }
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
  split; [exact SG|]. split; [exact SM|].
  pose proof (g_stride _ _ _ _ _ _ GO) as GS.
  split. { intros Hsc. ndestruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. nia. }
  split. { intros Hsc i Hi Ht. destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| lia].
           exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 _]. rewrite A0 in Ht. rewrite Z.bits_0 in Ht. discriminate. }
  intros Hsc. ndestruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. lia.
Qed.

(* [comment removed for export] *)
Lemma bit_slot_nonH : ltac2:(zQ "i73!h9!hm8!hm1!hnc!hp7!hj2!hk5!js1!hk0!hr2!hs1!ht0!hv3!hj9!js8!it4!ig2!jsf!jt6!n5!irb!ii4!j4!jtd!ijb!il1!il9!ju7!jue!jv4!kh0!kh7!khd!ki5!kic!kj6!kk0!ihb!oe&@4$h9$5@4$c$1$3$0$4@6$b$1$3$9$0$4$a$2&@4$ha$5@4$c$1$3$0$4@6$b$1$3$9$0$4$a$2&@4$h1$1$0@3$f$1$0^6@2$h4@2$6?2st^7^4>1g$5>1b@2$7$1$0>2ai$0>1i$0>0@3$8@1$h0$2@6$h8@2$7$1$0$2~0~1^3@1$h5?2st@2$d$2@2$i5@2$d$5^4^2>0@2$h3@2$h6Z^2@2$h6^2@1$i4@2$6?2st^5>0@2$hd@3$8$e@2$h7@1$i2@2$6?2st^6^3$h2@3$8$e@2$h7@1$i3@2$6?2st^6^3$h2@2$h3@3$8@1$h0$2@6$h8@2$7$1$0$2~0~1~2@1$h5?2st@1$hb$2@1$hc@3$i6@2$7$1$0~2@4$he$hf$i1$i0?2BL").
Proof. intros g b ai i.
  intros Hb Hil Hbits. assert (Hm : hosts st b g) by (exists ai; exact Hb).
  pose proof (is_part _ _ _ IS b g ai i Hb Hil) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm) in P.
  unfold one5, tbit in P. ndestruct P as (_ & nAB & nAC & nAD & _ & nBC & nBD & _).
  split.
  - destruct (s_groups st !! (fst b, sstart (MR st g) i)) eqn:E; [| reflexivity]. exfalso.
    destruct Hbits as [A|F]; [apply nAD| apply nBD]; split; auto; intros Y; rewrite Y in E; discriminate E.
  - intros C. destruct Hbits as [A|F]; [apply nAC| apply nBC]; split; auto.
Qed.

Lemma hdr_hosts : ltac2:(zQ "h30!hj2!hm1!hm8!h9!hnc!hp7!hr2!hs1!ht0!hv3!hj9!ig2!hk0!igb!hka!ii4!ijb!il1!il9>1b$0>2gh$1>0@3$c@1$b$1@6$h0$0$1@4$h1$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1@4$h2$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1^2@1$f?2st@2$a$1^1@2$d$0\1m$0@3$e?2st^4^1").
Proof. intros b gh.
  intros Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _). exists m. destruct gh as [gm gai]; cbn in Eg; subst gm. exists gai. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable LB : ltac2:(zQ "20!la!kp2@1$0$1").
Hypothesis CR : ltac2:(zQ "10!mn1@3$0?2st?2LB?2BL").

Lemma LB_blk : ltac2:(zQ "h00!h9!ki5!js1!n5!hk0!igb!jsf!kp2!oe!kpb!kq7!kr3!krf!ji4!jj4!ue>3blk$7>0@3$8$7^1?2LB@2$5$1\1c$1@2$5$0\3off$0@2$5$0\1n$0@2$3@3$8@2$2@2$2$1$0$0@4$6@2$2$1$0$0@4$6$1$0^3^2^1?2BL@2$3@3$4$1@1$b^5^3@2$3@3$4$0@1$a^5^1@3$4$0@1$9^5@2$e@2$d?2st^3@2$f$c^2").
Proof. intros blk.
  intros Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)). destruct k as [[c off] n].
  nexists c, off, n. cbn [bslot boff bsize fst snd] in C1, C2, C3. auto.
Qed.

(* [comment removed for export] *)
Lemma LB_geo : ltac2:(zQ "ie0!h9!n5!hm8!ki5!hk0!igb!isb!hj2!hnc!hm1!j4!hk5!hr2!hp7!jsf!js1!jj4!it4!ig2!kp2!irb!krf!oe!ue!ijb!hs1!ht0!hv3!il1!il9!ju7!hj9!kpb!kq7!kr3!hka!ks6!iu7!ksb!kk0!jib!iv1!jg2!ii4!jh8!kt8>3blk$h3>0@3$h6$h3^1?2LB@2$5$3\1c$3@2$5$0\3off$0@2$5$0\1n$0@2$5$7\1m$7@2$5$7\2bm$7@2$5$0\1i$0@2$5$6\1r$6@2$1@3$h6@2$f@2$f$3$0$0@4$e@2$f$3$0$0@4$e$3$0^7^6^5?2BL@2$1@3$4$3@1$i2^9^7@2$1@3$4$0@1$i1^9^5@2$1@3$i3?2st^3^4@2$1@2$1@2$aZ^2@2$a^2@1$i7@2$b?2st^4@2$1@3$4$3^7@4$e$2$0@3$h1$2$0^3@2$h4@2$b?2st^4^2@2$1@3$4@1$h2$9@6$h8$3$9@4$hc$7@4$hb$2$8$0$d@6$ha$2$8$c$0$d$h9$9@4$hd$7@4$hb$2$8$0$d@6$ha$2$8$c$0$d$h9$9^7@1$ib?2st@1$he$9@2$1@3$4@1$h2$6@6$h8$2$6@4$hc$2$8$c$6@4$hd$2$8$c$6@3$h1$2$0^3@1$ic?2st@2$hf$6^1@2$1@3$4$ia@1$i9^1$i5@2$1@3$4$0@1$i0^9@2$h0@2$h0@1$i8^1@2$h4@2$b?2st^4^2@2$h7$h5^6@2$1@2$aZ^6@2$1@2$aZ^5@2$a@2$h0@2$h7$h5^6^5@2$id@1$i6@2$b?2st^4$i4").
Proof. intros blk.
  intros Hb. destruct (LB_blk _ Hb) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh. assert (Hm : hosts st bm m) by (exists ai; exact Hh).
  destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr).
  nexists c, off, n, m, bm, i, r.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hf.
  repeat split; auto; try lia.
  rewrite C3, Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. lia.
Qed.

Lemma f_free_clear : ltac2:(zQ "20!kte!jk6@2$0@1$1?2st?2LB").
Proof.
  change (fact_free_clear st LB). intros g b i H Hi Hbits. fold (MR st g) in *. cbn zeta. rewrite !sstart_of_eq.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hil : 0 <= i <= m_last_idx (MR st g)). { destruct Hbits as [A|F]; [pose proof (M3 i Hi A); lia | pose proof (M4 i Hi F); lia]. }
  destruct (bit_slot_nonH _ _ _ _ Hb Hil Hbits) as [NH NB].
  pose proof (sstart_succ st g i) as SS.
  split.
  - intros b' gh Hb' Hf. destruct (hdr_hosts _ _ Hb') as [m' Hm'].
    destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hm Hil NH m' b' Hm' Hf) as [A|A]; unfold IB; lia.
  - intros blk Hblk Hf. destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr & Kr & Ea & Ho & Hn & Fit).
    rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr. exists r. split; [reflexivity|].
    rewrite Ea, C2. pose proof (sstart_succ st m2 i2) as SS2.
    assert (NE : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NB. rewrite <- Hf, <- Ec, <- C1.
      destruct (Forall2_In_l _ _ _ _ CR Hblk) as (k & HkB & (Ek & _)). rewrite Ek. apply in_map. exact HkB. }
    destruct (sep_ext _ _ _ _ IM IG IS g b i Hm Hil NH m2 b2 i2 Hm2 Hf Hi2 NE ltac:(rewrite Ec in NH2; exact NH2)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma f_avail_clear : ltac2:(zQ "20!kv1!jk6@2$0@1$1?2st?2LB").
Proof. intros g b i H Hi Ha. exact (f_free_clear g b i H Hi (or_introl Ha)). Qed.

Lemma f_hdr_clear : ltac2:(zQ "20!lg6!jk6@2$0@1$1?2st?2LB").
Proof.
  change (fact_hdr_clear st LB). intros b gh blk r Hb Hblk Hf Hr.
  destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r' & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr' & Kr & Ea & Ho & Hn & Fit).
  rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr' in Hr. inversion Hr; subst r'.
  destruct (hdr_hosts _ _ Hb) as [m' Hm']. rewrite Ea, C2. pose proof (sstart_succ st m2 i2).
  rewrite Ec in NH2. destruct (sep_ghdr _ _ _ _ IM IG IS m2 b2 i2 Hm2 Hi2 NH2 m' b Hm' (eq_sym Hf)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma f_blk_unknown : ltac2:(zQ "10!lh8@2$0?2st?2LB").
Proof.
  intros blk r Hblk Hr a Ha. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _). cbn [bslot fst snd] in Hs.
  pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U). cbn [bslot boff bsize fst snd] in U.
  rewrite C1 in Hr |- *. rewrite C3, C2 in Ha. unfold conc, get_region in Ha. rewrite Hr in Ha.
  destruct (U (a - r_base r) ltac:(lia)) as [h Hh]. exists h. exact Hh.
Qed.

Lemma f_blocks_disjoint : ltac2:(zQ "10!lid@2$0?2st?2LB").
Proof.
  intros b1 b2 H1 H2 Hf NE.
  destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1).
  destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
  rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
  rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
  assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
  rewrite E1 in N1. rewrite E2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma LB_blocks_ok : ltac2:(zQ "30!lk6!kp2!ll0@3$0$1@1$2?2st?2LB").
Proof.
  apply List.Forall_forall. intros blk Hblk. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
  constructor.
  - exists m, i. rewrite C1. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. fold (MR st m).
    split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|].
    split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|].
    exists off. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). rewrite C2, C3. repeat split; lia.
  - rewrite C1. destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr). rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. exists r. auto.
  - rewrite C2. exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
Qed.

Lemma LB_nodup : ltac2:(zQ "50!ki5!kh0!kr3!kp2!p3@2$4$0@4$1$3$0$2?2LB").
Proof.
  rewrite (Forall2_map_eq (corr1 st) blk_slot bslot LB BL CR ltac:(intros a b (E & _); exact E)).
  apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_rid : ltac2:(zQ "d0!isb!hm8!hr2!hnc!hj9!ig2!hk0!llc!jh8!lo1!ijb!il1!il9>3rid$1>1r$0>0@3$6@1$5$0@6$a$1$0@4$b$1$3$2$0@4$c$1$3$2$0^2@1$8?2st@2$4$0^1@2$9^3@1$7?2st").
Proof. intros rid r. exact (ir_ids _ _ _ IR rid r). Qed.
Lemma area_rid : ltac2:(zQ "h50!hm8!h9!lo7!hnc!hp7!js1!hj2!hr2!hs1!ht0!hv3!hj9!it4!ig2!hk0!loe!llc!lo1!ijb!il1!il9>1a@2$5$0$1>2ar$2>0@3$e@1$d$2@6$h2@2$5$0$1$2@4$h3$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2@4$h4$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2^2@1$f?2st@2$b$2^1@2$h1@3$c$0$1^3@1$h0?2st").
Proof. intros a ar. intros Ha. destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & _) & _). exact (region_rid _ _ Hr). Qed.
Lemma area_rid' : ltac2:(zQ "h60!hm8!h9!lo7!hnc!hp7!js1!hj2!hr2!hs1!ht0!hv3!ju7!it4!ig2!hk0!jue!loe!llc!lo1!ijb!il1!il9>1a@2$5$0$1>0@1$f@3$e@1$d$2@6$h3@2$5$0$1$2@4$h4$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2@4$h5$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2^1@1$h0?2st@1$b$2@2$h2@3$c$0$1^2@1$h1?2st").
Proof. intros a. intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [exact (area_rid _ _ E)| congruence]. Qed.
Lemma present_rid : ltac2:(zQ "h60!hm8!h9!is4!hnc!hp7!js1!hj2!hr2!hs1!ht0!hv3!ju7!it4!ig2!hk0!jue!lp8!llc!lo1!ijb!il1!il9>1m@2$5$0$1>0@1$f@3$e@1$d$2@6$h3@2$5$0$1$2@4$h4$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2@4$h5$6@4$a$0$3$1$4@6$9$0$3$7$1$4$8$2^1@1$h0?2st@1$b$2@2$h2@3$c$0$1^2@1$h1?2st").
Proof. intros m.
  intros Hm. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
  destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). unfold mslot, aadd. cbn [fst]. exact (area_rid _ _ Ha).
Qed.
Lemma nonzero_present : ltac2:(zQ "h40!is4!hm8!h9!hj2!hnc!hp7!hk0!jue!hr2!hs1!ht0!hv3!ju7!ig2!hk5!lq2!lp8!ijb!il1!il9>1m$3>0@1$7@3$6$0@2$e?2st^1$f@1$7@3$6@1$d$0@6$h1$3$0@4$h2$3@4$b$1$4$2$5@6$a$1$4$8$2$5$9$0@4$h3$3@4$b$1$4$2$5@6$a$1$4$8$2$5$9$0^2@1$h0?2st@1$c$0").
Proof. intros m. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; congruence. Qed.
Lemma listed_rid : ltac2:(zQ "80!hj2!it4!hm8!h9!lqa!llc!oe!lo1>1m$0>1h$4>0@3$6$0^2@1?2LS^1@2$7@3$1$2$3^3@1$5?2st").
Proof. intros m h. intros H. apply present_rid. exact (listed_present _ _ _ _ _ INV m h H). Qed.
Lemma hosts_rid : ltac2:(zQ "70!hj2!it4!hm8!h9!hka!llc!lo1>1b$0>1m$0>0@3$4?2st^2^1@2$6@3$1$2$3^3@1$5?2st").
Proof. intros b m. intros [ai Hb]. destruct (ig_region _ _ _ IG _ _ Hb) as (r & Hr & _). exact (region_rid _ _ Hr). Qed.

Lemma f_ptrs : fact_ptrs st.
Proof.
  split.
  - unfold ptrs_in. cbn zeta.
    assert (HD : forall h, optr_in (fun rid => (rid < s_next_rid st)%N) (get_head st h)).
    { intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (listed_rid _ _ (head_listed _ _ _ _ _ INV h a E)). }
    split; [exact (HD LFree)|].
    split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & _). exact (region_rid _ _ Hr). }
    split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_head _ IA q E)). }
    split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_tail _ IA q E)). }
    split. { destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:E; cbn; [| exact I].
             destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). ndestruct (CU rid off E) as (r & Hr & _). exact (region_rid _ _ Hr). }
    split; [intros sc; exact (HD (LActive sc))|].
    split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |rid off]; try exact I.
             ndestruct BR as (_ & r & Hr & _). exact (region_rid _ _ Hr). }
    split.
    { intros g. fold (MR st g). pose proof (il_link _ _ IL g) as [[L1 L2] L3].
      assert (NX : forall x, m_next (MR st g) = Some x -> (fst x < s_next_rid st)%N).
      { intros x Hx. destruct (L2 ltac:(rewrite Hx; discriminate)) as [h Hh]. exact (listed_rid _ _ (next_listed _ _ _ _ _ INV h g x Hh Hx)). }
      split. { destruct (m_prev (MR st g)) as [p|] eqn:Ep; cbn; [| exact I].
               destruct (m_next (MR st g)) as [x|] eqn:Ex; [| discriminate (L3 eq_refl)].
               destruct (L2 ltac:(discriminate)) as [h Hh]. exact (listed_rid _ _ (prev_listed _ _ _ _ _ INV h g p Hh Ep)). }
      split. { destruct (m_next (MR st g)) as [x|] eqn:Ex; cbn; [| exact I]. exact (NX x eq_refl). }
      destruct (m_mem (MR st g)) as [b|] eqn:Eb; cbn; [| exact I]. exact (hosts_rid _ _ (mem_hosts _ _ Eb)). }
    split.
    { intros a ar Ha. split; [exact (area_rid _ _ Ha)|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
      destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_rid' _ (NXT a' E)). }
    intros b gh Hb. destruct (hdr_hosts _ _ Hb) as [m Hm]. split; [exact (hosts_rid _ _ Hm)|].
    destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _). rewrite Eg. cbn. apply present_rid. apply nonzero_present. intros E. rewrite E in Hmem. cbn in Hmem. discriminate.
  - intros rid Hrid. split.
    + destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. pose proof (region_rid _ _ E). lia.
    + destruct (s_shadow st !! rid) as [sh|] eqn:E; [| reflexivity]. destruct (ish_dom _ _ ISH _ _ E) as (r & Hr & _). pose proof (region_rid _ _ Hr). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_group_inj : ltac2:(zQ "50!hj2!hk0!hka!ji4!h9>2b1$0>2b2$0>2m1$0>2m2$0>0@3$2?2st^4^2>0@3$2?2st^4^2>0@3$1$4@2$3?2st^6@2$3?2st^5@3$1$0^7^6").
Proof. intros b1 b2 m1 m2.
  intros H1 H2 E.
  destruct (conc_group _ _ H1) as (r1 & R1 & K1 & C1 & LO1 & HI1). destruct (conc_group _ _ H2) as (r2 & R2 & K2 & C2 & LO2 & HI2).
  destruct (N.eq_dec (fst b1) (fst b2)) as [Ef|NEf].
  - rewrite Ef, R2 in R1. inversion R1; subst r1. apply injective_projections; [exact Ef| lia].
  - exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NEf) as D. unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.

Lemma groups_count : ltac2:(zQ "h30!hm8!h9!hj2!hm1!hnc!hp7!hr2!hs1!ht0!hv3!l1!js1!lr2!ii4!j4!q0!lt2!il1!lu1@2$e@1$f@2$a@2$b$2$3@5$h0$2$3@4$h1$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3@4$h2$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3@1$d?2st$c").
Proof.
  rewrite <- (length_map (fun bh : aptr * ghdr => conc st (fst bh))).
  assert (HIN : forall bh, In bh (map_to_list (s_groups st)) -> s_groups st !! (fst bh) = Some (snd bh)).
  { intros [b h] Hin. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  apply NoDup_Z_length; [unfold alloc_ceiling; lia| |].
  - apply NoDup_map_on.
    + intros [b1 h1] [b2 h2] I1 I2 E. cbn in E. pose proof (HIN _ I1) as G1. pose proof (HIN _ I2) as G2. cbn in G1, G2.
      destruct (hdr_hosts _ _ G1) as [m1 Hm1]. destruct (hdr_hosts _ _ G2) as [m2 Hm2].
      pose proof (conc_group_inj _ _ _ _ Hm1 Hm2 E) as Eb. subst b2. rewrite G1 in G2. inversion G2. reflexivity.
    + pose proof (NoDup_fst_map_to_list (s_groups st)) as ND. apply NoDup_ListNoDup in ND.
      apply (NoDup_map_inv fst). exact ND.
  - intros x Hx. apply in_map_iff in Hx. ndestruct Hx as ([b h] & <- & Hin). cbn. pose proof (HIN _ Hin) as G. cbn in G.
    destruct (hdr_hosts _ _ G) as [m Hm]. destruct (conc_group _ _ Hm) as (r & Hr & Kr & C & LO & HI).
    destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CE & _). lia.
Qed.

Lemma gcnt_bound : ltac2:(zQ "60!lue!n5!h9!j4!pb!lv5>2sc$2@2$1@2$3Z@2$0?2st^1@2$4@2$0?2st^1@2$5+2+jc").
Proof. intros sc.
  unfold gcnt.
  pose proof (zsum_bound (map (fun bh : aptr * ghdr => match g_meta (snd bh) with
     | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0 | None => 0 end) (map_to_list (s_groups st))) 32) as ZS.
  rewrite length_map in ZS. pose proof groups_count as GC. unfold alloc_ceiling in GC.
  eassert (H : _); [| specialize (ZS H); lia].
  intros x Hx. apply in_map_iff in Hx. ndestruct Hx as ([b h] & <- & Hin). cbn.
  assert (G : s_groups st !! b = Some h). { apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  destruct (im_hdr _ _ _ IM _ _ G) as (m & Eg & Hmem & AI). rewrite Eg.
  destruct (hosts_GO _ _ (mem_hosts _ _ Hmem)) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of.
  destruct (m_sizeclass (MR st m) =? sc); lia.
Qed.

Lemma f_usage : ltac2:(zQ "20!lvb!jk6@1$0@1$1?2st").
Proof.
  intros i. rewrite usage_strip. destruct (c_usage (s_ctx st) !! i) as [v|] eqn:E.
  - pose proof (ia_usage_keys _ IA i v E) as Hi. rewrite (ia_usage _ IA i Hi). apply gcnt_bound.
  - unfold usage, ctx. rewrite E. cbn. lia.
Qed.
End MF.

End HCW.


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac inst f INV CR :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem areach_facts_proof : forall {resv} st LB, AREACH_from resv st LB -> @MFACTS_g resv st LB.
Proof.
  intros resv st LB AR. ndestruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  npose INV as (IR & IA & IM & IL & IG & IS & ISH).
  constructor.
  - inst LB_blocks_ok INV CR.
  - inst LB_nodup INV CR.
  - inst f_ticks INV CR.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx INV CR.
  - inst f_active INV CR.
  - inst f_gmeta INV CR.
  - inst f_avail_clear INV CR.
  - inst f_hdr0 INV CR.
  - inst f_free_clear INV CR.
  - inst f_hdr_clear INV CR.
  - inst f_usage INV CR.
  - inst f_masks INV CR.
  - inst f_maplen INV CR.
  - inst f_slots INV CR.
  - inst f_slots_complete INV CR.
  - inst f_ptrs INV CR.
  - inst f_blk_unknown INV CR.
  - inst f_blocks_disjoint INV CR.
  - inst f_cell_ticks INV CR.
Qed.

End HCW2.

