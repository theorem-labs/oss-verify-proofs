(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocFacts_AM.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export F_am_P.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_E~~~~~~0aam_init_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AM~~~~~~kb7AMpre_g79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~pccref_reserved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~uc9s_regions37Corelib4Init5Logichj62eq37Corelib7Numbers7BinNumshl01Nuc6region25stdpp9countablehn7bN_countable25stdpp4gmaphp74gmap35stdpp7numbers1Nhqb6eq_decuc5c_brkuc3ctxuc8brkstateuc4conchl01Zuc4aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_P~~~~~~hv23AMI79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~ij87optr_inhj64Trueij87ptrs_inuc8c_activeuc4mctxuccc_avail_metauch2c_avail_meta_areasuch0c_free_meta_headuch0c_meta_area_headuch0c_meta_area_tailuc6mstateuc7upd_ctxhn7bZ_countable35stdpp7numbers1Zjie6eq_decuc4areahn7eprod_countable25stdpp9decidablejm2bprod_eq_decuccget_meta_rec37Corelib4Init9Datatypesjp16optionjp14Somehj63not25stdpp4basejs26lookuphp7bgmap_lookupjp14Nonejp14produc9c_bouncesucec_mmap_counteruc5c_sequcbc_unmap_sequc7c_usageuc4metauc4optruc7s_areasuc8s_groupsucas_next_riducas_reserveduc8s_shadowuc7s_slotsuc6s_tickjs27is_Somejp14listhj63andhj62or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~kqf9meta_slotij86am_reluc7RKGroupuc4ghdruc5m_memuc6m_nextuc5meta0uc6r_kinduc5rkinduc6shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_A~~~~~~lkc7am_tookuch2c_avail_meta_countuc7s_metas46Stdlib6ZArith6BinInt1Zlr63subuc8AREA_HDRuc4aaddjp13fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_K~~~~~~lue8carve_stuc9META_SIZEuc6NSLOTSlr63addlr62lelr62ltlr63mulhj63iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocModel_B~~~~~~mmf9clr_linksuc5LFreeuc7dequeueuc6m_prevhj62exuc8c_secrethv2bctx_core_equc7BrkDeaduc7BrkLivelr63powucanew_regionjp14pairuc8mkRegionuc6r_baseuc5r_lenucbset_regionsjs26insert25stdpp8fin_mapsnm1amap_inserthp7h2gmap_partial_alter" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation RAMpre := (@AMpre_g _ ref_reserved).
Notation ram_pre := (am_pre_g ref_reserved).


Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section PURE.
Variable st : ltac2:(zQ "10!jgc$0").
Hypothesis AMP : ltac2:(zQ "20!p2!td@3$0?4HSEC@1$1?5HCEIL?2st").

Lemma rAMpre_init : ltac2:(zQ "30!jf!p2!td@3$1?4HSEC@1$2?5HCEIL@1$0?2st").
Proof. try hcb. try hsb.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
  destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
  - rewrite A3. lia.
  - right; reflexivity.
  - destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

Lemma ram_init_regions : ltac2:(zQ "80!hia!hka!hm9!jf!hme!ho8!hq3!hrc@3$1@4$6$2$7$5$4@1$0@1$3?2st@1$0?2st").
Proof. try hcb. try hsb. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_brk : ltac2:(zQ "50!hs6!hse!hka!jf!ht4@3$2$4@1$0@1$1@1$3?2st@1$0@1$1?2st").
Proof. try hcb. try hsb. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_conc : ltac2:(zQ "50!htf!hka!hu6!jf!hub>1q$4@3$1$2@2$0@1$3?2st^1@2$0?2st^1").
Proof. intros q. try hcb. try hsb. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

Lemma rAMI_init : ltac2:(zQ "20!jf!ij1@2$1?2st@1$0?2st").
Proof. try hcb. try hsb.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
  (split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | intros rid r Hr; exists r; repeat split; auto; lia
          | intros rid r' H1 H2; cbn in H1; congruence
          | cbn; lia
          | intros P _ HP; exact HP || (ndestruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
          | intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
          | exact (amp_rpos st AMP) ]).
  - cbn. rewrite (amp_s_secret st AMP). lia.
  - exact (amp_secret st AMP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rptrs_in_upd_ctx : ltac2:(zQ "h60!hse!inb!io6!hm9!hu6!ioe!ht4!ip9!iq4!hka!hub!iqb!ira!hs6!it0!iu4!iv8!jgc!jh5!jhf!hq3!jjf>1P>0$3P>3st0$h1>1f>1x$8$8>0@2$1^3@1$e@1^1@1$0^2>0@2$1^4@1$b@1^2@1$0^3>0@2$1^5@1$f@1^3@1$0^4>0@2$1^6@1$h0@1^4@1$0^5>0@2$1^7@1$c@1^5@1$0^6>0@3$9@4$h4$4$h5$h3$a@1$7@1^6@1$0^7@1$7@1$0^7>0M6\1x$6P@1$d@1^7@1$0^8$2$2\3rid$3\3off$4@1^b^2>0@2$5^a^9@2$5^b@2$h2^9^a").
Proof. intros P st0 f. try hcb. try hsb.
  (intros E1 E2 E3 E4 E5 E6 E7 nd_i1; ndestruct nd_i1 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E6.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_final : ltac2:(zQ "j72!hu6!hka!hm9!hub!hrc!jjf!hse!hq3!ho8!jhf!jk9!hme!jl0!jn3!jo2!jq9!jr3!jrb!hia!jse!jt8!ju7!juf!ioe!ip9!jv7!kg3!kh4!khc!kia!kj4!jgc!kjb!kk2!kkc!kl7!km4!kn1!knc!ko6!kof!kpa!kq2!kq9!ij1!kv1!kve!lg8!lh2!lh9!li1!lia!lj2!ljb!lk3&@4$7$3@4$d$2$4$0$5@6$c$2$4$8$0$5$9$a&@4$h4$3@4$d$2$4$0$5@6$c$2$4$8$0$5$9$a>3stX$hf>3st1$hf>2mo@1$f$3>0@2$ic?2st^3>0@3$1@4$7$0$5$9$3@1$h8@1$6^3@1$h8@1$6^4>0@3$1@4$7$0$5$9$0@1$hd@1$6^4@1$hd@1$6^5>0@3$1@4$7$0$5$9$0@1$hc@1$6^5@1$hc@1$6^6>0@3$1@4$7$0$5$9$0@1$h9@1$6^6@1$h9@1$6^7>0@3$1$0@1$hb@1$6^7@1$hb@1$6^8>0@3$1$0@1$ha@1$6^8@1$ha@1$6^9>0@3$1@4$7$3@4$d$2$4$0$5@6$c$2$4$8$0$5$9$j0@1$i2^9@1$i2^a>0@3$1@4$7$3@4$d$2$4$0$5@6$c$2$4$8$0$5$9@2$h6$3$0@1$i6^a@1$i6^b>0@3$1@4$7$2$4$8$j6@1$i5^b@1$i5^c>0@3$1$2@1$i7^c@1$i7^d>0@3$1@1$i9@2$h6$0$0@1$i4^d@1$i4^e>0@3$1@4$7$2$4$8$b@1$h2^e@1$h2^f>0@3$1$2@1$i3^f@1$i3^h0>0>1a$3>0@2$i8$a@6$h3$3$a~0~1^1@1$i1^h2@2$i8$a@6$h3$3$a~0~1^2@1$i1^h2>0>1g$3>0@1$h1@3$1@1$f$3@2$h0$3^1^h1>0@2$ib@1$h1@3$1$i0@1$j1@2$e?2st^2@1$h5$3@3$1$i0@1$j2@2$e?2st^2@1$h5$3@3$1$he@2$e^h4^3@2$e^h5^3>0>1m$3>0@3$1@1$f$3^h2@2$h0$3^1@2$ia@3$1$he@2$e^h4^2$j3@2$id^h4^2>0>1P>0$2P>0>3rid$2>1r$b>0@3$1@1$f$b@6$h3$2$b@4$7$2$4$8$b@4$h4$2$4$8$b^2@1$h2^h7@2$h0$b^1>0@1$h1@3$1$j5@1$j4^2$if@1^5^4>0@2$h7^2^h6@2$h7^3^h6@3$ie?2st^h4^h3").
Proof. intros stX st1 mo. try hcb. try hsb.
  intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
  destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split.
  - intros sc. unfold active. rewrite E1, C7. reflexivity.
  - intros sc. unfold usage. rewrite E2, C8. reflexivity.
  - intros i. unfold bounces. rewrite E4, C10. reflexivity.
  - intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
  - rewrite E5, C11. reflexivity.
  - rewrite E6, C1. reflexivity.
  - rewrite EG, XG. reflexivity.
  - rewrite ESl, XS. reflexivity.
  - rewrite ESh, XSH. reflexivity.
  - rewrite ET, XT. reflexivity.
  - rewrite ERs, XR. reflexivity.
  - intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
  - exact HR.
  - intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
  - intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
  - rewrite EN. exact XNX.
  - intros a Ha. apply HA. rewrite XA. exact Ha.
  - intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
    apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
  - intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ram_rel_none : ltac2:(zQ "50!ju7!ij1!kve!hub!jgc>3stX$4>0@2$1?2st^1@3$2?2st^2@1$0$3").
Proof. intros stX. try hcb. try hsb.
  intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
  - intros m Hm. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_take : ltac2:(zQ "hc0!hub!kj4!hm9!hu6!hrc!jjf!jr3!hka!hse!ho8!jhf!jl0!jn3!ju7!jq9!lob!ij1!kv1!kve!iqb!lp6!jgc!kjb!lqc!lse!jse!hq3!jt8>3stX$h5>1q$0>0@2$h0?2st^2>0@3$7$h6@1$h3@1$8?2st@2$6$0^2>0@3$7@1$e$1@6$h9$0$1@4$ha$0@4$c$2$4$3$5@6$b$2$4$9$3$5$a$1@4$hb$0@4$c$2$4$3$5@6$b$2$4$9$3$5$a$1^3@1$h7?2st@1$d$1>0@2$h1?2st^4@3$h2?2st@3$f^6^5@2$h8@1$h4@1$8^6+1@2$6$0^5").
Proof. intros stX q. try hcb. try hsb.
  intros AI AVM MQ MSq. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  unfold am_took. rewrite upd_meta_put.
  eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
  - intros a Ha. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
    + apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
  - intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta.
    + cbn. exact I.
    + cbn. exact I.
    + unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
    + npose HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
        try assumption; try reflexivity.
      cbn. rewrite C3, AVM in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_carve : ltac2:(zQ "ie2!hm9!hu6!hrc!jjf!hub!jk9!ho8!hme!jhf!jl0!jn3!hka!kj4!jse!hq3!jt8!jr3!jq9!lt5!lu0!ju7!juf!kk2!lu7!kq2!jrb!lob!mid!ij1!kve!mj9!mk5!lg8!iv8!hse!jgc!kjb!lj2!ljb!lqc!hia!mke!ml5!mlb!mm1!kof&@4$e$4@4$a$0$2$1$3@6$9$0$2$6$1$3$8$5&@4$f$4@4$a$0$2$1$3@6$9$0$2$6$1$3$8$5>3stX$i3>1p@2$h5$0$1>1r$7>0@2$hc?2st^3>0@3$b@1$h1$7@6$d$0$7@4$e$0$2$6$7@4$f$0$2$6$7@3$h7$0$1^3@1$i8^4@2$h0$7^2>0@1$h9@3$b$i6@1$i5^3$i0>0@3$b@1$h1$5@6$d@2$h5$0$1$5~0~1^5@1$h6^6@1$h4$5>0>1k$1>0@2$h8@2$iaZ^1@2$ib^1$hf@3$b@1$h1$c@6$d$4$c@4$e$4@4$a$0$2$1$3@6$9$0$2$6$1$3$8$c@4$f$4@4$a$0$2$1$3@6$9$0$2$6$1$3$8$c@2$h3^8@2$i9$h2@2$ic$he^2@1$i7^9@1$h4$c>0>2tl$4>0@3$b$i4@1$i1@1$i2^9@2$h0$4^1@2$id$5@6$d$4$5~0~1^2@1$h6^a@3$hd?2st@3$ha@2$hb^9^8@2$h3^8$h2+m4@2$h0$4@2$h3^8$h2").
Proof. intros stX p r. try hcb. try hsb.
  intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
  { replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }
  (* [comment removed for export] *)
  assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
            /\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
            /\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
            /\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
            /\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
            /\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
            /\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
  { destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
    - destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
      + intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
        * destruct H0 as (H1 & _). exact H1.
        * ndestruct H0 as (_ & H2 & _). exact H2.
        * ndestruct H0 as (_ & _ & H3 & _). exact H3.
        * exact HP.
        * exact HP.
        * ndestruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
        * npose H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
          assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
          { apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
          ndestruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
          unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
          split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
          split; [exact Q8|]. split; [| exact Q10].
          intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
          -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
          -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
    - rewrite (carve_st_none stX p HT ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. exact Ha.
      + intros P HP H0. npose H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
  ndestruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
  rewrite EC. unfold am_took. rewrite upd_meta_put.
  set (stD := set_areas _ stC).
  eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
     c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
  - intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
    + apply meta_slot_put_meta. nexists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
      split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
  - intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
    apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
    + unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
    + apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
      * destruct (RP P HPp HP0) as (H1 & _). exact H1.
      * exact HPp.
      * ndestruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
      * ndestruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
      * ndestruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
      * ndestruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
      * npose (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
        split; [exact H8|]. split; [| exact H10].
        intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
        -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
        -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_deq : ltac2:(zQ "h60!hub!hka!kjb!jo2!jr3!ju7!li1!jrb!it0!hse!lh9!mm8!ij1!mr5!kv1!kve!ms2!msa!mt4!kj4!lia!jgc>3stI$h5>1h$0>2nx$0>2pv$0>0@2$c?2st^4>0@3$1$2@1$8@1$9?2st@2$4$0^4>0@3$1$2@1$8@1$9^6@2$4$0^5>0@3$1$2@1$6@2$3?2st^6@2$4$0^5>0@3$1$2@1$h2@2$3?2st^7@2$4$0^5>0@2$b@3$1$0^7^8@3$1$0^6^8>0@2$e?2st^9>0@3$1$h3@1$d@2$3?2st^a$h4>0@3$1$2@1$a@2$3?2st^a@1$5$0>0@1$7@3$1$2@1$6@2$3?2st^b@1$5$0>0@3$1$2@1$a@2$3?2st^b@1$5$0>0@1$7@3$1$2@1$6@2$3?2st^c@1$5$0@3$f?2st@3$h1$h0^f^h0@2$4$0^f").
Proof. intros stI h nx pv. try hcb. try hsb.
  intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
  rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
  destruct (aptr_eqb nx h) eqn:E.
  - (* [comment removed for export] *)
    apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
      * change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; ndestruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
          ndestruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
      * npose HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
  - (* [comment removed for export] *)
    assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
    assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
    cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
    set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
    assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
    { change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
      rewrite !get_meta_rec_put_other by congruence. apply GM. }
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
      change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
      assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
      assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
      rewrite !get_meta_rec_put_other by assumption. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same, R3. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. npose HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      ndestruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
      assert (P1 : ptrs_in P st1).
      { unfold st1. apply MallocKit_A2.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
        - ndestruct (H8 pv) as (X & _ & _). exact X.
        - ndestruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P2 : ptrs_in P st2).
      { unfold st2. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. ndestruct (H8 nx) as (_ & X & _). exact X.
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| ndestruct (H8 nx) as (_ & _ & X); exact X].
          ndestruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P3 : ptrs_in P st3).
      { unfold st3. npose P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
        apply rptrs_in_upd_ctx; cbn; try reflexivity.
        - exact Q2.
        - change (ctx st2) with (ctx stI). exact H2.
        - change (ctx st2) with (ctx stI). exact H3.
        - change (ctx st2) with (ctx stI). exact H4.
        - change (ctx st2) with (ctx stI). exact H5.
        - change (ctx st2) with (ctx stI). exact H7.
        - exact P2. }
      apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
      rewrite R3. rewrite <- GM. exact Q3.
Qed.

(* [comment removed for export] *)
Lemma rAMI_ctx : ltac2:(zQ "i50!hme!hse!hka!hm9!kq2!mtd!hs6!ho8!hrc!jr3!kq9!hu6!hub!ht4!ira!jq9!jrb!ij1!lg8!mu3!iq4!kjb!lj2!ljb!hia!jse!hq3!jt8!lu7!mue!mvd!ng7!jgc!jh5!ml5!mlb!nh1>3stX$i0>1f>1x$h4$h4>0@2$h1?2st^2>0@2$hd@1$1^3@1^2@1$1^3>0@2$4@2$i2Z@1$h3@1^3@1$1^4@2$i3@1$h3@1^3@1$1^4@2$i4+2+k0>0@2$a@3$2$h5@1$e@1^4@1$1^5@1$e@1$1^5@2$5$c\1q$c@2$5$0\1r$0@2$4@3$2$h5@1$e@1^6@1$1^7@2$9$c^2@2$4@3$2@1$f$0@6$h9$3$0@4$ha$3$8$7$0@4$hb$3$8$7$0@3$hc$3$b^2@1$h8^7@2$9$0^1@1$h0@3$2$h7@1$h6^1$h2>0@2$a@3$2$d@1$6@1^5@1$1^6@1$6@1$1^6@2$a@3$2$d@1$6@1^5@1$1^6$he@2$5$3\3rid$3@2$5$b\3off$b@2$5$0\1r$0@2$4@3$2$d@1$6@1^8@1$1^9@2$hf^3^2@2$4@3$2@1$f$0@6$h9$3$0@4$ha$3$8$7$0@4$hb$3$8$7$0^3@1$h8^9@2$9$0^1@1$h0@3$2$h7@1$h6^1$h2@2$h1?2st@2$i1^6^7").
Proof. intros stX f. try hcb. try hsb.
  intros AI CE SR HA HB. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split; cbn; try assumption.
  - ndestruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
    ndestruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
    rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
  - intros P HPn HP0. npose (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    ndestruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
    + destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
    + destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
    + exact (XP P HPn HP0).
Qed.

Lemma rAMI_new_region : ltac2:(zQ "hb0!hm9!hu6!lu7!hka!jgc!hme!nh8!kq2!htf!kl7!jrb!ij1!ljb!ho8!hrc!jr3!jq9!ni5!juf!lg8!nid!hia!mke!mlb!jse!hq3!jt8>3stX$4>1k$c>4base$1>3len$1>0@2$b?2st^4>0@1$a@3$3$c^4$h3>0@2$h7Z^3@2$7@2$b?2st@3$2$4$0@4$6^6^5^4^7@2$7@3$3@1$h0$5@6$h8$0$5@4$h9$0$e$d$5@4$ha$0$e$d$5@1$9^7@1$h5@3$2$4$0@4$6^6^5^4^7@2$f$5@3$h4^6^5^4@2$7>1q@2$h2$0$1>0@1$a@3$3$0@3$2$0$1^1@1$9^8@3$3$1@2$8@3$2$4$0@4$6^8^7^6^9^2@2$8^9^2>3off$1@3$3$1@2$8@3$2$4$0@4$6^7^6^5^8@4$h1$0$1@1$9^8^1@2$h6^6^1").
Proof. intros stX k base len. try hcb. try hsb.
  intros AI NK LEN. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
  unfold new_region. cbn [fst].
  set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  split; [| split; [| split]].
  - split; cbn -[insert]; try assumption.
    + intros q r Hq. ndestruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
      destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
    + intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
    + unfold rid. lia.
    + intros P HPn HP0. apply (MallocKit_A2.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
      intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
    + intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
    + intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
  - rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
  - intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
  - intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

Lemma rAMI_grow : ltac2:(zQ "hd0!hme!hm9!ho8!hrc!hka!hq3!hu6!lj2!hia!jr3!jq9!kq2!ij1!htf!nid!jgc!nj8!mke!jse!jt8!jrb!lg8!hub!nk1!ljb!nk9!nl7!nn1!nnf>3stX$f>3rid$1>1r$0>3off$6>0@2$c?2st^4>0@3$4@1$a$0@6$h2$1$0@4$5$1$3$2$0@4$h3$1$3$2$0^4@1$8^5@2$9$0^3>0@1$h4@3$4$h8@1$7^4$h5>0@3$4$6@1$h7^5^4=3st'$f@2$h9@7$ha$1$0@4$5$1$3$2$0@4$hb$1$0@4$5$1$3$2$0@4$hc$1$3$2$0^7@3$e@1$7^6@1$h0^6@2$h1^5+hgg0@1$8^8^8@2$b@2$c?2st^1@2$b>1q$h6@3$4$6@2$d^2^1@2$d^a^1@3$4@1$a$0@6$h2$1$0@4$5$1$3$2$0@4$h3$1$3$2$0^8@1$8^1@2$9$0@3$e@1$7^7@1$h0^7@2$h1^6+hgg0").
Proof. intros stX rid r off. try hcb. try hsb.
  intros AI Hr NK LEN st'. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  assert (CQ : forall q, conc st' q = conc stX q).
  { intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
  split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
  split; cbn -[insert]; try assumption.
  - intros q rq Hq. ndestruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
    destruct (decide (q = rid)) as [->|NE].
    + rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
      intros HG. exfalso. apply NK. rewrite K'. exact HG.
    + exists r'. auto.
  - intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
  - intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
    destruct (decide (q = rid)) as [->|NE].
    + apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
    + apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
  - intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
    + destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
    + apply XF. exact Hq.
  - intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.

End HCW.

