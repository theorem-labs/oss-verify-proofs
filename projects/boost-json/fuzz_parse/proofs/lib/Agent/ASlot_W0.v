(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocKit_AB MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04mctx37Corelib4Init5Logick42eqk43and37Corelib7Numbers7BinNumsm31Z04optr0cc_avail_meta0h7c_avail_meta_area_count0h2c_avail_meta_areas0h2c_avail_meta_count05c_brk0h0c_free_meta_head0bc_init_done0h2c_meta_alloc_shift0h0c_meta_area_head0h0c_meta_area_tail0ec_mmap_counter08c_secret05c_seq0bc_unmap_seq07c_usage25stdpp9countablehn1bZ_countable25stdpp4gmaphp14gmap35stdpp7numbers1Zhq56eq_dec08brkstate04meta0am_freeable0am_last_idx08m_maplen05m_mem0bm_sizeclass79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~ig6bctx_ta_sameig69geom_sameig66ta_rel06mstate0aset_active0cget_meta_rec07m_avail07m_freed46Stdlib6ZArith6BinInt1Ziq12leiq12ltiq13powiq17testbit37Corelib4Init9Datatypesit74boolit73orbit74true04aptr08put_meta0am_set_next0am_set_prev07bounces0aset_bounce0ddecay_bouncesiq13sub04ghdrm31N35stdpp7numbers1Njm36eq_decit74Someiq14landhn1bN_countablehn1eprod_countable25stdpp9decidablejqfbprod_eq_decit76optionk43not06g_meta08s_groups0h4set_group_active_idx25stdpp4basekg86lookuphp1bgmap_lookup0aget_shadow06shadow04conc06active" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ctx_ta_same : ltac2:(zQ "10!je>1c$0>2c1$0P") := ltac2:(zQ "h80!l8!ld!nc!o0!o6!p4!qe!s3!t8!tf!v2!vf!hh4!hi7!hja!hka!hl4!hlb!hm8!je!ho2!hpd!hr6!hs0\1c$h3\2c1$h3@2$1@3$0$2@1$f^1@1$f^2@2$1@3$0$2@1$a^1@1$a^2@2$1@3$0$2@1$e^1@1$e^2@2$1@3$0$3@1$9^1@1$9^2@2$1@3$0$3@1$4^1@1$4^2@2$1@3$0$2@1$7^1@1$7^2@2$1@3$0$2@1$5^1@1$5^2@2$1@3$0$2@1$b^1@1$b^2@2$1@3$0$3@1$c^1@1$c^2@2$1@3$0$3@1$d^1@1$d^2@2$1@3$0$3@1$6^1@1$6^2@2$1@3$0@4$h5$2$h6$h4$2@1$h2^1@1$h2^2@2$1@3$0@4$h5$2$h6$h4$2@1$h1^1@1$h1^2@2$1@3$0$2@1$h0^1@1$h0^2@3$0$h7@1$8^1@1$8^2").

(* [comment removed for export] *)
Definition geom_same : ltac2:(zQ "10!hsa>1r$0>2r1$0P") := ltac2:(zQ "a0!l8!ld!nc!ht0!htc!hu8!hv2!hv9!hsa!o0\1r$8\2r1$8@2$1@3$0$9@1$6^1@1$6^2@2$1@3$0$2@1$4^1@1$4^2@2$1@3$0$2@1$3^1@1$3^2@2$1@3$0$2@1$7^1@1$7^2@3$0$2@1$5^1@1$5^2").

Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
  tr_regions : s_regions st1 = s_regions st;
  tr_shadow : s_shadow st1 = s_shadow st;
  tr_next : s_next_rid st1 = s_next_rid st;
  tr_areas : s_areas st1 = s_areas st;
  tr_slots : s_slots st1 = s_slots st;
  tr_tick : s_tick st1 = s_tick st;
  tr_secret : s_secret st1 = s_secret st;
  tr_reserved : s_reserved st1 = s_reserved st;
  tr_ctx : ctx_ta_same (ctx st) (ctx st1);
  tr_active : forall c, c <> sc -> active st1 c = active st c;
  tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
  tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
  (* [comment removed for export] *)
  tr_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
  tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
      0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
  (* [comment removed for export] *)
  tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
  tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
      exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
                 /\ (g_active_idx gh1 = g_active_idx gh
                     \/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.

Lemma ctx_ta_same_refl : ltac2:(zQ "20!ik7!je>1c$1@2$0^1^1").
Proof. intros c. repeat split; reflexivity. Qed.
Lemma geom_same_refl : ltac2:(zQ "20!il6!hsa>1r$1@2$0^1^1").
Proof. intros r. repeat split; reflexivity. Qed.

Ltac ta_auto :=
  first [ reflexivity
        | apply ctx_ta_same_refl
        | (cbn; repeat split; reflexivity)
        | (intros; apply geom_same_refl)
        | (intros ? ? ? Hb__; exact Hb__)
        | (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
        | (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
        | (intros; unfold bounces, ctx in *; cbn in *; lia)
        | idtac ].

Lemma ta_rel_refl : ltac2:(zQ "30!nc!im3!imd>2sc$0>2st$2@3$1^2^1^1").
Proof. intros sc st. constructor; ta_auto. Qed.

Lemma ta_rel_trans : ltac2:(zQ "30!im3!imd!nc>2sc$2>2st$1>3st1$1>3st2$1>0@3$0^4^3^2>0@3$0^5^3^2@3$0^6^5^3").
Proof. intros sc st st1 st2.
  intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
  destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
  constructor; try congruence.
  - unfold ctx_ta_same in *. ndestruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). ndestruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat split; congruence.
  - intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
  - intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
  - intros q. ndestruct (G1 q) as (?&?&?&?&?). ndestruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
  - intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
  - intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
  - intros b. rewrite GR2. apply GR1.
  - intros b gh2 H2. ndestruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). ndestruct (GM1 b gh1 H1) as (gh & H & M & AI).
    exists gh. split; [exact H|]. split; [congruence|].
    destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
    split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. ndestruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.

(* [comment removed for export] *)
Lemma ta_rel_set_active : ltac2:(zQ "50!nc!im3!imd!o0!in5>2sc$0>2st$2>1v$3@3$1^3^2@3$4^3^1^2").
Proof. intros sc st v.
  constructor; ta_auto.
  intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.

Lemma ta_rel_put_meta : ltac2:(zQ "h30!io1!iof!ip8!ld!ir9!irf!is5!isc!iuf!iv7!ive!l8!nc!il6!im3!jg6!hsa!imd!jgc>2sc$c>2st$h1>1g$f>1r$h0>0@2$d@2$0^3^2^1>0>1i$c>0@2$4Z^1>0@3$b$8@2$9@2$7@1$1^4^2@2$7@1$2^4^2$a@3$b$8@2$9@2$7@1$1@2$0^7^6^3@2$7@1$2@2$0^7^6^3$a>0>0@2$3@2$4Z@1$1@2$0^5^4@2$5@1$1@2$0^5^4@2$6+2+i0>0@2$3@2$4Z@1$2@2$0^6^5@2$5@1$2@2$0^6^5@2$6+2+i0@2$3@2$3@2$4Z@1$1^5@2$5@1$1^5@2$6+2+i0@2$3@2$4Z@1$2^5@2$5@1$2^5@2$6+2+i0@3$e^7^6@3$h2^5^4^6").
Proof. intros sc st g r.
  intros GS BS RS. constructor; ta_auto.
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
  - intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.

(* [comment removed for export] *)
Lemma ta_rel_put_links : ltac2:(zQ "90!o0!nc!im3!jg6!io1!jh6!ji2!imd!jgc>2sc$1>2st$7>1g$3>1p$0>1n$0@3$2^5^4@3$8^3@2$6^2@2$5^1@2$4^4^3^4").
Proof. intros sc st g p n. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_next : ltac2:(zQ "80!nc!im3!jg6!io1!jh6!imd!o0!jgc>2sc$0>2st$5>1g$2>1n$6@3$1^4^3@3$7^2@2$4^1@2$3^3^2^3").
Proof. intros sc st g n. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_prev : ltac2:(zQ "80!nc!im3!jg6!io1!ji2!imd!o0!jgc>2sc$0>2st$5>1g$2>1p$6@3$1^4^3@3$7^2@2$4^1@2$3^3^2^3").
Proof. intros sc st g p. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.

Lemma ta_rel_set_bounce : ltac2:(zQ "70!nc!ir9!ld!im3!jie!imd!jj7>2sc$0>2st$5>1i$0>1v$0>0@2$2@2$1Z^1@2$1^1@2$4^3^2@3$3^5^4@3$6^3^2^4").
Proof. intros sc st i v.
  intros Hv. constructor; ta_auto.
  intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

Lemma ta_rel_decay : ltac2:(zQ "70!nc!im3!jie!jk3!imd!ir9!jl2>2sc$0>2st$4>1c$0>0@2$5Z@2$2^2@2$6^1+7@3$1^4^3@2$3^2^3").
Proof. intros sc st c.
  intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
  apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
  apply ta_rel_set_bounce. lia.
Qed.

Lemma ta_rel_set_gai : ltac2:(zQ "hc0!nc!jg6!jl9!jlf!jn4!hr6!l8!jne!jo6!ir9!joe!ho2!jpd!js0!jsf!ld!jt9!im3!jtf!io1!hv9!imd!o0!ju7!jv1!kh4!hpd!khe>2sc$0>2st$h5>1b$1>2ai$0>0@2$f@2$9Z@2$8^1+hf@2$9@2$8^1+hf+hf>0>1h$2>1g$1>0@3$6@1$e$2@6$h9$1$2@4$ha$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2@4$hb$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2^5@1$h7^6@2$7$2^2>0@3$6$h6@1$h2^3@2$7$1^2@1$h0@3$6$0@1$h4@2$h3^8^3Z@3$h1^6^5@3$h8^4^3^5").
Proof. intros sc st b ai.
  intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
  unfold get_group in Hb.
  constructor; ta_auto.
  - intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq. split; intros _; eauto.
    + rewrite lookup_insert_ne by congruence. split; intros X; exact X.
  - intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
    + rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.

Lemma tr_get_shadow : ltac2:(zQ "70!kid!imd!l8!jlf!nc!im3!kj9>2sc$4>2st$1>3st1$1>3rid$3>0@3$5^4^3^2@3$2$6@2$0^3^2@2$0^4^2").
Proof. intros sc st st1 rid. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
Lemma tr_conc : ltac2:(zQ "60!nc!kk1!imd!l8!im3!jg6>2sc$0>2st$2>3st1$2>1q$5>0@3$4^4^3^2@3$3$0@2$1^3^2@2$1^4^2").
Proof. intros sc st st1 q. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
Lemma rec_set_gai : ltac2:(zQ "70!jg6!io1!l8!nc!hsa!imd!jv1>1b$0>2ai$3>2st$5>1q$0@3$2$4@2$1@3$6^4^3^2^1@2$1^2^1").
Proof. intros b ai st q. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
Lemma active_set_gai : ltac2:(zQ "70!nc!kk7!l8!jg6!imd!o0!jv1>1b$3>2ai$0>2st$4>1i$0@3$2$5@2$1@3$6^4^3^2^1@2$1^2^1").
Proof. intros b ai st i. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
