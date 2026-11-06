(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Shadow MI_WFree2 MI_WGroup.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr06mstate37Corelib7Numbers7BinNumskc1Nkc1Z06shadow37Corelib4Init9Datatypesn54prod37Corelib4Init5Logicp42eqn54Somen56optionn54pair25stdpp4bases46lookup25stdpp9countablet9bN_countablet9bZ_countable25stdpp4gmaphg64gmaphg6bgmap_lookup35stdpp7numbers1Nhi96eq_dec35stdpp7numbers1Zhk46eq_dec07r_cells08s_shadow06s_tick46Stdlib6NArith6BinNat1Nhna2ltp43andn53snd46Stdlib6ZArith6BinInt1Zhq42lep42ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hs72MRhq43subn53fstp42orhs76cnt_ofhs75hostshs76sstart02IB08m_maplen79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_TF2~~~~~~ik82PSik82TWik83TF0ik83TF279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WGroup~~~~~~iq03TKS08set_tick09hdr_havoc03wr8n54list37Corelib5Lists7ListDefjg93mapiq03wrs36Stdlib5Lists4Listjie2Inik89geom_kept04ghdrt9eprod_countable25stdpp9decidablejmbbprod_eq_dec08s_groups04meta0aget_shadowp43nothq46modulohq43addhq42ltiq02TFhs74INVL0am_last_idxn54None" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW : ltac2:(zQ "20!je!k4>2st$1>1P>0$0PP") := ltac2:(zQ "h40!m5!m9!md!od!q8!qd!r4!rd!t0!ua!v8!hh2!hha!hja!hl5!je!k4!hlf!hm8!hn2\2st$h0\1P>0$fP>3rid$0>2sh$2>1o$1>1v$1>1t$0>0@3$4@1$6$2@6$8$0$2@4$b$0$d$9$2@4$c$0$d$9$2^5@1$h2^7@2$5$2^4>0@3$4@1$6@2$3$1$0@6$8$1@2$3$1$0@4$b$1$e$a@2$3$1$0@4$c$1$e$a@2$3$1$0^4@1$h1^5@2$5@2$3$1$0@4$7$1$0^3^2>0@3$4$0^3@1$h3^9@1^9@4$7$0$1^8^6").

Definition TF0 : ltac2:(zQ "10!k4>2st$0P") := ltac2:(zQ "h40!m5!m9!md!od!qd!r4!q8!t0!ua!v8!hh2!hha!hja!hl5!rd!k4!hlf!hm8!hn2!hp2\2st$f>3rid$0>2sh$2>1o$1>1v$1>1t$0>0@3$6@1$5$2@6$7$0$2@4$a$0$c$8$2@4$b$0$c$8$2^5@1$h1^6@2$4$2^4>0@3$6@1$5@2$3$1$0@6$7$1@2$3$1$0@4$a$1$d$9@2$3$1$0@4$b$1$d$9@2$3$1$0^4@1$h0^5@2$4@2$3$1$0@4$e$1$0^3^2@2$h3^3@1$h2^8").

(* [comment removed for export] *)
Definition PS : ltac2:(zQ "20!je!k4>2st$1>1q$0P") := ltac2:(zQ "h20!m9!m5!hp8!hpe!je!hrc!q8!hs2!ig5!igb!ih2!ih8!ihd!ii7!ij0!ija!ije!k4\2st$h1\1q$4@2$7$4\1b$4@2$7$4\1m$4@2$2@3$d^4^2^1@2$2@3$6$1@3$a$1$0^2@3$a$1$0^3@2$b@2$7$0\1i$0@2$2@2$2@2$5Z^1@2$5^1@1$c@2$8^5^2@3$6$0@3$3$1$0^4@2$9@2$e@2$8^5^2^1$f@2$2@3$6$0@1$h0@2$8^4^1Z@2$2@2$5@2$9@3$3$1$0^2+3@3$3$1$0^3@2$5@3$3$1$0^3@2$9@3$3$1$0^2+1").

Definition TF2 : ltac2:(zQ "10!k4>2st$0P") := ltac2:(zQ "30!io6!ioc!k4\2st$2@2$1^1@1$0^1").

Lemma TF0_TW : ltac2:(zQ "40!ip2!ioc!je!k4>2st$3>1P>0$2P>0@1$0^2@2$1^3^2").
Proof. intros st P. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 : ltac2:(zQ "30!ip2!ip9!k4>2st$2>0@1$0^1@1$1^2"). Proof. intros st. apply TF0_TW. Qed.

Lemma TW_mono : ltac2:(zQ "30!je!ioc!k4>2st$2>1P>0$0P>2P'>0$0P>0>1q$0>0@1^3^1@1^3^2>0@2$1^4^3@2$1^5^3").
Proof. intros st P P'. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl : ltac2:(zQ "b0!q8!m5!ioc!k4!hm8!hn2!je!md!ua!hh2!hja>2st$3>3st'$3>1P>0$6P>0@3$0@4$9$1$a$8$7@1$4^2@1$4^3>0@3$0$1@1$5^3@1$5^4>0@2$2^5^3@2$2^5^4").
Proof. intros st st' P. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl : ltac2:(zQ "a0!q8!m5!ip2!k4!hm8!hn2!md!ua!hh2!hja>2st$3>3st'$3>0@3$0@4$8$1$9$7$6@1$4^1@1$4^2>0@3$0$1@1$5^2@1$5^3>0@1$2^4@1$2^4").
Proof. intros st st'. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma TF0_tick_new : ltac2:(zQ "70!hn2!m5!ip2!iu1!k4!iu8!hp2>2st$4>1t$1>0@2$3^2@1$0^2>0@2$6@1$0^3^2@1$2@2$5^3^4").
Proof. intros st t.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc : ltac2:(zQ "40!ip2!je!iv2!k4>2st$3>1b$1>0@1$0^2@1$0@2$2^2^3").
Proof. intros st b.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc : ltac2:(zQ "40!ioc!je!iv2!k4>2st$3>1b$1>1P>0$1P>0@2$0^3^1@2$0@2$2^3^4^2").
Proof. intros st b P.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' : ltac2:(zQ "50!ioc!je!m9!k4!ivd>2st$3>1q$1>1v$2>1P>0$1P>0@2$0^4^1>0@1^2^4@2$0@3$4^5^4^6^3").
Proof. intros st q v P.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs : ltac2:(zQ "a0!je!m9!od!ioc!ih2!jg2!ji0!ji7!k4!jk1>1l@1$5@2$2$0$1>2st$8>1P>0$0P>0@2$3^2^1>0>1q$0>0@3$9$0^1@4$6@2$2$0$1$0@2$4$0$1^5@1^4^2@2$3@2$7^5^4^3").
Proof. intros l.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

(* [comment removed for export] *)
Definition geom_kept : ltac2:(zQ "10!k4>2st$0>3st'$0P") := ltac2:(zQ "a0!ig5!m9!hp8!q8!ihd!ii7!ij0!je!ije!k4\2st$9\3st'$9>1b$7>1m$7>0@3$5^4^2^1@2$2@3$5^4^3^2@2$2>1i$1@3$3$1@2$6@2$0^5^3^1@2$6@2$0^6^3^1@2$2@3$3$1@1$4@2$0^4^2@1$4@2$0^5^2@3$3$1@1$8@2$0^4^2@1$8@2$0^5^2").


Lemma PS_mono : ltac2:(zQ "40!io6!k4!jk7!je>2st$1>3st'$1>1q$3>0@2$2^3^2>0@2$0^4^2@2$0^4^3").
Proof. intros st st' q.
  intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
  exists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept : ltac2:(zQ "b0!q8!m5!ip9!k4!hm8!hn2!jk7!md!ua!hh2!hja>2st$3>3st'$3>0@3$0@4$9$1$a$8$7@1$4^1@1$4^2>0@3$0$1@1$5^2@1$5^3>0@2$6^4^3>0@1$2^5@1$2^5").
Proof. intros st st'.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

(* [comment removed for export] *)
Lemma geom_kept_of : ltac2:(zQ "h62!jl4!je!m5!m9!hja!hl5!ua!v8!jla!jnc!q8!qd!r4!ig5!k4!job!t0!hh2!hha!ii7!jk7!jp5&@4$h1$1@4$9$2$4$3$5@6$8$2$4$6$3$5$7$0&@4$h2$1@4$9$2$4$3$5@6$8$2$4$6$3$5$7$0>2st$e>3st'$e>0>1b$1>1h$0>0@3$a@1$c$0@6$h0$1$0~0~1^2@1$f^4@2$b$0^1@3$a@1$c$0@6$h0$1$0~0~1^3@1$f^4@2$b$0^2>0>1b$1>1m$1>0@3$h3^5^2^1@3$a$h5@2$d^5^2@2$d^6^2@2$h4^4^3").
Proof. intros st st'.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

(* [comment removed for export] *)
Lemma wr8_cells_other : ltac2:(zQ "h00!m9!m5!od!v8!hl5!q8!jpb!hlf!t0!hh2!hha!r4!rd!jq7!k4!ivd>2st$e>1q@2$2$1$0>1v$0>3rid$1>1o$0>0@1$d@3$5@2$2$1$0@4$c$1$0^2^1^4@3$5@1$b@2$2$0$1@6$8$0@2$2$0$1@4$9$0$4$3@2$2$0$1@4$a$0$4$3@2$2$0$1^2@1$7@2$6@3$f^5^4^6^3@6$8$0@2$2$0$1@4$9$0$4$3@2$2$0$1@4$a$0$4$3@2$2$0$1^2@1$7@2$6^6^3").
Proof. intros st q v rid o.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other : ltac2:(zQ "h40!m9!od!m5!v8!hl5!jpb!hlf!t0!hh2!hha!ih2!jg2!r4!rd!q8!jq7!ji0!ji7!k4!jk1>1l@1$b@2$1@2$1$2$0$0>2st$h2>3rid$2>1o$0>0@1$f@3$h3@2$1$2$0@4$d$2$0^2^1@4$h0@2$1@2$1$2$0$0@2$1$2$0@2$a@2$1$2$0$0^4@3$e@1$c@2$1$0$2@6$7$0@2$1$0$2@4$8$0$4$3@2$1$0$2@4$9$0$4$3@2$1$0$2^2@1$6@2$5@2$h1^5^4^3@6$7$0@2$1$0$2@4$8$0$4$3@2$1$0$2@4$9$0$4$3@2$1$0$2^2@1$6@2$5^4^3").
Proof. intros l.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!jsa@5$0?1X?2st?1L?2BL?2LS").

Lemma sstart_res : ltac2:(zQ "90!m9!je!q8!ig5!ii7!ij0!ija!jqd!igb>1b$1>1x$1>1i$0>0@3$4?2st^3^2@3$2$0@2$7@2$8@2$5@2$3?2st^3^2$6+h0+c").
Proof. intros b x i.
  intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : ltac2:(zQ "10!ii7@3$0?2st?2bg?1g").
Hypothesis Hidx : ltac2:(zQ "40!hrc!hp8!ig5!jt2@2$1@2$0Z?3idx@2$0?3idx@1$3@2$2?2st?1g").
Hypothesis NH : ltac2:(zQ "h60!m5!m9!jl4!hja!hl5!je!ua!v8!jla!jnc!jte!ih2!r4!rd!od!q8!ig5!ij0!job!t0!hh2!hha@3$f@1$c$2@6$h3@2$e$0$1$2@4$h4$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2@4$h5$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2@4$d$0$1@3$b$0$1?2bg@2$h1@2$h0?2st?1g?3idx@1$h2?2st@1$a$2").

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma PS_not_interior : ltac2:(zQ "h00!m5!m9!ih2!hpe!ig5!ij0!hp8!q8!jq7!io6!ija!je!jr7!hrc!jre!igb>1q$b>0@2$9?2st^1>0@3$7$0@3$2$0$1^2@3$2$0$1?2bg@1$8@2$6@2$d@2$5@2$4?2st?1g?3idx@3$3$0$1^3@2$e@3$3$0$1^3@2$f@2$5@2$4?2st?1g@2$c?3idx+1$a").
Proof. intros q.
  intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    + (* [comment removed for export] *)
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  - (* [comment removed for export] *)
    destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
    destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_interior_old : ltac2:(zQ "ha0!m9!m5!od!ig5!ij0!v8!hl5!qd!ih2!r4!rd!hp8!q8!ip9!ija!jpb!hlf!hn2!hp2!jr7!hrc!jre!igb!t0!hh2!hha>0@1$d?2st>1o$0>1v$0>1t$1>0@3$c@1$9@2$2$0$1@6$h7$0@2$2$0$1@4$h8$0$6$5@2$2$0$1@4$h9$0$6$5@2$2$0$1^3@1$h0@2$f?2st@3$8$1$0?2bg@2$7@2$2$0$1@4$a$0$1^2^1>0@2$b@2$h4@2$4@2$3?2st?1g?3idx^4@2$h5^4@2$h6@2$4@2$3?2st?1g@2$h3?3idx+1$e@2$h2^3@1$h1?2st").
Proof.
  intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

(* [comment removed for export] *)
Lemma TF2_ghdr_old : ltac2:(zQ "h90!m9!m5!od!hpe!q8!v8!hl5!qd!ih2!r4!rd!hp8!ip9!je!jpb!hlf!hn2!hp2!jr7!hrc!jre!jqd!t0!hh2!hha>1p$d>0@1$c?2st>0@3$4$0@2$h5@3$3$1$0^2+h0Z>1o$0>1v$0>1t$1>0@2$b@2$h3@3$3$1$0^6^3@2$h4^3@2$h2@3$3$1$0^6+c>0@3$4@1$9@2$2$0$1@6$h6$0@2$2$0$1@4$h7$0$6$5@2$2$0$1@4$h8$0$6$5@2$2$0$1^4@1$f@2$e?2st@3$8$1$0^7@2$7@2$2$0$1@4$a$0$1^3^2@2$h1^3@1$h0?2st").
Proof. intros p.
  intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_TF : ltac2:(zQ "20!ip9!js4>0@1$0?2st@1$1?2st").
Proof.
  intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.
(* [comment removed for export] *)
