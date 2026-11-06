(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WTry.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WTry2~~~~~~hc8TA_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m76mstatem74metam74aptrm78upd_metam74optrm7aset_activem7ddecay_bouncesm77LActivem77dequeue37Corelib4Init9Datatypesvf4listvf4cons37Corelib4Init5Logichi52eqhi52ex36Stdlib5Lists4Listhk52Inm74ghdr01N35stdpp7numbers1Nhm86eq_dec35stdpp7numbers1Zho36eq_dechi53andvf4Some25stdpp9countablehqcbN_countablehqcbZ_countablehqceprod_countable25stdpp9decidablehudbprod_eq_decvf6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~ih62MRm7bm_sizeclassm76mkGhdrm78s_groups46Stdlib6ZArith6BinInt1Zinc2leinc2lt25stdpp4baseiq06lookup25stdpp4gmapir64gmapir6bgmap_lookupih67head_ofm76m_next79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~iud4mledih63blkih66extrasm75lheadhi53notih64INVLm76activem77m_availm77m_freedhc5GOODHvf4boolvf4truem79mask_uptoinc4landinc7testbitvf4prodvf4Nonevf3fstvf4pairhi52orih66sstart79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WFree2~~~~~~jt65xpendm74UNITm75ctz32m7aget_stridem7am_last_idxm7asize_classinc3mulm7bm_set_avail89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WTry23TRY~~~~~~kmb7TA_POSTm71Mm76ta_finm79try_availih66x_pendih67x_fresh" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
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
Lemma taf_refl : ltac2:(zQ "30!h9!lc!q5>2st$2>2sc$0@3$1^2^2^1"). Proof. intros st sc. constructor; auto. Qed.
Lemma taf_trans : ltac2:(zQ "30!lc!q5!h9>1a$1>1b$1>1c$1>2sc$2>0@3$0^4^3^1>0@3$0^4^3^2@3$0^6^4^3").
Proof. intros a b c sc.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
  all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
  all: try (intros sc'; rewrite (B8 sc'); apply A8).
  all: split; congruence.
Qed.
Lemma taf_upd_meta : ltac2:(zQ "60!qe!h9!lc!r5!q5!rc>2st$4>1m$3>1f>0$0$0>2sc$1@3$2^4@3$5^3^2^4^1").
Proof. intros st m f sc. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active : ltac2:(zQ "50!h9!lc!q5!s7!se>2st$2>2sc$0>1v$3@3$1^3@3$4^2^1^3^2").
Proof. intros st sc v.
  constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay : ltac2:(zQ "40!h9!lc!tb!q5>2st$3>2sc$0>3sc0$0@3$1^3@2$2^1^3^2").
Proof. intros st sc sc0. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue : ltac2:(zQ "60!h9!lc!ub!r5!v5!q5>2st$5>2sc$0>1m$3@3$1^3@3$4@1$2^2^1^3^2").
Proof. intros st sc m.
  destruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). destruct FC.
  constructor; auto.
  all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
  all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (split; assumption).
Qed.

(* [comment removed for export] *)
Section HEADFACTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : ltac2:(zQ "10!jl1@5$0?1X?2st?1L?2BL?2LS").
Hypothesis HA : ltac2:(zQ "50!hq5!hj9!jl9!r5!s7@3$1$4@2$2?2st?2sc@2$0$3?1m").
Lemma hd_list : ltac2:(zQ "60!r5!hh7!hhe!hj9!hjf!ub@2$4@1$1$0\4rest@1$1$0@3$3@1$1$0@1?2LS@1$5?2sc@3$2$0?1m^1").
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
  destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
Lemma hd_in : ltac2:(zQ "30!ub!r5!hl8@3$2$1?1m@1?2LS@1$0?2sc").
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
Lemma hd_facts : ltac2:(zQ "h80!h9!r5!hle!hm5!hn9!hp4!hpe!hq5!hj9!hjf!hrd!hsc!htb!hve!igd!il4!ila!im8!in1!ip4!ipa!iqc!is2!isa@2$6@2$6@2$h3Z?2sc@2$h4?2sc+j0@2$6@3$8$0@1$h0@2$f?2st?1m?2sc@2$9$1\1b$1@2$9$0\2ai$0@3$8@1$e$2@6$h5$1$2@4$h6$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2@4$h7$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2^2@1$h2?2st@2$7$2@2$h1@2$7$1?1m^1").
Proof.
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C). split; [exact A|]. split; [exact C|]. exists b, ai. exact Hb.
Qed.
Lemma hd_head : ltac2:(zQ "60!hq5!hj9!it9!ub!r5!s7@3$1$5@1$2@1?2LS@1$3?2sc@2$0$4?1m").
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
Lemma hd_next : ltac2:(zQ "a0!r5!hq5!hpe!hj9!hjf!il4!ub!iu4!s7!hl8@2$4$0\2mn$0@2$2@3$3$8@1$7@2$5?2st?1m@2$1$0^1@3$9$0^1@1?2LS@1$6?2sc").
Proof.
  destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _). exists y. auto.
Qed.
End HEADFACTS.

(* [comment removed for export] *)
Definition GOODH : ltac2:(zQ "80!hh7!r5!h9!ji9!jj1!jj8!jk2!q5>1X$5>2st$7>1L$3>2BL@1$0$4>2LS>0$6@1$0$1>2sc$2>1m$1P") := ltac2:(zQ "h20!hpe!hj9!h9!r5!hh7!il4!hq5!jka!ji9!jl1!jj1!jj8!jl9!jk2!jm2!jmc!q5!s7\1X$b\2st$h0\1L$8\2BL@1$4$a\2LS>0$d@1$4$3\2sc$2\1m$3@2$0@5$9^7^6^5^4^3@2$0@3$1$h1@2$c^6^2@2$6$3^1@2$0@3$1$2@1$e@2$5^6^1Z@1$7@3$1$2@1$f@2$5^6^1Z").

Section STEPS.
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : ltac2:(zQ "50!r5!jr2!igd!hj9!kt3@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis HF : ltac2:(zQ "50!r5!jr2!igd!hj9!ktd@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis Hsc : ltac2:(zQ "30!hpe!ip4!ipa@2$0@2$1Z?2sc@2$2?2sc+j0").

(* [comment removed for export] *)
Lemma rotate_ok : ltac2:(zQ "c0!r5!hh7!jk2!hq5!jn6!hj9!hjf!il4!iu4!q5!s7!se>2st$9>2LS>0$2@1$1$0>1m$0>2mn$0>0@7$4?1X^4?1L?2BL^3?2sc^2>0@3$5$a@1$8@2$7^5^3@2$3$0^2@2$6>0$2@1$1$0\3LS'>0$2@1$1$0@7$4?1X@3$b?2sc@2$3$0^4^7?1L?2BL^1?2sc^4").
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

(* [comment removed for export] *)
Lemma dequeue_exhausted_ok : ltac2:(zQ "h40!r5!hj9!hh7!hpe!h9!il4!ub!jk2!s7!hq5!hjf!jl1!it9!jl9!v5!jm2!jmc!hhe!jka!q5>2st$h3>2LS>0$7@1$2$0>1m$0>0@5$b?1X^3?1L?2BL^2>0@3$1$8@2$d^4?2sc@2$9$0^2>0@3$1$4@1$f@2$5^5^3Z>0@3$1$4@1$h0@2$5^6^4Z@2$a>0$7@1$2$0\3LS'>0$7@1$2$0@2$a@1$2$0\4rest@1$2$0@2$3@5$b?1X@3$e@1$6?2sc^7^9?1L?2BL^2@2$3@3$1@1$2$0@1^8@1$6?2sc@3$h1$0^7^1@2$3@3$1$8@2$d@3$e@1$6?2sc^7^9?2sc@1$c^1>2m1$0>0@3$1$8@1$c^2@2$9$0^1@2$3@3$1$4@1$f@2$5^b^2Z@1$h2@3$1$4@1$h0@2$5^b^2Z").
Proof. intros st LS m.
  intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
  assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
  { apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl).
    { destruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _).
      exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ ltac:(rewrite G5; exact Hb))). }
    intros bb aix Hbb.
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
End STEPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_upto_all : ltac2:(zQ "80!h9!ip4!hj9!jne!jo5!joc!jp8!jq0>1f$0>1n$0>0@2$1Z^2>0@2$1Z^2>0>1i$0>0@2$1Z^1>0@3$2$3@2$7^6^2$4@2$1^3^6@3$2$0@2$6^5@1$5^4^5").
Proof. intros f n.
  intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
  destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.

Lemma land_mask_upto_zero_above : ltac2:(zQ "90!h9!ip4!hj9!jne!jo5!joc!jp8!ipa!jq0>1f$0>1n$0>0@2$1Z^2>0@2$1Z^2>0@3$2$0@2$6^4@1$5^3Z>1i$0>0@2$1Z^1>0@3$2$3@2$8^7^2$4@2$7^7^3").
Proof. intros f n.
  intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
  assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
  rewrite H, Z.bits_0 in T. discriminate.
Qed.

Section TRY.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : ltac2:(zQ "50!r5!jr2!igd!hj9!kt3@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis HF : ltac2:(zQ "50!r5!jr2!igd!hj9!ktd@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis Hsc : ltac2:(zQ "30!hpe!ip4!ipa@2$0@2$1Z?2sc@2$2?2sc+j0").

Definition TA_POST : ltac2:(zQ "50!q5!hh7!h9!r5!jk2>2st$0>3st1$0>5first$2>3LS1>0$4@1$1$3P") := ltac2:(zQ "ic0!h9!hpe!hm5!r5!hj9!hle!hq5!jqb!hjf!il4!ip4!hn9!hp4!jl1!jl9!q5!s7!hrd!hsc!htb!hve!jr2!jr9!hh7!igd!jrf!jka!js6!jsc!kh7!lc!ki0!ki7!kif!jk2!kjc!ila!im8!in1!kk9!kl6!iqc!is2!isa\2st$f\3st1$f\5first$0\3LS1>0$i2@1$h7$3@2$1@3$he^4^3?2sc@2$hb@2$1@3$4$0^2Z@2$1@3$4$h0@2$e^3?2sc@1$h5$3@5$d?1X^3?1L?2BL^1@2$8$3\1g$3@2$8@2$7$2$0\2bg@2$7$2$0@2$8$0\2ai$0@2$8$0\3idx$0@2$1@1$ha@3$4$0^6Z@2$1@2$aZ^6@2$1@3$4$0@1$i0^6^1@2$1@3$4$h0@2$e^7?2sc@2$6$3^4@2$1@3$4@1$h8$5@6$i9@2$7$2$0$5@4$ia$3@4$h4$2$b$0$c@6$h3$2$b$h1$0$c$h2$5@4$ib$3@4$h4$2$b$0$c@6$h3$2$b$h1$0$c$h2$5^3@1$i6^7@2$6$5@2$i5@2$6$3^4^2@2$1@2$1@2$aZ^1@2$a^1@1$i3@2$9^7^4@2$1@3$4$0@1$i4@2$9^7^4?2sc@2$1@2$a@2$i8$hf@1$i7?2sc@1$i1@2$9^7^4@5$d@2$hd?1X@2$6@2$7$2$0@4$h9$2$0@3$h6$2$0^3@2$hc@2$9^7^4^1^7?1L?2BL^5").

Lemma set_avail_views : ltac2:(zQ "90!h9!hj9!kld!hpe!jsc!kif!kjc!ila!qe>1v$0>1r$8@2$3@3$1$0@1$6@2$2^2^1@1$6^1@2$3@3$1$0@1$7@2$2^2^1@1$7^1@2$3@3$1$0@1$5@2$2^2^1@1$5^1>1i$0@3$1$0@2$4@2$2^3^2^1@2$4^2^1").
Proof. intros v r. destruct r; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fin_ok : ltac2:(zQ "h30!h9!r5!hj9!q5!hh7!hjf!jk2!hq5!hpe!jka!jl1!il4!lc!kqf!kra!jl9!jm2!s7!kre>3st0$3>2st$3>2LS>0$6@1$4$1>1m$1>4mask$0>0@5$a?1X^4?1L?2BL^3>0@3$c^6^5?2sc>0@3$2$h1@2$f^6?2sc@2$7$1^4>0@3$2$0@1$h0@2$b^7^5^4>0@1$9@3$2$0^5Z@2$5$3\3st1$3@2$5$0\5first$0@2$5>0$6@1$4$1\3LS1>0$6@1$4$1@2$8@3$2@1$e?1T@5$h2?1T^c^a^9?1k@2?1k^3^2@4$d^d^3^2^1").
Proof. intros st0 st LS m mask.
  intros INV TF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_ok : ltac2:(zQ "c0!hh7!hjf!r5!jk2!q5!h9!hpe!hj9!jl1!kqf!kra!ks7>2st$4>2LS>0$3@1$0$2>0@5$8?1X^2?1L?2BL^1@2$1$4\3st1$4@2$1$5\5first$5@2$1>0$3@1$0$2\3LS1>0$3@1$0$2@2$6@3$7@1$a?1T@5$b?1T?2sc^6?1k?4bail@2?1k^3^2@4$9^6^3^2^1").
Proof. intros st LS.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
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
      + (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
End TRY.
