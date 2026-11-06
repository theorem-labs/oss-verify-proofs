(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~he6extras79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m54aptr04None03nil37Corelib7Numbers7BinNumsr51Nhe3mkXm56mstatem56region37Corelib4Init5Logicua2eq25stdpp9countablehg3bN_countable35stdpp7numbers1Nhi36eq_dec04Some06optionm59s_regionsm58s_secret25stdpp4basehm36lookup25stdpp4gmaphn94gmaphn9bgmap_lookupua3andr51Zm57RKGroupm56r_kindm55rkind79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WSlot~~~~~~hs12GP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WAMeta~~~~~~ig78AM_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WTry2~~~~~~il48TA_frame04prodm54metam54optr04pairm5am_last_idxm58m_maplenm55m_memm5bm_sizeclasshe6cnt_ofhe6sstarths16geo_ofm5aget_stridem54ghdr35stdpp7numbers1Zjh86eq_dechg3bZ_countablehg3eprod_countable25stdpp9decidablejl4bprod_eq_deche2MRm58s_groups79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_TF2~~~~~~jo49geom_keptm55meta0m57s_metasm58put_metahe5hostsm57LActivem59mask_upto46Stdlib6ZArith6BinInt1Zkga5ldiffkga2lekga3subkga3leb04andb04boolkga7testbit04conshe4INVLhs14X_asua3not36Stdlib5Lists4Listkn12Inm56mkGhdrm56mkMetakga2ltm56activem54UNITm5asize_classkga3muljo43TF2" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition X_as : ltac2:(zQ "30!h8!lc!q3>4idle@1$0$2$1") := ltac2:(zQ "60!q3!qa!h8!r0!se!t2\4idle@1$2$0@5$5^1@1$3$0@1$1$0@1$1$4@1$1$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GP : ltac2:(zQ "10!t8>2st$0>3st'$0P") := ltac2:(zQ "h20!u1!se!ve!hh4!hj4!hje!hk4!t8!hkc!hl8!hmf!ho5!hod!hpc!hq2!hq6!hr0!hr9\2st$7\3st'$7@2$d>3rid$1>1r$0>0@3$2@1$6$0@6$a$1$0@4$b$1$4$3$0@4$c$1$4$3$0^2@1$8^4@2$5$0^1>0@3$2$h1@1$h0^2$f@3$2@1$6$0@6$a$1$0@4$b$1$4$3$0@4$c$1$4$3$0^4@1$8^5@2$5$0^3@3$2$e@1$9^1@1$9^2").
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans : ltac2:(zQ "20!ig1!t8>1a$1>1b$1>1c$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros a b c. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq : ltac2:(zQ "b0!ve!t8!hkc!hl8!se!hq2!ig1!u1!hh4!ho5!hj4>2st$1>3st'$1>0@3$0@4$9$4$a$8$7@1$2^1@1$2^2>0@3$0$5@1$3^2@1$3^3@2$6^4^3").
Proof. intros st st'. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf : ltac2:(zQ "30!t8!ik8!ig1>2st$0>3st'$0>0@2$1^2^1@2$2^3^2").
Proof. intros st st'. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf : ltac2:(zQ "40!t8!hq2!ig1!ip4>2st$0>3st'$0>2sc$1>0@3$3^3^2^1@2$2^4^3").
Proof. intros st st' sc. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geo_of : ltac2:(zQ "40!iq0!hq2!iq6!iqd>1r$2@2$0@2$0@2$0$3$1$1$1") := ltac2:(zQ "90!hq2!ir4!iq0!iqd!ira!is7!it2!ita!iq6\1r$8@4$1@2$2@2$2$3$0$0$0@4$1@2$2$3$0$0@4$1$3$0@1$6^1@1$4^1@1$5^1@1$7^1").

Lemma geo_facts : ltac2:(zQ "b0!hq2!ve!iq0!hpc!iu8!iv1!iva!jg4!is7!iq6!iqd>1r$9>2r'$9>0@3$1@2$2@2$2@2$2$a$0$0$0@1$6^1@1$6^2@2$3>1i$0@3$1$0@2$5^3^1@2$5^4^1@2$3@3$1$0@1$4^2@1$4^3@2$3@3$1$0@1$8^2@1$8^3@3$1$0@1$7^2@1$7^3").
Proof. intros r r'.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo : ltac2:(zQ "h72!hq2!jh1!se!q3!hj4!ji9!hh4!jj3!jk2!jm5!iq0!ve!hje!hk4!jn4!iva!t8!jn9!hmf!ho5!hod!js2!iqd&@4$h3$3@4$9$2$4$0$5@6$8$2$4$6$0$5$7$1&@4$h4$3@4$9$2$4$0$5@6$8$2$4$6$0$5$7$1>2st$h0>3st'$h0>0>1b$3>1h$1>0@3$b@1$d$1@6$h2$3$1~0~1^2@1$h1^4@2$c$1^1@3$b@1$d$1@6$h2$3$1~0~1^3@1$h1^4@2$c$1^2>0>1x$3@3$b@2$a@2$a@2$a$h6$0$0$0@1$f@2$e^3^1@1$f@2$e^4^1@2$h5^4^3").
Proof. intros st st'.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "40!kl6!klc!km3!q3@5$1@1$2@3$0$3?1m?4idle?2st?1L?2BL?2LS").
Hypothesis NIm : ltac2:(zQ "30!kmb!q3!ko4@1$0@3$2$1?1m?4idle").
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : ltac2:(zQ "h20!iq6!se!hq2!hj4!ji9!q3!hh4!jj3!jk2!jm5!hje!hk4!ve!jsf!jt7!hmf!ho5!hod@3$c@1$b$0@6$f$5$0@4$h0$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0@4$h1$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0?1m@1$e?2st@2$a$0$d").
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : ltac2:(zQ "40!ve!jsf!t8!ju1@3$0$2@3$3?1m$1?2st?2st").
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (X_as (m :: idle)) st L BL LS m LFree INV ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| split; [left; reflexivity| tauto]])) as INV2.
  unfold XQ in INV2. cbn [xidle x_idle x_zomb x_pend x_orph x_fresh X_as] in INV2. rewrite (rem_cons_self m idle NIm) in INV2.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : ltac2:(zQ "h20!jh1!se!hq2!q3!hj4!ji9!hje!hh4!jj3!jk2!jm5!hk4!ve!koa!jn9!hmf!ho5!hod@3$c@1$b$0@6$f$3$0@4$h0$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0@4$h1$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0?1b@1$e?3st2@2$6$0@2$d@2$6$3?1m?2ai").
Hypothesis Em : ltac2:(zQ "90!q3!jve!qa!hje!ve!jn4!iq6!kp3!kj1@3$4$6@2$5?3st2?1m@9$7@1$2$0@1$2$0@2$3$0?1b@1$1?2ai@2$8@1$1?4last@1$1?2ai?4last+1?2sc?2ml").
Hypothesis Hai : ltac2:(zQ "20!kib!hpc@2$1@2$0Z?2ai@2$0?2ai?4last").
Hypothesis Hl : ltac2:(zQ "10!kib@2$0?4last+hf").
Hypothesis Hsc : ltac2:(zQ "30!hpc!kib!kpc@2$0@2$1Z?2sc@2$2?2sc+j0").
Hypothesis HA : ltac2:(zQ "50!qa!ve!kq2!q3!iqd@3$1$4@2$2?3st2?2sc@1$0$3").
Hypothesis UND : ltac2:(zQ "90!ve!hq2!hpc!jn4!kqb!jg4!kr2!kpc!krf>0@2$7@1$5@2$3?3st2?1m@2$8$4@1$6?2sc@2$2@3$0$1?2aiZ@3$0$1?4lastZ").
Hypothesis TF : ltac2:(zQ "10!ks6@1$0?3st2").

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : ltac2:(zQ "10!juc@3$0?3st2?1b?1m"). Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : ltac2:(zQ "50!q3!h8!r0!ve!jv4@3$3@1$1$0@1?2LS@1$4?2sc@1$2$0").
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred : ltac2:(zQ "60!hq2!jve!ve!ki2!kib!kj1>1a$0>0@2$4Z^1@3$2$0@2$5@1$1^2+1@2$3@1$1^2+1").
Proof. intros a.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' : ltac2:(zQ "90!kj8!kjf!kk5!ve!hq2!jve!kib!kj1!kkb>1i$4>0@2$6Z^1@3$3$2@2$8@2$7@1$5?2ai+1^2@2$1@2$0+1^2@2$0^2?2ai").
Proof. intros i.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros E63. exfalso. rewrite Em in E63. cbn in E63. lia.
  - intros AF. exfalso. pose proof (f_equal (fun z => Z.testbit z 0) AF) as TT. cbn beta in TT.
    rewrite Z.lor_spec, testbit_avail', Elast, testbit_mask_upto in TT by lia.
    destruct (Z.testbit (mask_upto last - mask_upto ai) 0) eqn:F0; [exact (M5 0 ltac:(lia) (M7 0 ltac:(lia)) F0)|].
    cbn in TT. replace (0 <=? last) with true in TT by (symmetry; apply Z.leb_le; lia). discriminate.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2
    /\ s_areas st4 = s_areas st2.
Proof.
  exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  { (* [comment removed for export] *)
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV4))))) _ _ _ ltac:(rewrite G4; exact Hb))). }
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity|]. split; [rewrite F8; reflexivity| rewrite F4; reflexivity].
Qed.
End FINISH.
