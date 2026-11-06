(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~06extras37Corelib4Init9Datatypesk66option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m74aptr03mkX06x_idle06x_orph06x_pend06x_zombm74meta37Corelib4Init5Logict82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_List~~~~~~v17data_ofk64Nonet83iffm76m_nextm76m_prevm75meta0m76mkMetam75m_memm74optr02MRt83and37Corelib7Numbers7BinNumsho31Zm77m_availm7am_freeablem77m_freedm7am_last_idxm78m_maplenm7bm_sizeclassm7aget_stride05gbase06sstartm7bslot_start'06cnt_of04gend79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres4~~~~~~ii0dctx_but_headsm74mctxm75s_ctxm75lheadm76mstatem78set_headk64list05inv_Lv18lists_okk63nil07head_ofk63appk64const83not05hosts0alive_group08frontierho31Nm76regionm75usage04gcnt04INVL35stdpp7numbers1Njh66eq_dec35stdpp7numbers1Zjj16eq_dec25stdpp9countablejkcbN_countablejkcbZ_countablejkceprod_countable25stdpp9decidablejodbprod_eq_decm77s_metas25stdpp4basejr76lookup25stdpp4gmapjsd4gmapjsdbgmap_lookupk64Some36Stdlib5Lists4Listjv72Int82orv14fupdm75LFreem77LActive46Stdlib6ZArith6BinInt1Zkie2lekie2ltm78c_active07in_listm74ghdrt82exm78s_groups08group_okm76mkGhdrm78get_head79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~kpb4mled03blk07x_freshii06xfreshk64prodk64pairt85Falsem74PGSZkie3mulm74UNITm7asize_classm77s_areasm7as_next_ridm79s_regionsm7as_reservedm78s_secretm78s_shadowm77s_slotsm76s_tickv18queue_stm74aream76shadowm77dequeue79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres3~~~~~~lqd3remlqd5xidle89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres45QUEUE~~~~~~lvd2XQ" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition xfresh : ltac2:(zQ "30!je!le!q5>1X$0>1f@1$1$2$0") := ltac2:(zQ "80!le!je!qc!r1!r9!s1!s9!q5\1X$1\1f@1$0$7@5$2@1$3^2@1$6^2@1$5^2@1$4^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma data0_shape : ltac2:(zQ "a0!t1!uc!hj0!hja!hk1!q5!hk7!hl0!hl9!hm1>1r$0@2$4@3$1$0@1$2^1@1$2$8@3$1$0^1@9$9@1$7^1@1$6^1@1$3$5ZZZZZZ").
Proof. intros r.
  destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.

Lemma data0_mem : ltac2:(zQ "80!uc!hj0!t1!hja!q5!hma!hl9!hn2>1r$2>0@3$0$2@1$1^1@1$1$6@3$0$7@1$5^2@1$3$4").
Proof. intros r. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.

Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : ltac2:(zQ "50!hn9!hj0!uc!q5!t1>1x$3@3$2$4@1$1@2$0?3st'^1@1$1@2$0?2st^1").
Lemma de_fields : ltac2:(zQ "d0!hn9!uc!hnd!hpc!hq1!hqb!hr8!hs2!hsf!hma!hta!q5!hn2>1x$b@2$2@3$1$c@1$9@2$0?3st'^1@1$9@2$0?2st^1@2$2@3$1$3@1$4@2$0?3st'^1@1$4@2$0?2st^1@2$2@3$1$3@1$6@2$0?3st'^1@1$6@2$0?2st^1@2$2@3$1$3@1$7@2$0?3st'^1@1$7@2$0?2st^1@2$2@3$1$3@1$5@2$0?3st'^1@1$5@2$0?2st^1@2$2@3$1$3@1$a@2$0?3st'^1@1$a@2$0?2st^1@3$1$3@1$8@2$0?3st'^1@1$8@2$0?2st^1").
Proof. intros x. apply data_of_eq. apply DE. Qed.
Lemma de_mem : ltac2:(zQ "50!hn9!hma!uc!q5!hn2>1x$3@3$2$4@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_avail : ltac2:(zQ "50!hn9!hq1!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_freed : ltac2:(zQ "50!hn9!hr8!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_last : ltac2:(zQ "50!hn9!hs2!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_freeable : ltac2:(zQ "50!hn9!hqb!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_sc : ltac2:(zQ "50!hn9!hta!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_maplen : ltac2:(zQ "50!hn9!hsf!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply de_fields. Qed.
Lemma de_stride : ltac2:(zQ "50!hn9!hu8!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. apply get_stride_data. apply DE. Qed.
Lemma de_gbase : ltac2:(zQ "40!hn9!hv5!q5!uc>1x$2@3$3$2@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. unfold gbase. rewrite de_mem. reflexivity. Qed.
Lemma de_sstart : ltac2:(zQ "50!hpc!hn9!hvc!uc!q5>1x$4>1i$0@3$3$0@2$2@2$1?3st'^2^1@2$2@2$1?2st^2^1"). Proof. intros x i. unfold sstart. rewrite de_gbase, de_stride. reflexivity. Qed.
Lemma de_slot_start' : ltac2:(zQ "50!hn9!q5!ig4!uc!hpc>1x$1>1i$4@3$3$1@2$2@2$0?3st'^2^1@2$2@2$0?2st^2^1").
Proof. intros x i. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
Lemma de_cnt : ltac2:(zQ "50!hn9!ih2!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. unfold cnt_of. rewrite de_last. reflexivity. Qed.
Lemma de_gend : ltac2:(zQ "50!hn9!iha!uc!hpc!q5>1x$4@3$2$3@1$1@2$0?3st'^1@1$1@2$0?2st^1"). Proof. intros x. unfold gend. rewrite de_sstart, de_cnt. reflexivity. Qed.
End DEXT.

(* [comment removed for export] *)
Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
  cb_secret : c_secret c' = c_secret c;
  cb_init : c_init_done c' = c_init_done c;
  cb_mc : c_mmap_counter c' = c_mmap_counter c;
  cb_am : c_avail_meta c' = c_avail_meta c;
  cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cb_mah : c_meta_area_head c' = c_meta_area_head c;
  cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cb_usage : c_usage c' = c_usage c;
  cb_unmap : c_unmap_seq c' = c_unmap_seq c;
  cb_bounces : c_bounces c' = c_bounces c;
  cb_seq : c_seq c' = c_seq c;
  cb_brk : c_brk c' = c_brk c
}.
Lemma cbh_refl : ltac2:(zQ "20!im0!in1>1c$1@2$0^1^1"). Proof. intros c. constructor; reflexivity. Qed.
Lemma cbh_set_head : ltac2:(zQ "60!in8!im0!io0!io8!hn2!ip1>2st$3>1h$2>1v$4@2$1@1$0^3@1$0@3$5^2^1^3").
Proof. intros st h v. destruct h; constructor; reflexivity. Qed.

Lemma inv_L_lists : ltac2:(zQ "60!ipc!iq3!iqa!q5!io0!io8>2st$5>2LS>0$4@1$0$3>0@2$1^2^1@2$2^3^2").
Proof. intros st LS. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.

Lemma head_of_app : ltac2:(zQ "90!q5!ipc!ir5!uc!irb!is4!isa!it1!hn2>1l@1$1$0>1g$0>0@1$7@3$3@1$1$0^2@1$2$0@3$3$8@1$4@3$5$0^3@3$6$0^2@1$2$0@1$4^3").
Proof. intros l g. destruct l; cbn; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!jh0@5$0?1X?2st?1L?2BL?2LS").
Hypothesis DE : ltac2:(zQ "50!hn9!hj0!uc!q5!t1>1x$3@3$2$4@1$1@2$0?3st'^1@1$1@2$0?2st^1").
Hypothesis KEYS : ltac2:(zQ "h32!t1!iv4!hpc!ji7!jk2!q5!jld!jmc!jnb!jpe!hja!le!uc!it1!jqd!js3!jt9!ju1!hk1&@4$h0$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0&@4$h1$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0>1x$5@2$h2@1$d@3$c@1$b$0@6$f$5$0~0~1^1@1$e?3st'@1$a$0@1$d@3$c@1$b$0@6$f$5$0~0~1^1@1$e?2st@1$a$0").
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
           (HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
           (HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st).
Hypothesis HC : ltac2:(zQ "20!in8!im0@2$1@1$0?2st@1$0?3st'").
Hypothesis XE : ltac2:(zQ "90!uc!le!hnd!r9!s1!s9!q5!ipc!iv4@2$2@3$0@1$1$6@1$4?2X'@1$4?1X@2$2@3$0@1$1$8@1$3?2X'@1$3?1X@3$0@1$7$6@1$5?2X'@1$5?1X").
Hypothesis LO' : ltac2:(zQ "10!iqa@2$0?3st'?3LS'").
Hypothesis H_free : ltac2:(zQ "80!hj0!q5!uc!hn9!khc!t1!hl9!kga>1m$1>0@3$7$1^1@1?3LS'$4@3$2$5@1$0@2$3?2st^2@1$0$6").
Hypothesis H_active : ltac2:(zQ "b0!hnd!hpc!q5!uc!hn9!ite!ki4!hta!kga!kk6!kkc>2sc$1>1m$2>0@3$8$2^1@1?3LS'@1$6^2@2$0@2$0@2$9Z^3@2$a^3+j0@2$0@2$5?2st^2@3$3$1@1$7@2$4?2st^2^3").
Hypothesis H_keys : ltac2:(zQ "a0!q5!ipc!ir5!hnd!uc!it1!hpc!ki4!kk6!kkc>2sc$6>0@1$5@3$4@1$1$0@1?3LS'@1$7^1@1$2$0@2$3@2$8Z^2@2$9^2+j0").
Hypothesis H_actkeys : ltac2:(zQ "f0!q5!hpc!jmc!jk2!jv0!le!hnd!uc!kl2!in8!kk6!kkc!js3!jt9!ju1>2sc$1>1g$0>0@3$7@1$5$0@6$c$1$0@4$d$1$3$2$0@4$e$1$3$2$0^2@1$8@1$9?3st'@2$4$0^1@2$6@2$aZ^3@2$b^3+j0").
Hypothesis H_idle : ltac2:(zQ "h70!q5!t1!iv4!hpc!ji7!jk2!jld!jmc!jnb!jpe!jv0!le!hnd!uc!it1!kld!r1!hl9!jqd!kga!js3!jt9!ju1>1m$0>0@3$h3$0^1@1$h0?2X'@2$c@3$d@1$b$1@6$h4$0$1@4$h5$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1@4$h6$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1^2@1$h2?3st'@2$a$1$h1@1$e@2$f?3LS'^2").
Hypothesis H_zomb : ltac2:(zQ "c0!q5!hja!hnd!uc!hn9!hn2!it1!kld!s9!hk7!hl0!kga>1z$0>0@3$b$0^1@1$8?1X@2$2@3$3$5@1$9@2$4?3st'^2@1$1$0@2$2@3$3$5@1$a@2$4?3st'^2@1$1$0@1$6@2$7?3LS'^2").
Hypothesis H_groups : ltac2:(zQ "i33!q5!uc!hpc!hn9!it1!jv0!hnd!le!km6!hta!iv4!ku4!kkc!ji7!jk2!ki4!hq1!hr8!kld!kga!jld!jmc!jnb!jpe!irb!lhb!hu8!hs2!ko7!kn2!li2!lh4!js3!jt9!ju1&@3$1@1$7$0@1$b?2X'@2$5$0^4&@1$4~0&@2$6@3$1$2@1$h0@2$3?2st^7Z@3$1$2@1$h1@2$3?2st^7Z>1m$0>1b$0>2ai$2>0@3$1@1$7$8@6$i0$0$8@4$i1$0@4$h7$a$d$2$e@6$h6$a$d$h4$2$e$h5$8@4$i2$0@4$h7$a$d$2$e@6$h6$a$d$h4$2$e$h5$8^2@1$hd?2st@2$5$8@2$hc@2$5$0^3^1@2$6>0~1>0@2$c^3@1$hb@2$3?2st^5@3$h3$0^6@1?3LS'@1$f@1$9@2$3?2st^6@2$6>0~1>0@2$c@1$9@2$3?2st^5+j0>0@1$4@2$h2?3LS'^6~2@2$6>0~1>2sc$2>0@3$h3$0^6@1?3LS'@1$f^1>0@1$4@3$1@1$7$0@2$5$0^7@1$h8@1?3LS'@1$f^2@2$6@3$1$2@1$h0@2$3?2st^8Z@1$4@3$1$2@1$h1@2$3?2st^8Z@2$6>0@3$1$2@1$9@2$3?2st^4+jf@1$4@2$h2?3LS'^5>0~1>0@2$c@1$9@2$3?2st^5+j0>0@2$c@1$ha@2$3?2st^6@2$hf$h9@1$he@1$9@2$3?2st^6~2").
(* [comment removed for export] *)
Hypothesis H_all : ltac2:(zQ "h80!q5!t1!iv4!hpc!ji7!jk2!kh0!kga!jld!jmc!jnb!jpe!hja!le!uc!it1!kld!ite!r1!s9!jqd!js3!jt9!ju1>1m$0>0@1$f@3$e@1$d$1@6$h5$0$1@4$h6$0@4$b$2$4$3$5@6$a$2$4$8$3$5$9$1@4$h7$0@4$b$2$4$3$5@6$a$2$4$8$3$5$9$1^1@1$h4?2st@1$c$1@2$6@2$h1?2st^2@2$6@2$h0?3LS'^2@2$6@3$7$0^2@1$h2?2X'@3$7$0^2@1$h3?1X").
(* [comment removed for export] *)
Hypothesis XF : ltac2:(zQ "c0!iv4!hpc!jv0!le!kve!kv7!uc!ku4!lgd!q5!lh4!kk6>3rid$0>1q$1>0@2$b+1^1>0@3$6@1$3$9@1$7?1X@2$2@2$5$0$1@4$4$0$1^3@2$a^2$8@3$6@1$3$9@1$7?2X'@2$2@2$5$0$1@4$4$0$1^4@2$a^3$8").

Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.

Lemma rl_hosts : ltac2:(zQ "30!it7!q5!hk1>1b$1>1m$1@2$2@3$0?3st'^2^1@3$0?2st^2^1"). Proof. intros b m. apply hosts_ext. exact HG. Qed.
Lemma rl_live : ltac2:(zQ "30!ite!hk1!q5>1m$2@2$1@2$0?3st'^1@2$0?2st^1"). Proof. intros m. apply live_group_ext. exact HG. Qed.
Lemma rl_frontier : ltac2:(zQ "50!iua!uc!iv4!hpc!iv9>3rid$2>1r$4@3$1$3@3$0?3st'^2^1@3$0?2st^2^1").
Proof. intros rid r. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
Lemma rl_usage : ltac2:(zQ "30!hpc!jg2!uc>2sc$0@3$2$0@2$1?3st'^1@2$1?2st^1").
Proof. intros sc. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
Lemma rl_gcnt : ltac2:(zQ "30!hpc!jga!uc>2sc$0@3$2$0@2$1?3st'^1@2$1?2st^1").
Proof. intros sc.
  apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.

Theorem INVL_relink : ltac2:(zQ "10!jh0@5$0?2X'?3st'?1L?2BL?3LS'").
Proof.
  destruct XE as (XP & XO & XZ).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
    + intros rid r q H1 H2 H3 H4 H5. rewrite HA. rewrite rl_frontier in H4. apply (ir_pages rid r q H1 H2 H3 H4). intros E. apply H5. exact (XF rid q H3 E).
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
    + intros a ar k Ha Hk Ht. apply KEYS. exact (ia_carved a ar k Ha Hk Ht).
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5 MAL]; constructor.
    + intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
    + intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
    + intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
    + exact H_idle.
    + intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
      split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
    + intros m Hm. apply KEYS in Hm. rewrite rl_live, XZ. exact (H_all m Hm).
  - (* [comment removed for export] *) destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
    + intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
    + intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
    + intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5 GOE]; constructor.
    + intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
      destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
      * apply KEYS. exact g_present.
      * destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
      * intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
    + intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
    + intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. unfold allfree. rewrite !davail, !dfreed, !dlast, !dsc. eapply GOE; eassumption.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6 SBG]; constructor.
    + intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
    + intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
    + intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
    + intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
    + intros k m i Hk H1 H2. rewrite HS in H1. rewrite dsc in H2. rewrite HR. eapply SBG; eassumption.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); auto.
Qed.
End RELINK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma present_MR : ltac2:(zQ "h52!t1!iv4!hpc!ji7!jk2!q5!jld!jmc!jnb!jpe!le!uc!jqd!js3!jt9!ju1!hja!jv0!it1!hn9!io8&@4$e$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0&@4$f$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0>2st$h4>1x$5>0@1$h2@3$b@1$a$0@6$d$5$0~0~1^1@1$c^2@1$h0$0@3$b@1$a$0@6$d$5$0~0~1^2@1$c^3@2$h1$0@2$h3^3^2").
Proof. intros st x. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.

Lemma fupd_in : ltac2:(zQ "a0!q5!io0!kga!ipc!hnd!uc!hk1!it1!kh0!kh5>2LS>0$1@1$3$0>1h$1>1l@1$3$0>2h'$1>1m$0@2$6@3$2$0^1@4$9^5^4^3^2@2$8@2$4@3$5$1^2^4@3$2$0^1^3@2$4@1$7@3$5$1^2^4@3$2$0^1@1^5^2").
Proof. intros LS h l h' m.
  unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
  all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.

Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!jh0@5$0?1X?2st?1L?2BL?2LS").

Lemma old_lists : ltac2:(zQ "10!iqa@2$0?2st?2LS"). Proof. apply inv_L_lists. exact (proj1 (proj2 (proj2 (proj2 INV)))). Qed.
Lemma old_free : ltac2:(zQ "80!hj0!q5!uc!hn9!khc!t1!hl9!kga>1m$1>0@3$7$1^1@1?2LS$4@3$2$5@1$0@2$3?2st^2@1$0$6").
Proof. intros m. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
Lemma old_active : ltac2:(zQ "b0!hnd!hpc!q5!uc!hn9!ite!ki4!hta!kga!kk6!kkc>2sc$1>1m$2>0@3$8$2^1@1?2LS@1$6^2@2$0@2$0@2$9Z^3@2$a^3+j0@2$0@2$5?2st^2@3$3$1@1$7@2$4?2st^2^3").
Proof. intros sc m. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
Lemma old_keys : ltac2:(zQ "a0!q5!ipc!ir5!hnd!uc!it1!hpc!ki4!kk6!kkc>2sc$6>0@1$5@3$4@1$1$0@1?2LS@1$7^1@1$2$0@2$3@2$8Z^2@2$9^2+j0").
Proof. intros sc. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
Lemma old_actkeys : ltac2:(zQ "f0!q5!hpc!jmc!jk2!jv0!le!hnd!uc!kl2!in8!kk6!kkc!js3!jt9!ju1>2sc$1>1g$0>0@3$7@1$5$0@6$c$1$0@4$d$1$3$2$0@4$e$1$3$2$0^2@1$8@1$9?2st@2$4$0^1@2$6@2$aZ^3@2$b^3+j0").
Proof. intros sc g. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
Lemma old_idle : ltac2:(zQ "h70!q5!t1!iv4!hpc!ji7!jk2!jld!jmc!jnb!jpe!jv0!le!hnd!uc!it1!kld!r1!hl9!jqd!kga!js3!jt9!ju1>1m$0>0@3$h3$0^1@1$h0?1X@2$c@3$d@1$b$1@6$h4$0$1@4$h5$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1@4$h6$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1^2@1$h2?2st@2$a$1$h1@1$e@2$f?2LS^2").
Proof. intros m. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
Lemma old_zomb : ltac2:(zQ "hd0!q5!km6!hnd!uc!iv4!hpc!ji7!jk2!hja!hn9!hn2!jld!jmc!jnb!jpe!jv0!le!kmd!it1!kld!s9!hma!hk7!hl0!kn2!kga!js3!jt9!ju1>1z$0>0@3$h9$0^1@1$h4?1X@2$2@3$3$a@1$h6@2$9?2st^2@1$8$0@2$2@3$3$a@1$h7@2$9?2st^2@1$8$0@2$2@1$h2@2$h3?2LS^2@2$h1$0\1b$0@2$2@3$3$a@1$h5@2$9?2st^3@2$f$0^1@3$3@1$h0$1@6$ha$0$1@4$hb$0@4$e$4$6$5$7@6$d$4$6$b$5$7$c$1@4$hc$0@4$e$4$6$5$7@6$d$4$6$b$5$7$c$1^1@1$h8?2st@1$8$1").
Proof. intros z. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
Lemma old_group : ltac2:(zQ "h30!q5!hpc!km6!iv4!ji7!jk2!jv0!jld!jmc!jnb!jpe!le!uc!knd!ko7!kn2!js3!jt9!ju1>1m$0>1b$0>2ai$1>0@3$c@1$b$2@6$h0$0$2@4$h1$0@4$a$3$4$1$5@6$9$3$4$7$1$5$8$2@4$h2$0@4$a$3$4$1$5@6$9$3$4$7$1$5$8$2^2@1$f?2st@2$6$2@2$e@2$6$0^3^1@6$d?1X?2st?2LS^4^3^2").
Proof. intros m b ai. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
Lemma old_63 : ltac2:(zQ "h60!hpc!q5!km6!iv4!ji7!jk2!jv0!uc!jld!jmc!jnb!jpe!le!it1!hn9!kld!hta!ko7!kn2!js3!jt9!ju1>1m$1>1b$1>2ai$0>0@3$7@1$c$2@6$h3$1$2@4$h4$1@4$b$3$4$0$5@6$a$3$4$8$0$5$9$2@4$h5$1@4$b$3$4$0$5@6$a$3$4$8$0$5$9$2^2@1$h2?2st@2$6$2@2$h1@2$6$1^3^1>0@3$7$0@1$h0@2$e?2st^4+jf@1$d@2$f?2LS^5").
Proof. intros m b ai. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.
(* [comment removed for export] *)
Lemma listed_next : ltac2:(zQ "90!q5!hja!uc!it1!hn9!io0!hk7!hn2!kga>1m$0>1h$5>0@3$8$0^2@1?2LS^1@1$3@3$2$7@1$6@2$4?2st^3@1$1$0").
Proof. intros m h. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
Lemma listed_present : ltac2:(zQ "h40!q5!t1!iv4!hpc!ji7!jk2!jld!jmc!jnb!jpe!hja!le!uc!it1!io0!jqd!kga!js3!jt9!ju1>1m$0>1h$e>0@3$h0$0^2@1?2LS^1@1$d@3$c@1$b$1@6$h1$0$1@4$h2$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1@4$h3$0@4$9$2$4$3$5@6$8$2$4$6$3$5$7$1^3@1$f?2st@1$a$1").
Proof. intros m h. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
Lemma head_listed : ltac2:(zQ "70!q5!jv0!uc!kp0!io0!hn2!kga>1h$4>1a$0>0@3$2$5@2$3?2st^2@2$1$0^1@3$6$0^2@1?2LS^3").
Proof. intros h a. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
Lemma prev_listed : ltac2:(zQ "80!q5!kga!jv0!uc!hn9!io0!hl0!hn2>1h$5>1a$0>1x$0>0@3$1$0^2@1?2LS^3>0@3$3$7@1$6@2$4?2st^3@2$2$0^2@3$1$0^3@1?2LS^5").
Proof. intros h a x. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
Lemma next_listed : ltac2:(zQ "80!q5!kga!jv0!uc!hn9!io0!hk7!hn2>1h$5>1a$0>1x$0>0@3$1$0^2@1?2LS^3>0@3$3$7@1$6@2$4?2st^3@2$2$0^2@3$1$0^3@1?2LS^5").
Proof. intros h a x. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
Lemma idle_unlisted : ltac2:(zQ "50!q5!kga!it1!r1!io0>1m$0>1h$4>0@3$1$0^2@1$3?1X@1$2@3$1$0^3@1?2LS^2").
Proof. intros m h. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
Lemma zomb_unlisted : ltac2:(zQ "50!q5!kga!it1!s9!io0>1z$0>1h$4>0@3$1$0^2@1$3?1X@1$2@3$1$0^3@1?2LS^2").
Proof. intros z h. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
Lemma idle_not_live : ltac2:(zQ "50!q5!it1!ite!r1!kga>1m$0>0@3$4$0^1@1$3?1X@1$1@2$2?2st^2").
Proof. intros m.
  intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
Lemma zomb_not_live : ltac2:(zQ "50!q5!it1!ite!s9!kga>1z$0>0@3$4$0^1@1$3?1X@1$1@2$2?2st^2").
Proof. intros z.
  intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
Lemma free_not_live : ltac2:(zQ "50!q5!it1!ite!khc!kga>1m$0>0@3$4$0^1@1?2LS$3@1$1@2$2?2st^2").
Proof. intros m.
  intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_set_fresh : ltac2:(zQ "d0!q5!ipc!le!jh0!hja!uc!kt7!ktf!je!ku4!kud!io0!io8>1X$8>2st$c>1L$6>2BL@1$1$7>2LS>0$b@1$1$0>1f@1$2$0>0@5$3^6^5^4^3^2>0@3$5@1$2$0@1$9^7@1$4$0@5$3@2$a^8^3^7^6^5^4").
Proof. intros X st L BL LS f.
  intros INV HF.
  refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
    split; [| split; [| split; [| split]]].
    + intros _. exact (g_partial _ _ _ _ _ _ GO NF).
    + intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
    + intros _. exact (g_rest _ _ _ _ _ _ GO NF).
    + exact (old_63 _ _ _ _ _ INV m b ai Hb).
    + intros _. exact (g_under _ _ _ _ _ _ GO NF).
  - cbn. exact (im_all _ _ _ (proj1 (proj2 (proj2 INV)))).
  - intros rid q _ E. rewrite HF in E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma meta_not_page : ltac2:(zQ "hf0!iv4!hpc!t1!ji7!jk2!kv7!q5!ipc!uc!jld!jmc!jnb!jpe!hja!le!kve!lg5!it1!kt7!jh0!ktf!je!lgd!io0!io8!jqd!kk6!lh4!js3!jt9!ju1>1X$h5>2st$h8>1L$h2>2BL@1$7$h4>2LS>0$h7@1$7$6>1m@2$5$0$1>3rid$0>1q$1>0@5$h3^8^7^6^5^4>0@1$h1@3$8@1$e$2@6$hc@2$5$0$1$2@4$hd$6@4$c$0$3$1$4@6$b$0$3$9$1$4$a$2@4$he$6@4$c$0$3$1$4@6$b$0$3$9$1$4$a$2^4@1$h9^8@1$d$2>0@2$ha+1^3>0@3$8@2$5$0$1^6@4$f$0$1^5@2$hb^4$h6$h0").
Proof. intros X st L BL LS m rid q.
  intros INV Hm Hq E. pose proof INV as (IR & IA & _).
  destruct (s_metas st !! m) as [mr|] eqn:Em; [| exact (Hm eq_refl)].
  destruct (ia_metas _ IA m mr Em) as (a & ar & k & Ha & Hk & Emk).
  destruct (ia_areas _ IA a ar Ha) as ((r & _ & _ & Pa & _) & _).
  subst m. unfold mslot, aadd in Emk. inversion Emk.
  unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
  assert (HH : (q * 4096) mod 4096 = (snd a + (24 + 40 * k)) mod 4096) by congruence.
  rewrite Z.mod_mul in HH by lia. rewrite Z.add_mod, Pa, Z.add_0_l, Z.mod_mod in HH by lia.
  rewrite Z.mod_small in HH by lia. lia.
Qed.

Lemma INVL_clear_fresh : ltac2:(zQ "ie1!q5!hpc!hn9!uc!iv4!ji7!jk2!hnd!km6!t1!jv0!le!it1!hta!kkc!jld!jmc!jnb!jpe!ki4!hq1!hr8!hja!ipc!jh0!kga!js3!jt9!ju1!kt7!ktf!je!irb!kld!ku4!kud!lhb!hu8!io0!hs2!ko7!io8!kn2!jqd!li2!lh4&@2$7@3$3$1@1$h4@2$2^d^9Z@3$3$1@1$h5@2$2^d^9Z>1X$hf>2st$i9>1L$hd>2BL@1$h7$he>2LS>0$i6@1$h7$0>1g$0>0@5$h8^6^5^4^3^2>0@3$3@1$b$0@1$i2^7@2$a$0^2>0@1$c@3$3@1$b$9@6$ha$0$9@4$hb$0@4$h2$4$5$1$6@6$h1$4$5$f$1$6$h0$9@4$hc$0@4$h2$4$5$1$6@6$h1$4$5$f$1$6$h0$9^3@1$ib^7@1$h6$9>0>1b$0>2ai$1>0@3$3@1$b$8@6$ha$0$8@4$hb$0@4$h2$4$5$1$6@6$h1$4$5$f$1$6$h0$8@4$hc$0@4$h2$4$5$1$6@6$h1$4$5$f$1$6$h0$8^2@1$ia^a@2$a$8@2$i8@2$a$0^6^1@2$7>0@2$e^2@1$i7@2$2^b^7@3$h9$0^8@1^9@1$h3@1$d@2$2^c^8@2$7>0@2$e@1$d@2$2^b^7+j0>0@1$c@2$i1^9^8~0@2$7>2sc$1>0@3$h9$0^8@1^9@1$h3^1>0@1$c@3$3@1$b$0@2$a$0^9@1$i0@1^a@1$h3^2@2$7@3$3$1@1$h4@2$2^e^aZ@1$c@3$3$1@1$h5@2$2^e^aZ>0@2$e@1$d@2$2^b^7+j0>0@2$e@1$i5@2$2^c^8@2$id$i4@1$ic@1$d@2$2^c^8~0@5$h8@2$i3^a@1$h6$0^9^8^7^6").
Proof. intros X st L BL LS g.
  intros INV HF PRESg OB.
  refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    destruct (aptr_eq_dec m g) as [->|NE].
    + destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
    + assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      split; [| split; [| split; [| split]]].
      * intros _. exact (g_partial _ _ _ _ _ _ GO NF).
      * intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
      * intros _. exact (g_rest _ _ _ _ _ _ GO NF).
      * exact (old_63 _ _ _ _ _ INV m b ai Hb).
      * intros _. exact (g_under _ _ _ _ _ _ GO NF).
  - cbn. exact (im_all _ _ _ (proj1 (proj2 (proj2 INV)))).
  - intros rid q Hq E. exfalso. rewrite HF in E. injection E as Eg. exact (meta_not_page X st L BL LS g rid q INV PRESg Hq Eg).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma queue_frame : ltac2:(zQ "i00!iv4!hpc!hnd!uc!ji7!jk2!q5!jld!jt9!jmc!jnb!jpe!kv7!io8!lif!in8!kn2!lj9!lk6!ll2!llf!lma!ln5!lnf!ipc!lo8!im0!lp3!km6!io0!iv9!lpa>1h$hd>1g$6>2st$d=3st'$d@3$h9^3^2^1@2$2@3$3@4$8$0$4$7$he@1$h2^1@1$h2^2@2$2@3$3@4$8$0$4$7$hf@1$h5^1@1$h5^2@2$2@3$3$0@1$h1^1@1$h1^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9$hb@1$e^1@1$e^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9$hc@1$h0^1@1$h0^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9@2$c$6$1@1$h6^1@1$h6^2@2$2@3$3$0@1$h7^1@1$h7^2@2$2@3$3$1@1$h4^1@1$h4^2@2$2@3$3@1$h8@2$c$1$1@1$h3^1@1$h3^2@2$ha@1$f^2@1$f^1").
Proof. intros h g st.
  unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
    repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma queue_metas_other : ltac2:(zQ "ha2!q5!iv4!hpc!ji7!jk2!t1!uc!jld!jmc!jnb!jpe!it1!jv0!hn2!jqd!js3!jt9!ju1!le!hnd!hn9!lo8!kp0!io0!hl0!io8&@4$h0$0@4$a$1$3$2$4@6$9$1$3$7$2$4$8$5&@4$h1$0@4$a$1$3$2$4@6$9$1$3$7$2$4$8$5>1h$h7>1g$0>2st$h9>1x$0>0@1$b@3$6$0^1^3>0>1a$0>0@3$6$d@2$h6^4^6@2$c$0^1@2$h3@1$b@3$6$0^4^2@1$b@3$6$d@1$h8@2$h4^5^2@2$c$0^4@3$6@1$h2$5@6$f$0$5~0~1^3@1$e@3$h5^6^5^4@6$f$0$5~0~1^3@1$e^4").
Proof. intros h g st x.
  intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
  - destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
    destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
  - rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma dequeue_frame : ltac2:(zQ "i00!iv4!hpc!hnd!uc!ji7!jk2!q5!jld!jt9!jmc!jnb!jpe!kv7!io8!lif!in8!kn2!lj9!lk6!ll2!llf!lma!ln5!lnf!ipc!im0!lp3!lq3!km6!io0!iv9!lpa>1h$hd>1m$6>2st$d=3st'$d@3$hb^3^2^1@2$2@3$3@4$8$0$4$7$he@1$h2^1@1$h2^2@2$2@3$3@4$8$0$4$7$hf@1$h5^1@1$h5^2@2$2@3$3$0@1$h1^1@1$h1^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9$ha@1$e^1@1$e^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9$hc@1$h0^1@1$h0^2@2$2@3$3@4$8$6@4$b$0$4$1$5@6$a$0$4$7$1$5$9@2$c$6$1@1$h6^1@1$h6^2@2$2@3$3$0@1$h7^1@1$h7^2@2$2@3$3$1@1$h4^1@1$h4^2@2$2@3$3@1$h8@2$c$1$1@1$h3^1@1$h3^2@2$h9@1$f^2@1$f^1").
Proof. intros h m st.
  unfold dequeue.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
  repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma dequeue_metas_other : ltac2:(zQ "h92!q5!iv4!hpc!ji7!jk2!t1!uc!jld!jmc!jnb!jpe!it1!jv0!hn9!hn2!jqd!js3!jt9!ju1!le!lq3!io0!hk7!hl0!io8&@4$h1$0@4$a$1$3$2$4@6$9$1$3$7$2$4$8$5&@4$h2$0@4$a$1$3$2$4@6$9$1$3$7$2$4$8$5>1h$h5>1m$0>2st$h8>1x$0>0@1$b@3$6$0^1^3>0@1$b@3$6$e@1$h7@2$d^3^4@2$c$0^2>0@1$b@3$6$e@1$h6@2$d^4^5@2$c$0^3@3$6@1$h3$5@6$h0$0$5~0~1^4@1$f@3$h4^7^6^5@6$h0$0$5~0~1^4@1$f^5").
Proof. intros h m st x.
  intros NE NP NN. unfold dequeue, MR in *.
  rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.

Lemma get_head_active : ltac2:(zQ "e0!hpc!q5!jmc!jk2!uc!ki4!kl2!kp0!io8!hn2!in8!js3!jt9!ju1>2st$8>2sc$0@3$4$9@2$7^2@1$5^1@6$b$0$1@4$c$0$3$2$1@4$d$0$3$2$1^1@1$6@1$a^2").
Proof. intros st sc. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : ltac2:(zQ "10!jh0@5$0?1X?2st?1L?2BL?2LS").
Hypothesis NL : ltac2:(zQ "60!hja!uc!hn9!q5!hk7!hn2@3$1$5@1$4@2$2?2st?1g@1$0$3").
Hypothesis PRES : ltac2:(zQ "h20!t1!iv4!hpc!ji7!jk2!q5!jld!jmc!jnb!jpe!hja!le!uc!it1!jqd!js3!jt9!ju1@1$d@3$c@1$b$0@6$f$5$0@4$h0$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0@4$h1$5@4$9$1$3$2$4@6$8$1$3$6$2$4$7$0?1g@1$e?2st@1$a$0").
Hypothesis HQ : ltac2:(zQ "h40!hnd!q5!uc!hpc!hn9!hj0!io0!kga!jv0!le!it1!ite!ku4!r1!s9!hta!t1!hl9!kk6!kkcM6\1h$6P?1h\2sc$3@2$0@2$0@2$h2Z^1@2$h3^1+j0@2$0@2$b?2st?1g@2$0@3$2$3@1$f@2$4?2st?1g^1@3$2@1$9$1@1$c?1X@2$8$1?1g@2$0@3$2$h0@1$5@2$4?2st?1g@1$5$h1@2$0@3$7$1?1g@1$d?1X@1$a@3$7$1?1g@1$e?1X").
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).
(* [comment removed for export] *)
Definition XQ : ltac2:(zQ "10!je$0") := ltac2:(zQ "60!io0!hpc!je!r1!lud!lv4M0\1h$0$2?1h\2sc$1?1X@2$5?1X@2$4?1g@1$3?1X").
Lemma XQ_pend : ltac2:(zQ "50!s1!le!uc!mk3!q5@3$2@1$1$4@1$0$3@1$0?1X"). Proof. unfold XQ. destruct h; reflexivity. Qed.
Lemma XQ_orph : ltac2:(zQ "50!r9!le!uc!iv4!mk3@3$2@1$1$3@1$0$4@1$0?1X"). Proof. unfold XQ. destruct h; reflexivity. Qed.
Lemma XQ_zomb : ltac2:(zQ "50!s9!ipc!uc!mk3!q5@3$2@1$1$4@1$0$3@1$0?1X"). Proof. unfold XQ. destruct h; reflexivity. Qed.
Lemma XQ_fresh : ltac2:(zQ "50!ku4!le!uc!mk3!q5@3$2@1$1$4@1$0$3@1$0?1X"). Proof. unfold XQ. destruct h; reflexivity. Qed.
Lemma XQ_idle : ltac2:(zQ "a0!q5!uc!r1!kga!hnd!hk1!it1!mk3!khc!io0>1m$0@2$5@3$3$0^1@1$2$7@2$4@3$3$0^1@1$2?1X>0@3$1$9?1h$8@1$6@3$1$0^2?1g").
Proof. intros m.
  unfold XQ. destruct h as [sc|]; cbn.
  - split; [intros H; split; [exact H| discriminate]| intros [H _]; exact H].
  - rewrite in_rem. split; [intros [A B]; auto| intros [A B]; auto].
Qed.

Lemma q_in m h' : In m (LS' h') <-> In m (LS h') \/ (h' = h /\ m = g).
Proof.
  unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
Lemma q_in_list m : in_list LS' m <-> in_list LS m \/ m = g.
Proof.
  unfold in_list. split.
  - intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
  - intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
Lemma g_not_idle : ltac2:(zQ "50!it1!r1!mk3!q5!kga@1$0@3$4$3?1g@1$1$2").
Proof.
  rewrite XQ_idle. destruct h as [sc|].
  - destruct HQ as (_ & Hl & _). intros [Hi _]. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
  - intros [_ NE]. exact (NE eq_refl eq_refl).
Qed.
Lemma g_not_zomb : ltac2:(zQ "40!it1!s9!q5!kga@1$0@3$3$2?1g@1$1?1X").
Proof.
  destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
Lemma untouched x : (forall h', ~ In x (LS h')) -> x <> g -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
  - intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.

Theorem INVL_queue : INVL XQ st' L BL LS'.
Proof.
  destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X XQ st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
    destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
    + exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
  - rewrite XQ_pend, XQ_orph, XQ_zomb. auto.
  - apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
  - intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
  - intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
  - intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
    + subst h. exact (proj1 HQ).
    + unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
  - intros m Hm0. pose proof Hm0 as Hm. apply XQ_idle in Hm as [Hm _]. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
    assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm0)).
    split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
    rewrite q_in_list. tauto.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
    rewrite E, q_in_list. repeat split; auto. tauto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. rewrite XQ_fresh. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
    + intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
      * apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
        -- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
        -- rewrite fupd_ne in Hh by exact NE. exact Hh.
      * exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
    + intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
      destruct h as [sc|].
      * destruct HQ as (A & _ & C & _). lia.
      * pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
        rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
  - (* [comment removed for export] *) intros m Hm. destruct (im_all _ _ _ (proj1 (proj2 (proj2 INV))) m Hm) as [A|[A|[A|A]]].
    + left. exact A.
    + right. left. rewrite q_in_list. left. exact A.
    + destruct (aptr_eq_dec m g) as [->|NE]; [right; left; rewrite q_in_list; right; reflexivity|].
      right. right. left. apply XQ_idle. split; [exact A| intros _; exact NE].
    + right. right. right. exact A.
  - intros rid q _ E. rewrite XQ_fresh. exact E.
Qed.
End QUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : ltac2:(zQ "10!jh0@5$0?1X?2st?1L?2BL?2LS").
Hypothesis HL : ltac2:(zQ "50!q5!is4!isa!ipc!uc@3$4@1$3$0@1?2LS?1h@3$1$0?2l1@3$2$0?1m?2l2").
Hypothesis HX : ltac2:(zQ "h20!uc!q5!hnd!hpc!je!io0!hja!jv0!isa!le!kmd!kh0!ku4!r1!lv4!kud!ki4!khc@2$b@2$a$3\2sc$3@2$2@3$0$5?1h@1$h0^1@2$2@3$0@1$9$1@1$c?1X@1$6$1@3$0$4?2X'@2$f?1X@2$7$1?1m@2$2@3$0$5?1h$h1@3$0$4?2X'@2$e?1X@3$8$1?1m@1$d?1X").
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).

Lemma m_listed : In m (LS h). Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma d_in x h' : In x (LS' h') -> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
Lemma d_in_rev x h' : In x (LS h') -> x <> m -> In x (LS' h').
Proof.
  intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
  - left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
  - right. auto.
Qed.
Lemma d_in_list x : in_list LS' x -> in_list LS x.
Proof. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
Lemma m_out : ~ in_list LS' m.
Proof.
  intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
  - pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
    destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
  - apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
Lemma untouched_d x : (forall h', ~ In x (LS h')) -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI. apply dequeue_metas_other.
  - intros ->. exact (NI h m_listed).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
  - intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
Lemma nonhead_old x : In x (LS' h) -> Some x <> head_of (LS' h) -> Some x <> head_of (LS h).
Proof.
  intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
  - intros E. inversion E. subst x.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
    apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
  - exact Hh.
Qed.
Lemma MR'_m : MR st' m = data_of (MR st m).
Proof.
  pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
  unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.

Theorem INVL_dequeue : INVL X' st' L BL LS'.
Proof.
  destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
    destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
    + exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
  - destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
  - apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
  - intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
  - intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
  - intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
    destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
    apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
  - intros x Hx.
    assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
    { intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
      - rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
      - intros IL'. exact (NI (d_in_list x IL')). }
    destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
    destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
    split; [| exact m_out].
    rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
    apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
    rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
  - intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
    destruct (aptr_eq_dec x m) as [->|NEm].
    + destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
      * pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
        rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
      * exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
    + assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
      { destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
      split; [| split; [| split; [| split]]].
      5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
      * intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
      * intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
      * intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
        destruct (decide (LActive sc = h)) as [E|NE].
        -- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
        -- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
      * intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
  - (* [comment removed for export] *) intros x Hx. destruct (im_all _ _ _ (proj1 (proj2 (proj2 INV))) x Hx) as [A|[[h' A]|[A|A]]].
    + left. exact A.
    + destruct (aptr_eq_dec x m) as [->|NE].
      * destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn.
        -- left. pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (_ & A2 & _). exact A2.
        -- right. right. left. left. reflexivity.
      * right. left. exists h'. apply d_in_rev; [exact A| exact NE].
    + right. right. left. destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [exact A| right; exact A].
    + right. right. right. exact A.
  - intros rid q _ E. destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD in E; discriminate| exact E].
Qed.
End DEQUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : ltac2:(zQ "10!jh0@5$0?1X?2st?1L?2BL?2LS").
Hypothesis HL : ltac2:(zQ "50!q5!isa!ipc!uc!ki4@3$3@1$2$0@1?2LS@1$4?2sc@3$1$0?1a?4rest").
Hypothesis Hn : ltac2:(zQ "60!jv0!uc!hn9!q5!hk7!hn2@3$1$5@1$4@2$2?2st?1a@2$0$3?2a'").
Hypothesis OB : ltac2:(zQ "d0!uc!q5!it1!hpc!hn9!jv0!ipc!ir5!le!hnd!ku4!hq1!hr8>0@1$2@3$0@1$8$1@1$a?1X@2$5$1?1a>0@1$2@3$0@1$6$1?4rest@1$7$1@2$9@3$0$3@1$b@2$4?2st?1aZ@1$2@3$0$3@1$c@2$4?2st?1aZ").
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).

Lemma r_in x h' : In x (LS' h') <-> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
  - unfold h. rewrite HL, in_app_iff. cbn. tauto.
  - tauto.
Qed.
Lemma r_in_list x : in_list LS' x <-> in_list LS x.
Proof. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.

Theorem INVL_rotate : INVL X st' L BL LS'.
Proof.
  refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
            _ _ _ _ _ _ _ _ _ _).
  - auto.
  - apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
  - intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
  - intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
  - intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
    destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
  - intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
    destruct (decide (LActive sc0 = h)) as [E|NE].
    + apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
    + rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
    unfold st'. rewrite set_head_metas. exact E.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
    + intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
      * unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
        apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
        -- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
           unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
           pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
           apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
        -- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
      * unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
    + intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
  - (* [comment removed for export] *) intros m Hm. destruct (im_all _ _ _ (proj1 (proj2 (proj2 INV))) m Hm) as [A|[A|[A|A]]]; [left; exact A| right; left; rewrite r_in_list; exact A| right; right; left; exact A| right; right; right; exact A].
  - intros rid q _ E. exact E.
Qed.
End ROTATE.
(* [comment removed for export] *)
