(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate37Corelib4Init5Logick92eqk93and37Corelib7Numbers7BinNumsm81Z37Corelib4Init9Datatypeso54listo54bool08as_cache0fas_cache_inited09as_chunks06as_env05as_gq0h0as_internal_init07as_maps0das_n_reserved0cas_ptr_array09as_qcache07as_qmax07as_qmin0aas_regions06as_sec0cas_space_beg05as_tq06qcache05chunk07mapping06pclass06region06schunk46Stdlib5FSetscFMapPositivebPositiveMaphof1t79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~hrbfsame_but_shadow05paint06effecto54prodo54truek92ex0eaddr_is_in_mem46Stdlib6ZArith6BinInt1Zik44lando54Someo56optiono54pair0dpoison_shadowik43addik43sub04mkPC06set_pc09upd_chunk05rq_rz07rq_sizeik42le06get_pc0fcompact_to_addr08pc_countik44lnotik42lto54conso55falsek93notk92or0aCAllocated0bam_malloc_k08class_id0bcompute_req08kMaxSize0bkNumClasses07mkChunk09pc_chunks03req09rq_needed0arq_primary0csize_too_bighrb9hit_statem88positive37Corelib4Init6Specifjqf7sumboolhof4findhof3key56Stdlib5FSetscFMapPositivebPositiveMap1Ejte6eq_dechof3addk93iff0achunk_list36Stdlib5Lists4Listkia2In0bch_user_beg04ckey" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition same_but_shadow : ltac2:(zQ "10!k1>1a$0>1b$0P") := ltac2:(zQ "hd0!ld!m2!o1!pd!q4!qb!r5!s6!t1!t9!u0!v3!vc!hgb!hh9!hi4!hid!hj6!hk2!hka!hl8!k1!hlf!hm7!hme!hn7!hnf!ho7!hr6\1a$h5\1b$h5@2$1@3$0$2@1$h3^2@1$h3^1@2$1@3$0$2@1$d^2@1$d^1@2$1@3$0@1$3$ha@1$h1^2@1$h1^1@2$1@3$0$4@1$6^2@1$6^1@2$1@3$0@1$3$h9@1$5^2@1$5^1@2$1@3$0$2@1$c^2@1$c^1@2$1@3$0@1$3$hb@1$h2^2@1$h2^1@2$1@3$0@1$hc$h7@1$7^2@1$7^1@2$1@3$0$h6@1$h4^2@1$h4^1@2$1@3$0$h6@1$9^2@1$9^1@2$1@3$0$4@1$a^2@1$a^1@2$1@3$0@1$3$h8@1$b^2@1$b^1@2$1@3$0@1$3$2@1$8^2@1$8^1@2$1@3$0$2@1$f^2@1$f^1@2$1@3$0$2@1$h0^2@1$h0^1@3$0$2@1$e^2@1$e^1").

Lemma sbs_refl : ltac2:(zQ "20!k1!hvf>1a$0@2$1^1^1"). Proof. intros; repeat split; reflexivity. Qed.
Lemma sbs_trans : ltac2:(zQ "20!k1!hvf>1a$0>1b$0>1c$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof. intros a b c H1 H2. unfold same_but_shadow in *. intuition congruence. Qed.
Lemma sbs_paint : ltac2:(zQ "40!o1!k1!ih2!hvf>2st$1>2lo$0>2hi$0>1v$0@2$3@4$2^4^3^2^1^4").
Proof. intros. destruct st; repeat split; reflexivity. Qed.

Lemma poison_shadow_some : ltac2:(zQ "h30!k1!pd!ld!o1!ih9!q4!ii1!ii8!iif!ij4!ilc!im4!imb!in4!m2!inb!hvf!ioa!ip1>2st$0>1a$3>2sz$3>1v$3>0@3$2$3@2$a^3+7Z>0@3$2$5@1$9^4$7>0@3$2$3@2$a^4+7Z>0@3$2$5@1$9@2$h2@2$h1^6^5+8$7@2$8$0\3st'$0@2$8@1$1$4\2ev@1$1$4@2$e@3$2@1$c@2$6$0@1$1$4@4$f^a^9^8^7@2$b@2$6$0@1$1$4@4$d$0@1$1$4^2^1@2$h0^2^a").
Proof.
  intros st a sz v H1 H2 H3 H4. unfold poison_shadow. rewrite H1, H2, H3, H4. cbn [negb Z.eqb].
  set (st' := if 0 <? sz then paint st a (a + sz) v else st).
  assert (S : same_but_shadow st' st) by (subst st'; destruct (0 <? sz); [apply sbs_paint| apply sbs_refl]).
  repeat match goal with |- context [if ?b then _ else _] => destruct b; try (neexists 2; split; [reflexivity| exact S]) end.
  all: neexists 2; split; [reflexivity| exact S].
Qed.

(* [comment removed for export] *)
Definition hit_state : ltac2:(zQ "40!o1!k1!pd!hm7>2st$1>1c$0>3cnt$0>4rest@1$2$0>2ch$3$1") := ltac2:(zQ "80!o1!pd!k1!hm7!ip8!ipe!iq6!ip1\2st$2\1c$0\3cnt$0\4rest@1$1$0\2ch$3@2$6@3$5^5^4@2$4@2$7^3+1^2^1").

(* [comment removed for export] *)
Lemma am_malloc_hit : ltac2:(zQ "ib0!o1!ld!pd!k1!q4!ii1!ih9!ir1!ii8!ir8!ioa!is1!ij4!is7!ilc!in4!m2!iif!isf!iu0!iua!iv2!im4!iv8!ivf!imb!jg7!jgd!jh2!jhe!jib!jj5!jk2!jkc!jl9!jm2!jmd!jn2!jnd!jo9!jp7!hvf!ip1>2st$3>1n$0>5kaddr$0>1c$0>2cp$0>4rest@1$2$0>0@2$bZ^5=1r$i4@1$hf^6=6needed$0@1$i5^1=1U$0@2$a@3$h2^9^6^5@1$7^2>0@3$1$4@1$i7^3$h8>0@2$b^3$i0>0@3$1$0^9@1$he^4>0@2$h0@2$h5Z^a@2$h5^a$i1>0@3$1@1$2$0@1$i3@2$d^e^b@3$h7$0^a^9>0@1$ha@3$1$0@1$h3@2$d^f^cZ>0@3$1$0@2$e^7+7Z>0@3$1$4@1$c^8$8>0@3$1$4@1$c@2$ia@2$a^9@2$e@1$9^b@1$h4+7+8$8>0@3$1$4@1$c@2$a^a@2$e@1$9^c@1$h4+7$8>0@2$hb@3$1$0@1$7^d+h0@2$b+i0@1$7^d>0@3$1$4@1$i6^e$8>0@2$b@2$a@1$7^f@1$9^f^e@2$h1$3\3st'$3@2$h1@1$2$6\2ev@1$2$6@2$h0@3$1@1$h9@2$5@2$5$0$3@1$2$6@3$hd^h9^h8^h7@2$h6@2$5@2$5$0$3@1$2$6@4$f@2$5$0$3@1$2$6@4$f$0$3^h0^2^1@2$i9^2@5$i8^h9^h6@1$h3@2$d^h9^h6^h4@6$i2@3$h2^h9^h6^h5^h0@1$9^h2@1$7^h2^h6$hc").
Proof.
  intros st n kaddr c cp rest Hn r needed U TB NK Hc HC PCS CNT AL8 IM1 IM2 IM3 RZ16 PRIM FIT.
  unfold am_malloc_k. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold r. rewrite TB.
  fold needed. replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite <- Hc. unfold cache_alloc.
  replace ((c =? 0) || (kNumClasses <=? c)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply Z.leb_gt; lia]).
  replace (pc_count (get_pc st c) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNT).
  rewrite PCS.
  assert (CA : forall st1, as_space_beg st1 = as_space_beg st -> compact_to_addr st1 c cp = compact_to_addr st c cp)
    by (intros st1 E; unfold compact_to_addr, region_beg; rewrite E; reflexivity).
  rewrite (CA (set_pc _ _ _)) by (destruct st; reflexivity). fold U.
  replace (compact_to_addr st c cp + needed <? U + rq_size r) with false by (symmetry; apply Z.ltb_ge; subst U; lia).
  rewrite PRIM. cbn [negb].
  set (st2 := upd_chunk _ _).
  set (rd := Z.land (rq_size r) (Z.lnot 7)).
  assert (RD8 : Z.land rd 7 = 0) by (subst rd; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 7) 7), Z.land_lnot_diag, Z.land_0_r; reflexivity).
  assert (S14 : exists st4 ev4, (if 0 <? rd then poison_shadow st2 U rd 0 else Some (st2, [])) = Some (st4, ev4) /\ same_but_shadow st4 st2).
  { destruct (0 <? rd). 2:{ neexists 2. split; [reflexivity| apply sbs_refl]. }
    ndestruct (poison_shadow_some st2 U rd 0 AL8 IM1 RD8 IM2) as (st4 & ev4 & E & S). exists st4, ev4. split; [exact E| exact S]. }
  ndestruct S14 as (st4 & ev4 & E14 & S4). rewrite E14.
  fold rd in IM3. rewrite IM3. cbn [negb].
  assert (S15 : exists st5 ev5, (if negb (rq_size r =? rd) then Some (paint st4 (U + rd) (U + rd + 8) (Z.land (rq_size r) 7), [EShadow1 (U + rd) (Z.land (rq_size r) 7)]) else Some (st4, []))
                               = Some (st5, ev5) /\ same_but_shadow st5 st4).
  { destruct (negb (rq_size r =? rd)); neexists 2; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]. }
  ndestruct S15 as (st5 & ev5 & E15 & S5). rewrite E15.
  replace (negb (U - kChunkHeaderSize =? compact_to_addr st c cp) && (U - kChunkHeaderSize <? compact_to_addr st c cp + 16)) with false.
  2:{ symmetry. unfold kChunkHeaderSize. subst U. destruct RZ16 as [E|GE].
      - rewrite E. replace (compact_to_addr st c cp + 16 - 16 =? compact_to_addr st c cp) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      - rewrite andb_false_iff. right. apply Z.ltb_ge. lia. }
  neexists 2. split; [reflexivity|].
  eapply sbs_trans; [exact S5|]. eapply sbs_trans; [exact S4|]. subst st2. unfold hit_state. apply sbs_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import FMapPositive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Lemma gadd_find : ltac2:(zQ "c0!hm7!ld!jq4!imb!jg7!js4!jsf!jt7!im4!kg7!kh1!hr6>2mp@1$b$0>1k$7>2k'$7>1v$0@3$1@1$3$0@3$6$0^2@4$a$0^3^1^4M5\0@2$5@3$1$2^3^2@1$4@3$1$2^3^2@1$3$0@2$9^3^2\0@3$1$2^3^2@2$8$0^2\0@1$4@3$1$2^3^2@3$6$0^3^5").
Proof.
  intros mp k k' v. destruct (PositiveMap.E.eq_dec k k') as [E|NE].
  - apply PositiveMap.find_1. apply PositiveMap.add_1. exact E.
  - destruct (PositiveMap.find k' mp) as [w|] eqn:F.
    + apply PositiveMap.find_1. apply PositiveMap.add_2; [exact NE|]. apply PositiveMap.find_2. exact F.
    + destruct (PositiveMap.find k' (PositiveMap.add k v mp)) as [w|] eqn:G; [|reflexivity].
      exfalso. apply PositiveMap.find_2 in G. apply PositiveMap.add_3 in G; [|exact NE]. apply PositiveMap.find_1 in G. congruence.
Qed.

Lemma chunk_list_in_iff : ltac2:(zQ "c0!hm7!jt7!im4!imb!ld!iif!kh8!s6!k1!khe!jsf!kjd>2st$8>1x$0@2$6@3$b$0^1@1$9^2@2$5$1\1k$1@3$4@1$3$0@3$a$0^1@1$7^3@2$2$0^2").
Proof.
  intros st x. unfold chunk_list. rewrite in_map_iff. split.
  - intros [[k v] [E Hin]]. cbn in E. subst v. exists k. apply PositiveMap.elements_complete. exact Hin.
  - intros [k F]. exists (k, x). split; [reflexivity|]. apply PositiveMap.elements_correct. exact F.
Qed.

Lemma chunk_list_upd_iff : ltac2:(zQ "h20!hm7!ld!jt7!im4!imb!m2!iif!kh8!jg7!jgd!s6!k1!kk3!khe!kl0!iq6!jsf!kjd>2st$b>2ch$0>1x$0@2$7@3$h1$0^1@1$d@2$f^3^2@2$9@3$1$0^1^2@2$6$2\1k$2@2$5@3$1@1$4$0@3$h0$0^1@1$a^4@2$3$0^2@1$8@3$1$2^1@1$e@1$c^3").
Proof.
  intros st ch x. rewrite chunk_list_in_iff. unfold upd_chunk, set_chunks. cbn [as_chunks]. split.
  - intros [k F]. rewrite gadd_find in F. destruct (PositiveMap.E.eq_dec (ckey (ch_user_beg ch)) k) as [E|NE].
    + left. congruence.
    + right. exists k. split; [exact F| congruence].
  - intros [->|[k [F NE]]].
    + exists (ckey (ch_user_beg ch)). rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [reflexivity| congruence].
    + exists k. rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [congruence| exact F].
Qed.
