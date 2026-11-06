(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel BothAllocCons BothAllocCons2 BothAllocConsC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AG_FreeModel AllocBudget.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate37Corelib4Init9Datatypesk94listk96optionk94prod37Corelib7Numbers7BinNumsn81Z06effectk94None05chunk06cstatek94Somek94pair09as_chunks0acb_recycle0cch_chunk_beg08ch_state0afind_chunk0h1set_internal_init09upd_chunk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAG_FreeModel~~~~~~hhb3qch37Corelib4Init5Logichm42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh0AG_FreePassModel~~~~~~hne7flip_sthm43andk94bool08as_cache0fas_cache_inited05as_gq07as_maps0das_n_reserved0cas_ptr_array09as_qcache07as_qmax07as_qmin0aas_regions06as_sec0cas_space_beg05as_tq06qcachek94true0h0as_internal_init0bch_user_beg04ckey07mapping06pclass06region06schunk46Stdlib5FSetscFMapPositivebPositiveMapis23addis21thm42ex0aCAllocatedhnecam_free_pass69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBothAllocCons~~~~~~jh75INITQ69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothAllocConsC~~~~~~jm05PINVc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AllocWf~~~~~~jqa2WF" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition am_free_pass : ltac2:(zQ "60!k1!m1!m8!n1!p1!p5>2st$0>1p$4@1$2@2$3$0@1$1$5") := ltac2:(zQ "h30!k1!m1!p5!n1!m8!pd!q4!qb!r3!ra!p1!s1!sc!t8!u6!v0!vc!hh0!hld\2st$0\1p$a=3st0$0@1$h0^2M4\1x@1$4$6@1$4@2$3$0@1$1$2@2$f@1$b^1^2\2ch$6M7\1x$7@1$4@2$3$0@1$1$2@1$e^1M4\1x@1$4@2$3$0@1$1$2@1$4@2$3$0@1$1$2@2$c@2$h1^2@1$h2^1@1$d^1\2p0@2$3$0@1$1$2M3\2p0@2$3$0@1$1$2@1$4@2$3$0@1$1$2^1\3st2$0\3ev2@1$1$2@2$8@2$3$0@1$1$2@4$9$0@1$1$2^2^1@1$5@2$3$0@1$1$2@1$5@2$3$0@1$1$2@1$5@2$3$0@1$1$2").

(* [comment removed for export] *)
Definition flip_st : ltac2:(zQ "20!k1!q4>2st$0>2ch$1$0") := ltac2:(zQ "50!k1!q4!vc!hh0!hld\2st$0\2ch$1@2$3@1$2^2@1$4^1").

Lemma flip_st_fields : ltac2:(zQ "i20!hn8!hs5!ht0!p1!m1!q4!ht7!hte!hu8!s1!hv9!ig0!ig9!ih8!ii6!ij1!ija!ik3!ikf!il7!im5!imc!in4!inb!k1!ioe!ipb!iq1!iqa!ir2!ira!hld!iu9!iv0>2st$h8>2ch$5@2$2@3$0$3@1$h3@2$1^2^1@1$h3^2@2$2@3$0$3@1$d@2$1^2^1@1$d^2@2$2@3$0@1$4$hd@1$h1@2$1^2^1@1$h1^2@2$2@3$0$6@1$8@2$1^2^1@1$8^2@2$2@3$0@1$4$hc@1$7@2$1^2^1@1$7^2@2$2@3$0$3@1$c@2$1^2^1@1$c^2@2$2@3$0@1$4$he@1$h2@2$1^2^1@1$h2^2@2$2@3$0$h5@1$h4@2$1^2^1@1$h4^2@2$2@3$0$h5@1$a@2$1^2^1@1$a^2@2$2@3$0$6@1$h7@2$1^2^1$h6@2$2@3$0@1$4$hb@1$b@2$1^2^1@1$b^2@2$2@3$0$3@1$f@2$1^2^1@1$f^2@2$2@3$0$3@1$h0@2$1^2^1@1$h0^2@2$2@3$0$3@1$e@2$1^2^1@1$e^2@3$0@1$i1$5@1$9@2$1^2^1@4$i0$5@1$ha@1$h9^1@1$hf^1@1$9^2").
Proof.
  intros st ch. unfold flip_st, upd_chunk, set_chunks, set_internal_init, qch. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma am_free_pass_shape : ltac2:(zQ "h50!k1!m1!p5!n1!hn8!q4!r3!m8!ra!ht0!iv5!p1!ivb!s1!sc!t8!u6!qb!v0!jg7!hs5>2st$0>1p$b>3st'$0>2ev@1$1$2>0@3$4@1$7@2$3$0@1$1$2@2$h3^4^3@2$6@2$3$0@1$1$2@4$8$0@1$1$2^2^1@2$a$5\2ch$5@2$9@3$4@1$7$5@2$h2@1$d^6^5@2$6$5^1@2$9@3$4$h1@1$h0^1$c@3$4@1$7@2$3$0@1$1$2@2$e@2$h4^6^1@1$f^1@2$6@2$3$0@1$1$2@4$8$0@1$1$2^4^3").
Proof.
  intros st p st' ev H. unfold am_free_pass in H.
  change (as_chunks (set_internal_init st)) with (as_chunks st) in H. destruct (find_chunk (as_chunks st) p) as [ch|] eqn:F; [| discriminate H].
  exists ch. split; [reflexivity|]. destruct (ch_state ch); [| discriminate H]. split; [reflexivity|].
  unfold flip_st. destruct (cb_recycle _ _) as [[st2 ev2]|]; [| discriminate H]. injection H as <- <-. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem am_free_pass_sbpa : ltac2:(zQ "d0!k1!m1!p5!hn8!p1!n1!ih8!il7!r3!m8!ra!ht0!jg7>2st$0>1p$4>3st'$0>2ev@1$1$2>0@3$3@1$9@2$5$0@1$1$2@2$c^4^3@2$8@2$5$0@1$1$2@4$a$0@1$1$2^2^1@2$b@3$3$4@1$7^3@1$7^5@3$3$4@1$6^3@1$6^5").
Proof.
  intros st p st' ev H. ndestruct (am_free_pass_shape st p st' ev H) as (ch & F & ST & CB).
  pose proof (cb_recycle_sbpa _ _ _ _ CB) as [S1 S2]. npose (flip_st_fields st ch) as (E1 & E2 & _).
  rewrite S1, S2, E1, E2. split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem am_free_pass_initq : ltac2:(zQ "b0!k1!m1!p5!n1!jl7!r3!m8!ra!hn8!p1!jg7>2st$0>1p$9>3st'$0>2ev@1$1$2>0@1$4^4>0@3$8@1$6@2$3$0@1$1$2@2$a^5^4@2$5@2$3$0@1$1$2@4$7$0@1$1$2^3^2@1$4^4").
Proof.
  intros st p st' ev IQ H. ndestruct (am_free_pass_shape st p st' ev H) as (ch & F & ST & CB).
  pose proof (cb_recycle_inited _ _ _ _ CB) as (I1 & T1 & G1). npose (flip_st_fields st ch) as (_ & _ & _ & E4 & _ & _ & _ & E8 & E9 & _).
  unfold INITQ in *. rewrite T1, G1, E8, E9. rewrite E4 in I1. destruct IQ as [IQ|IQ]; [left; exact (I1 IQ)| right; exact IQ].
Qed.

(* [comment removed for export] *)
Theorem PINVc_am_free_pass : ltac2:(zQ "c0!k1!m1!p5!n1!jq1!r3!m8!ra!hn8!p1!jg7!ju7>2st$0>1p$9>3st'$0>2ev@1$1$2>0@1$b^4>0@1$4^5>0@3$8@1$6@2$3$0@1$1$2@2$a^6^5@2$5@2$3$0@1$1$2@4$7$0@1$1$2^4^3@1$4^5").
Proof.
  intros st p st' ev W [CO NM] H. ndestruct (am_free_pass_shape st p st' ev H) as (ch & F & ST & CB).
  pose proof (WF_free_env st W) as FE. npose FE as (LENR & LENC & K & CSO).
  pose proof (find_chunk_In _ _ _ F) as INch.
  assert (POS : 0 < ch_user_beg ch) by (destruct (K _ _ (proj1 (chunk_list_find st ch K) INch)) as [_ P]; exact P).
  set (st0 := set_internal_init st).
  assert (F0 : cview st0 = cview st /\ as_regions st0 = as_regions st /\ as_cache st0 = as_cache st /\ as_chunks st0 = as_chunks st /\ as_space_beg st0 = as_space_beg st).
  { subst st0. repeat split; reflexivity. }
  ndestruct F0 as (CV0 & RG0 & CA0 & CH0 & SB0).
  assert (CO0 : COMPLETE st0 noX) by (exact (COMPLETE_view _ _ _ (eq_sym CV0) CO)).
  assert (K0 : keys_ok (as_chunks st0)) by (rewrite CH0; exact K).
  assert (IN0 : In ch (chunk_list st0)) by (unfold chunk_list; rewrite CH0; exact INch).
  assert (CO1 : COMPLETE (flip_st st ch) noX).
  { unfold flip_st. fold st0. apply (upd_chunk_complete_restate st0 noX (qch ch) ch K0 IN0); [reflexivity| reflexivity| reflexivity| exact CO0]. }
  assert (FE1 : free_env (flip_st st ch)).
  { unfold flip_st. fold st0. apply (free_env_transfer st (upd_chunk st0 (qch ch))); [cbn; exact SB0| cbn; rewrite ?RG0; exact LENR| cbn; rewrite ?CA0; exact LENC| apply keys_ok_upd; [exact K0| exact POS]| | exact FE].
    intros x IN. apply chunk_list_upd_iff in IN. destruct IN as [->|(k & Fk & NE)].
    - right. exists ch. split; [exact INch| repeat split; reflexivity].
    - left. apply chunk_list_in_iff. exists k. rewrite <- ?CH0. exact Fk. }
  destruct (cb_recycle_complete _ noX _ _ _ FE1 CO1 CB) as (CO2 & _ & _ & _ & _ & _ & _ & _ & RS).
  split; [exact CO2|].
  intros c Hc. rewrite (ncarved_regs st' (flip_st st ch) c RS).
  unfold ncarved, get_region. rewrite (proj1 (proj2 (proj2 (flip_st_fields st ch)))). apply (NM c Hc).
Qed.
