(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z01N37Corelib4Init5Logichf2eq37Corelib4Init9Datatypesj84pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~l75known79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~pd5Knownpd9cell_readpd7cellvalpdaget_shadowpd6mstatepd6shadowj84prodj84Somej86optionhf3and46Stdlib6ZArith6BinInt1Zhj52lehj52lt25stdpp4basehl96lookup25stdpp9countablehmfbN_countablehmfbZ_countable25stdpp4gmaphpe4gmaphpebgmap_lookup35stdpp7numbers1Nhs16eq_dec35stdpp7numbers1Zhtc6eq_decpd7r_cellspd8s_shadowhj54landhj56modulol77byte_ofhj53divhj53addhj53mulhj53powhj56shiftrj83sndl75mslotpd6NSLOTSpd4PGSZpd4aptrpd7area_of" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma known_at : ltac2:(zQ "a0!h9!hc!j3!l0!p5!tb!u3!uf!v9!hg6>2st$9>3rid$1>1o$0>1v$0>4rid'$1>2o'$0>0@3$4^6@4$3$1$0^5^4^3>0@3$2$0^2^5>0@3$2$1^4^7@3$2$7@2$6@2$8^9^5^4@1$5^6").
Proof. intros st rid o v rid' o'. intros H -> ->. exact H. Qed.

(* [comment removed for export] *)
Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
  (forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
  ftree L (rd8 st q k) Post.
Proof.
  intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
  - apply H. apply Hk. reflexivity.
  - cbn [ftree]. intros v Hv. unfold peek_answer_ok.
    destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.

Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
  (forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
  ftree L (rd16 st q k) Post.
Proof.
  intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma known_byte : ltac2:(zQ "h90!h9!hc!hgf!hh8!j3!hhf!hi6!hif!hkd!hl3!hm5!ho0!hof!hqa!hr2!ht2!hud!l0!tb!u3!uf!v9!hg6!hv7!ig1>2st$h6>3rid$1>1o$0>1v$0>0>2sh$2>2o'$0>2v'$0>1t$1>0@3$4@1$6$2@6$a$1$2@4$d$1$f$b$2@4$e$1$f$b$2^7@1$h8^8@2$5$2^4>0@3$4@1$6@2$3$0$1@6$a$0@2$3$0$1@4$d$0$h0$c@2$3$0$1@4$e$0$h0$c@2$3$0$1^4@1$h7^5@2$5@2$3$0$1@4$h1$0$1^3^2@2$7@2$8Z^4@2$9^4+hg0>0@3$4$h4@2$h3@2$h5^5^4^3@1$h2^2@2$7@2$8Z^3@2$9^3+hg0").
Proof. intros st rid o v.
  intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
  - destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
  - rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_255 : ltac2:(zQ "50!h9!j3!igc!hkd!ih4>1x$0>0@2$3Z^1@3$1$0@2$2^2+vf@2$4^2+hg0").
Proof. intros x. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma byte_of_0 : ltac2:(zQ "50!h9!j3!ihe!hkd!ih4>1x$0>0@2$3Z^1@3$1$0@2$2^2Z@2$4^2+hg0").
Proof. intros x. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
Lemma byte_of_1 : ltac2:(zQ "60!h9!j3!ihe!ii8!hkd!ih4>1x$0>0@2$4Z^1@3$1$0@2$2^2+1@2$5@2$3^2+hg0+hg0").
Proof. intros x. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_2 : ltac2:(zQ "60!h9!j3!ihe!ii8!hkd!ih4>1x$0>0@2$4Z^1@3$1$0@2$2^2+2@2$5@2$3^2+hggg0+hg0").
Proof. intros x. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_3 : ltac2:(zQ "60!h9!j3!ihe!ii8!hkd!ih4>1x$0>0@2$4Z^1@3$1$0@2$2^2+3@2$5@2$3^2+hggggg0+hg0").
Proof. intros x. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.

Lemma byte_of_range : ltac2:(zQ "50!hkd!h9!ihe!hif!hl3>1x$1>1k$1>0@2$0Z^2>0@2$0Z^2@2$3@2$0Z@2$2^4^3@2$4@2$2^4^3+hg0").
Proof. intros x k.
  intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma u16_bytes : ltac2:(zQ "90!h9!ihe!hif!j3!iif!hkd!hl3!ij6!ijd>1q$0>0@2$2@2$5Z^1@2$6^1@2$8+2+h0@3$3$0@2$4@2$1^2Z@2$7+hg0@2$1^2+1^2").
Proof. intros q. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.

Lemma u32_bytes : ltac2:(zQ "90!ihe!iif!ij6!h9!hif!j3!hkd!hl3!ijd>1r$3>0@2$4@2$6Z^1@2$7^1@2$8+2+i0@3$5$3@2$1@2$1@2$1@2$0^2Z@2$2+hg0@2$0^2+1@2$2+hggg0@2$0^2+2@2$2+hggggg0@2$0^2+3^2").
Proof. intros r.
  intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
  pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
  pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
  rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

(* [comment removed for export] *)
Lemma land31_idx : ltac2:(zQ "70!h9!hkd!hif!j3!iif!igc!ij6>1i$0>1r$0>0@2$2@2$1Z^2@2$1^2+hf>0@2$1Z^2@3$3$0@2$5@2$4^4@2$6+i0^3+hf^4").
Proof. intros i r.
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma shiftr5_res : ltac2:(zQ "70!h9!hkd!hif!j3!iif!ij6!ik4>1i$0>1r$0>0@2$2@2$1Z^2@2$1^2+hf>0@2$1Z^2@3$3$0@2$6@2$4^4@2$5+i0^3+5^3").
Proof. intros i r.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma area_of_mslot : ltac2:(zQ "e0!h9!j3!hc!hh8!ike!hif!il4!ilc!im5!imc!in3!hkd!hl3!ih4>1a@2$3$2$0>1k$0>0@3$1$0@2$d@3$4$2$0^2$8Z>0@2$5@2$bZ^2@2$c^2$7@3$1$9@1$a@2$6^4^3^4").
Proof. intros a k.
  intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
  rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
