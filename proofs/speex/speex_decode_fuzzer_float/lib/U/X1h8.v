(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qz X1r0 X1nv X1r1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1it X1h9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma Forall_upd_nat : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_nat l i v).
Proof.
intros P l. induction l as [|x l IH]; intros [|i] v Hl Hv; cbn; [constructor| constructor| |];
inversion Hl; subst; constructor; auto.
Qed.
Lemma Forall_zupd : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (zupd l i v).
Proof. intros P l i v Hl Hv. unfold zupd. destruct (i <? 0); [exact Hl|]. apply Forall_upd_nat; auto. Qed.

Lemma s64_range : forall x, -2^63 <= s64 x < 2^63.
Proof. intros x. unfold s64. pose proof (Z.mod_pos_bound (x + 2^63) (2^64) ltac:(lia)). lia. Qed.

Lemma lor512_range : forall v, 0 <= v < 2048 -> 0 <= Z.lor v 512 < 2048.
Proof.
intros v Hv. pose proof (proj2 (Z.lor_nonneg v 512) ltac:(lia)) as NN. split; [exact NN|].
destruct (Z.eq_dec v 0) as [->|NZ]; [rewrite Z.lor_0_l; lia|].
assert (HL : Z.log2 (Z.lor v 512) = Z.max (Z.log2 v) (Z.log2 512)) by (apply Z.log2_lor; lia).
assert (Z.log2 v < 11) by (apply Z.log2_lt_pow2; lia).
change (Z.log2 512) with 9 in HL.
destruct (Z.eq_dec (Z.lor v 512) 0) as [E|]; [apply Z.lor_eq_0_iff in E; lia|].
apply (Z.log2_lt_pow2 (Z.lor v 512) 11); lia.
Qed.

Lemma seg_loop_vals : forall vals bos fill packet saved lac gran f p s,
Forall (fun v => 0 <= v < 256) vals ->
seg_loop vals bos fill packet saved = (lac, gran, f, p, s) ->
Forall (fun v => 0 <= v < 512) lac /\ Forall (fun g => g = -1) gran.
Proof.
induction vals as [|v vals IH]; intros bos fill packet saved lac gran f p s Hb E; cbn [seg_loop] in E.
- inversion E; subst. split; constructor.
- inversion Hb as [|v' vals' Hv Hvals]; subst v' vals'.
destruct (seg_loop vals false (fill + 1) (if v <? 255 then fill + 1 else packet) (if v <? 255 then fill else saved))
as [[[[lac' gran'] f'] p'] s'] eqn:E'.
injection E as E1 E2 E3 E4 E5. subst lac gran f p s.
destruct (IH _ _ _ _ _ _ _ _ _ Hvals E') as [L G].
split; constructor; auto.
destruct bos; [| lia].
pose proof (proj2 (Z.lor_nonneg v 256) ltac:(lia)) as NN. split; [exact NN|].
destruct (Z.eq_dec v 0) as [->|NZ]; [rewrite Z.lor_0_l; lia|].
assert (HL : Z.log2 (Z.lor v 256) = Z.max (Z.log2 v) (Z.log2 256)) by (apply Z.log2_lor; lia).
assert (Z.log2 v < 8) by (apply Z.log2_lt_pow2; lia). change (Z.log2 256) with 8 in HL.
destruct (Z.eq_dec (Z.lor v 256) 0) as [E|]; [apply Z.lor_eq_0_iff in E; lia|].
apply (Z.log2_lt_pow2 (Z.lor v 256) 9); lia.
Qed.

Section Vals.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types os : stream_st ptr.

#[using="Type"] Lemma lacing_vals_ok_returned' : forall os, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_returned os)).
Proof.
intros os H. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; try apply Forall_zdrop; destruct os; cbn in *; exact H.
Qed.
#[using="Type"] Lemma granules_ok_returned : forall os, granules_ok (os_granules os) -> granules_ok (os_granules (pagein_returned os)).
Proof.
intros os H. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; try apply Forall_zdrop; destruct os; cbn in *; exact H.
Qed.

#[using="Type"] Lemma lacing_vals_ok_unroll' : forall os pn, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_unroll os pn)).
Proof.
intros os pn H. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| exact H].
destruct (negb (os_pageno _ =? -1)); cbn.
- apply Forall_app. split; [apply Forall_ztake; destruct os; exact H|]. constructor; [cbv beta; lia| constructor].
- apply Forall_ztake. destruct os; exact H.
Qed.
#[using="Type"] Lemma granules_ok_unroll : forall os pn, granules_ok (os_granules os) -> granules_ok (os_granules (pagein_unroll os pn)).
Proof.
intros os pn H. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| exact H].
destruct (negb (os_pageno _ =? -1)); cbn.
- apply Forall_app. split; [apply Forall_ztake; destruct os; exact H|]. constructor; [unfold GRANULE_UNSPEC; cbv beta; lia| constructor].
- apply Forall_ztake. destruct os; exact H.
Qed.

#[using="Type"] Lemma body_returned_set_blocks : forall {ptr} (os : stream_st ptr) b bs l g ls,
os_body_returned (set_blocks os b bs l g ls) = os_body_returned os.
Proof. intros. destruct os; reflexivity. Qed.
#[using="Type"] Lemma vals_set_blocks : forall os b bs l g ls,
os_lacing (set_blocks os b bs l g ls) = os_lacing os /\ os_granules (set_blocks os b bs l g ls) = os_granules os.
Proof. intros. destruct os; split; reflexivity. Qed.
#[using="Type"] Lemma vals_pagein_body : forall os body skipped bodysize,
os_lacing (pagein_body os body skipped bodysize) = os_lacing os /\ os_granules (pagein_body os body skipped bodysize) = os_granules os.
Proof. intros. destruct os; split; reflexivity. Qed.

#[using="Type"] Lemma lacing_vals_ok_segments : forall os hdr bos segptr,
bytes_ok (lacing_of hdr) -> lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_segments os hdr bos segptr)).
Proof.
intros os hdr bos segptr Hb H. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f] p] sv] eqn:E.
destruct (seg_loop_vals _ _ _ _ _ _ _ _ _ _ (bytes_ok_zdrop segptr _ Hb) E) as [L _].
assert (A : lacing_vals_ok (os_lacing os ++ lac)).
{ apply Forall_app. split; [exact H|]. eapply Forall_impl; [| exact L]. cbv beta. intros; lia. }
unfold set_lacing, set_tail; cbn.
destruct (negb (ogg_page_eos hdr =? 0)); [| exact A].
destruct (0 <? f); [| exact A].
apply Forall_zupd; [exact A|]. apply lor512_range. apply (Forall_znth _ _ _ A). lia.
Qed.

#[using="Type"] Lemma granules_ok_segments : forall os hdr bos segptr,
bytes_ok (lacing_of hdr) -> granules_ok (os_granules os) -> granules_ok (os_granules (pagein_segments os hdr bos segptr)).
Proof.
intros os hdr bos segptr Hb H. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f] p] sv] eqn:E.
destruct (seg_loop_vals _ _ _ _ _ _ _ _ _ _ (bytes_ok_zdrop segptr _ Hb) E) as [_ G].
assert (A : granules_ok (os_granules os ++ gran)).
{ apply Forall_app. split; [exact H|]. eapply Forall_impl; [| exact G]. cbv beta. intros; lia. }
unfold set_lacing, set_tail; cbn.
destruct (negb (sv =? -1)); [| exact A].
apply Forall_zupd; [exact A|]. unfold ogg_page_granulepos. apply s64_range.
Qed.
End Vals.

Section Leaf.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Implicit Types os : stream_st ptr.

#[using="Type"] Lemma in_leaves_munr : forall {A} (s : St) (x : A) s', in_leaves (munr (A:=A) s) (Ok (x, s')) -> False.
Proof. intros A s x s' H. cbn in H. discriminate H. Qed.

#[using="Type"] Lemma mfree_opt_leaf : forall o s x s', in_leaves (mfree_opt lib_free o s) (Ok (x, s')) -> True.
Proof. intros; exact I. Qed.

#[using="Type"] Lemma clear_leaf : forall os s x s', in_leaves (ogg_stream_clear lib_free os s) (Ok (x, s')) -> x = stream_zero.
Proof.
intros os s x s' H. unfold ogg_stream_clear in H.
apply in_leaves_mbind in H as (u1 & s1 & _ & H).
apply in_leaves_mbind in H as (u2 & s2 & _ & H).
apply in_leaves_mbind in H as (u3 & s3 & _ & H).
apply in_leaves_mret in H. congruence.
Qed.

#[using="Type"] Lemma lacing_expand_leaf : forall os needed s r os' s',
os_has_blocks os -> 0 <= needed -> 0 <= os_lacing_storage os ->
in_leaves (os_lacing_expand lib_realloc lib_free os needed s) (Ok ((r, os'), s')) ->
(r = 0 /\ exists l g ls, 0 <= ls /\ os_lacing_storage os <= ls /\ ls <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * needed + 32) /\
os' = set_blocks os (os_body_data os) (os_body_storage os) (Some l) (Some g) ls)
\/ (r = -1 /\ os' = stream_zero).
Proof.
intros os needed s r os' s' sfH_; first [ sf_destruct 6%nat sfH_ as b l g Hb Hl Hg | sf_fb; destruct sfH_ as (b & l & g & Hb & Hl & Hg) ]; intros Hn Hs H. unfold os_lacing_expand in H.
destruct (os_lacing_fill os <? os_lacing_storage os - needed) eqn:Hfit.
{ apply in_leaves_mret in H. injection H as -> -> ->. left. split; [reflexivity|].
first [ unshelve sf_eexists 3%nat; [ exact (l) | exact (g) | exact ((os_lacing_storage os)) | ] | sf_fb; exists l, g, (os_lacing_storage os) ]. split; [exact Hs|]. split; [lia|]. split; [lia|]. rewrite <- Hl, <- Hg. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit.
destruct (LONG_MAX - needed <? os_lacing_storage os).
{ apply in_leaves_mbind in H as (z & s1 & Hz & H). apply clear_leaf in Hz. apply in_leaves_mret in H. injection H as -> -> ->. right. auto. }
rewrite Hl, Hg in H.
set (ls := if os_lacing_storage os + needed <? LONG_MAX - 32 then _ else _) in H.
assert (Hls : 0 <= ls /\ os_lacing_storage os <= ls /\ ls <= os_lacing_fill os + 2 * needed + 32).
{ subst ls. destruct (Z.ltb_spec (os_lacing_storage os + needed) (LONG_MAX - 32)); lia. }
apply in_leaves_mbind in H as (r1 & s1 & _ & H).
destruct r1 as [l'|].
- apply in_leaves_mbind in H as (r2 & s2 & _ & H). destruct r2 as [g'|].
+ apply in_leaves_mret in H. injection H as -> -> ->. left. split; [reflexivity|].
first [ unshelve sf_eexists 3%nat; [ exact (l') | exact (g') | exact (ls) | ] | sf_fb; exists l', g', ls ]. split; [lia|]. split; [lia|]. split; [lia|]. destruct os; reflexivity.
+ apply in_leaves_mbind in H as (z & s3 & Hz & H). apply clear_leaf in Hz. apply in_leaves_mret in H. injection H as -> -> ->. right. auto.
- apply in_leaves_mbind in H as (z & s3 & Hz & H). apply clear_leaf in Hz. apply in_leaves_mret in H. injection H as -> -> ->. right. auto.
Qed.

#[using="Type"] Lemma body_expand_leaf : forall os needed s r os' s',
os_has_blocks os -> 0 <= needed -> 0 <= os_body_storage os ->
in_leaves (os_body_expand lib_realloc lib_free os needed s) (Ok ((r, os'), s')) ->
(r = 0 /\ exists b bs, 0 <= bs /\ os_body_storage os <= bs /\ bs <= Z.max (os_body_storage os) (os_body_fill os + 2 * needed + 1024) /\
os' = set_blocks os (Some b) bs (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os))
\/ (r = -1 /\ os' = stream_zero).
Proof.
intros os needed s r os' s' sfH_; first [ sf_destruct 6%nat sfH_ as b l g Hb Hl Hg | sf_fb; destruct sfH_ as (b & l & g & Hb & Hl & Hg) ]; intros Hn Hs H. unfold os_body_expand in H.
destruct (os_body_fill os <? os_body_storage os - needed) eqn:Hfit.
{ apply in_leaves_mret in H. injection H as -> -> ->. left. split; [reflexivity|].
exists b, (os_body_storage os). split; [exact Hs|]. split; [lia|]. split; [lia|]. rewrite <- Hb. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit.
destruct (LONG_MAX - needed <? os_body_storage os).
{ apply in_leaves_mbind in H as (z & s1 & Hz & H). apply clear_leaf in Hz. apply in_leaves_mret in H. injection H as -> -> ->. right. auto. }
rewrite Hb in H.
set (bs := if os_body_storage os + needed <? LONG_MAX - 1024 then _ else _) in H.
assert (Hbs : 0 <= bs /\ os_body_storage os <= bs /\ bs <= os_body_fill os + 2 * needed + 1024).
{ subst bs. destruct (Z.ltb_spec (os_body_storage os + needed) (LONG_MAX - 1024)); lia. }
apply in_leaves_mbind in H as (r1 & s1 & _ & H).
destruct r1 as [b'|].
- apply in_leaves_mret in H. injection H as -> -> ->. left. split; [reflexivity|].
exists b', bs. replace (bs * 1) with bs by lia. split; [lia|]. split; [lia|]. split; [lia| reflexivity].
- apply in_leaves_mbind in H as (z & s3 & Hz & H). apply clear_leaf in Hz. apply in_leaves_mret in H. injection H as -> -> ->. right. auto.
Qed.

#[using="Type"] Lemma hstream_ok_zero : hstream_ok (stream_zero (ptr:=ptr)).
Proof.
unfold hstream_ok. split; [apply stream_zero_inv|]. split; [apply stream_zero_body_inv|]. unfold stream_zero; cbn.
split; [constructor|]. split; [constructor|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros H; exfalso; apply H; reflexivity|]. split; [intros H; exfalso; apply H; reflexivity|]. right; reflexivity.
Qed.

#[using="Type"] Theorem pagein_leaf_proof_gen : forall os (hdr body : list Z) (s s' : St) (r : Z) os',
hstream_ok os ->
bytes_ok hdr -> 27 <= zlength hdr -> 0 <= znth hdr 26 -> zlength hdr = 27 + znth hdr 26 ->
zsum (lacing_of hdr) = zlength body -> bytes_ok body ->
in_leaves (ogg_stream_pagein lib_realloc lib_free os hdr body s) (Ok ((r, os'), s')) ->
(r = 0 \/ r = -1)
/\ hstream_ok os'
/\ (os_serialno os' = os_serialno os \/ os' = stream_zero)
/\ 0 <= os_lacing_fill os' <= os_lacing_fill os + znth hdr 26 + 1
/\ 0 <= os_body_fill os' <= os_body_fill os + zlength body
/\ os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32)
/\ os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024)
/\ os_body_returned os' = 0.
Proof.
intros os hdr body s s' r os' HOK Hhdr H27 Hseg Hlen Hsum Hbody H.
pose proof HOK as sfP_; first [ sf_destruct 12%nat sfP_ as Hinv Hbi Hlv Hgv Hbs Hls Hbn Hln Hgn Hb16 Hl1024 Hall | sf_fb; destruct sfP_ as (Hinv & Hbi & Hlv & Hgv & Hbs & Hls & Hbn & Hln & Hgn & Hb16 & Hl1024 & Hall) ].
assert (Hlac : bytes_ok (lacing_of hdr)) by (unfold lacing_of; apply bytes_ok_ztake, bytes_ok_zdrop; exact Hhdr).
pose proof Hinv as (SA & SB & _). pose proof (body_inv_fill_nonneg os Hbi) as Hbf0.
pose proof (body_inv_returned_le_fill os Hbi) as Hbr0. pose proof Hbi as (_ & HbrNN & _).
pose proof (zlength_nonneg body) as ZB.
assert (ZLEN : zlength (lacing_of hdr) <= znth hdr 26).
{ pose proof (zlength_ztake_le_n (znth hdr 26) (zdrop 27 hdr) Hseg) as ZL. exact ZL. }
unfold ogg_stream_pagein in H.

destruct (ogg_stream_check os) eqn:Hck.
{ apply in_leaves_mret in H. injection H as -> -> ->. split; [right; reflexivity|]. split; [exact HOK|]. split; [left; reflexivity|].
assert (BR0 : os_body_returned os = 0).
{ unfold ogg_stream_check in Hck. destruct Hall as [(B1 & B2 & B3)| ->]; [| reflexivity].
destruct (os_body_data os); [cbn in Hck; discriminate| exfalso; apply B1; reflexivity]. }
repeat split; lia. }
assert (Hhas : os_has_blocks os).
{ unfold ogg_stream_check in Hck. destruct Hall as [(B1 & B2 & B3)| ->]; [| cbn in Hck; discriminate].
unfold os_has_blocks. destruct (os_body_data os) as [b|]; [| exfalso; apply B1; reflexivity].
destruct (os_lacing_vals os) as [l|]; [| exfalso; apply B2; reflexivity].
destruct (os_granule_vals os) as [g|]; [| exfalso; apply B3; reflexivity]. first [ unshelve sf_eexists 3%nat; [ exact (b) | exact (l) | exact (g) | ] | sf_fb; exists b, l, g ]; auto. }
first [ sf_destruct 6%nat Hhas as b0 l0 g0 Eb0 El0 Eg0 | sf_fb; destruct Hhas as (b0 & l0 & g0 & Eb0 & El0 & Eg0) ].
pose proof (pagein_returned_inv os Hinv) as sfP_; first [ sf_destruct 9%nat sfP_ as Hinv1 Hret1 Elv Egv Ebd Els Ebs Esn Epn | sf_fb; destruct sfP_ as (Hinv1 & Hret1 & Elv & Egv & Ebd & Els & Ebs & Esn & Epn) ].
pose proof (pagein_returned_body_inv os Hinv Hbi) as sfP_; first [ sf_destruct 4%nat sfP_ as Hbody1 Hbr1 Hbf1 Hlf1 | sf_fb; destruct sfP_ as (Hbody1 & Hbr1 & Hbf1 & Hlf1) ].
pose proof (lacing_vals_ok_returned' os Hlv) as Hlv1. pose proof (granules_ok_returned os Hgv) as Hgv1.
set (os1 := pagein_returned os) in *.
assert (Hhas1 : os_has_blocks os1) by (exists b0, l0, g0; rewrite Ebd, Elv, Egv; auto).
assert (HOK1 : hstream_ok os1).
{ unfold hstream_ok. rewrite Ebd, Elv, Egv, Ebs, Els. split; [exact Hinv1|]. split; [exact Hbody1|]. split; [exact Hlv1|]. split; [exact Hgv1|].
split; [lia|]. split; [lia|]. split; [exact Hbn|]. split; [exact Hln|]. split; [exact Hgn|]. split; [exact Hb16|]. split; [exact Hl1024|].
left. rewrite Eb0, El0, Eg0. repeat split; discriminate. }
assert (SAME1 : (r = 0 \/ r = -1) /\ hstream_ok os1 /\ os_serialno os1 = os_serialno os /\
0 <= os_lacing_fill os1 <= os_lacing_fill os + znth hdr 26 + 1 /\ 0 <= os_body_fill os1 <= os_body_fill os + zlength body /\
os_lacing_storage os1 <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32) /\
os_body_storage os1 <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024) -> True) by (intros; exact I).
clear SAME1.

destruct (negb (ogg_page_serialno hdr =? os_serialno os1)).
{ apply in_leaves_mret in H. injection H as -> -> ->. split; [right; reflexivity|]. split; [exact HOK1|]. split; [left; exact Esn|]. rewrite Hlf1, Hbf1, Els, Ebs, Hbr1. repeat split; lia. }
destruct (0 <? ogg_page_version hdr).
{ apply in_leaves_mret in H. injection H as -> -> ->. split; [right; reflexivity|]. split; [exact HOK1|]. split; [left; exact Esn|]. rewrite Hlf1, Hbf1, Els, Ebs, Hbr1. repeat split; lia. }

apply in_leaves_mbind in H as ([r2 os2] & s2 & HLE & H). cbn beta iota in H.
apply lacing_expand_leaf in HLE; [| exact Hhas1| lia| rewrite Els; exact Hls].
destruct HLE as [(-> & (l2 & g2 & ls2 & Hls2 & Hls2M & Hls2B & Eos2)) | (-> & ->)].
2:{ cbn in H. apply in_leaves_mret in H. injection H as -> -> ->. split; [right; reflexivity|]. split; [apply hstream_ok_zero|]. split; [right; reflexivity|].
unfold stream_zero; cbn -[znth zlength]. repeat split; lia. }
cbn [negb Z.eqb] in H.
assert (Hinv2 : stream_inv os2 /\ os_lacing_returned os2 = 0 /\ body_inv os2 /\ os_lacing_fill os2 = os_lacing_fill os1 /\ os_body_fill os2 = os_body_fill os1 /\
os_body_storage os2 = os_body_storage os /\ os_lacing_storage os2 = ls2 /\ os_lacing os2 = os_lacing os1 /\ os_granules os2 = os_granules os1 /\
os_body_data os2 = Some b0 /\ os_lacing_vals os2 = Some l2 /\ os_granule_vals os2 = Some g2 /\ os_serialno os2 = os_serialno os).
{ rewrite Eos2. pose proof (set_blocks_inv os1 (os_body_data os1) (os_body_storage os1) (Some l2) (Some g2) ls2 Hinv1) as [A B].
split; [exact A|]. split; [rewrite B; exact Hret1|]. split; [apply set_blocks_body_inv; exact Hbody1|].
unfold set_blocks; cbn. rewrite Ebs, Ebd, Eb0, Esn. repeat split; reflexivity. }
first [ rename Hinv2 into sfR_; sf_destruct 13%nat sfR_ as Hinv2 Hret2 Hbody2 Hlf2 Hbf2 Ebs2 Els2 Elac2 Egr2 Ebd2 Elv2 Egv2 Esn2 | sf_fb; destruct Hinv2 as (Hinv2 & Hret2 & Hbody2 & Hlf2 & Hbf2 & Ebs2 & Els2 & Elac2 & Egr2 & Ebd2 & Elv2 & Egv2 & Esn2) ].
assert (Hbrt2 : os_body_returned os2 = 0) by (rewrite Eos2, body_returned_set_blocks; exact Hbr1).

pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2) as sfP_; first [ sf_destruct 8%nat sfP_ as Hinv3 Hret3 Elv3 Egv3 Ebd3 Els3 Ebs3 Hlf3 | sf_fb; destruct sfP_ as (Hinv3 & Hret3 & Elv3 & Egv3 & Ebd3 & Els3 & Ebs3 & Hlf3) ].
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2 Hbody2) as (Hbody3 & Hbf3 & Hbr3).
pose proof (lacing_vals_ok_unroll' os2 (ogg_page_pageno hdr) ltac:(rewrite Elac2; exact Hlv1)) as Hlv3.
pose proof (granules_ok_unroll os2 (ogg_page_pageno hdr) ltac:(rewrite Egr2; exact Hgv1)) as Hgv3.
assert (Esn3 : os_serialno (pagein_unroll os2 (ogg_page_pageno hdr)) = os_serialno os2).
{ unfold pagein_unroll. destruct (negb _); [| reflexivity]. destruct (negb _); destruct os2; reflexivity. }
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.
assert (Hhas3 : os_has_blocks os3) by (exists b0, l2, g2; rewrite Ebd3, Elv3, Egv3; auto).
pose proof (pagein_skip_sum os3 hdr Hlac) as Bsk.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped]. destruct Bsk as [Hsegptr Hskipped].
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as Hzs.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hlac)) as N1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hlac)) as N2.
assert (Hbsz : 0 <= zlength body - skipped <= zlength body) by lia.
pose proof Hinv3 as (TA & TB & _). pose proof (body_inv_fill_nonneg os3 Hbody3) as Hbf3nn.

apply in_leaves_mbind in H as ([r4 os4] & s4 & HBE & H). cbn beta iota in H.
assert (CASE4 : (r4 = 0 /\ exists os3', stream_inv os3' /\ os_lacing_returned os3' = 0 /\ os_has_blocks os3' /\ body_inv os3' /\
os_lacing os3' = os_lacing os3 /\ os_granules os3' = os_granules os3 /\ os_lacing_fill os3' = os_lacing_fill os3 /\ os_lacing_packet os3' = os_lacing_packet os3 /\
os_body_fill os3' = os_body_fill os3 /\ os_lacing_storage os3' = os_lacing_storage os3 /\ os_serialno os3' = os_serialno os3 /\
os_lacing_vals os3' = os_lacing_vals os3 /\ os_granule_vals os3' = os_granule_vals os3 /\ os_body_data os3' <> None /\
os_body_storage os <= os_body_storage os3' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024) /\
os_body_returned os3' = 0 /\
os4 = (if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3'))
\/ (r4 <> 0 /\ os4 = stream_zero)).
{ destruct (negb (zlength body - skipped =? 0)) eqn:Hnz.
- apply in_leaves_mbind in HBE as ([r5 os5] & s5 & HBE & HK). cbn beta iota in HK.
apply body_expand_leaf in HBE; [| exact Hhas3| lia| rewrite Ebs3; lia].
destruct HBE as [(-> & (b4 & bs4 & Hbs4 & Hbs4M & Hbs4B & Eos5)) | (-> & ->)].
+ cbn [negb Z.eqb] in HK. apply in_leaves_mret in HK. injection HK as -> -> ->. left. split; [reflexivity|]. exists os5. subst os5.
pose proof (set_blocks_inv os3 (Some b4) bs4 (os_lacing_vals os3) (os_granule_vals os3) (os_lacing_storage os3) Hinv3) as [A4 B4].
split; [exact A4|]. split; [rewrite B4; exact Hret3|].
split; [first [ unshelve sf_eexists 3%nat; [ exact (b4) | exact (l2) | exact (g2) | ] | sf_fb; exists b4, l2, g2 ]; unfold set_blocks; cbn; rewrite Elv3, Egv3; auto|].
split; [apply set_blocks_body_inv; exact Hbody3|].
unfold set_blocks; cbn. rewrite Ebs3, Ebs2 in Hbs4B, Hbs4M. repeat split; try reflexivity; try lia; try discriminate.
+ cbn in HK. apply in_leaves_mret in HK. injection HK as -> -> ->. right. split; [lia| reflexivity].
- apply in_leaves_mret in HBE. injection HBE as -> -> ->. left. split; [reflexivity|]. exists os3.
split; [exact Hinv3|]. split; [exact Hret3|]. split; [exact Hhas3|]. split; [exact Hbody3|].
do 9 (split; [reflexivity|]). split; [rewrite Ebd3, Ebd2; discriminate|]. split; [rewrite Ebs3, Ebs2; lia|]. split; [rewrite Hbr3; exact Hbrt2| reflexivity]. }
destruct CASE4 as [(-> & (os3' & I3' & R3' & Hhas3' & B3' & L3' & G3' & LF3' & LP3' & BF3' & LS3' & SN3' & LV3' & GV3' & BD3' & BS3' & BR3' & ->)) | (Hne & ->)].
2:{ destruct (negb (r4 =? 0)) eqn:En.
- apply in_leaves_mret in H. injection H as -> -> ->. split; [right; reflexivity|]. split; [apply hstream_ok_zero|]. split; [right; reflexivity|]. unfold stream_zero; cbn -[znth zlength]. repeat split; lia.
- apply Bool.negb_false_iff in En. apply Z.eqb_eq in En. lia. }
cbn [negb Z.eqb] in H. apply in_leaves_mret in H. injection H as -> -> ->.
pose proof (pagein_body_segments_body_inv os3' hdr body bos segptr skipped I3' R3' B3' Hlac Hsum Hsegptr Hskipped) as PBS.
cbv zeta in PBS. first [ sf_destruct 4%nat PBS as Hbody5 Hbf5 _ Hbr5 | sf_fb; destruct PBS as (Hbody5 & Hbf5 & _ & Hbr5) ].
set (os4 := if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3') in *.
assert (H4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ os_lacing_fill os4 = os_lacing_fill os3 /\
os_lacing_packet os4 = os_lacing_packet os3 /\ os_lacing_storage os4 = os_lacing_storage os3 /\
os_body_storage os4 = os_body_storage os3' /\ os_lacing os4 = os_lacing os3 /\ os_granules os4 = os_granules os3 /\
os_serialno os4 = os_serialno os3 /\ os_lacing_vals os4 = os_lacing_vals os3 /\ os_granule_vals os4 = os_granule_vals os3 /\ os_body_data os4 <> None).
{ subst os4. destruct (negb (zlength body - skipped =? 0)).
- pose proof (pagein_body_inv os3' body skipped (zlength body - skipped) I3') as [A B].
split; [exact A|]. split; [rewrite B; exact R3'|].
unfold pagein_body, set_body; cbn. rewrite LF3', LP3', LS3', L3', G3', SN3', LV3', GV3'. repeat split; try reflexivity. exact BD3'.
- rewrite <- LF3', <- LP3', <- LS3', <- L3', <- G3', <- SN3', <- LV3', <- GV3'. split; [exact I3'|]. split; [exact R3'|]. repeat split; try reflexivity. exact BD3'. }
first [ sf_destruct 12%nat H4 as I4 R4 LF4 LP4 LS4 BS4 L4 G4 SN4 LV4 GV4 BD4 | sf_fb; destruct H4 as (I4 & R4 & LF4 & LP4 & LS4 & BS4 & L4 & G4 & SN4 & LV4 & GV4 & BD4) ].
pose proof I4 as (U1 & U2 & _).
pose proof (pagein_segments_frame os4 hdr bos segptr Hlac Hsegptr U2) as FR. cbv zeta in FR.
first [ sf_destruct 8%nat FR as F1 F2 F3 F4 F5 F6 F7 F8 | sf_fb; destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8) ].
assert (SN5 : os_serialno (pagein_segments os4 hdr bos segptr) = os_serialno os4) by (unfold pagein_segments; destruct (seg_loop _ _ _ _ _) as [[[[? ?] ?] ?] ?]; reflexivity).
split; [left; reflexivity|]. split.
{ unfold hstream_ok. split; [apply pagein_segments_inv; auto; lia|]. split; [exact Hbody5|].
split; [apply lacing_vals_ok_segments; [exact Hlac| rewrite L4; exact Hlv3]|].
split; [apply granules_ok_segments; [exact Hlac| rewrite G4; exact Hgv3]|].
rewrite F1, F2, F3, F4, F5, LS4, BS4, LV4, GV4, Els3, Els2, Elv3, Egv3, Elv2, Egv2.
split; [lia|]. split; [lia|]. split; [intros E; exfalso; exact (BD4 E)|]. split; [intros; discriminate|]. split; [intros; discriminate|].
split; [intros _; pose proof (Hb16 ltac:(rewrite Eb0; discriminate)); lia|].
split; [intros _; pose proof (Hl1024 ltac:(rewrite El0; discriminate)); rewrite Els in Hls2M; lia|].
left. split; [exact BD4|]. split; discriminate. }
split; [left; rewrite SN5, SN4, Esn3, Esn2; reflexivity|].
rewrite Hbf5, BF3', F8, F5, F4, LF4, LS4, BS4, Els3, Els2, Hbr5, BR3'. rewrite Els in Hls2B. lia.
Qed.
End Leaf.

Theorem pagein_leaf_proof : pagein_leaf_stmt.
Proof.
intros St ptr lib_realloc lib_free os hdr body s s' r os' HOK Hh H27 Hseg Hlen Hsum Hb HL.
pose proof (pagein_leaf_proof_gen lib_realloc lib_free os hdr body s s' r os' HOK Hh H27 Hseg Hlen Hsum Hb HL) as sfP_; first [ sf_destruct 8%nat sfP_ as A1 A2 A3 A4 A5 A6 A7 _ | sf_fb; destruct sfP_ as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _) ].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6| exact A7].
Qed.

Theorem pagein_leaf_returned :
forall (St ptr : Type) (lib_realloc : ptr -> Z -> M St (option ptr)) (lib_free : ptr -> M St unit)
(os : stream_st ptr) (hdr body : list Z) (s s' : St) (r : Z) (os' : stream_st ptr),
hstream_ok os ->
bytes_ok hdr -> 27 <= zlength hdr -> 0 <= znth hdr 26 -> zlength hdr = 27 + znth hdr 26 ->
zsum (lacing_of hdr) = zlength body -> bytes_ok body ->
in_leaves (ogg_stream_pagein lib_realloc lib_free os hdr body s) (Ok ((r, os'), s')) ->
os_body_returned os' = 0.
Proof.
intros St ptr lib_realloc lib_free os hdr body s s' r os' HOK Hh H27 Hseg Hlen Hsum Hb HL.
pose proof (pagein_leaf_proof_gen lib_realloc lib_free os hdr body s s' r os' HOK Hh H27 Hseg Hlen Hsum Hb HL) as sfP_; first [ sf_destruct 8%nat sfP_ as _ _ _ _ _ _ _ A8 | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & A8) ]. exact A8.
Qed.
