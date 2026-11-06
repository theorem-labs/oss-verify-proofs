(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1nv X1rb.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ListFacts.

#[using="Type"] Lemma low8_nonneg : forall v, 0 <= low8 v.
Proof. intros v. unfold low8. apply Z.land_nonneg. right. lia. Qed.

#[using="Type"] Lemma low8_lt256 : forall v, low8 v < 256.
Proof.
intros v. unfold low8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

#[using="Type"] Lemma sum_low_nonneg : forall l, 0 <= sum_low l.
Proof. induction l as [|v l IH]; cbn; [lia|]. pose proof (low8_nonneg v). unfold low8 in *. lia. Qed.

#[using="Type"] Lemma sum_low_app : forall l1 l2, sum_low (l1 ++ l2) = sum_low l1 + sum_low l2.
Proof. induction l1 as [|v l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

#[using="Type"] Lemma ztake_zdrop_split : forall (k : Z) (l : list Z), 0 <= k -> l = ztake k l ++ zdrop k l.
Proof. intros k l Hk. unfold ztake, zdrop. symmetry. apply firstn_skipn. Qed.

#[using="Type"] Lemma sum_low_split : forall k l, 0 <= k -> sum_low l = sum_low (ztake k l) + sum_low (zdrop k l).
Proof. intros k l Hk. rewrite (ztake_zdrop_split k l Hk) at 1. apply sum_low_app. Qed.

#[using="Type"] Lemma zdrop_zdrop : forall a b l, 0 <= a -> 0 <= b -> zdrop b (zdrop a l) = zdrop (a + b) l.
Proof. intros. unfold zdrop. rewrite skipn_skipn. f_equal. lia. Qed.

#[using="Type"] Lemma zdrop_0 : forall l, zdrop 0 l = l.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma sum_low_zdrop_split : forall a k l, 0 <= a -> 0 <= k ->
sum_low (zdrop a l) = sum_low (zslice a k l) + sum_low (zdrop (a + k) l).
Proof.
intros a k l Ha Hk. unfold zslice. rewrite (sum_low_split k (zdrop a l) Hk). rewrite zdrop_zdrop by lia. reflexivity.
Qed.

#[using="Type"] Lemma sum_low_bytes : forall l, bytes_ok l -> sum_low l = zsum l.
Proof.
induction l as [|v l IH]; intros Hb; cbn; [reflexivity|].
inversion Hb as [|v' l' Hv Hl]; subst. rewrite IH by exact Hl. pose proof (low8_byte v Hv) as E. unfold low8 in E. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma zsum_split : forall k l, 0 <= k -> zsum l = zsum (ztake k l) + zsum (zdrop k l).
Proof. intros k l Hk. rewrite (ztake_zdrop_split k l Hk) at 1. apply zsum_app. Qed.

#[using="Type"] Lemma ztake_full : forall n l, zlength l <= n -> ztake n l = l.
Proof. intros. unfold ztake, zlength in *. apply firstn_all2. lia. Qed.

#[using="Type"] Lemma zdrop_nil : forall n l, zlength l <= n -> 0 <= n -> zdrop n l = [].
Proof. intros. unfold zdrop, zlength in *. apply skipn_all2. lia. Qed.

#[using="Type"] Lemma zslice_full_tail : forall a n l, 0 <= a -> zlength l <= a + n -> zslice a n l = zdrop a l.
Proof.
intros a n l Ha H. unfold zslice.
destruct (Z.le_gt_cases a (zlength l)).
- apply ztake_full. rewrite zlength_zdrop by lia. lia.
- rewrite zdrop_nil by lia. unfold ztake. rewrite firstn_nil. reflexivity.
Qed.

Definition lacing_val_ok (v : Z) : Prop := 0 <= v < 1024 \/ low8 v = 0.

#[using="Type"] Lemma lacing_val_ok_byte : forall v, 0 <= v < 256 -> lacing_val_ok v.
Proof. intros. left. lia. Qed.

#[using="Type"] Lemma lor_lt_pow2 : forall v m n, 0 <= v < 2 ^ n -> 0 <= m < 2 ^ n -> Z.lor v m < 2 ^ n.
Proof.
intros v m n Hv Hm.
destruct (Z.lt_ge_cases n 0) as [Hn|Hn]. { rewrite Z.pow_neg_r in Hv by lia. lia. }
assert (H1 : Z.lor v m mod 2 ^ n = Z.lor v m).
{ rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia.
rewrite !Z.mod_small by lia. reflexivity. }
rewrite <- H1. apply Z.mod_pos_bound. lia.
Qed.

#[using="Type"] Lemma lacing_val_ok_lor256 : forall v, 0 <= v < 256 -> lacing_val_ok (Z.lor v 256).
Proof.
intros v Hv. left. split; [apply Z.lor_nonneg; lia|].
change 1024 with (2 ^ 10). apply lor_lt_pow2; [lia|]. lia.
Qed.

#[using="Type"] Lemma lacing_val_ok_lor512 : forall v, lacing_val_ok v -> lacing_val_ok (Z.lor v 512).
Proof.
intros v [Hv|Hv].
- left. split; [apply Z.lor_nonneg; lia|]. change 1024 with (2 ^ 10). apply lor_lt_pow2; lia.
- right. rewrite low8_lor512. exact Hv.
Qed.

#[using="Type"] Lemma lacing_val_ok_hole : lacing_val_ok 1024.
Proof. right. reflexivity. Qed.

#[using="Type"] Lemma lacing_val_hole_low8 : forall v, lacing_val_ok v -> Z.land v 1024 <> 0 -> low8 v = 0.
Proof.
intros v [Hv|Hv] Hh; [|exact Hv]. exfalso. apply Hh.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n 10) as [->|Hne].
- destruct (Z.testbit v 10) eqn:T; [|reflexivity]. exfalso.
assert (2 ^ 10 <= v). { apply Z.testbit_true in T; [|lia]. change 1024 with (2^10) in Hv.
pose proof (Z.div_pos v (2^10)). pose proof (Z.mod_pos_bound (v / 2 ^ 10) 2).
assert (1 <= v / 2 ^ 10) by (destruct (Z.eq_dec (v / 2 ^ 10) 0) as [E|E]; [rewrite E in T; cbn in T; lia| lia]).
pose proof (Z.mul_div_le v (2^10) ltac:(lia)). lia. }
change 1024 with (2 ^ 10) in Hv. lia.
- change 1024 with (2 ^ 10). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 10 n); [lia|]. apply Bool.andb_false_r.
Qed.

#[using="Type"] Lemma Forall_ztake : forall (P : Z -> Prop) n l, Forall P l -> Forall P (ztake n l).
Proof. intros P n l H. unfold ztake. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
#[using="Type"] Lemma Forall_zdrop : forall (P : Z -> Prop) n l, Forall P l -> Forall P (zdrop n l).
Proof. intros P n l H. unfold zdrop. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.

#[using="Type"] Lemma upd_nat_Forall : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_nat l i v).
Proof.
induction l as [|x l IH]; intros [|i] v Hl Hv; cbn; auto.
- inversion Hl; subst. constructor; auto.
- inversion Hl; subst. constructor; auto.
Qed.
#[using="Type"] Lemma Forall_zupd : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (zupd l i v).
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_Forall. Qed.

#[using="Type"] Lemma sum_low_upd_nat : forall l i v, (i < length l)%nat -> low8 v = low8 (nth i l 0) -> sum_low (upd_nat l i v) = sum_low l.
Proof.
induction l as [|x l IH]; intros [|i] v Hi Hv; cbn in *; try lia.
- unfold low8 in Hv. rewrite Hv. reflexivity.
- rewrite IH; auto. lia.
Qed.

#[using="Type"] Lemma sum_low_zupd_lor512 : forall l i, sum_low (zupd l i (Z.lor (znth l i) 512)) = sum_low l.
Proof.
intros l i. unfold zupd, znth. destruct (Z.ltb_spec i 0); [reflexivity|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- apply sum_low_upd_nat; [assumption|]. apply low8_lor512.
- rewrite nth_overflow by lia.
revert H0. generalize (Z.to_nat i). clear. induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma Forall_In_znth : forall (P : Z -> Prop) l i, Forall P l -> P 0 -> P (znth l i).
Proof.
intros P l i H H0. unfold znth. destruct (i <? 0); [exact H0|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- rewrite Forall_forall in H. apply H. apply nth_In. assumption.
- rewrite nth_overflow by lia. exact H0.
Qed.

#[using="Type"] Lemma ztake_0 : forall l : list Z, ztake 0 l = [].
Proof. reflexivity. Qed.
#[using="Type"] Lemma ztake_1_cons : forall x (l : list Z), ztake 1 (x :: l) = [x].
Proof. reflexivity. Qed.

#[using="Type"] Lemma znth_head_zdrop : forall (l : list Z) n x t, 0 <= n -> zdrop n l = x :: t -> znth l n = x.
Proof.
intros l n x t Hn Ed. replace n with (n + 0) by lia. rewrite <- znth_zdrop by lia. rewrite Ed. reflexivity.
Qed.

#[using="Type"] Lemma skip_continued_sum : forall l n s, skip_continued l = (n, s) -> 0 <= n <= zlength l /\ s = zsum (ztake n l).
Proof.
induction l as [|v l IH]; intros n s E; cbn [skip_continued] in E.
- inversion E; subst. rewrite zlength_nil, ztake_0. cbn [zsum]. lia.
- rewrite zlength_cons. destruct (Z.ltb_spec v 255).
+ inversion E; subst. rewrite ztake_1_cons. cbn [zsum]. pose proof (zlength_nonneg l). lia.
+ destruct (skip_continued l) as [n' s'] eqn:E'. inversion E; subst. destruct (IH n' s' eq_refl) as [Hn Hs].
split; [lia|]. unfold ztake in *. replace (Z.to_nat (n' + 1)) with (S (Z.to_nat n')) by lia. cbn [firstn zsum]. lia.
Qed.

#[using="Type"] Lemma seg_loop_sum : forall vals bos fill packet saved lac gran f p s,
Forall (fun v => 0 <= v < 256) vals ->
seg_loop vals bos fill packet saved = (lac, gran, f, p, s) ->
sum_low lac = zsum vals /\ Forall lacing_val_ok lac.
Proof.
induction vals as [|v vals IH]; intros bos fill packet saved lac gran f p s Hb E; cbn [seg_loop] in E.
- inversion E; subst. cbn. split; [reflexivity| constructor].
- inversion Hb as [|v' vals' Hv Hvals]; subst v' vals'.
destruct (seg_loop vals false (fill + 1) (if v <? 255 then fill + 1 else packet) (if v <? 255 then fill else saved))
as [[[[lac' gran'] f'] p'] s'] eqn:E'.
injection E as E1 E2 E3 E4 E5. subst lac gran f p s.
destruct (IH _ _ _ _ _ _ _ _ _ Hvals E') as [Hs Hok].
cbn [sum_low zsum]. rewrite Hs. split.
+ destruct bos.
* pose proof (low8_lor256 v) as L. unfold low8 in L. rewrite L. pose proof (low8_byte v Hv) as L2. unfold low8 in L2. rewrite L2. reflexivity.
* pose proof (low8_byte v Hv) as L2. unfold low8 in L2. rewrite L2. reflexivity.
+ constructor; [|exact Hok]. destruct bos; [apply lacing_val_ok_lor256; exact Hv| apply lacing_val_ok_byte; exact Hv].
Qed.

#[using="Type"] Lemma gather255_sum : forall rest size eos bytes n n' eos' bytes',
gather255 size rest eos bytes n = Some (n', eos', bytes') ->
bytes' = bytes + sum_low (ztake (n' - n) rest) /\ n <= n'.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n n' eos' bytes' G; cbn [gather255] in G.
- destruct (size =? 255); [discriminate|]. inversion G; subst. rewrite Z.sub_diag, ztake_0. cbn [sum_low]. lia.
- destruct (size =? 255).
+ apply IH in G. destruct G as [Hb Hn]. split; [|lia].
unfold ztake in *. replace (Z.to_nat (n' - n)) with (S (Z.to_nat (n' - (n + 1)))) by lia. cbn [firstn sum_low].
cbn [firstn sum_low] in Hb. lia.
+ inversion G; subst. rewrite Z.sub_diag, ztake_0. cbn [sum_low]. lia.
Qed.

End ListFacts.

Section BodyInv.
Context {ptr : Type}.
Implicit Types os : stream_st ptr.

Definition body_inv os : Prop :=
zlength (os_body os) = os_body_fill os /\ 0 <= os_body_returned os /\
os_body_returned os + sum_low (zdrop (os_lacing_returned os) (os_lacing os)) = os_body_fill os /\
Forall lacing_val_ok (os_lacing os).

#[using="Type"] Lemma body_inv_returned_le_fill : forall os, body_inv os -> os_body_returned os <= os_body_fill os.
Proof. intros os (A & B & C & D). pose proof (sum_low_nonneg (zdrop (os_lacing_returned os) (os_lacing os))). lia. Qed.

#[using="Type"] Lemma body_inv_fill_nonneg : forall os, body_inv os -> 0 <= os_body_fill os.
Proof. intros os H. pose proof (body_inv_returned_le_fill os H). destruct H as (A & B & C & D). lia. Qed.

#[using="Type"] Lemma stream_zero_body_inv : body_inv stream_zero.
Proof. unfold body_inv, stream_zero; cbn. repeat split; try lia. constructor. Qed.

#[using="Type"] Lemma ogg_stream_init_body_inv : forall b l g sn,
body_inv (mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 sn 0 0 0).
Proof. intros. unfold body_inv; cbn. repeat split; try lia. constructor. Qed.

#[using="Type"] Lemma ogg_stream_reset_body_inv : forall os, body_inv (ogg_stream_reset os).
Proof. intros. unfold body_inv, ogg_stream_reset; cbn. repeat split; try lia. constructor. Qed.

#[using="Type"] Lemma ogg_stream_reset_serialno_body_inv : forall os sn r os',
body_inv os -> ogg_stream_reset_serialno os sn = (r, os') -> body_inv os'.
Proof.
intros os sn r os' H E. unfold ogg_stream_reset_serialno in E.
destruct (ogg_stream_check os); inversion E; subst; [exact H|].
unfold body_inv, ogg_stream_reset; cbn. repeat split; try lia. constructor.
Qed.

#[using="Type"] Lemma set_blocks_body_inv : forall os b bs l g ls, body_inv os -> body_inv (set_blocks os b bs l g ls).
Proof. intros. unfold body_inv, set_blocks in *; cbn. tauto. Qed.

#[using="Type"] Lemma set_tail_body_inv : forall os e p n, body_inv os -> body_inv (set_tail os e p n).
Proof. intros. unfold body_inv, set_tail in *; cbn. tauto. Qed.

#[using="Type"] Lemma pagein_returned_body_inv : forall os, stream_inv os -> body_inv os ->
body_inv (pagein_returned os) /\ os_body_returned (pagein_returned os) = 0 /\
os_body_fill (pagein_returned os) = os_body_fill os - os_body_returned os /\
os_lacing_fill (pagein_returned os) = os_lacing_fill os - os_lacing_returned os.
Proof.
intros os (A & B & C & D & F) (Hlen & Hret & Hsum & Hok). unfold pagein_returned.
pose proof (sum_low_nonneg (zdrop (os_lacing_returned os) (os_lacing os))) as Hnn.
set (os1 := if negb (os_body_returned os =? 0) then _ else os).
assert (H1 : body_inv os1 /\ os_body_returned os1 = 0 /\ os_body_fill os1 = os_body_fill os - os_body_returned os /\
os_lacing_returned os1 = os_lacing_returned os /\ os_lacing os1 = os_lacing os /\
os_lacing_fill os1 = os_lacing_fill os /\ os_lacing_packet os1 = os_lacing_packet os /\
os_granules os1 = os_granules os /\ os_lacing_storage os1 = os_lacing_storage os).
{ subst os1. destruct (Z.eqb_spec (os_body_returned os) 0) as [Ez|Ez]; cbn [negb].
- repeat split; try assumption; try lia.
- unfold body_inv, set_body; cbn. repeat split; try assumption; try lia.
rewrite zlength_ztake; [reflexivity|]. rewrite zlength_zdrop by lia. lia. }
destruct H1 as (I1 & R1 & F1 & LR1 & L1 & LF1 & LP1 & G1 & LS1).
destruct (Z.eqb_spec (os_lacing_returned os1) 0) as [Ez|Ez]; cbn [negb].
- rewrite <- LF1, <- LR1, Ez, Z.sub_0_r. auto.
- unfold body_inv, set_lacing; cbn. destruct I1 as (J1 & J2 & J3 & J4). rewrite L1, LR1 in *.
repeat split; try lia.
+ rewrite zdrop_0. rewrite R1 in J3. lia.
+ apply Forall_zdrop. exact J4.
Qed.

#[using="Type"] Lemma pagein_unroll_body_inv : forall os pageno, stream_inv os -> os_lacing_returned os = 0 -> body_inv os ->
body_inv (pagein_unroll os pageno) /\
os_body_fill (pagein_unroll os pageno) <= os_body_fill os /\
os_body_returned (pagein_unroll os pageno) = os_body_returned os.
Proof.
intros os pageno (A & B & C & D & F) HR (Hlen & Hret & Hsum & Hok). unfold pagein_unroll.
rewrite HR, ?zdrop_0 in Hsum.
destruct (Z.eqb_spec pageno (os_pageno os)); cbn [negb].
{ repeat split; try assumption; try lia. rewrite HR, ?zdrop_0. exact Hsum. }
set (lp := os_lacing_packet os). set (lf := os_lacing_fill os).
assert (Esl : zslice lp (lf - lp) (os_lacing os) = zdrop lp (os_lacing os)).
{ apply zslice_full_tail; [lia|]. rewrite C. lia. }
rewrite Esl.
pose proof (sum_low_split lp (os_lacing os) ltac:(lia)) as Hsplit.
pose proof (sum_low_nonneg (zdrop lp (os_lacing os))) as Hnn1.
pose proof (sum_low_nonneg (ztake lp (os_lacing os))) as Hnn2.
unfold set_lacing, set_body; simpl.
destruct (Z.eqb_spec (os_pageno os) (-1)); unfold body_inv; simpl; rewrite ?HR, ?zdrop_0.
- repeat split; try lia.
+ rewrite zlength_ztake; [reflexivity| lia].
+ apply Forall_ztake. exact Hok.
- repeat split; try lia.
+ rewrite zlength_ztake; [reflexivity| lia].
+ rewrite sum_low_app. cbn [sum_low]. change (Z.land 1024 255) with 0. lia.
+ apply Forall_app. split; [apply Forall_ztake; exact Hok|]. constructor; [apply lacing_val_ok_hole| constructor].
Qed.

#[using="Type"] Lemma pagein_skip_sum : forall os hdr, bytes_ok (lacing_of hdr) ->
let '(bos, segptr, skipped) := pagein_skip os hdr in
0 <= segptr <= zlength (lacing_of hdr) /\ skipped = zsum (ztake segptr (lacing_of hdr)).
Proof.
intros os hdr Hb. unfold pagein_skip.
destruct (negb (ogg_page_continued hdr =? 0)).
- destruct (_ || _ || _).
+ pose proof (skip_continued_sum (lacing_of hdr)) as S. destruct (skip_continued (lacing_of hdr)) as [n s].
destruct (S n s eq_refl) as [Hn Hs]. split; [exact Hn| exact Hs].
+ rewrite ztake_0. cbn [zsum]. pose proof (zlength_nonneg (lacing_of hdr)). lia.
- rewrite ztake_0. cbn [zsum]. pose proof (zlength_nonneg (lacing_of hdr)). lia.
Qed.

#[using="Type"] Lemma pagein_body_segments_body_inv : forall os hdr body bos segptr skipped,
stream_inv os -> os_lacing_returned os = 0 -> body_inv os ->
bytes_ok (lacing_of hdr) -> zsum (lacing_of hdr) = zlength body ->
0 <= segptr <= zlength (lacing_of hdr) -> skipped = zsum (ztake segptr (lacing_of hdr)) ->
let bodysize := zlength body - skipped in
let os4 := if negb (bodysize =? 0) then pagein_body os body skipped bodysize else os in
body_inv (pagein_segments os4 hdr bos segptr) /\
os_body_fill (pagein_segments os4 hdr bos segptr) = os_body_fill os + bodysize /\ 0 <= bodysize <= zlength body /\
os_body_returned (pagein_segments os4 hdr bos segptr) = os_body_returned os.
Proof.
intros os hdr body bos segptr skipped Hinv HR (Hlen & Hret & Hsum & Hok) Hb Hzs Hseg Hsk. cbv zeta.
rewrite HR, ?zdrop_0 in Hsum.
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as Hsp.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hb)) as N1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hb)) as N2.
assert (Hbs : 0 <= zlength body - skipped <= zlength body) by lia.
set (os4 := if negb (zlength body - skipped =? 0) then _ else os).
assert (H4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ os_lacing os4 = os_lacing os /\
os_lacing_fill os4 = os_lacing_fill os /\ os_lacing_packet os4 = os_lacing_packet os /\
os_body_returned os4 = os_body_returned os /\ Forall lacing_val_ok (os_lacing os4) /\
os_body_fill os4 = os_body_fill os + (zlength body - skipped) /\ zlength (os_body os4) = os_body_fill os4).
{ subst os4. destruct (Z.eqb_spec (zlength body - skipped) 0) as [Ez|Ez]; cbn [negb].
- split; [exact Hinv|]. repeat split; try assumption; lia.
- pose proof (pagein_body_inv os body skipped (zlength body - skipped) Hinv) as [I4 R4]. split; [exact I4|].
unfold pagein_body, set_body in *; simpl in *. repeat split; try assumption; try lia.
rewrite zlength_app, zlength_zslice; lia. }
destruct H4 as (I4 & R4 & L4 & LF4 & LP4 & BR4 & OK4 & BF4 & BL4).
unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os4) (os_lacing_packet os4) (-1))
as [[[[lac gran] f'] p'] s'] eqn:E.
pose proof (seg_loop_sum _ _ _ _ _ _ _ _ _ _ (bytes_ok_zdrop segptr _ Hb) E) as [Hlsum Hlok].
unfold body_inv, set_lacing, set_tail; cbn. rewrite R4, ?zdrop_0, BR4, BF4, L4.
split; [|split; [reflexivity| split; [exact Hbs| reflexivity]]].
split; [rewrite BL4, BF4; reflexivity|]. split; [exact Hret|]. split.
- assert (G : forall lacing, sum_low lacing = sum_low (os_lacing os ++ lac) ->
os_body_returned os + sum_low lacing = os_body_fill os + (zlength body - skipped)).
{ intros lacing ->. rewrite sum_low_app, Hlsum. lia. }
destruct (negb (ogg_page_eos hdr =? 0)); [destruct (0 <? f')|]; apply G; try reflexivity.
apply sum_low_zupd_lor512.
- assert (OKapp : Forall lacing_val_ok (os_lacing os ++ lac)) by (apply Forall_app; auto).
destruct (negb (ogg_page_eos hdr =? 0)); [destruct (0 <? f')|]; try exact OKapp.
apply Forall_zupd; [exact OKapp|]. apply lacing_val_ok_lor512.
apply Forall_In_znth; [exact OKapp| left; lia].
Qed.

#[using="Type"] Lemma packetout_body_inv : forall os r op os',
stream_inv os -> body_inv os -> packetout os = Some ((r, op), os') ->
body_inv os' /\ os_body_fill os' = os_body_fill os /\ os_body os' = os_body os /\
match op with
| Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill os /\
zlength (packet_data os' p) = pk_bytes p
| None => True
end.
Proof.
intros os r op os' Hinv (Hlen & Hret & Hsum & Hok) E. pose proof Hinv as (A & B & C & D & F). unfold packetout in E.
destruct (Z.leb_spec (os_lacing_packet os) (os_lacing_returned os)).
{ inversion E; subst. repeat split; auto. }
set (ptr0 := os_lacing_returned os) in *.
pose proof (sum_low_zdrop_split ptr0 1 (os_lacing os) ltac:(lia) ltac:(lia)) as Hsp1.
assert (Hone : sum_low (zslice ptr0 1 (os_lacing os)) = low8 (znth (os_lacing os) ptr0)).
{ unfold zslice. pose proof (ztake_zdrop_split ptr0 (os_lacing os) ltac:(lia)) as Es.
assert (Hl : 0 < zlength (zdrop ptr0 (os_lacing os))) by (rewrite zlength_zdrop; lia).
destruct (zdrop ptr0 (os_lacing os)) as [|x t] eqn:Ed; [rewrite zlength_nil in Hl; lia|].
rewrite ztake_1_cons. cbn [sum_low].
assert (Ez : znth (os_lacing os) ptr0 = x) by (eapply znth_head_zdrop; [|exact Ed]; lia). rewrite Ez. unfold low8. lia. }
destruct (negb (Z.land (znth (os_lacing os) ptr0) 1024 =? 0)) eqn:Hh.
{ inversion E; subst. unfold body_inv, set_tail, set_lacing; cbn. repeat split; auto; try lia.
rewrite Hsp1, Hone in Hsum.
assert (L0 : low8 (znth (os_lacing os) ptr0) = 0).
{ apply lacing_val_hole_low8; [apply Forall_In_znth; [exact Hok| left; lia]|].
destruct (Z.eqb_spec (Z.land (znth (os_lacing os) ptr0) 1024) 0); [discriminate| assumption]. }
rewrite L0 in Hsum. lia. }
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:G; [|discriminate].
pose proof (gather255_sum _ _ _ _ _ _ _ _ G) as [Hbytes Hn]. rewrite Z.sub_0_r in Hbytes.

assert (Hb2 : bytes = sum_low (zslice ptr0 (n + 1) (os_lacing os))).
{ rewrite Hbytes. unfold zslice.
pose proof (ztake_zdrop_split ptr0 (os_lacing os) ltac:(lia)) as Es.
assert (Hl : 0 < zlength (zdrop ptr0 (os_lacing os))) by (rewrite zlength_zdrop; lia).
rewrite <- (zdrop_zdrop ptr0 1) by lia.
destruct (zdrop ptr0 (os_lacing os)) as [|x t] eqn:Ed; [rewrite zlength_nil in Hl; lia|].
unfold ztake, zdrop. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. cbn [firstn skipn sum_low].
change (skipn (Z.to_nat 1) (x :: t)) with t.
assert (Ez : znth (os_lacing os) ptr0 = x) by (eapply znth_head_zdrop; [|exact Ed]; lia). rewrite Ez. unfold low8. lia. }
clear Hbytes. inversion E; subst. cbn -[Z.add Z.sub Z.mul Z.land sum_low zslice zdrop].
pose proof (sum_low_zdrop_split ptr0 (n + 1) (os_lacing os) ltac:(lia) ltac:(lia)) as Hsp.
pose proof (sum_low_nonneg (zslice ptr0 (n + 1) (os_lacing os))) as N1.
pose proof (sum_low_nonneg (zdrop (ptr0 + (n + 1)) (os_lacing os))) as N2.
unfold body_inv; cbn. repeat split; try lia.
- replace (ptr0 + n + 1) with (ptr0 + (n + 1)) by lia. lia.
- exact Hok.
- unfold packet_data; cbn. rewrite zlength_zslice; lia.
Qed.

#[using="Type"] Lemma ogg_stream_packetout_body_inv : forall os r op os',
stream_inv os -> body_inv os -> ogg_stream_packetout os = Some ((r, op), os') ->
body_inv os' /\ os_body_fill os' = os_body_fill os /\ os_body os' = os_body os /\
match op with
| Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill os /\
zlength (packet_data os' p) = pk_bytes p
| None => True
end.
Proof.
intros os r op os' Hinv Hb E. unfold ogg_stream_packetout in E.
destruct (ogg_stream_check os). { inversion E; subst. split; [exact Hb|]. repeat split; auto. }
eapply packetout_body_inv; eauto.
Qed.

#[using="Type"] Lemma pagein_segments_frame : forall os hdr bos segptr,
bytes_ok (lacing_of hdr) -> 0 <= segptr <= zlength (lacing_of hdr) -> os_lacing_packet os <= os_lacing_fill os ->
let os' := pagein_segments os hdr bos segptr in
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
os_body_fill os' = os_body_fill os /\ os_body os' = os_body os /\
os_lacing_fill os' = os_lacing_fill os + (zlength (lacing_of hdr) - segptr).
Proof.
intros os hdr bos segptr Hb Hseg Hpf. cbv zeta. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f] p] sv] eqn:E.
pose proof (seg_loop_spec _ _ _ _ _ _ _ _ _ _ (bytes_ok_zdrop segptr _ Hb) Hpf E) as (Z1 & Z2 & Z3 & _).
unfold set_lacing, set_tail; cbn -[Z.add Z.sub]. repeat split; try reflexivity.
rewrite Z3. rewrite zlength_zdrop by lia. reflexivity.
Qed.

End BodyInv.

Section SyncFacts.
Context {ptr : Type}.
Implicit Types sy : sync_st ptr.

#[using="Type"] Lemma sync_fail_no_page : forall sy ret bytes r og sy', sync_fail sy ret bytes = ((r, og), sy') -> og = None.
Proof. intros sy ret bytes r og sy' E. unfold sync_fail in E. inversion E. reflexivity. Qed.

#[using="Type"] Lemma ogg_sync_pageseek_pos : forall sy r og sy',
ogg_sync_pageseek sy = ((r, Some og), sy') ->
pg_hdr og = sy_returned sy /\ sy_returned sy' = pg_hdr og + pg_header_len og + pg_body_len og /\
r = pg_header_len og + pg_body_len og.
Proof.
intros sy r og sy' E. unfold ogg_sync_pageseek in E.
destruct (ogg_sync_check sy); [inversion E|].
match type of E with context [match ?hp with | Some _ => _ | None => _ end] => destruct hp as [[[]|sy0]|] eqn:Hp end.
- apply sync_fail_no_page in E. discriminate.
- destruct (sy_fill sy - sy_returned sy <? sy_bodybytes sy0 + sy_headerbytes sy0); [inversion E|].
match type of E with context [if ?c then sync_fail _ _ _ else _] => destruct c end;
[apply sync_fail_no_page in E; discriminate|].
inversion E; subst. cbn -[Z.add]. lia.
- inversion E.
Qed.

#[using="Type"] Lemma pageout_loop_frame : forall fuel sy r og sy',
sync_inv sy -> pageout_loop fuel sy = Some ((r, og), sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\ sy_returned sy <= sy_returned sy' /\
match og with
| Some pg => sy_returned sy <= pg_hdr pg /\ sy_returned sy' = pg_hdr pg + pg_header_len pg + pg_body_len pg
| None => True
end.
Proof.
induction fuel as [|fuel IH]; intros sy r og sy' Hinv E; [discriminate|].
cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1] eqn:E1.
pose proof (ogg_sync_pageseek_inv sy r1 og1 sy1 Hinv E1) as (Hinv1 & Hf & Hb & Hd & Hs & Hneg & Hpos).
destruct (Z.ltb_spec 0 r1).
{ inversion E; subst. specialize (Hpos ltac:(lia)). split; [exact Hinv1|]. repeat (split; [assumption|]).
destruct og as [pg|]; [|exact I]. destruct (ogg_sync_pageseek_pos _ _ pg _ E1) as (P1 & P2 & P3). lia. }
destruct (Z.eqb_spec r1 0).
{ inversion E; subst. specialize (Hpos ltac:(lia)). split; [exact Hinv1|]. repeat (split; [assumption|]). exact I. }
specialize (Hneg ltac:(lia)).
destruct (sy_unsynced sy1 =? 0).
{ inversion E; subst. cbn. unfold sync_inv in *; cbn. repeat split; first [tauto | lia]. }
destruct (IH sy1 r og sy' Hinv1 E) as (A & B & C & D & F & G & P).
split; [exact A|]. rewrite B, C, D, F. repeat split; try assumption; try lia.
destruct og as [pg|]; [|exact I]. lia.
Qed.

#[using="Type"] Theorem ogg_sync_pageout_frame : forall sy r og sy',
sync_inv sy -> ogg_sync_pageout sy = Some ((r, og), sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\ sy_returned sy <= sy_returned sy' /\
match og with
| Some pg => sy_returned sy <= pg_hdr pg /\ sy_returned sy' = pg_hdr pg + pg_header_len pg + pg_body_len pg
| None => True
end.
Proof.
intros sy r og sy' Hinv E. unfold ogg_sync_pageout in E.
destruct (ogg_sync_check sy). { inversion E; subst. split; [exact Hinv|]. repeat (split; [reflexivity|]). exact I. }
eapply pageout_loop_frame; eauto.
Qed.

#[using="Type"] Lemma page_ok_body_len : forall sy og, sync_inv sy -> page_ok sy og ->
zsum (lacing_of (page_header sy og)) = zlength (page_body sy og) /\
zlength (page_header sy og) = 27 + znth (page_header sy og) 26 /\ 0 <= znth (page_header sy og) 26.
Proof.
intros sy og Hinv (P0 & P1 & P2 & P3 & P4 & P5 & P6).
unfold page_header, page_body, lacing_of.
assert (Hn26 : znth (zslice (pg_hdr og) (pg_header_len og) (sy_buf sy)) 26 = znth (sy_buf sy) (pg_hdr og + 26)).
{ apply znth_zslice; lia. }
rewrite Hn26. rewrite zslice_zslice by lia. rewrite <- P3.
rewrite !zlength_zslice by lia. lia.
Qed.

End SyncFacts.

Section OggSafeM.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.

Variable reall : ptr -> Prop.
Hypothesis Hmal_big : forall X n, REALL_MIN <= n ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hrea : forall X p n, reall p -> REALL_MIN <= n < MMAP_THRESHOLD ->
mspec (own (p :: X)) (lib_realloc p n) (fun r s mo => match r with Some q => own (q :: X) s mo /\ reall q | None => own (p :: X) s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Hypothesis Hmal_some : forall n, 0 <= n < X1nv.SOME_MAX -> mspecA (lib_malloc n) (fun r => r <> None).
Hypothesis Hrea_some : forall p n, 0 <= n < X1nv.SOME_MAX -> mspecA (lib_realloc p n) (fun r => r <> None).

Implicit Types sy : sync_st ptr.
Implicit Types os : stream_st ptr.

#[using="Type"] Lemma sync_inv2_set_block : forall sy (d : option ptr) st, sync_inv2 sy ->
sync_inv2 (mkSync d (sy_buf sy) st (sy_fill sy) (sy_returned sy) (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
Proof. intros sy d st [[A B] C]. unfold sync_inv2, sync_inv, sync_hdr in *; cbn in *. tauto. Qed.

Definition sync_ok sy : Prop := sync_inv2 sy /\ 0 <= sy_storage sy /\ (sy_data sy = None -> sy_storage sy = 0) /\ sy_reall reall sy.

#[using="Type"] Lemma ogg_sync_init_ok : sync_ok ogg_sync_init.
Proof. split; [apply ogg_sync_init_inv2|]. cbn. split; [lia|]. split; [lia|]. intros q E. discriminate E. Qed.

#[using="Hmal_big Hrea Hfree Hmal_some Hrea_some"] Lemma ogg_sync_buffer_spec2 : forall X sy size, 0 <= size -> sync_ok sy ->
size + (sy_fill sy - sy_returned sy) + 4096 < MMAP_THRESHOLD ->
mspec (own (sy_ptrs sy ++ X)) (ogg_sync_buffer lib_malloc lib_realloc lib_free sy size)
(fun r s mo => let '(res, sy') := r in own (sy_ptrs sy' ++ X) s mo /\ sync_ok sy' /\
(sy_returned sy' = 0 /\ sy_fill sy' = sy_fill sy - sy_returned sy /\
match res with
| Some (q, off) => off = sy_fill sy' /\ sy_data sy' = Some q /\ sy_fill sy' + size <= sy_storage sy'
| None => size = 0
end)).
Proof.
intros X sy size Hsz (Hinv & Hst & Hnul & Hrl) Hbound. pose proof Hinv as [[R1 R2] _]. unfold ogg_sync_buffer.
apply mspec_if; intros Hck. { unfold ogg_sync_check in Hck. apply Z.ltb_lt in Hck. lia. }
set (sy1 := if negb (sy_returned sy =? 0) then _ else sy).
assert (E1 : sync_inv2 sy1 /\ sy_data sy1 = sy_data sy /\ sy_fill sy1 = sy_fill sy - sy_returned sy /\ sy_storage sy1 = sy_storage sy /\
sy_returned sy1 = 0).
{ subst sy1. destruct (Z.eqb_spec (sy_returned sy) 0) as [Ez|Ez]; cbn [negb].
- split; [exact Hinv|]. repeat split; auto; lia.
- pose proof (sync_compact_inv2 sy Hinv) as C. cbn in C. split; [exact C|]. repeat split; auto. }
destruct E1 as (I1 & Ed & Ef & Es & Er).
assert (EP : sy_ptrs sy1 = sy_ptrs sy) by (unfold sy_ptrs; rewrite Ed; reflexivity).
assert (RL1 : sy_reall reall sy1) by (intros q E; apply Hrl; rewrite <- Ed; exact E).
rewrite <- EP.
apply mspec_if; intros Hgrow.
- apply mspec_if; intros Hbig. { apply Z.ltb_lt in Hbig. unfold INT_MAX, MMAP_THRESHOLD in *. lia. }
apply Z.ltb_lt in Hgrow.
eapply mspec_bind with (Q1 := fun ret s mo => match ret with Some q => own (q :: X) s mo /\ reall q | None => False end).
{ unfold sy_ptrs. destruct (sy_data sy1) as [p|] eqn:Edd; cbn.
- eapply mspec_post; [apply mspec_some; [apply Hrea| apply Hrea_some]|]. 4:{ intros [q|] s mo H; exact H. } { apply RL1. exact Edd. }
+ rewrite Ef. unfold REALL_MIN. lia.
+ rewrite Ef. unfold X1nv.SOME_MAX, MMAP_THRESHOLD in *. lia.
- eapply mspec_post; [apply mspec_some; [apply Hmal_big; unfold REALL_MIN; lia| apply Hmal_some; rewrite Ef; unfold X1nv.SOME_MAX, MMAP_THRESHOLD in *; lia]|].
intros [q|] s mo H; exact H. }
intros [q|]; cbn beta iota.
+ apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. cbn. split; [exact H|]. split.
{ split; [apply sync_inv2_set_block; exact I1|]. cbn. split; [lia|]. split; [intros; discriminate|]. intros q' E; injection E as <-; exact Hq. }
cbn. rewrite Er, Ef. repeat split; try lia.
+ apply mspec_false.
- apply mspec_ret. intros s mo H. cbn beta iota. apply Z.ltb_ge in Hgrow.
assert (OK1 : sync_ok sy1). { split; [exact I1|]. rewrite Es, Ed. split; [exact Hst|]. split; [exact Hnul| exact RL1]. }
destruct (sy_data sy1) as [p|] eqn:Edd.
+ split; [exact H|]. split; [exact OK1|]. repeat split; auto; lia.
+ split; [exact H|]. split; [exact OK1|]. repeat split; auto.
assert (Hz : sy_storage sy = 0) by (apply Hnul; congruence). lia.
Qed.

#[using="Hrea Hfree"] Lemma os_body_expand_spec2 : forall X os needed, os_has_blocks os -> os_reall reall os -> 0 <= needed -> 0 <= os_body_storage os ->
(os_body_storage os - needed <= os_body_fill os -> os_body_storage os + needed + 1024 < MMAP_THRESHOLD) ->
mspec (own (os_ptrs os ++ X)) (os_body_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists b bs, 0 <= bs /\ bs <= Z.max (os_body_storage os) (os_body_fill os + 2 * needed + 1024) /\
os' = set_blocks os b bs (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os))
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound. pose proof HR as (R1 & R2 & R3 & R4). unfold os_body_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_body_data os), (os_body_storage os). split; [exact Hs|]. split; [lia|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply X1nv.ogg_sync_clear_spec || apply X1nv.ogg_stream_clear_spec; eauto|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hb. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
eapply mspec_bind.
{ eapply mspec_pre; [apply Hrea|]. 3:{ intros s mo H. exact H. } { apply R1. exact Hb. }
destruct (Z.ltb_spec (os_body_storage os + needed) (LONG_MAX - 1024)); unfold MMAP_THRESHOLD, LONG_MAX, REALL_MIN in *; lia. }
intros [q|]; cbn beta iota.
- apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. split; [|split].
+ unfold os_ptrs, set_blocks; cbn. first [exact H | rewrite Hl, Hg; exact H].
+ unfold os_reall, set_blocks; cbn. split; [intros b0 E; injection E as <-; exact Hq|]. split; [intros l0 E; injection E as <-; apply R2; exact Hl|].
split; [intros g0 E; injection E as <-; apply R3; exact Hg|]. intros _. split; [destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia| exact S10].
+ left. split; [reflexivity|]. split; [exists q, l, g; unfold set_blocks; cbn; auto|]. eexists _, _. split; [|split; [|reflexivity]].
* destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia.
* destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia.
- eapply mspec_bind. { eapply mspec_pre; [apply X1nv.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs. rewrite Hb, Hl, Hg. exact H. }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

#[using="Hrea Hfree Hperm"] Lemma os_lacing_expand_spec2 : forall X os needed, os_has_blocks os -> os_reall reall os -> 0 <= needed -> 0 <= os_lacing_storage os ->
(os_lacing_storage os - needed <= os_lacing_fill os -> (os_lacing_storage os + needed + 32) * 8 < MMAP_THRESHOLD) ->
mspec (own (os_ptrs os ++ X)) (os_lacing_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists l g ls, 0 <= ls /\ ls <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * needed + 32) /\
os' = set_blocks os (os_body_data os) (os_body_storage os) l g ls)
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound. pose proof HR as (R1 & R2 & R3 & R4). unfold os_lacing_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_lacing_vals os), (os_granule_vals os), (os_lacing_storage os). split; [exact Hs|]. split; [lia|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply X1nv.ogg_stream_clear_spec; eauto|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hl, Hg. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
set (ls := if os_lacing_storage os + needed <? LONG_MAX - 32 then _ else _).
assert (Hls : 0 <= ls /\ ls * 8 < MMAP_THRESHOLD /\ ls <= os_lacing_fill os + 2 * needed + 32 /\ os_lacing_storage os <= ls).
{ subst ls. destruct (Z.ltb_spec (os_lacing_storage os + needed) (LONG_MAX - 32)); unfold MMAP_THRESHOLD, LONG_MAX in *; lia. }
destruct Hls as (Hls & Hls8 & HlsB & HlsM).
eapply mspec_bind.
{ eapply (X1nv.own_perm_pre own Hperm); [apply (perm_swap b l)|]. eapply mspec_pre; [apply Hrea; [apply R2; exact Hl| unfold SIZEOF_INT, REALL_MIN; lia]|]. intros s mo H; exact H. }
intros [l'|]; cbn beta iota.
- apply mspec_pure. intros Hl'. eapply mspec_bind.
{ eapply (X1nv.own_perm_pre own Hperm) with (Y := g :: l' :: b :: X).
{ eapply Permutation_trans; [apply (perm_swap l' g) | apply perm_skip; apply (perm_swap b g)]. }
eapply mspec_pre; [apply Hrea; [apply R3; exact Hg| unfold SIZEOF_INT64, REALL_MIN; lia]|]. intros s mo H; exact H. }
intros [g'|]; cbn beta iota.
+ apply mspec_pure. intros Hg'. apply mspec_ret. intros s mo H. split; [|split].
* unfold os_ptrs, set_blocks; cbn. rewrite ?Hb. cbn. eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g')|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g')|]. apply (perm_swap b l').
* unfold os_reall, set_blocks; cbn. split; [intros b0 E; apply R1; rewrite <- E; first [exact Hb | reflexivity]|]. split; [intros l0 E; injection E as <-; exact Hl'|].
split; [intros g0 E; injection E as <-; exact Hg'|]. intros NE. split; [exact S16| lia].
* left. split; [reflexivity|]. split; [exists b, l', g'; unfold set_blocks; cbn; auto|]. eexists _, _, _.
split; [exact Hls|]. split; [lia| reflexivity].
+ eapply mspec_bind.
{ eapply mspec_pre; [apply X1nv.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs, set_blocks; cbn. rewrite ?Hb, ?Hg; cbn.
eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g)|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g)|]. apply (perm_swap b l'). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
- eapply mspec_bind. { eapply mspec_pre; [apply X1nv.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs. rewrite ?Hb, ?Hl, ?Hg. cbn.
eapply Hperm; [|exact H]. apply (perm_swap b l). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

Definition pagein_post (os : stream_st ptr) (hdr body : list Z) (os' : stream_st ptr) : Prop :=
os_ok reall os' /\ body_inv os' /\
0 <= os_lacing_fill os' <= os_lacing_fill os + znth hdr 26 + 1 /\
0 <= os_body_fill os' <= os_body_fill os + zlength body /\
0 <= os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32) /\
0 <= os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024).

#[using="Type"] Lemma pagein_post_zero : forall os hdr body, os_ok reall os -> body_inv os -> 0 <= znth hdr 26 ->
pagein_post os hdr body stream_zero.
Proof.
intros os hdr body (Hbl & Hinv & Hbs & Hls & HRl) Hb Hn. pose proof (body_inv_fill_nonneg os Hb).
destruct Hinv as (A & B & _). pose proof (zlength_nonneg body).
unfold pagein_post. split; [apply (stream_zero_ok reall)|]. split; [apply stream_zero_body_inv|]. unfold stream_zero; simpl. lia.
Qed.

#[using="Type"] Lemma pagein_post_same : forall os hdr body, os_ok reall os -> body_inv os -> 0 <= znth hdr 26 ->
pagein_post os hdr body os.
Proof.
intros os hdr body Hok Hb Hn. pose proof Hok as (Hbl & Hinv & Hbs & Hls & HRl). pose proof (body_inv_fill_nonneg os Hb).
destruct Hinv as (A & B & _). pose proof (zlength_nonneg body).
unfold pagein_post. split; [exact Hok|]. split; [exact Hb|]. lia.
Qed.

#[using="Hrea Hfree Hperm"] Theorem ogg_stream_pagein_spec2 : forall X os hdr body,
os_ok reall os -> body_inv os -> bytes_ok (lacing_of hdr) -> 0 <= znth hdr 26 -> zsum (lacing_of hdr) = zlength body ->
(os_lacing_storage os + znth hdr 26 + 33) * 8 < MMAP_THRESHOLD ->
os_body_storage os + zlength body + 1024 < MMAP_THRESHOLD ->
mspec (own (os_ptrs os ++ X)) (ogg_stream_pagein lib_realloc lib_free os hdr body)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ pagein_post os hdr body os').
Proof.
intros X os hdr body Hok0 Hbody Hlac Hseg Hsum HboundL HboundB. pose proof Hok0 as (Hbl & Hinv & Hbs & Hls & HRl). unfold ogg_stream_pagein.
apply mspec_if; intros Hck.
{ apply mspec_ret. intros s mo H. split; [exact H|]. apply pagein_post_same; auto. }
assert (Hhas : os_has_blocks os).
{ unfold ogg_stream_check in Hck. unfold os_blocks_ok in Hbl. unfold os_has_blocks.
destruct (os_body_data os) as [b|] eqn:Eb; [|discriminate].
destruct (os_lacing_vals os) as [l|] eqn:El; [|destruct (os_granule_vals os); contradiction].
destruct (os_granule_vals os) as [g|] eqn:Eg; [|contradiction]. exists b, l, g; auto. }
pose proof (pagein_returned_inv os Hinv) as (Hinv1 & Hret1 & Elv & Egv & Ebd & Els & Ebs & Esn & Epn).
pose proof (pagein_returned_body_inv os Hinv Hbody) as (Hbody1 & Hbr1 & Hbf1 & Hlf1).
pose proof (body_inv_fill_nonneg os Hbody) as Hbf0. pose proof (body_inv_returned_le_fill os Hbody) as Hbr0.
pose proof Hinv as (SA & SB & _). pose proof Hbody as (_ & HbrNN & _).
set (os1 := pagein_returned os) in *.
assert (Eptrs1 : os_ptrs os1 = os_ptrs os) by (unfold os_ptrs; rewrite Elv, Egv, Ebd; reflexivity).
assert (Hhas1 : os_has_blocks os1).
{ destruct Hhas as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite Ebd, Elv, Egv. auto. }
assert (HRl1 : os_reall reall os1) by (eapply os_reall_frame; [exact Ebd| exact Elv| exact Egv| rewrite Ebs; lia| rewrite Els; lia| exact HRl]).
assert (Hok1 : os_ok reall os1).
{ unfold os_ok. split; [apply os_has_blocks_ok; exact Hhas1|]. split; [exact Hinv1|]. rewrite Ebs, Els. split; [lia|]. split; [lia| exact HRl1]. }
assert (Hpost1 : pagein_post os hdr body os1).
{ unfold pagein_post. split; [exact Hok1|]. split; [exact Hbody1|]. rewrite Hlf1, Hbf1, Els, Ebs. pose proof (zlength_nonneg body). lia. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. rewrite Eptrs1. split; [exact H| exact Hpost1]. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. rewrite Eptrs1. split; [exact H| exact Hpost1]. }
eapply mspec_bind.
{ rewrite <- Eptrs1. apply os_lacing_expand_spec2; [exact Hhas1| exact HRl1| lia| rewrite Els; exact Hls|]. intros _. rewrite Els. lia. }
intros [r os2]. cbn beta iota.
apply mspec_pointwise. intros s0 mo0 (Hown2 & HRl2 & Hcase).
destruct Hcase as [(-> & Hhas2 & (l2 & g2 & ls2 & Hls2 & Hls2B & Eos2)) | (-> & ->)].
2:{ cbn. apply mspec_ret. intros s mo [-> ->]. split; [exact Hown2| apply pagein_post_zero; auto]. }
cbn [negb Z.eqb].

assert (Hinv2 : stream_inv os2 /\ os_lacing_returned os2 = 0 /\ 0 <= os_body_storage os2 /\ 0 <= os_lacing_storage os2 /\
body_inv os2 /\ os_lacing_fill os2 = os_lacing_fill os1 /\ os_body_fill os2 = os_body_fill os1 /\
os_body_storage os2 = os_body_storage os /\ os_lacing_storage os2 = ls2).
{ rewrite Eos2. pose proof (set_blocks_inv os1 (os_body_data os1) (os_body_storage os1) l2 g2 ls2 Hinv1) as [A B].
split; [exact A|]. split; [rewrite B; exact Hret1|]. split; [unfold set_blocks; cbn; rewrite Ebs; lia|]. split; [unfold set_blocks; cbn; lia|].
split; [apply set_blocks_body_inv; exact Hbody1|]. unfold set_blocks; cbn. rewrite Ebs. repeat split; reflexivity. }
destruct Hinv2 as (Hinv2 & Hret2 & Hbs2 & Hls2' & Hbody2 & Hlf2 & Hbf2 & Ebs2 & Els2).
pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2) as (Hinv3 & Hret3 & Elv3 & Egv3 & Ebd3 & Els3 & Ebs3 & Hlf3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2 Hbody2) as (Hbody3 & Hbf3 & Hbr3).
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.
assert (Eptrs3 : os_ptrs os3 = os_ptrs os2) by (unfold os_ptrs; rewrite Elv3, Egv3, Ebd3; reflexivity).
assert (HRl3 : os_reall reall os3) by (eapply os_reall_frame; [exact Ebd3| exact Elv3| exact Egv3| rewrite Ebs3; lia| rewrite Els3; lia| exact HRl2]).
assert (Hhas3 : os_has_blocks os3).
{ destruct Hhas2 as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite Ebd3, Elv3, Egv3. auto. }
pose proof (pagein_skip_sum os3 hdr Hlac) as Bsk.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped]. destruct Bsk as [Hsegptr Hskipped].
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as Hzs.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hlac)) as N1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hlac)) as N2.
assert (Hbsz : 0 <= zlength body - skipped <= zlength body) by lia.
pose proof Hinv3 as (TA & TB & _). pose proof (body_inv_fill_nonneg os3 Hbody3) as Hbf3nn.

eapply mspec_bind with
(Q1 := fun r s mo => let '(rc, os4) := r in own (os_ptrs os4 ++ X) s mo /\
((rc = 0 /\ exists os3', stream_inv os3' /\ os_lacing_returned os3' = 0 /\ os_has_blocks os3' /\ body_inv os3' /\ os_reall reall os3' /\
os_lacing os3' = os_lacing os3 /\ os_lacing_fill os3' = os_lacing_fill os3 /\ os_lacing_packet os3' = os_lacing_packet os3 /\
os_body_fill os3' = os_body_fill os3 /\ os_lacing_storage os3' = os_lacing_storage os3 /\
0 <= os_body_storage os3' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024) /\
os4 = (if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3'))
\/ (rc <> 0 /\ os4 = stream_zero))).
{ apply mspec_if; intros Hnz.
- eapply mspec_bind.
{ eapply mspec_pre; [apply os_body_expand_spec2; [exact Hhas3| exact HRl3| lia| rewrite Ebs3; exact Hbs2|]|].
{ intros _. rewrite Ebs3, Ebs2. lia. }
intros s mo [-> ->]. rewrite Eptrs3. exact Hown2. }
intros [rc os4]. cbn beta iota. apply mspec_pointwise. intros s1 mo1 (Hown4 & HRl4 & Hc4).
destruct Hc4 as [(-> & Hhas4 & (b4 & bs4 & Hbs4 & Hbs4B & Eos4)) | (-> & ->)].
+ cbn [negb Z.eqb]. apply mspec_ret. intros s mo [-> ->]. split.
* subst os4. unfold os_ptrs, pagein_body, set_blocks in *; cbn in *. exact Hown4.
* left. split; [reflexivity|]. exists os4. subst os4.
pose proof (set_blocks_inv os3 b4 bs4 (os_lacing_vals os3) (os_granule_vals os3) (os_lacing_storage os3) Hinv3) as [A4 B4].
split; [exact A4|]. split; [rewrite B4; exact Hret3|]. split; [exact Hhas4|]. split; [apply set_blocks_body_inv; exact Hbody3|]. split; [exact HRl4|].
unfold set_blocks; cbn. rewrite Ebs3, Ebs2 in Hbs4B. repeat split; try reflexivity; try lia.
rewrite Hnz. reflexivity.
+ cbn. apply mspec_ret. intros s mo [-> ->]. split; [exact Hown4|]. right. split; [lia| reflexivity].
- apply mspec_ret. intros s mo [-> ->]. rewrite Eptrs3. split; [exact Hown2|]. left. split; [reflexivity|].
exists os3. split; [exact Hinv3|]. split; [exact Hret3|]. split; [exact Hhas3|]. split; [exact Hbody3|]. split; [exact HRl3|].
rewrite Ebs3, Ebs2. repeat split; try reflexivity; try lia. rewrite Hnz. reflexivity. }
intros [rc os4]. cbn beta iota. apply mspec_pointwise. intros s1 mo1 [Hown4 Hc4].
destruct Hc4 as [(-> & (os3' & I3' & R3' & Hhas3' & B3' & RL3' & L3' & LF3' & LP3' & BF3' & LS3' & BS3' & ->)) | (Hne & ->)].
- cbn [negb Z.eqb]. apply mspec_ret. intros s mo [-> ->].
pose proof (pagein_body_segments_body_inv os3' hdr body bos segptr skipped I3' R3' B3' Hlac Hsum Hsegptr Hskipped) as PBS.
cbv zeta in PBS. destruct PBS as (Hbody5 & Hbf5 & _ & Hbr5).
set (os4 := if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3') in *.
assert (H4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ os_has_blocks os4 /\ os_lacing_fill os4 = os_lacing_fill os3 /\
os_lacing_packet os4 = os_lacing_packet os3 /\ os_lacing_storage os4 = os_lacing_storage os3 /\
os_body_storage os4 = os_body_storage os3' /\ os_ptrs os4 = os_ptrs os3').
{ subst os4. destruct (negb (zlength body - skipped =? 0)).
- pose proof (pagein_body_inv os3' body skipped (zlength body - skipped) I3') as [A B].
split; [exact A|]. split; [rewrite B; exact R3'|].
split. { destruct Hhas3' as (b & l & g & Hb & Hl & Hg). exists b, l, g. unfold pagein_body, set_body; cbn. auto. }
unfold pagein_body, set_body, os_ptrs; cbn. rewrite LF3', LP3', LS3'. repeat split; reflexivity.
- rewrite <- LF3', <- LP3', <- LS3'. split; [exact I3'|]. split; [exact R3'|]. split; [exact Hhas3'|]. repeat split; reflexivity. }
destruct H4 as (I4 & R4 & Hhas4 & LF4 & LP4 & LS4 & BS4 & P4).
assert (HRl4 : os_reall reall os4).
{ subst os4. destruct (negb (zlength body - skipped =? 0)); [| exact RL3']. unfold pagein_body, set_body. eapply os_reall_frame; [..| exact RL3']; cbn; try reflexivity; lia. }
pose proof I4 as (U1 & U2 & _).
pose proof (pagein_segments_frame os4 hdr bos segptr Hlac Hsegptr U2) as FR. cbv zeta in FR.
destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
split.
+ assert (EQ : os_ptrs (pagein_segments os4 hdr bos segptr) = os_ptrs os4) by (unfold os_ptrs; rewrite F1, F2, F3; reflexivity).
rewrite EQ. exact Hown4.
+ unfold pagein_post. split.
{ unfold os_ok. split.
{ apply os_has_blocks_ok. destruct Hhas4 as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite F1, F2, F3. auto. }
split; [apply pagein_segments_inv; auto; lia|]. rewrite F4, F5, LS4, BS4, Els3, Els2. split; [lia|]. split; [lia|].
eapply os_reall_frame; [exact F1| exact F2| exact F3| rewrite F4; lia| rewrite F5; lia| exact HRl4]. }
split; [exact Hbody5|].
rewrite Hbf5, BF3', F8, F5, F4, LF4, LS4, BS4, Els3, Els2.
pose proof (zlength_ztake_le_n (znth hdr 26) (zdrop 27 hdr) Hseg) as ZL. change (ztake (znth hdr 26) (zdrop 27 hdr)) with (lacing_of hdr) in ZL.
pose proof (zlength_nonneg body). pose proof (zlength_nonneg (lacing_of hdr)). lia.
- destruct (negb (rc =? 0)) eqn:En.
+ apply mspec_ret. intros s mo [-> ->]. split; [exact Hown4| apply pagein_post_zero; auto].
+ apply Bool.negb_false_iff in En. apply Z.eqb_eq in En. lia.
Qed.
End OggSafeM.

Section PacketoutFacts.
Context {ptr : Type}.
Implicit Types os : stream_st ptr.

#[using="Type"] Lemma packetout_frame : forall os r op os',
stream_inv os -> packetout os = Some ((r, op), os') ->
stream_inv os' /\
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
os_lacing_fill os' = os_lacing_fill os /\ os_body_fill os' = os_body_fill os /\ os_serialno os' = os_serialno os /\
os_lacing_returned os <= os_lacing_returned os' <= os_lacing_fill os /\
(r = 1 -> op <> None /\ os_lacing_returned os < os_lacing_returned os').
Proof.
intros os r op os' Hinv E. pose proof (packetout_stream_inv os r op os' Hinv E) as Hinv'.
pose proof (packetout_inv os r op os' (stream_inv_lacing_inv os Hinv) E) as (L & HL & HB & HP & HR).
pose proof Hinv' as (A' & B' & _). rewrite HP in *.
split; [exact Hinv'|].
unfold packetout in E.
destruct (Z.leb_spec (os_lacing_packet os) (os_lacing_returned os)).
{ inversion E; subst. repeat split; auto; try lia. }
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)).
{ inversion E; subst. cbn -[Z.add Z.sub Z.le Z.lt] in *. repeat split; auto; try lia. all: intros Hr; lia. }
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:G; [|discriminate].
pose proof (gather255_sum _ _ _ _ _ _ _ _ G) as [_ Hn].
inversion E; subst. cbn -[Z.add Z.sub Z.le Z.lt Z.land sum_low ztake zdrop znth] in *. repeat split; auto; try lia. all: try congruence; try lia.
Qed.

#[using="Type"] Lemma ogg_stream_packetout_frame : forall os r op os',
stream_inv os -> ogg_stream_packetout os = Some ((r, op), os') ->
stream_inv os' /\
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
os_lacing_fill os' = os_lacing_fill os /\ os_body_fill os' = os_body_fill os /\ os_serialno os' = os_serialno os /\
os_lacing_returned os <= os_lacing_returned os' <= os_lacing_fill os /\
(r = 1 -> op <> None /\ os_lacing_returned os < os_lacing_returned os') /\
(os_body_data os = None -> os' = os /\ r = 0).
Proof.
intros os r op os' Hinv E. unfold ogg_stream_packetout, ogg_stream_check in E.
destruct (os_body_data os) eqn:Eb.
- pose proof (packetout_frame os r op os' Hinv E) as F. rewrite Eb in F. repeat split; try apply F; try assumption.
all: match goal with H : Some _ = None |- _ => discriminate H end.
- inversion E; subst. pose proof Hinv as (A & B & _). split; [exact Hinv|]. repeat split; auto; try lia.
Qed.

End PacketoutFacts.
