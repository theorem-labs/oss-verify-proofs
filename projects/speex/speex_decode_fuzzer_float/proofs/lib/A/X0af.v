(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09u.
Import ListNotations.
Open Scope Z_scope.

Section ListFacts.

Lemma low8_nonneg : forall v, 0 <= low8 v.
Proof. intros v. unfold low8. apply Z.land_nonneg. right. lia. Qed.

Lemma low8_lt256 : forall v, low8 v < 256.
Proof.
intros v. unfold low8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma sum_low_nonneg : forall l, 0 <= sum_low l.
Proof. induction l as [|v l IH]; cbn; [lia|]. pose proof (low8_nonneg v). unfold low8 in *. lia. Qed.

Lemma sum_low_app : forall l1 l2, sum_low (l1 ++ l2) = sum_low l1 + sum_low l2.
Proof. induction l1 as [|v l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma ztake_zdrop_split : forall (k : Z) (l : list Z), 0 <= k -> l = ztake k l ++ zdrop k l.
Proof. intros k l Hk. unfold ztake, zdrop. symmetry. apply firstn_skipn. Qed.

Lemma sum_low_split : forall k l, 0 <= k -> sum_low l = sum_low (ztake k l) + sum_low (zdrop k l).
Proof. intros k l Hk. rewrite (ztake_zdrop_split k l Hk) at 1. apply sum_low_app. Qed.

Lemma zdrop_zdrop : forall a b l, 0 <= a -> 0 <= b -> zdrop b (zdrop a l) = zdrop (a + b) l.
Proof. intros. unfold zdrop. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma zdrop_0 : forall l, zdrop 0 l = l.
Proof. intros. reflexivity. Qed.

Lemma sum_low_zdrop_split : forall a k l, 0 <= a -> 0 <= k ->
sum_low (zdrop a l) = sum_low (zslice a k l) + sum_low (zdrop (a + k) l).
Proof.
intros a k l Ha Hk. unfold zslice. rewrite (sum_low_split k (zdrop a l) Hk). rewrite zdrop_zdrop by lia. reflexivity.
Qed.

Lemma sum_low_bytes : forall l, bytes_ok l -> sum_low l = zsum l.
Proof.
induction l as [|v l IH]; intros Hb; cbn; [reflexivity|].
inversion Hb as [|v' l' Hv Hl]; subst. rewrite IH by exact Hl. pose proof (low8_byte v Hv) as E. unfold low8 in E. rewrite E. reflexivity.
Qed.

Lemma zsum_split : forall k l, 0 <= k -> zsum l = zsum (ztake k l) + zsum (zdrop k l).
Proof. intros k l Hk. rewrite (ztake_zdrop_split k l Hk) at 1. apply zsum_app. Qed.

Lemma ztake_full : forall n l, zlength l <= n -> ztake n l = l.
Proof. intros. unfold ztake, zlength in *. apply firstn_all2. lia. Qed.

Lemma zdrop_nil : forall n l, zlength l <= n -> 0 <= n -> zdrop n l = [].
Proof. intros. unfold zdrop, zlength in *. apply skipn_all2. lia. Qed.

Lemma zslice_full_tail : forall a n l, 0 <= a -> zlength l <= a + n -> zslice a n l = zdrop a l.
Proof.
intros a n l Ha H. unfold zslice.
destruct (Z.le_gt_cases a (zlength l)).
- apply ztake_full. rewrite zlength_zdrop by lia. lia.
- rewrite zdrop_nil by lia. unfold ztake. rewrite firstn_nil. reflexivity.
Qed.

Definition lacing_val_ok (v : Z) : Prop := 0 <= v < 1024 \/ low8 v = 0.

Lemma lacing_val_ok_byte : forall v, 0 <= v < 256 -> lacing_val_ok v.
Proof. intros. left. lia. Qed.

Lemma lor_lt_pow2 : forall v m n, 0 <= v < 2 ^ n -> 0 <= m < 2 ^ n -> Z.lor v m < 2 ^ n.
Proof.
intros v m n Hv Hm.
destruct (Z.lt_ge_cases n 0) as [Hn|Hn]. { rewrite Z.pow_neg_r in Hv by lia. lia. }
assert (H1 : Z.lor v m mod 2 ^ n = Z.lor v m).
{ rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia.
rewrite !Z.mod_small by lia. reflexivity. }
rewrite <- H1. apply Z.mod_pos_bound. lia.
Qed.

Lemma lacing_val_ok_lor256 : forall v, 0 <= v < 256 -> lacing_val_ok (Z.lor v 256).
Proof.
intros v Hv. left. split; [apply Z.lor_nonneg; lia|].
change 1024 with (2 ^ 10). apply lor_lt_pow2; [lia|]. lia.
Qed.

Lemma lacing_val_ok_lor512 : forall v, lacing_val_ok v -> lacing_val_ok (Z.lor v 512).
Proof.
intros v [Hv|Hv].
- left. split; [apply Z.lor_nonneg; lia|]. change 1024 with (2 ^ 10). apply lor_lt_pow2; lia.
- right. rewrite low8_lor512. exact Hv.
Qed.

Lemma lacing_val_ok_hole : lacing_val_ok 1024.
Proof. right. reflexivity. Qed.

Lemma lacing_val_hole_low8 : forall v, lacing_val_ok v -> Z.land v 1024 <> 0 -> low8 v = 0.
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

Lemma Forall_ztake : forall (P : Z -> Prop) n l, Forall P l -> Forall P (ztake n l).
Proof. intros P n l H. unfold ztake. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zdrop : forall (P : Z -> Prop) n l, Forall P l -> Forall P (zdrop n l).
Proof. intros P n l H. unfold zdrop. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.

Lemma upd_nat_Forall : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_nat l i v).
Proof.
induction l as [|x l IH]; intros [|i] v Hl Hv; cbn; auto.
- inversion Hl; subst. constructor; auto.
- inversion Hl; subst. constructor; auto.
Qed.
Lemma Forall_zupd : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (zupd l i v).
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_Forall. Qed.

Lemma sum_low_upd_nat : forall l i v, (i < length l)%nat -> low8 v = low8 (nth i l 0) -> sum_low (upd_nat l i v) = sum_low l.
Proof.
induction l as [|x l IH]; intros [|i] v Hi Hv; cbn in *; try lia.
- unfold low8 in Hv. rewrite Hv. reflexivity.
- rewrite IH; auto. lia.
Qed.

Lemma sum_low_zupd_lor512 : forall l i, sum_low (zupd l i (Z.lor (znth l i) 512)) = sum_low l.
Proof.
intros l i. unfold zupd, znth. destruct (Z.ltb_spec i 0); [reflexivity|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- apply sum_low_upd_nat; [assumption|]. apply low8_lor512.
- rewrite nth_overflow by lia.
revert H0. generalize (Z.to_nat i). clear. induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
rewrite IH by lia. reflexivity.
Qed.

Lemma Forall_In_znth : forall (P : Z -> Prop) l i, Forall P l -> P 0 -> P (znth l i).
Proof.
intros P l i H H0. unfold znth. destruct (i <? 0); [exact H0|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- rewrite Forall_forall in H. apply H. apply nth_In. assumption.
- rewrite nth_overflow by lia. exact H0.
Qed.

Lemma ztake_0 : forall l : list Z, ztake 0 l = [].
Proof. reflexivity. Qed.
Lemma ztake_1_cons : forall x (l : list Z), ztake 1 (x :: l) = [x].
Proof. reflexivity. Qed.

Lemma znth_head_zdrop : forall (l : list Z) n x t, 0 <= n -> zdrop n l = x :: t -> znth l n = x.
Proof.
intros l n x t Hn Ed. replace n with (n + 0) by lia. rewrite <- znth_zdrop by lia. rewrite Ed. reflexivity.
Qed.

Lemma skip_continued_sum : forall l n s, skip_continued l = (n, s) -> 0 <= n <= zlength l /\ s = zsum (ztake n l).
Proof.
induction l as [|v l IH]; intros n s E; cbn [skip_continued] in E.
- inversion E; subst. rewrite zlength_nil, ztake_0. cbn [zsum]. lia.
- rewrite zlength_cons. destruct (Z.ltb_spec v 255).
+ inversion E; subst. rewrite ztake_1_cons. cbn [zsum]. pose proof (zlength_nonneg l). lia.
+ destruct (skip_continued l) as [n' s'] eqn:E'. inversion E; subst. destruct (IH n' s' eq_refl) as [Hn Hs].
split; [lia|]. unfold ztake in *. replace (Z.to_nat (n' + 1)) with (S (Z.to_nat n')) by lia. cbn [firstn zsum]. lia.
Qed.

Lemma seg_loop_sum : forall vals bos fill packet saved lac gran f p s,
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

Lemma gather255_sum : forall rest size eos bytes n n' eos' bytes',
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

Lemma body_inv_returned_le_fill : forall os, body_inv os -> os_body_returned os <= os_body_fill os.
Proof. intros os (A & B & C & D). pose proof (sum_low_nonneg (zdrop (os_lacing_returned os) (os_lacing os))). lia. Qed.

Lemma body_inv_fill_nonneg : forall os, body_inv os -> 0 <= os_body_fill os.
Proof. intros os H. pose proof (body_inv_returned_le_fill os H). destruct H as (A & B & C & D). lia. Qed.

Lemma stream_zero_body_inv : body_inv stream_zero.
Proof. unfold body_inv, stream_zero; cbn. repeat split; try lia. constructor. Qed.

Lemma ogg_stream_init_body_inv : forall b l g sn,
body_inv (mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 sn 0 0 0).
Proof. intros. unfold body_inv; cbn. repeat split; try lia. constructor. Qed.

Lemma ogg_stream_reset_body_inv : forall os, body_inv (ogg_stream_reset os).
Proof. intros. unfold body_inv, ogg_stream_reset; cbn. repeat split; try lia. constructor. Qed.

Lemma ogg_stream_reset_serialno_body_inv : forall os sn r os',
body_inv os -> ogg_stream_reset_serialno os sn = (r, os') -> body_inv os'.
Proof.
intros os sn r os' H E. unfold ogg_stream_reset_serialno in E.
destruct (ogg_stream_check os); inversion E; subst; [exact H|].
unfold body_inv, ogg_stream_reset; cbn. repeat split; try lia. constructor.
Qed.

Lemma set_blocks_body_inv : forall os b bs l g ls, body_inv os -> body_inv (set_blocks os b bs l g ls).
Proof. intros. unfold body_inv, set_blocks in *; cbn. tauto. Qed.

Lemma set_tail_body_inv : forall os e p n, body_inv os -> body_inv (set_tail os e p n).
Proof. intros. unfold body_inv, set_tail in *; cbn. tauto. Qed.

Lemma pagein_returned_body_inv : forall os, stream_inv os -> body_inv os ->
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

Lemma pagein_unroll_body_inv : forall os pageno, stream_inv os -> os_lacing_returned os = 0 -> body_inv os ->
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

Lemma pagein_skip_sum : forall os hdr, bytes_ok (lacing_of hdr) ->
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

Lemma pagein_body_segments_body_inv : forall os hdr body bos segptr skipped,
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

Lemma packetout_body_inv : forall os r op os',
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

Lemma ogg_stream_packetout_body_inv : forall os r op os',
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

Lemma pagein_segments_frame : forall os hdr bos segptr,
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

Lemma sync_fail_no_page : forall sy ret bytes r og sy', sync_fail sy ret bytes = ((r, og), sy') -> og = None.
Proof. intros sy ret bytes r og sy' E. unfold sync_fail in E. inversion E. reflexivity. Qed.

Lemma ogg_sync_pageseek_pos : forall sy r og sy',
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

Lemma pageout_loop_frame : forall fuel sy r og sy',
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

Theorem ogg_sync_pageout_frame : forall sy r og sy',
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

Lemma page_ok_body_len : forall sy og, sync_inv sy -> page_ok sy og ->
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

Section PacketoutFacts.
Context {ptr : Type}.
Implicit Types os : stream_st ptr.

Lemma packetout_frame : forall os r op os',
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

Lemma ogg_stream_packetout_frame : forall os r op os',
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

