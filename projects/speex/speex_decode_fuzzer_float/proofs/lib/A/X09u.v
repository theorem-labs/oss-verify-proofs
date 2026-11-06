(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz.
Import ListNotations.
Open Scope Z_scope.

Section OggFacts.
Context {ptr : Type}.
Implicit Types sy : sync_st ptr.

Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

Definition sync_inv sy : Prop :=
0 <= sy_returned sy <= sy_fill sy /\ sy_fill sy <= zlength (sy_buf sy) /\
0 <= sy_headerbytes sy /\ 0 <= sy_bodybytes sy /\ bytes_ok (sy_buf sy).

Lemma bytes_ok_zdrop : forall n l, bytes_ok l -> bytes_ok (zdrop n l).
Proof. intros n l H. unfold bytes_ok, zdrop in *. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_ztake : forall n l, bytes_ok l -> bytes_ok (ztake n l).
Proof. intros n l H. unfold bytes_ok, ztake in *. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_zslice : forall off n l, bytes_ok l -> bytes_ok (zslice off n l).
Proof. intros. unfold zslice. apply bytes_ok_ztake, bytes_ok_zdrop. assumption. Qed.
Lemma znth_bytes_ok : forall l i, bytes_ok l -> 0 <= znth l i < 256.
Proof.
intros l i H. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. assumption.
- rewrite nth_overflow by assumption. lia.
Qed.
Lemma zsum_bytes_nonneg : forall l, bytes_ok l -> 0 <= zsum l.
Proof. intros l H. apply zsum_nonneg. unfold bytes_ok in H. eapply Forall_impl; [|exact H]. cbv beta. intros; lia. Qed.

Lemma sync_fail_inv : forall sy sy0 r og sy',
sync_inv sy ->
sy_data sy0 = sy_data sy -> sy_buf sy0 = sy_buf sy -> sy_storage sy0 = sy_storage sy ->
sy_fill sy0 = sy_fill sy -> sy_returned sy0 = sy_returned sy ->
1 <= sy_fill sy - sy_returned sy ->
sync_fail sy0 (sy_returned sy) (sy_fill sy - sy_returned sy) = ((r, og), sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\
(r < 0 -> sy_returned sy < sy_returned sy') /\ (0 <= r -> sy_returned sy <= sy_returned sy').
Proof.
intros sy sy0 r og sy' Hinv Hd Hb Hs Hf Hr Hbytes E. unfold sync_fail in E.
unfold sync_inv in *.
destruct (find_byte CHAR_O _ _) as [j|] eqn:F; inversion E; subst; cbn -[Z.add Z.sub Z.opp].
- apply find_byte_range in F.
pose proof (zlength_ztake_le_n (sy_fill sy - sy_returned sy - 1) (zdrop (sy_returned sy + 1) (sy_buf sy0)) ltac:(lia)) as L1.
unfold zslice in F. rewrite Hb in *. repeat split; try tauto; try lia.
- rewrite Hf, Hb in *. repeat split; try tauto; try lia.
Qed.

Lemma ogg_sync_pageseek_inv : forall sy r og sy',
sync_inv sy -> ogg_sync_pageseek sy = ((r, og), sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\
(r < 0 -> sy_returned sy < sy_returned sy') /\ (0 <= r -> sy_returned sy <= sy_returned sy').
Proof.
intros sy r og sy' Hinv E. unfold ogg_sync_pageseek in E.
destruct (ogg_sync_check sy) eqn:Hck.
{ inversion E; subst. unfold sync_inv in *. repeat split; try tauto; intros; lia. }

assert (TAIL : forall (crc_ok : bool) (sy0 : sync_st ptr),
sy_data sy0 = sy_data sy -> sy_buf sy0 = sy_buf sy -> sy_storage sy0 = sy_storage sy ->
sy_fill sy0 = sy_fill sy -> sy_returned sy0 = sy_returned sy -> sy_unsynced sy0 = sy_unsynced sy ->
1 <= sy_headerbytes sy0 -> 0 <= sy_bodybytes sy0 ->
(if sy_fill sy - sy_returned sy <? sy_bodybytes sy0 + sy_headerbytes sy0 then (0, None, sy0)
else if negb crc_ok
then sync_fail sy0 (sy_returned sy) (sy_fill sy - sy_returned sy)
else (sy_headerbytes sy0 + sy_bodybytes sy0,
Some {| pg_hdr := sy_returned sy; pg_header_len := sy_headerbytes sy0; pg_body_len := sy_bodybytes sy0 |},
{| sy_data := sy_data sy0; sy_buf := sy_buf sy; sy_storage := sy_storage sy0; sy_fill := sy_fill sy0;
sy_returned := sy_returned sy + (sy_headerbytes sy0 + sy_bodybytes sy0);
sy_unsynced := 0; sy_headerbytes := 0; sy_bodybytes := 0 |})) = (r, og, sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\
(r < 0 -> sy_returned sy < sy_returned sy') /\ (0 <= r -> sy_returned sy <= sy_returned sy')).
{ intros crc_ok sy0 Hd Hb Hs Hf Hr Hu Hh Hbb E0.
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (sy_bodybytes sy0 + sy_headerbytes sy0)).
- inversion E0; subst. unfold sync_inv in *. rewrite Hb, Hf, Hr. repeat split; try tauto; try lia.
- destruct crc_ok; cbn [negb] in E0.
2: { eapply sync_fail_inv; eauto. lia. }
+ inversion E0; subst. unfold sync_inv in *. cbn -[Z.add Z.sub]. rewrite Hf. repeat split; try tauto; try lia. }
destruct (sy_headerbytes sy =? 0) eqn:Hhb0.
- destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) 27) as [Hlt|Hge].
{ inversion E; subst. unfold sync_inv in *. repeat split; try tauto; intros; lia. }
destruct (negb (list_eqb _ OGGS_MAGIC)) eqn:Hmagic.
{ eapply (sync_fail_inv sy sy); eauto. lia. }
assert (Hbufok : bytes_ok (sy_buf sy)) by (unfold sync_inv in Hinv; tauto).
pose proof (znth_bytes_ok (sy_buf sy) (sy_returned sy + 26) Hbufok) as Hnseg.
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (znth (sy_buf sy) (sy_returned sy + 26) + 27)) as [Hlt2|Hge2].
{ inversion E; subst. unfold sync_inv in *. repeat split; try tauto; intros; lia. }
eapply TAIL; [..|exact E]; cbn; auto; try lia.
unfold sync_inv in Hinv. pose proof (zsum_bytes_nonneg _ (bytes_ok_zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) _ Hbufok)). lia.
- eapply TAIL; [..|exact E]; auto.
+ apply Z.eqb_neq in Hhb0. unfold sync_inv in Hinv. lia.
+ unfold sync_inv in Hinv. lia.
Qed.

Lemma pageout_loop_some : forall fuel sy,
sync_inv sy -> (Z.to_nat (sy_fill sy - sy_returned sy) < fuel)%nat ->
exists res, pageout_loop fuel sy = Some res.
Proof.
induction fuel as [|fuel IH]; intros sy Hinv Hm; [lia|].
cbn [pageout_loop].
destruct (ogg_sync_pageseek sy) as [[r og] sy1] eqn:E.
pose proof (ogg_sync_pageseek_inv sy r og sy1 Hinv E) as (Hinv1 & Hf & Hb & Hd & Hs & Hneg & Hpos).
destruct (Z.ltb_spec 0 r); [eexists; reflexivity|].
destruct (Z.eqb_spec r 0); [eexists; reflexivity|].
destruct (sy_unsynced sy1 =? 0); [eexists; reflexivity|].
apply IH; [exact Hinv1|]. specialize (Hneg ltac:(lia)). unfold sync_inv in Hinv1. lia.
Qed.

Theorem ogg_sync_pageout_total : forall sy, sync_inv sy -> ogg_sync_pageout sy <> None.
Proof.
intros sy Hinv. unfold ogg_sync_pageout. destruct (ogg_sync_check sy); [discriminate|].
destruct (pageout_loop_some (pageout_fuel sy) sy Hinv) as [res ->]; [|discriminate].
unfold pageout_fuel. lia.
Qed.

Lemma pageout_loop_inv : forall fuel sy r og sy',
sync_inv sy -> pageout_loop fuel sy = Some ((r, og), sy') ->
sync_inv sy' /\ sy_fill sy' = sy_fill sy /\ sy_buf sy' = sy_buf sy /\ sy_data sy' = sy_data sy /\
sy_storage sy' = sy_storage sy /\ sy_returned sy <= sy_returned sy'.
Proof.
induction fuel as [|fuel IH]; intros sy r og sy' Hinv E; [discriminate|].
cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1] eqn:E1.
pose proof (ogg_sync_pageseek_inv sy r1 og1 sy1 Hinv E1) as (Hinv1 & Hf & Hb & Hd & Hs & Hneg & Hpos).
destruct (Z.ltb_spec 0 r1). { inversion E; subst. specialize (Hpos ltac:(lia)). unfold sync_inv in *. repeat split; try tauto; try lia. }
destruct (Z.eqb_spec r1 0). { inversion E; subst. specialize (Hpos ltac:(lia)). unfold sync_inv in *. repeat split; try tauto; try lia. }
specialize (Hneg ltac:(lia)).
destruct (sy_unsynced sy1 =? 0).
{ inversion E; subst. unfold sync_inv in *. cbn. repeat split; first [tauto | lia]. }
destruct (IH sy1 r og sy' Hinv1 E) as (A & B & C & D & F & G). repeat split; try tauto; try congruence; try lia.
all: unfold sync_inv in *; tauto.
Qed.

Implicit Types os : stream_st ptr.

Definition low8 (v : Z) : Z := Z.land v 255.

Definition lacing_inv os : Prop :=
0 <= os_lacing_returned os <= os_lacing_packet os /\ os_lacing_packet os <= zlength (os_lacing os) /\
(os_lacing_returned os < os_lacing_packet os -> low8 (znth (os_lacing os) (os_lacing_packet os - 1)) <> 255).

Lemma gather255_some : forall rest size eos bytes n,
(size <> 255 \/ exists k, (k < length rest)%nat /\ low8 (nth k rest 0) <> 255) ->
gather255 size rest eos bytes n <> None.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n Hex; cbn [gather255].
- destruct (Z.eqb_spec size 255); [|discriminate]. destruct Hex as [?|(k & Hk & _)]; [lia| cbn in Hk; lia].
- destruct (Z.eqb_spec size 255); [|discriminate].
apply IH. destruct Hex as [?|(k & Hk & Hlow)]; [lia|].
destruct k as [|k]; cbn in Hlow; [left; exact Hlow|].
right. exists k. cbn in Hk. split; [lia| exact Hlow].
Qed.

Lemma znth_zdrop : forall l n i, 0 <= n -> 0 <= i -> znth (zdrop n l) i = znth l (n + i).
Proof.
intros l n i Hn Hi. unfold znth, zdrop. destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec (n + i) 0); [lia|].
rewrite nth_skipn. f_equal. lia.
Qed.

Theorem packetout_total : forall os, lacing_inv os -> packetout os <> None.
Proof.
intros os (Hr & Hp & Hlast). unfold packetout.
destruct (Z.leb_spec (os_lacing_packet os) (os_lacing_returned os)); [discriminate|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)); [discriminate|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:G; [discriminate|].
exfalso. revert G. apply gather255_some.
destruct (Z.eq_dec (Z.land (znth (os_lacing os) (os_lacing_returned os)) 255) 255) as [E|NE]; [|left; exact NE].
right. specialize (Hlast ltac:(lia)).

assert (Hne : os_lacing_returned os <> os_lacing_packet os - 1).
{ intros HH. apply Hlast. unfold low8. rewrite <- HH. exact E. }
exists (Z.to_nat (os_lacing_packet os - 1 - (os_lacing_returned os + 1))). split.
- unfold zdrop. rewrite length_skipn. unfold zlength in Hp. lia.
- unfold low8 in *.
replace (nth (Z.to_nat (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) (zdrop (os_lacing_returned os + 1) (os_lacing os)) 0)
with (znth (zdrop (os_lacing_returned os + 1) (os_lacing os)) (os_lacing_packet os - 1 - (os_lacing_returned os + 1))).
2:{ unfold znth. destruct (Z.ltb_spec (os_lacing_packet os - 1 - (os_lacing_returned os + 1)) 0); [lia| reflexivity]. }
rewrite znth_zdrop by lia.
replace (os_lacing_returned os + 1 + (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) with (os_lacing_packet os - 1) by lia.
exact Hlast.
Qed.

Theorem ogg_stream_packetout_total : forall os, lacing_inv os -> ogg_stream_packetout os <> None.
Proof.
intros os H. unfold ogg_stream_packetout. destruct (ogg_stream_check os); [discriminate|]. apply packetout_total. exact H.
Qed.

Lemma gather255_bound : forall rest size eos bytes n n' eos' bytes',
gather255 size rest eos bytes n = Some (n', eos', bytes') -> n <= n' <= n + zlength rest.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n n' eos' bytes' G; cbn [gather255] in G.
- destruct (size =? 255); [discriminate|]. inversion G; subst. rewrite zlength_nil. lia.
- rewrite zlength_cons. destruct (size =? 255).
+ apply IH in G. lia.
+ inversion G; subst. pose proof (zlength_nonneg rest). lia.
Qed.

Lemma gather255_size_ne : forall rest size eos bytes n n' e' b',
gather255 size rest eos bytes n = Some (n', e', b') -> size <> 255 -> n' = n.
Proof.
intros rest size eos bytes n n' e' b' G Hs. destruct rest; cbn [gather255] in G;
(destruct (Z.eqb_spec size 255); [lia|]); inversion G; reflexivity.
Qed.

Lemma gather255_first : forall rest size eos bytes n n' e' b' k,
gather255 size rest eos bytes n = Some (n', e', b') ->
(k < length rest)%nat -> low8 (nth k rest 0) <> 255 -> n' <= n + Z.of_nat k + 1.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n n' e' b' k G Hk Hlow; [cbn in Hk; lia|].
cbn [gather255] in G. destruct (Z.eqb_spec size 255).
- destruct k as [|k].
+ cbn in Hlow. apply gather255_size_ne in G; [lia|]. unfold low8 in Hlow. exact Hlow.
+ cbn in Hk, Hlow. eapply IH in G; [| | exact Hlow]; [|lia]. rewrite Nat2Z.inj_succ. lia.
- inversion G; subst. lia.
Qed.

Lemma packetout_inv : forall os r op os',
lacing_inv os -> packetout os = Some ((r, op), os') ->
lacing_inv os' /\ os_lacing os' = os_lacing os /\ os_body os' = os_body os /\
os_lacing_packet os' = os_lacing_packet os /\ os_lacing_returned os <= os_lacing_returned os'.
Proof.
intros os r op os' Hinv E. pose proof Hinv as (Hr & Hp & Hlast). unfold packetout in E.
destruct (Z.leb_spec (os_lacing_packet os) (os_lacing_returned os)).
{ inversion E; subst. repeat split; auto; try tauto. lia. }
specialize (Hlast ltac:(lia)).
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)).
{ inversion E; subst. unfold lacing_inv; cbn. repeat split; auto; try lia. }
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:G; [|discriminate].
inversion E; subst. unfold lacing_inv; cbn.

assert (Hn : 0 <= n /\ os_lacing_returned os + n <= os_lacing_packet os - 1).
{ pose proof (gather255_bound _ _ _ _ _ _ _ _ G) as B.
destruct (Z.eq_dec (Z.land (znth (os_lacing os) (os_lacing_returned os)) 255) 255) as [E255|NE].
- assert (Hne : os_lacing_returned os <> os_lacing_packet os - 1).
{ intros HH. apply Hlast. unfold low8. rewrite <- HH. exact E255. }
pose proof (gather255_first _ _ _ _ _ _ _ _ (Z.to_nat (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) G) as F.
assert (HF : n <= 0 + Z.of_nat (Z.to_nat (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) + 1).
{ apply F.
- unfold zdrop. rewrite length_skipn. unfold zlength in Hp. lia.
- unfold low8 in *.
replace (nth (Z.to_nat (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) (zdrop (os_lacing_returned os + 1) (os_lacing os)) 0)
with (znth (zdrop (os_lacing_returned os + 1) (os_lacing os)) (os_lacing_packet os - 1 - (os_lacing_returned os + 1))).
2:{ unfold znth. destruct (Z.ltb_spec (os_lacing_packet os - 1 - (os_lacing_returned os + 1)) 0); [lia| reflexivity]. }
rewrite znth_zdrop by lia.
replace (os_lacing_returned os + 1 + (os_lacing_packet os - 1 - (os_lacing_returned os + 1))) with (os_lacing_packet os - 1) by lia.
exact Hlast. }
rewrite Z2Nat.id in HF by lia. lia.
- apply gather255_size_ne in G; [|exact NE]. lia. }
repeat split; auto; try lia.
Qed.

Definition stream_inv os : Prop :=
0 <= os_lacing_returned os <= os_lacing_packet os /\ os_lacing_packet os <= os_lacing_fill os /\
zlength (os_lacing os) = os_lacing_fill os /\ zlength (os_granules os) = os_lacing_fill os /\
(os_lacing_returned os < os_lacing_packet os -> low8 (znth (os_lacing os) (os_lacing_packet os - 1)) <> 255).

Lemma stream_inv_lacing_inv : forall os, stream_inv os -> lacing_inv os.
Proof. intros os (A & B & C & D & E). unfold lacing_inv. rewrite C. repeat split; lia. Qed.

Lemma stream_zero_inv : stream_inv stream_zero.
Proof. unfold stream_inv, stream_zero; cbn. repeat split; try lia. Qed.

Lemma ogg_stream_reset_inv : forall os, stream_inv (ogg_stream_reset os).
Proof. intros. unfold stream_inv, ogg_stream_reset; cbn. repeat split; try lia. Qed.

Lemma ogg_stream_reset_serialno_inv : forall os sn r os',
stream_inv os -> ogg_stream_reset_serialno os sn = (r, os') -> stream_inv os'.
Proof.
intros os sn r os' H E. unfold ogg_stream_reset_serialno in E. destruct (ogg_stream_check os); inversion E; subst; [exact H|].
unfold stream_inv, ogg_stream_reset; cbn. repeat split; try lia.
Qed.

Lemma packetout_stream_inv : forall os r op os',
stream_inv os -> packetout os = Some ((r, op), os') -> stream_inv os'.
Proof.
intros os r op os' Hinv E.
pose proof (packetout_inv os r op os' (stream_inv_lacing_inv os Hinv) E) as (L & HL & HB & HP & HR).

unfold packetout in E. unfold stream_inv in *. destruct Hinv as (A & B & C & D & F).
destruct (os_lacing_packet os <=? os_lacing_returned os); [inversion E; subst; repeat split; auto; lia|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)).
{ inversion E; subst; cbn in *. unfold lacing_inv in L; cbn in L. repeat split; try lia; tauto. }
destruct (gather255 _ _ _ _ _) as [[[n e] by_]|]; [|discriminate]. inversion E; subst; cbn in *.
unfold lacing_inv in L; cbn in L. repeat split; try lia; tauto.
Qed.

Lemma znth_app_l : forall l1 l2 i, 0 <= i < zlength l1 -> znth (l1 ++ l2) i = znth l1 i.
Proof. intros. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|]. apply app_nth1. lia. Qed.
Lemma znth_app_r : forall l1 l2 i, zlength l1 <= i -> znth (l1 ++ l2) i = znth l2 (i - zlength l1).
Proof.
intros. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec (i - Z.of_nat (length l1)) 0); [lia|].
rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_ztake : forall n l i, 0 <= i < n -> znth (ztake n l) i = znth l i.
Proof.
intros. unfold znth, ztake. destruct (Z.ltb_spec i 0); [lia|].
rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat n)); [reflexivity| lia].
Qed.

Lemma low8_1024 : low8 1024 = 0.
Proof. reflexivity. Qed.

Lemma pagein_returned_inv : forall os, stream_inv os ->
stream_inv (pagein_returned os) /\ os_lacing_returned (pagein_returned os) = 0 /\
os_lacing_vals (pagein_returned os) = os_lacing_vals os /\ os_granule_vals (pagein_returned os) = os_granule_vals os /\
os_body_data (pagein_returned os) = os_body_data os /\ os_lacing_storage (pagein_returned os) = os_lacing_storage os /\
os_body_storage (pagein_returned os) = os_body_storage os /\ os_serialno (pagein_returned os) = os_serialno os /\
os_pageno (pagein_returned os) = os_pageno os.
Proof.
intros os (A & B & C & D & F). unfold pagein_returned.
set (os1 := if negb (os_body_returned os =? 0) then _ else os).
assert (H1 : os_lacing os1 = os_lacing os /\ os_granules os1 = os_granules os /\ os_lacing_fill os1 = os_lacing_fill os /\
os_lacing_packet os1 = os_lacing_packet os /\ os_lacing_returned os1 = os_lacing_returned os /\
os_lacing_vals os1 = os_lacing_vals os /\ os_granule_vals os1 = os_granule_vals os /\ os_body_data os1 = os_body_data os /\
os_lacing_storage os1 = os_lacing_storage os /\ os_body_storage os1 = os_body_storage os /\ os_serialno os1 = os_serialno os /\
os_pageno os1 = os_pageno os).
{ subst os1. destruct (negb (os_body_returned os =? 0)); cbn; repeat split; reflexivity. }
destruct H1 as (L1 & G1 & F1 & P1 & R1 & LV1 & GV1 & BD1 & LS1 & BS1 & SN1 & PN1).
destruct (Z.eqb_spec (os_lacing_returned os1) 0) as [Hz|Hnz]; cbn [negb].
- unfold stream_inv. rewrite L1, G1, F1, P1, R1, LV1, GV1, BD1, LS1, BS1, SN1, PN1 in *. repeat split; auto; lia.
- unfold stream_inv; cbn [os_lacing os_granules os_lacing_fill os_lacing_packet os_lacing_returned set_lacing set_body set_tail os_lacing_vals os_granule_vals os_body_data os_lacing_storage os_body_storage os_body os_body_fill os_body_returned os_serialno os_pageno os_e_o_s os_b_o_s os_header_fill os_packetno os_granulepos]. rewrite L1, G1, F1, P1, R1 in *. rewrite !zlength_zdrop by lia.
repeat split; auto; try lia.
intros Hlt. rewrite znth_zdrop by lia.
replace (os_lacing_returned os + (os_lacing_packet os - os_lacing_returned os - 1)) with (os_lacing_packet os - 1) by lia.
apply F. lia.
Qed.

Lemma pagein_unroll_inv : forall os pageno, stream_inv os -> os_lacing_returned os = 0 ->
stream_inv (pagein_unroll os pageno) /\ os_lacing_returned (pagein_unroll os pageno) = 0 /\
os_lacing_vals (pagein_unroll os pageno) = os_lacing_vals os /\ os_granule_vals (pagein_unroll os pageno) = os_granule_vals os /\
os_body_data (pagein_unroll os pageno) = os_body_data os /\ os_lacing_storage (pagein_unroll os pageno) = os_lacing_storage os /\
os_body_storage (pagein_unroll os pageno) = os_body_storage os /\
os_lacing_fill (pagein_unroll os pageno) <= os_lacing_fill os + 1.
Proof.
intros os pageno (A & B & C & D & F) HR. unfold pagein_unroll.
destruct (Z.eqb_spec pageno (os_pageno os)); cbn [negb].
{ unfold stream_inv. repeat split; auto; lia. }
cbn [os_lacing os_granules os_lacing_fill os_lacing_packet os_lacing_returned set_lacing set_body set_tail os_lacing_vals os_granule_vals os_body_data os_lacing_storage os_body_storage os_body os_body_fill os_body_returned os_serialno os_pageno os_e_o_s os_b_o_s os_header_fill os_packetno os_granulepos].
destruct (Z.eqb_spec (os_pageno os) (-1)); cbn [negb]; unfold stream_inv; cbn [os_lacing os_granules os_lacing_fill os_lacing_packet os_lacing_returned set_lacing set_body set_tail os_lacing_vals os_granule_vals os_body_data os_lacing_storage os_body_storage os_body os_body_fill os_body_returned os_serialno os_pageno os_e_o_s os_b_o_s os_header_fill os_packetno os_granulepos].
- rewrite !zlength_ztake by lia. repeat split; auto; try lia.
intros Hlt. rewrite znth_ztake by lia. apply F. lia.
- rewrite !zlength_app, !zlength_ztake by lia. rewrite !zlength_cons, !zlength_nil. repeat split; auto; try lia.
intros _. rewrite znth_app_r by (rewrite zlength_ztake; lia). rewrite zlength_ztake by lia.
replace (os_lacing_packet os + 1 - 1 - os_lacing_packet os) with 0 by lia.
change (low8 (znth [1024] 0)) with 0. lia.
Qed.

Lemma low8_byte : forall v, 0 <= v < 256 -> low8 v = v.
Proof. intros. unfold low8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma low8_lor256 : forall v, low8 (Z.lor v 256) = low8 v.
Proof. intros. unfold low8. rewrite Z.land_lor_distr_l. change (Z.land 256 255) with 0. apply Z.lor_0_r. Qed.
Lemma low8_lor512 : forall v, low8 (Z.lor v 512) = low8 v.
Proof. intros. unfold low8. rewrite Z.land_lor_distr_l. change (Z.land 512 255) with 0. apply Z.lor_0_r. Qed.

Lemma seg_loop_spec : forall vals bos fill packet saved lac gran f p s,
Forall (fun v => 0 <= v < 256) vals -> packet <= fill ->
seg_loop vals bos fill packet saved = (lac, gran, f, p, s) ->
zlength lac = zlength vals /\ zlength gran = zlength vals /\ f = fill + zlength vals /\
packet <= p <= f /\ (s = saved \/ fill <= s < f) /\
(p <> packet -> fill < p /\ low8 (znth lac (p - fill - 1)) <> 255).
Proof.
induction vals as [|v vals IH]; intros bos fill packet saved lac gran f p s Hb Hp E; cbn [seg_loop] in E.
- inversion E; subst. rewrite !zlength_nil. repeat split; auto; try lia.
- inversion Hb as [|v' vals' Hv Hvals]; subst v' vals'.
destruct (seg_loop vals false (fill + 1) (if v <? 255 then fill + 1 else packet) (if v <? 255 then fill else saved))
as [[[[lac' gran'] f'] p'] s'] eqn:E'.
injection E as E1 E2 E3 E4 E5. subst lac gran f p s.
assert (Hp' : (if v <? 255 then fill + 1 else packet) <= fill + 1) by (destruct (v <? 255); lia).
pose proof (IH _ _ _ _ _ _ _ _ _ Hvals Hp' E') as (L1 & L2 & F1 & P1 & S1 & T1).
rewrite !zlength_cons.
split; [lia|]. split; [lia|]. split; [lia|].
split; [destruct (Z.ltb_spec v 255); lia|].
split; [destruct (Z.ltb_spec v 255); lia|].
intros Hne. destruct (Z.eq_dec p' (if v <? 255 then fill + 1 else packet)) as [Ep|Np].
+ destruct (Z.ltb_spec v 255); [|lia]. split; [lia|].
rewrite Ep. replace (fill + 1 - fill - 1) with 0 by lia.
change (znth ((if bos then Z.lor v 256 else v) :: lac') 0) with (if bos then Z.lor v 256 else v).
destruct bos; rewrite ?low8_lor256, low8_byte by lia; lia.
+ destruct (T1 Np) as [T2 T3]. split; [lia|].
unfold znth in *. destruct (Z.ltb_spec (p' - fill - 1) 0); [lia|]. destruct (Z.ltb_spec (p' - (fill + 1) - 1) 0); [lia|].
replace (Z.to_nat (p' - fill - 1)) with (S (Z.to_nat (p' - (fill + 1) - 1))) by lia. cbn [nth]. exact T3.
Qed.

Lemma znth_zupd_other : forall l i j v, i <> j -> znth (zupd l i v) j = znth l j.
Proof. intros. apply znth_zupd_neq. assumption. Qed.

Lemma pagein_segments_inv : forall os hdr bos segptr, stream_inv os -> os_lacing_returned os = 0 ->
Forall (fun v => 0 <= v < 256) (lacing_of hdr) -> 0 <= segptr ->
stream_inv (pagein_segments os hdr bos segptr).
Proof.
intros os hdr bos segptr (A & B & C & D & F) HR Hbytes Hseg. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f'] p'] s'] eqn:E.
assert (Hvals : Forall (fun v => 0 <= v < 256) (zdrop segptr (lacing_of hdr))).
{ unfold zdrop. rewrite <- (firstn_skipn (Z.to_nat segptr) (lacing_of hdr)) in Hbytes. apply Forall_app in Hbytes. tauto. }
pose proof (seg_loop_spec _ _ _ _ _ _ _ _ _ _ Hvals B E) as (L1 & L2 & F1 & P1 & S1 & T1).
unfold stream_inv. cbn [os_lacing os_granules os_lacing_fill os_lacing_packet os_lacing_returned set_lacing set_tail].
rewrite HR.
assert (Llac : zlength (os_lacing os ++ lac) = f') by (rewrite zlength_app; lia).
assert (Lgr : zlength (if negb (s' =? -1) then zupd (os_granules os ++ gran) s' (ogg_page_granulepos hdr) else os_granules os ++ gran) = f').
{ destruct (negb (s' =? -1)); rewrite ?zlength_zupd, zlength_app; lia. }
repeat split; try lia.
- destruct (negb (ogg_page_eos hdr =? 0)); [destruct (0 <? f'); [rewrite zlength_zupd|]|]; exact Llac.
- intros Hlt.

assert (Hterm : low8 (znth (os_lacing os ++ lac) (p' - 1)) <> 255).
{ destruct (Z.eq_dec p' (os_lacing_packet os)) as [Ep|Np].
- rewrite Ep. rewrite znth_app_l by lia. apply F. lia.
- destruct (T1 Np) as [T2 T3]. rewrite znth_app_r by lia. rewrite C.
replace (p' - 1 - os_lacing_fill os) with (p' - os_lacing_fill os - 1) by lia. exact T3. }
destruct (negb (ogg_page_eos hdr =? 0)); [|exact Hterm].
destruct (Z.ltb_spec 0 f'); [|exact Hterm].
destruct (Z.eq_dec (f' - 1) (p' - 1)) as [Ei|Ni].
+ rewrite Ei. rewrite znth_zupd_eq by (rewrite Llac; lia). rewrite low8_lor512. rewrite <- Ei.
rewrite Ei. exact Hterm.
+ rewrite znth_zupd_other by exact Ni. exact Hterm.
Qed.

Lemma pagein_body_inv : forall os body skipped bodysize, stream_inv os ->
stream_inv (pagein_body os body skipped bodysize) /\
os_lacing_returned (pagein_body os body skipped bodysize) = os_lacing_returned os.
Proof. intros os body skipped bodysize H. unfold stream_inv, pagein_body in *; cbn. tauto. Qed.

Lemma set_blocks_inv : forall os b bs l g ls, stream_inv os ->
stream_inv (set_blocks os b bs l g ls) /\ os_lacing_returned (set_blocks os b bs l g ls) = os_lacing_returned os.
Proof. intros. unfold stream_inv, set_blocks in *; cbn. tauto. Qed.

Lemma ogg_sync_init_inv : sync_inv (ogg_sync_init (ptr:=ptr)).
Proof. unfold sync_inv, ogg_sync_init; cbn. rewrite zlength_nil. repeat split; try lia. unfold bytes_ok; apply Forall_nil. Qed.

Lemma sync_write_inv : forall sy bytes, sync_inv sy -> bytes_ok bytes ->
sync_inv (sync_write sy (sy_fill sy) bytes) /\
zlength (sy_buf (sync_write sy (sy_fill sy) bytes)) = sy_fill sy + zlength bytes /\
sy_fill (sync_write sy (sy_fill sy) bytes) = sy_fill sy /\ sy_returned (sync_write sy (sy_fill sy) bytes) = sy_returned sy /\
sy_storage (sync_write sy (sy_fill sy) bytes) = sy_storage sy.
Proof.
intros sy bytes (A & B & C & D & E) Hb. unfold sync_inv, sync_write; cbn.
rewrite zlength_app, zlength_ztake by lia. pose proof (zlength_nonneg bytes).
repeat split; try lia. unfold bytes_ok in *. apply Forall_app. split; [apply bytes_ok_ztake; exact E| exact Hb].
Qed.

Lemma ogg_sync_wrote_inv : forall sy n r sy', sync_inv sy -> 0 <= n -> sy_fill sy + n <= zlength (sy_buf sy) ->
ogg_sync_wrote sy n = (r, sy') ->
sync_inv sy' /\ sy_buf sy' = sy_buf sy /\ (r = 0 -> sy_fill sy' = sy_fill sy + n) /\ (r <> 0 -> sy' = sy) /\
sy_returned sy' = sy_returned sy /\ sy_storage sy' = sy_storage sy /\ sy_data sy' = sy_data sy.
Proof.
intros sy n r sy' (A & B & C & D & E) Hn Hlen Ew. unfold ogg_sync_wrote in Ew.
destruct (ogg_sync_check sy). { inversion Ew; subst. unfold sync_inv. repeat split; auto; lia. }
destruct (Z.ltb_spec (sy_storage sy) (sy_fill sy + n)).
{ inversion Ew; subst. unfold sync_inv. repeat split; auto; lia. }
inversion Ew; subst. unfold sync_inv; cbn. repeat split; auto; lia.
Qed.

Lemma sync_compact_inv : forall sy, sync_inv sy ->
let fill := sy_fill sy - sy_returned sy in
sync_inv (mkSync (sy_data sy) (ztake fill (zdrop (sy_returned sy) (sy_buf sy))) (sy_storage sy) fill 0
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)) /\
zlength (ztake fill (zdrop (sy_returned sy) (sy_buf sy))) = fill.
Proof.
intros sy (A & B & C & D & E). cbn. unfold sync_inv; cbn.
rewrite zlength_ztake by (rewrite zlength_zdrop by lia; lia).
repeat split; try lia. apply bytes_ok_ztake, bytes_ok_zdrop. exact E.
Qed.

Definition sync_hdr sy : Prop :=
(sy_headerbytes sy = 0 -> sy_bodybytes sy = 0) /\
(sy_headerbytes sy <> 0 ->
sy_headerbytes sy = 27 + znth (sy_buf sy) (sy_returned sy + 26) /\
sy_returned sy + sy_headerbytes sy <= sy_fill sy /\
sy_bodybytes sy = zsum (zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) (sy_buf sy))).

Definition sync_inv2 sy : Prop := sync_inv sy /\ sync_hdr sy.

Definition page_ok sy (og : page) : Prop :=
0 <= pg_hdr og /\ pg_header_len og = 27 + znth (sy_buf sy) (pg_hdr og + 26) /\ 0 <= znth (sy_buf sy) (pg_hdr og + 26) /\
pg_body_len og = zsum (zslice (pg_hdr og + 27) (znth (sy_buf sy) (pg_hdr og + 26)) (sy_buf sy)) /\
pg_hdr og + pg_header_len og + pg_body_len og <= sy_fill sy /\ sy_fill sy <= zlength (sy_buf sy) /\
0 <= pg_body_len og.

Lemma sync_fail_shape : forall (syh : sync_st ptr) ret bytes r og sy',
1 <= bytes -> ret + bytes = sy_fill syh ->
sync_fail syh ret bytes = ((r, og), sy') -> r < 0 /\ og = None /\ sy_headerbytes sy' = 0.
Proof.
intros syh ret bytes r og sy' Hb Hf E. unfold sync_fail in E.
destruct (find_byte CHAR_O _ _) as [j|] eqn:F; inversion E; subst; cbn.
- apply find_byte_range in F. repeat split; lia.
- repeat split; lia.
Qed.

Lemma ogg_sync_pageseek_inv2 : forall sy r og sy',
sync_inv2 sy -> ogg_sync_pageseek sy = ((r, og), sy') ->
sync_inv2 sy' /\
match og with
| Some pg => 0 < r /\ page_ok sy' pg
| None => r <= 0
end.
Proof.
intros sy r og sy' [Hinv Hhdr] E.
pose proof (ogg_sync_pageseek_inv sy r og sy' Hinv E) as (Hinv' & Hf & Hb & Hd & Hs & Hneg & Hpos).
unfold ogg_sync_pageseek in E.
destruct (ogg_sync_check sy) eqn:Hck.
{ inversion E; subst. split; [split; assumption| lia]. }

set (sy0 := mkSync (sy_data sy) (sy_buf sy) (sy_storage sy) (sy_fill sy) (sy_returned sy) (sy_unsynced sy)
(znth (sy_buf sy) (sy_returned sy + 26) + 27)
(sy_bodybytes sy + zsum (zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) (sy_buf sy)))) in E.
assert (TAIL : forall (crc_ok : bool) (syh : sync_st ptr),
sy_data syh = sy_data sy -> sy_buf syh = sy_buf sy -> sy_storage syh = sy_storage sy ->
sy_fill syh = sy_fill sy -> sy_returned syh = sy_returned sy -> sy_unsynced syh = sy_unsynced sy ->
sy_headerbytes syh = 27 + znth (sy_buf sy) (sy_returned sy + 26) ->
sy_bodybytes syh = zsum (zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) (sy_buf sy)) ->
sy_returned sy + sy_headerbytes syh <= sy_fill sy ->
(if sy_fill sy - sy_returned sy <? sy_bodybytes syh + sy_headerbytes syh then (0, None, syh)
else if negb crc_ok
then sync_fail syh (sy_returned sy) (sy_fill sy - sy_returned sy)
else (sy_headerbytes syh + sy_bodybytes syh,
Some {| pg_hdr := sy_returned sy; pg_header_len := sy_headerbytes syh; pg_body_len := sy_bodybytes syh |},
{| sy_data := sy_data syh; sy_buf := sy_buf sy; sy_storage := sy_storage syh; sy_fill := sy_fill syh;
sy_returned := sy_returned sy + (sy_headerbytes syh + sy_bodybytes syh);
sy_unsynced := 0; sy_headerbytes := 0; sy_bodybytes := 0 |})) = (r, og, sy') ->
sync_hdr sy' /\ match og with Some pg => 0 < r /\ page_ok sy' pg | None => r <= 0 end).
{ intros crc_ok syh Hd0 Hb0 Hs0 Hf0 Hr0 Hu0 Hh0 Hbb0 Hfit E0.
assert (Hnseg : 0 <= znth (sy_buf sy) (sy_returned sy + 26)) by (apply znth_bytes_ok; unfold sync_inv in Hinv; tauto).
assert (Hbb : 0 <= sy_bodybytes syh).
{ rewrite Hbb0. apply zsum_bytes_nonneg. apply bytes_ok_zslice. unfold sync_inv in Hinv; tauto. }
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (sy_bodybytes syh + sy_headerbytes syh)).
- inversion E0; subst. split; [|lia]. unfold sync_hdr. rewrite Hb0, Hr0, Hf0. split; [intros HH; lia|]. intros _. repeat split; assumption.
- destruct crc_ok; cbn [negb] in E0.
+ inversion E0; subst. split. { unfold sync_hdr; cbn. split; [reflexivity|]. intros HH. exfalso. apply HH. reflexivity. }
cbn. split. { lia. } unfold page_ok; cbn. unfold sync_inv in Hinv. rewrite Hf0. repeat split; try lia; match goal with |- ?g => idtac g end.
+ pose proof (sync_fail_shape syh (sy_returned sy) (sy_fill sy - sy_returned sy) _ _ _ ltac:(lia) ltac:(rewrite Hf0; lia) E0) as (R1 & -> & R3).
split; [| lia]. pose proof E0 as E1. unfold sync_fail in E1. destruct (find_byte _ _ _); inversion E1; subst;
unfold sync_hdr; cbn; split; intros; auto; congruence. }
destruct (sy_headerbytes sy =? 0) eqn:Hhb0.
- destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) 27).
{ inversion E; subst. split; [split; assumption| lia]. }
destruct (negb (list_eqb _ OGGS_MAGIC)).
{ pose proof (sync_fail_shape sy (sy_returned sy) (sy_fill sy - sy_returned sy) _ _ _ ltac:(lia) ltac:(lia) E) as (R1 & -> & R3).
split; [| lia]. split; [assumption|]. pose proof E as E1. unfold sync_fail in E1. destruct (find_byte _ _ _); inversion E1; subst;
unfold sync_hdr; cbn; split; intros; auto; congruence. }
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (znth (sy_buf sy) (sy_returned sy + 26) + 27)).
{ inversion E; subst. split; [split; [assumption| exact Hhdr]| lia]. }
apply Z.eqb_eq in Hhb0. destruct Hhdr as [Hz _]. specialize (Hz Hhb0).
destruct (TAIL _ sy0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; rewrite Hz; lia) ltac:(cbn; lia) E) as [H1 H2].
split; [split; assumption| exact H2].
- apply Z.eqb_neq in Hhb0. destruct Hhdr as [_ Hnz]. destruct (Hnz Hhb0) as (A & B & C).
destruct (TAIL _ sy eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl A C B E) as [H1 H2].
split; [split; assumption| exact H2].
Qed.

Lemma pageout_loop_inv2 : forall fuel sy r og sy',
sync_inv2 sy -> pageout_loop fuel sy = Some ((r, og), sy') ->
sync_inv2 sy' /\ match og with Some pg => r = 1 /\ page_ok sy' pg | None => r <> 1 end.
Proof.
induction fuel as [|fuel IH]; intros sy r og sy' Hinv E; [discriminate|].
cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1] eqn:E1.
pose proof (ogg_sync_pageseek_inv2 sy r1 og1 sy1 Hinv E1) as [Hinv1 Hog].
destruct (Z.ltb_spec 0 r1).
{ inversion E; subst. split; [exact Hinv1|]. destruct og; [split; [reflexivity| tauto]| lia]. }
destruct (Z.eqb_spec r1 0).
{ inversion E; subst. split; [exact Hinv1|]. destruct og1; [lia| cbn; lia]. }
destruct (sy_unsynced sy1 =? 0).
{ inversion E; subst. destruct og1; [destruct Hog; lia|]. split; [| cbn; lia].
destruct Hinv1 as [[A B] C]. unfold sync_inv2, sync_inv, sync_hdr in *; cbn in *. tauto. }
apply (IH sy1); assumption.
Qed.

Theorem ogg_sync_pageout_inv2 : forall sy r og sy',
sync_inv2 sy -> ogg_sync_pageout sy = Some ((r, og), sy') ->
sync_inv2 sy' /\ match og with Some pg => r = 1 /\ page_ok sy' pg | None => r <> 1 end.
Proof.
intros sy r og sy' Hinv E. unfold ogg_sync_pageout in E.
destruct (ogg_sync_check sy). { inversion E; subst. split; [exact Hinv| cbn; lia]. }
eapply pageout_loop_inv2; eauto.
Qed.

Lemma zslice_zslice : forall a n b m l, 0 <= a -> 0 <= b -> 0 <= m -> b + m <= n ->
zslice b m (zslice a n l) = zslice (a + b) m l.
Proof.
intros a n b m l Ha Hb Hm Hle. unfold zslice, ztake, zdrop.

rewrite skipn_firstn_comm. rewrite firstn_firstn.
replace (Init.Nat.min (Z.to_nat m) (Z.to_nat n - Z.to_nat b)) with (Z.to_nat m) by lia.
rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma znth_zslice : forall off len l i, 0 <= off -> 0 <= i < len -> znth (zslice off len l) i = znth l (off + i).
Proof.
intros. unfold zslice. rewrite znth_ztake by lia. rewrite znth_zdrop by lia. reflexivity.
Qed.

Lemma page_ok_pagein_pre : forall sy og, sync_inv sy -> page_ok sy og ->
let hdr := page_header sy og in let body := page_body sy og in
Forall (fun v => 0 <= v < 256) (lacing_of hdr) /\ 0 <= znth hdr 26 /\
zsum (lacing_of hdr) <= zlength body /\ zlength body = pg_body_len og /\ zlength hdr = pg_header_len og /\
Forall (fun v => 0 <= v < 256) hdr /\ Forall (fun v => 0 <= v < 256) body.
Proof.
intros sy og Hinv (P0 & P1 & P2 & P3 & P4 & P5 & P6). cbv zeta.
assert (HB : bytes_ok (sy_buf sy)) by (unfold sync_inv in Hinv; tauto).
unfold page_header, page_body, lacing_of.
assert (Hn26 : znth (zslice (pg_hdr og) (pg_header_len og) (sy_buf sy)) 26 = znth (sy_buf sy) (pg_hdr og + 26)).
{ apply znth_zslice; lia. }
rewrite Hn26.
rewrite zslice_zslice by lia.
repeat split.
- apply bytes_ok_zslice. exact HB.
- apply znth_bytes_ok. exact HB.
- rewrite <- P3. rewrite zlength_zslice; lia.
- rewrite zlength_zslice; lia.
- rewrite zlength_zslice; lia.
- apply bytes_ok_zslice. exact HB.
- apply bytes_ok_zslice. exact HB.
Qed.

Lemma ogg_sync_init_inv2 : sync_inv2 (ogg_sync_init (ptr:=ptr)).
Proof. split; [apply ogg_sync_init_inv|]. unfold sync_hdr, ogg_sync_init; cbn. split; intros; [reflexivity| congruence]. Qed.

Lemma znth_app_ztake_l : forall n (l bytes : list Z) i, 0 <= i < n -> n <= zlength l -> znth (ztake n l ++ bytes) i = znth l i.
Proof. intros. rewrite znth_app_l by (rewrite zlength_ztake; lia). apply znth_ztake. lia. Qed.

Lemma zslice_app_ztake_l : forall n (l bytes : list Z) off len, 0 <= off -> 0 <= len -> off + len <= n -> n <= zlength l ->
zslice off len (ztake n l ++ bytes) = zslice off len l.
Proof.
intros. unfold zslice, ztake, zdrop.
rewrite skipn_app. rewrite length_firstn. unfold zlength in *.
replace (Z.to_nat off - Nat.min (Z.to_nat n) (length l))%nat with 0%nat by lia. cbn [skipn].
rewrite firstn_app. rewrite length_skipn, length_firstn.
replace (Z.to_nat len - (Nat.min (Z.to_nat n) (length l) - Z.to_nat off))%nat with 0%nat by lia.
rewrite firstn_O, app_nil_r. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma sync_write_inv2 : forall sy bytes, sync_inv2 sy -> bytes_ok bytes -> sync_inv2 (sync_write sy (sy_fill sy) bytes).
Proof.
intros sy bytes [Hinv Hhdr] Hb. split; [apply sync_write_inv; assumption|].
destruct Hinv as (A & B & C & D & E). destruct Hhdr as [Hz Hnz].
unfold sync_hdr, sync_write; cbn. split; [exact Hz|]. intros Hne. destruct (Hnz Hne) as (R1 & R2 & R3).
assert (Hn : 0 <= znth (sy_buf sy) (sy_returned sy + 26)) by (apply znth_bytes_ok; exact E).
rewrite znth_app_ztake_l by lia. rewrite zslice_app_ztake_l by lia. repeat split; assumption.
Qed.

Lemma ogg_sync_wrote_inv2 : forall sy n r sy', sync_inv2 sy -> 0 <= n -> sy_fill sy + n <= zlength (sy_buf sy) ->
ogg_sync_wrote sy n = (r, sy') -> sync_inv2 sy'.
Proof.
intros sy n r sy' [Hinv Hhdr] Hn Hlen Ew.
pose proof (ogg_sync_wrote_inv sy n r sy' Hinv Hn Hlen Ew) as (I1 & Hb & Hf0 & Hf1 & Hr & Hs & Hd).
split; [exact I1|].
unfold ogg_sync_wrote in Ew. destruct (ogg_sync_check sy); [inversion Ew; subst; exact Hhdr|].
destruct (sy_storage sy <? sy_fill sy + n); inversion Ew; subst; [exact Hhdr|].
destruct Hhdr as [Hz Hnz]. unfold sync_hdr; cbn. split; [exact Hz|]. intros Hne. destruct (Hnz Hne) as (R1 & R2 & R3).
repeat split; try assumption. lia.
Qed.

Lemma sync_compact_inv2 : forall sy, sync_inv2 sy ->
let fill := sy_fill sy - sy_returned sy in
sync_inv2 (mkSync (sy_data sy) (ztake fill (zdrop (sy_returned sy) (sy_buf sy))) (sy_storage sy) fill 0
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
Proof.
intros sy [Hinv Hhdr]. cbn. split; [apply (sync_compact_inv sy Hinv)|].
destruct Hinv as (A & B & C & D & E). destruct Hhdr as [Hz Hnz].
unfold sync_hdr; cbn. split; [exact Hz|]. intros Hne. destruct (Hnz Hne) as (R1 & R2 & R3).
assert (Hn : 0 <= znth (sy_buf sy) (sy_returned sy + 26)) by (apply znth_bytes_ok; exact E).
assert (E26 : znth (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy))) (0 + 26) = znth (sy_buf sy) (sy_returned sy + 26)).
{ rewrite znth_ztake by lia. rewrite znth_zdrop by lia. reflexivity. }
rewrite E26.
assert (ES : zslice (0 + 27) (znth (sy_buf sy) (sy_returned sy + 26)) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
= zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) (sy_buf sy)).
{ change (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy))) with (zslice (sy_returned sy) (sy_fill sy - sy_returned sy) (sy_buf sy)).
rewrite zslice_zslice by lia. reflexivity. }
rewrite ES. repeat split; try assumption. lia.
Qed.
End OggFacts.
