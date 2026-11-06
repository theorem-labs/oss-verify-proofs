(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode. The decoder half of the agreement between the library models (DgnLib.v) and the
   harness's checks (DgnDecHarness.v): no check of the decoder loop of fuzz/fuzz_decode.c (:324-339) aborts, for every body
   of bytes, every length and every personality.
   - the field lemmas (note_ok, sysex_ok, fader_ok, jog_ok, vpot_ok, cc_other_ok, other_ok): for a message the grammar
     gives (spec_msg_step, code 1), the event decode_note / decode_sysex / the control-change branches of
     diginet_decoder_next make (diginet_decode.c:20-35, :37-105, :130-157) passes the message and kind tests of
     check_events_step (fuzz_decode.c:171-173, :183) and every test of check_events_fields (:187-263) against the
     event spec_event_of gives;
   - the fader pairing (fader_lookahead): the LSB lookahead through the peek cursor (diginet_decode.c:135-142) tests
     what owed_at tests (fuzz_decode.c:141-149), reads the same LSB, and leaves the peek cursor where owed_at's next
     step starts;
   - decoder_step_ok: one pass of the loop, from a decoder whose cursor stands where owed_at's step starts;
   - dgn_events_loop_ok, dgn_events_loop_ok_desk: the whole loop, from diginet_decoder_init.
   The cursor fact every step rests on is DgnAgreeCursor.diginet_msg_next_step. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness DgnAgreeCursor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- tactics ---- *)

Ltac zbool :=
  cbv beta;
  repeat match goal with
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  end; cbn [andb orb]; try reflexivity; try lia.

Ltac destr_ifs :=
  repeat match goal with
  | |- context [if ?c then _ else _] =>
      lazymatch c with true => fail | false => fail | _ => destruct c eqn:? end
  end.

Ltac unfold_consts :=
  cbv [SPEC_EV_FADER SPEC_EV_TOUCH SPEC_EV_STRIP_BUTTON SPEC_EV_SECTION_BUTTON SPEC_EV_VPOT SPEC_EV_JOG
       SPEC_EV_RING SPEC_EV_METER SPEC_EV_STRIP_LEDS SPEC_EV_SCRIBBLE SPEC_EV_COUNTER SPEC_EV_SYSTEM SPEC_EV_OTHER
       DIGINET_EV_FADER DIGINET_EV_TOUCH DIGINET_EV_STRIP_BUTTON DIGINET_EV_SECTION_BUTTON DIGINET_EV_VPOT
       DIGINET_EV_JOG DIGINET_EV_RING DIGINET_EV_METER DIGINET_EV_STRIP_LEDS DIGINET_EV_SCRIBBLE
       DIGINET_EV_COUNTER DIGINET_EV_SYSTEM DIGINET_EV_OTHER
       SPEC_MAKER SPEC_FN_RING SPEC_FN_METER SPEC_FN_LEDS SPEC_FN_COUNTER SPEC_FN_SCRIBBLE SPEC_FN_SYSTEM
       DIGINET_SYSEX_MAKER DIGINET_FN_RING DIGINET_FN_METER DIGINET_FN_LEDS DIGINET_FN_COUNTER
       DIGINET_FN_SCRIBBLE DIGINET_FN_SYSTEM SPEC_CHARS_MAX DIGINET_SCRIBBLE_MAX SPEC_DIGITS
       DIGINET_COUNTER_DIGITS SPEC_BTN_TOUCH DIGINET_BTN_TOUCH SPEC_ZONE_FIRST SPEC_ZONE_LAST
       DIGINET_ZONE_FIRST DIGINET_ZONE_LAST SPEC_JOG_CC DIGINET_JOG_CC SPEC_VPOTS].

Ltac ev_simpl :=
  cbn [de_set_kind de_set_strip de_set_button de_set_zone de_set_on de_set_right de_set_addr
       de_set_lsb_missing de_set_value de_set_delta de_set_mask de_set_segments de_set_len
       de_set_text de_set_seg de_set_dots de_set_device de_set_msg
       de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value de_delta
       de_mask de_segments de_len de_text de_seg de_dots de_device de_msg
       se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len se_dots se_value
       se_mask se_delta se_segments se_text se_seg
       ow_m ow_e ow_lsb_missing ow_next ow_status_out
       dgn_event_zero se_other se_with_value].

Ltac fin_ev :=
  repeat progress (unfold_consts; ev_simpl; rewrite ?Z.eqb_refl, ?implb_true_r;
                   cbn [Z.eqb Pos.eqb andb orb implb negb]);
  try reflexivity.

(* ---- bytes ---- *)

Lemma in_zseq : forall n x, 0 <= x < Z.of_nat n -> In x (zseq n).
Proof.
  intros n x Hx. unfold zseq. apply in_map_iff. exists (Z.to_nat x). split.
  - apply Z2Nat.id. lia.
  - apply in_seq. lia.
Qed.

Lemma zseq_in : forall n x, In x (zseq n) -> 0 <= x < Z.of_nat n.
Proof.
  intros n x Hx. unfold zseq in Hx. apply in_map_iff in Hx as [k [<- Hk]].
  apply in_seq in Hk. lia.
Qed.

Lemma byte_forall2 : forall (P : Z -> Z -> bool),
  forallb (fun x => forallb (P x) (zseq 256)) (zseq 256) = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> P x y = true.
Proof.
  intros P H x y Hx Hy.
  exact (byte_forall_zseq (P x) (byte_forall_zseq (fun x => forallb (P x) (zseq 256)) H x Hx) y Hy).
Qed.

Lemma u8_small : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.

(* the bit reads of decode_note and decode_sysex against spec.h's, over one byte *)
Lemma u8_land63 : forall x, 0 <= x < 256 -> u8 (Z.land x 63) = Z.land x 63.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall_zseq (fun x => u8 (Z.land x 63) =? Z.land x 63) ltac:(vm_compute; reflexivity) x Hx).
Qed.

Lemma u8_land31 : forall x, 0 <= x < 256 -> u8 (Z.land x 31) = Z.land x 31.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall_zseq (fun x => u8 (Z.land x 31) =? Z.land x 31) ltac:(vm_compute; reflexivity) x Hx).
Qed.

Lemma bit6 : forall x, 0 <= x < 256 ->
  u8 (int_of_bool (negb (Z.land x 64 =? 0))) = Z.land (Z.shiftr x 6) 1.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall_zseq (fun x => u8 (int_of_bool (negb (Z.land x 64 =? 0))) =? Z.land (Z.shiftr x 6) 1)
           ltac:(vm_compute; reflexivity) x Hx).
Qed.

Lemma bit5 : forall x, 0 <= x < 256 ->
  u8 (int_of_bool (negb (Z.land x 32 =? 0))) = Z.land (Z.shiftr x 5) 1.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall_zseq (fun x => u8 (int_of_bool (negb (Z.land x 32 =? 0))) =? Z.land (Z.shiftr x 5) 1)
           ltac:(vm_compute; reflexivity) x Hx).
Qed.

Lemma ring_bit6 : forall x, 0 <= x < 256 ->
  Z.land (Z.shiftr x 6) 1 = if negb (Z.land x 64 =? 0) then 1 else 0.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (byte_forall_zseq (fun x => Z.land (Z.shiftr x 6) 1 =? (if negb (Z.land x 64 =? 0) then 1 else 0))
           ltac:(vm_compute; reflexivity) x Hx).
Qed.

(* ---- the ring's LEDs and the meter's segments, checked over every pair of bytes ---- *)

(* diginet_decode.c:55-61 against spec.h:445-451, from LED 1's bit q *)
Definition ring_check (q p1 p2 : Z) : bool :=
  ring_loop (u16 q) p1 p2 0 7 =? fold_left (ring_step p1 p2) (map (fun k => k + 2) (zseq 14)) q.

Lemma ring_table0 : forallb (fun x => forallb (ring_check 0 x) (zseq 256)) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ring_table1 : forallb (fun x => forallb (ring_check 1 x) (zseq 256)) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ring_agrees : forall p0 p1 p2, 0 <= p0 < 256 -> 0 <= p1 < 256 -> 0 <= p2 < 256 ->
  ring_loop (u16 (if negb (Z.land p0 64 =? 0) then 1 else 0)) p1 p2 0 7 = ring_mask p0 p1 p2.
Proof.
  intros p0 p1 p2 H0 H1 H2. unfold ring_mask. rewrite (ring_bit6 p0 H0).
  apply Z.eqb_eq. destruct (negb (Z.land p0 64 =? 0)).
  - exact (byte_forall2 (ring_check 1) ring_table1 p1 p2 H1 H2).
  - exact (byte_forall2 (ring_check 0) ring_table0 p1 p2 H1 H2).
Qed.

(* diginet_codec.c:209-215 against spec.h:372-378 on the mask of diginet_decode.c:70 / spec.h:462 *)
Definition meter_check (p1 p2 : Z) : bool :=
  diginet_meter_segments (u16 (Z.lor (Z.shiftl (Z.land p1 127) 7) (Z.land p2 127))) =?
  spec_segments (u16 (Z.lor (Z.shiftl (Z.land p1 127) 7) (Z.land p2 127))).

Lemma meter_table : forallb (fun x => forallb (meter_check x) (zseq 256)) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma meter_agrees : forall p1 p2, 0 <= p1 < 256 -> 0 <= p2 < 256 ->
  diginet_meter_segments (u16 (Z.lor (Z.shiftl (Z.land p1 127) 7) (Z.land p2 127))) =
  spec_segments (u16 (Z.lor (Z.shiftl (Z.land p1 127) 7) (Z.land p2 127))).
Proof.
  intros p1 p2 H1 H2. apply Z.eqb_eq. exact (byte_forall2 meter_check meter_table p1 p2 H1 H2).
Qed.

(* ---- the scribble's text and the counter's digits ---- *)

Lemma length_list_set : forall l i v, length (list_set l i v) = length l.
Proof.
  induction l as [|x t IH]; intros i v; [reflexivity|].
  destruct i; cbn [list_set length]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma nth_list_set_eq : forall l i v d, (i < length l)%nat -> nth i (list_set l i v) d = v.
Proof.
  induction l as [|x t IH]; intros i v d H; cbn [length] in H; [lia|].
  destruct i as [|j]; cbn [list_set nth]; [reflexivity | apply IH; lia].
Qed.

Lemma nth_list_set_ne : forall l i v j d, i <> j -> nth j (list_set l i v) d = nth j l d.
Proof.
  induction l as [|x t IH]; intros [|i] v [|j] d H; cbn [list_set nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma length_copy_text : forall fuel text b src i, length (copy_text text b src i fuel) = length text.
Proof.
  induction fuel as [|f IH]; intros text b src i; cbn [copy_text]; [reflexivity|].
  rewrite IH, length_list_set. reflexivity.
Qed.

Lemma nth_copy_text : forall fuel text b src i j,
  0 <= i -> 0 <= j -> (Z.to_nat j < length text)%nat ->
  nth (Z.to_nat j) (copy_text text b src i fuel) 0 =
  if (i <=? j) && (j <? i + Z.of_nat fuel) then byte_at b (src + j) else nth (Z.to_nat j) text 0.
Proof.
  induction fuel as [|f IH]; intros text b src i j Hi Hj Hl; cbn [copy_text].
  - zbool.
  - rewrite IH by (rewrite ?length_list_set; lia).
    destruct (Z.eq_dec j i) as [-> | Hne].
    + rewrite nth_list_set_eq by lia. zbool.
    + rewrite nth_list_set_ne by lia. zbool.
Qed.

Lemma nth_counter_loop : forall fuel seg b pl k j,
  0 <= k -> k + Z.of_nat fuel <= 8 -> 0 <= j -> (Z.to_nat j < length seg)%nat ->
  nth (Z.to_nat j) (counter_loop seg b pl k fuel) 0 =
  if (8 - k - Z.of_nat fuel <=? j) && (j <=? 7 - k) then byte_at b (pl + 2 + (7 - j))
  else nth (Z.to_nat j) seg 0.
Proof.
  induction fuel as [|f IH]; intros seg b pl k j Hk Hf Hj Hl; cbn [counter_loop].
  - zbool.
  - rewrite IH by (rewrite ?length_list_set; lia).
    unfold DIGINET_COUNTER_DIGITS.
    destruct (Z.eq_dec j (7 - k)) as [-> | Hne].
    + replace (8 - 1 - k) with (7 - k) by lia.
      rewrite nth_list_set_eq by lia.
      replace (7 - (7 - k)) with k by lia. zbool.
    + rewrite nth_list_set_ne by lia. zbool.
Qed.

Lemma bytes_eq_intro : forall n x y, (forall k, 0 <= k < n -> byte_at x k = byte_at y k) ->
  bytes_eq n x y = true.
Proof.
  intros n x y H. unfold bytes_eq. apply forallb_forall. intros k Hk.
  apply zseq_in in Hk. apply Z.eqb_eq. apply H. lia.
Qed.

Lemma nth_map_seq0 : forall (g : nat -> Z) n j, (j < n)%nat -> nth j (map g (seq 0 n)) 0 = g j.
Proof.
  intros g n j H. rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma byte_at_map_zseq : forall f n k, 0 <= k < Z.of_nat n -> byte_at (map f (zseq n)) k = f k.
Proof.
  intros f n k Hk. unfold byte_at, zseq. rewrite map_map.
  rewrite (nth_map_seq0 (fun x => f (Z.of_nat x))) by lia. cbv beta. f_equal. lia.
Qed.

(* diginet_decode.c:86-88 against spec.h:480-481: the first l characters, and the NUL after them *)
Lemma scribble_text_eq : forall b src l text, 1 <= l <= 8 -> length text = 9%nat ->
  bytes_eq l (list_set (copy_text text b src 0 (Z.to_nat l)) (Z.to_nat l) 0)
    (map (fun k => if k <? l then byte_at b (src + k) else 0) (zseq 8)) = true.
Proof.
  intros b src l text Hl Ht. apply bytes_eq_intro. intros k Hk.
  rewrite byte_at_map_zseq by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  unfold byte_at at 1. rewrite nth_list_set_ne by lia.
  rewrite nth_copy_text by (try rewrite Ht; lia).
  rewrite Z2Nat.id by lia. zbool.
Qed.

Lemma scribble_text_nul : forall b src l text, 0 <= l <= 8 -> length text = 9%nat ->
  byte_at (list_set (copy_text text b src 0 (Z.to_nat l)) (Z.to_nat l) 0) l = 0.
Proof.
  intros b src l text Hl Ht. unfold byte_at. apply nth_list_set_eq.
  rewrite length_copy_text, Ht. lia.
Qed.

(* diginet_decode.c:96-97 against spec.h:491 *)
Lemma counter_seg_eq : forall b pl seg, length seg = 8%nat ->
  bytes_eq 8 (counter_loop seg b pl 0 8) (map (fun k => byte_at b (pl + 2 + 8 - 1 - k)) (zseq 8)) = true.
Proof.
  intros b pl seg Hs. apply bytes_eq_intro. intros k Hk.
  rewrite byte_at_map_zseq by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  unfold byte_at at 1. rewrite nth_counter_loop by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  zbool. f_equal. lia.
Qed.

(* ---- the message the cursor hands the decoder ---- *)

(* what the decoder reads of the library's message: its status, data bytes and payload, and the place, length
   and running flag check_events_step compares (fuzz_decode.c:171-173) *)
Definition msg_fits (m : spec_msg) (msg : dgn_msg) : Prop :=
  dm_status msg = sm_status m /\ dm_d1 msg = sm_d1 m /\ dm_d2 msg = sm_d2 m /\
  dm_sysex msg = sm_sysex_at m /\ dm_sysex_len msg = sm_sysex_len m /\ msg_agrees m msg = true.

Lemma msg_fits_step : forall m, msg_fits m (msg_of_step m).
Proof.
  intros m. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (msg_agrees_of_step m)))))).
Qed.

Lemma spec_msg_step_d2 : forall b len pos status, Forall (fun x => 0 <= x < 256) b ->
  0 <= sm_d2 (spec_msg_step b len pos status) < 256.
Proof.
  intros b len pos status Hb. unfold spec_msg_step. cbv zeta.
  destr_ifs; cbn [sm_d2]; first [lia | apply byte_at_range; exact Hb].
Qed.

(* ---- the field lemmas ---- *)

(* the event the decoder starts from once diginet_msg_next returned 1 (diginet_decode.c:115-117) *)
Definition ev0 (msg : dgn_msg) : dgn_event := de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero).

(* the message and kind tests of check_events_step (fuzz_decode.c:171-173, :183) and check_events_fields *)
Definition event_ok (b : list Z) (o : owed) (ev : dgn_event) : bool :=
  (msg_agrees (ow_m o) (de_msg ev) && (de_kind ev =? se_kind (ow_e o))) && check_events_fields_ok b o ev.

(* a key, a touch or a zone key (diginet_decode.c:20-35; spec.h:397-411) *)
Lemma note_ok : forall b m msg n s, msg_fits m msg -> 0 <= sm_d2 m < 256 ->
  Z.land (sm_status m) 240 = 144 ->
  event_ok b (Owed m (spec_event_of b m) 0 n s) (decode_note msg (ev0 msg)) = true.
Proof.
  intros b m msg n s (_ & Hd1 & Hd2 & _ & _ & Hag) Hr Hf.
  assert (Hne : (sm_status m =? 240) = false).
  { apply Z.eqb_neq. intros E. rewrite E in Hf. cbn in Hf. discriminate Hf. }
  unfold event_ok, spec_event_of, decode_note, ev0. cbv zeta.
  rewrite Hf, Hd1, Hd2, (u8_land63 _ Hr), (bit6 _ Hr).
  unfold_consts. cbn [Z.eqb Pos.eqb].
  destruct ((24 <=? Z.land (sm_d2 m) 63) && (Z.land (sm_d2 m) 63 <=? 29));
    [| destruct (sm_d1 m =? 9)];
    unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, Hne; fin_ev.
Qed.

(* every sysex: F0 13 and its function, or OTHER (diginet_decode.c:37-105; spec.h:428-499) *)
Lemma sysex_ok : forall b m msg n s, Forall (fun x => 0 <= x < 256) b -> msg_fits m msg ->
  sm_status m = 240 ->
  event_ok b (Owed m (spec_event_of b m) 0 n s) (decode_sysex b msg (ev0 msg)) = true.
Proof.
  intros b m msg n s Hb (_ & _ & _ & Hsx & Hsl & Hag) Hs.
  assert (Hf1 : (Z.land (sm_status m) 240 =? 144) = false) by (rewrite Hs; reflexivity).
  assert (Hf2 : (Z.land (sm_status m) 240 =? 176) = false) by (rewrite Hs; reflexivity).
  assert (Hf3 : (sm_status m =? 240) = true) by (rewrite Hs; reflexivity).
  unfold event_ok, spec_event_of, decode_sysex, ev0. cbv zeta.
  rewrite Hf1, Hf2, Hf3, Hsx, Hsl. cbn [negb].
  rewrite ?u8_land63, ?u8_land31, ?bit5, ?ring_agrees, ?meter_agrees by (apply byte_at_range; exact Hb).
  unfold_consts. destr_ifs;
    unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, Hf3;
    try (match goal with
         | E : ((?pn <? 3) || (8 <? ?pn - 2)) = false |- _ =>
             apply orb_false_iff in E as [E1 E2]; apply Z.ltb_ge in E1; apply Z.ltb_ge in E2;
             rewrite (u8_small (pn - 2)) by lia;
             rewrite scribble_text_eq, scribble_text_nul by (reflexivity || lia)
         end);
    try (rewrite counter_seg_eq by reflexivity);
    fin_ev.
Qed.

(* a fader, with or without its LSB (diginet_decode.c:130-145; fuzz_decode.c:136-149), over any event whose
   fields are the fader's *)
Lemma fader_ok : forall b m e lm n s ev,
  msg_agrees m (de_msg ev) = true -> (sm_status m =? 240) = false ->
  se_kind e = SPEC_EV_FADER -> de_kind ev = DIGINET_EV_FADER ->
  de_strip ev = se_strip e -> de_value ev = se_value e -> de_lsb_missing ev = lm ->
  event_ok b (Owed m e lm n s) ev = true.
Proof.
  intros b m e lm n s ev Ha Hs Hk Hk' Hst Hv Hl.
  unfold event_ok, check_events_fields_ok. cbv zeta. cbn [ow_m ow_e ow_lsb_missing].
  rewrite Ha, Hs, Hk, Hk', Hst, Hv, Hl. fin_ev.
Qed.

Lemma cc_status : forall m, (Z.land (sm_status m) 240 =? 176) = true -> (sm_status m =? 240) = false.
Proof.
  intros m H. apply Z.eqb_neq. intros E. rewrite E in H. cbn in H. discriminate H.
Qed.

(* the jog (diginet_decode.c:146-150; spec.h:419-421) *)
Lemma jog_ok : forall b m msg n s, msg_fits m msg ->
  (Z.land (sm_status m) 240 =? 144) = false -> (Z.land (sm_status m) 240 =? 176) = true ->
  (sm_d1 m <? 32) = false -> (sm_d1 m =? 92) = true ->
  event_ok b (Owed m (spec_event_of b m) 0 n s)
    (de_set_delta (s16 (dm_d2 msg - 64)) (de_set_kind DIGINET_EV_JOG (ev0 msg))) = true.
Proof.
  intros b m msg n s (_ & _ & Hd2 & _ & _ & Hag) H1 H2 H3 H4.
  pose proof (cc_status m H2) as H5.
  unfold event_ok, spec_event_of, ev0. cbv zeta. unfold_consts. rewrite H1, H2, H3, H4, Hd2.
  unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, H5; fin_ev.
Qed.

(* a V-Pot (diginet_decode.c:151-156; spec.h:422-425) *)
Lemma vpot_ok : forall b m msg n s, msg_fits m msg ->
  (Z.land (sm_status m) 240 =? 144) = false -> (Z.land (sm_status m) 240 =? 176) = true ->
  (sm_d1 m <? 32) = false -> (sm_d1 m =? 92) = false ->
  ((64 <=? sm_d1 m) && (sm_d1 m <? 64 + 24)) = true ->
  event_ok b (Owed m (spec_event_of b m) 0 n s)
    (de_set_delta (s16 (dm_d2 msg - 64)) (de_set_strip (u8 (dm_d1 msg - 64)) (de_set_kind DIGINET_EV_VPOT (ev0 msg))))
  = true.
Proof.
  intros b m msg n s (_ & Hd1 & Hd2 & _ & _ & Hag) H1 H2 H3 H4 H6.
  pose proof (cc_status m H2) as H5.
  unfold event_ok, spec_event_of, ev0. cbv zeta. unfold_consts. rewrite H1, H2, H3, H4, H6, Hd1, Hd2.
  unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, H5; fin_ev.
Qed.

(* any other control change (diginet_decode.c:157; spec.h:426) *)
Lemma cc_other_ok : forall b m msg n s, msg_fits m msg ->
  (Z.land (sm_status m) 240 =? 144) = false -> (Z.land (sm_status m) 240 =? 176) = true ->
  (sm_d1 m <? 32) = false -> (sm_d1 m =? 92) = false ->
  ((64 <=? sm_d1 m) && (sm_d1 m <? 64 + 24)) = false ->
  event_ok b (Owed m (spec_event_of b m) 0 n s) (ev0 msg) = true.
Proof.
  intros b m msg n s (_ & _ & _ & _ & _ & Hag) H1 H2 H3 H4 H6.
  pose proof (cc_status m H2) as H5.
  unfold event_ok, spec_event_of, ev0. cbv zeta. unfold_consts. rewrite H1, H2, H3, H4, H6.
  unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, H5; fin_ev.
Qed.

(* any other channel message (diginet_decode.c:127-128; spec.h:427) *)
Lemma other_ok : forall b m msg n s, msg_fits m msg ->
  (Z.land (sm_status m) 240 =? 144) = false -> (Z.land (sm_status m) 240 =? 176) = false ->
  (sm_status m =? 240) = false ->
  event_ok b (Owed m (spec_event_of b m) 0 n s) (ev0 msg) = true.
Proof.
  intros b m msg n s (_ & _ & _ & _ & _ & Hag) H1 H2 H3.
  unfold event_ok, spec_event_of, ev0. cbv zeta. rewrite H1, H2, H3. cbn [negb].
  unfold check_events_fields_ok; cbv zeta; ev_simpl; rewrite Hag, H3; fin_ev.
Qed.

(* ---- owed_at, case by case ---- *)

Lemma spec_kind_fader : forall b m, se_kind (spec_event_of b m) = SPEC_EV_FADER ->
  Z.land (sm_status m) 240 = 176 /\ sm_d1 m < 32.
Proof.
  intros b m. unfold spec_event_of, se_other. cbv zeta.
  destr_ifs; cbn [se_kind]; unfold_consts; intro K; try discriminate K.
  split; [apply Z.eqb_eq | apply Z.ltb_lt]; assumption.
Qed.

Lemma spec_event_fader : forall b m, Z.land (sm_status m) 240 = 176 -> sm_d1 m < 32 ->
  spec_event_of b m =
  {| se_kind := SPEC_EV_FADER; se_strip := sm_d1 m; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
     se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := u16 (Z.shiftl (sm_d2 m) 3);
     se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}.
Proof.
  intros b m Hf Hd. unfold spec_event_of. cbv zeta. rewrite Hf.
  replace (sm_d1 m <? 32) with true by (symmetry; apply Z.ltb_lt; exact Hd).
  reflexivity.
Qed.

Lemma owed_at_nomsg : forall b len pos status m, m = spec_msg_step b len pos status -> sm_code m <> 1 ->
  owed_at b len pos status = Owed m se_zero 0 (sm_next m) (sm_status_out m).
Proof.
  intros b len pos status m Em H. subst m. unfold owed_at. cbv zeta.
  replace (sm_code (spec_msg_step b len pos status) =? 1) with false
    by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma owed_at_event : forall b len pos status m, m = spec_msg_step b len pos status -> sm_code m = 1 ->
  se_kind (spec_event_of b m) <> SPEC_EV_FADER ->
  owed_at b len pos status = Owed m (spec_event_of b m) 0 (sm_next m) (sm_status_out m).
Proof.
  intros b len pos status m Em H1 H2. subst m. unfold owed_at. cbv zeta. rewrite H1.
  replace (se_kind (spec_event_of b (spec_msg_step b len pos status)) =? SPEC_EV_FADER) with false
    by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

Lemma owed_at_fader : forall b len pos status m ml, m = spec_msg_step b len pos status -> sm_code m = 1 ->
  se_kind (spec_event_of b m) = SPEC_EV_FADER -> ml = spec_msg_step b len (sm_next m) (sm_status_out m) ->
  owed_at b len pos status =
  if (sm_code ml =? 1) && (Z.land (sm_status ml) 240 =? 176) && (sm_d1 ml =? 32 + sm_d1 m) then
    Owed m (se_with_value (spec_event_of b m)
              (u16 (Z.lor (se_value (spec_event_of b m)) (u16 (Z.land (Z.shiftr (sm_d2 ml) 4) 7)))))
      0 (sm_next ml) (sm_status_out ml)
  else Owed m (spec_event_of b m) 1 (sm_next m) (sm_status_out m).
Proof.
  intros b len pos status m ml Em H1 H2 Eml. subst ml m. unfold owed_at. cbv zeta. rewrite H1, H2.
  reflexivity.
Qed.

(* The fader pairing: diginet_decoder_next's LSB test through the peek cursor (diginet_decode.c:135-138) is
   owed_at's (fuzz_decode.c:142-143), the LSB byte it reads (:139) is owed_at's (:144), and the peek cursor
   (:140) stands where owed_at's next step starts (:145-146). *)
Lemma fader_lookahead : forall b len m ml rl lsb peek,
  Forall (fun x => 0 <= x < 256) b ->
  ml = spec_msg_step b len (sm_next m) (sm_status_out m) ->
  diginet_msg_next b (DgnCursor len (sm_next m) (sm_status_out m)) dgn_msg_zero = (rl, lsb, peek) ->
  ((rl =? 1) && (Z.land (dm_status lsb) 240 =? 176) && (dm_d1 lsb =? 32 + sm_d1 m)) =
    ((sm_code ml =? 1) && (Z.land (sm_status ml) 240 =? 176) && (sm_d1 ml =? 32 + sm_d1 m)) /\
  rl = sm_code ml /\ (rl = 1 -> dm_d2 lsb = sm_d2 ml) /\
  peek = DgnCursor len (sm_next ml) (sm_status_out ml).
Proof.
  intros b len m ml rl lsb peek Hb Eml E.
  destruct (diginet_msg_next_step b len (sm_next m) (sm_status_out m) dgn_msg_zero rl lsb peek Hb E)
    as [Hr [Hc Hm]].
  rewrite <- Eml in Hr, Hc, Hm.
  split; [| split; [exact Hr | split; [intros H1; rewrite (Hm H1); reflexivity | exact Hc]]].
  destruct (Z.eq_dec rl 1) as [R1 | R1].
  - rewrite (Hm R1), <- Hr, R1. reflexivity.
  - rewrite <- Hr. replace (rl =? 1) with false by (symmetry; apply Z.eqb_neq; exact R1). reflexivity.
Qed.

(* ---- one pass of the decoder loop ---- *)

Lemma events_step_ok_msg : forall b o ev, sm_code (ow_m o) = 1 ->
  events_step_ok b (EventsStep o 1 ev) = event_ok b o ev.
Proof.
  intros b o ev H. unfold events_step_ok, check_events_step_ok, event_ok. cbn [es_o es_rd es_ev].
  rewrite H. reflexivity.
Qed.

Lemma events_step_ok_nomsg : forall b o rd ev, rd = sm_code (ow_m o) -> rd <> 1 ->
  events_step_ok b (EventsStep o rd ev) = true.
Proof.
  intros b o rd ev H1 H2. unfold events_step_ok, check_events_step_ok. cbn [es_o es_rd es_ev].
  rewrite <- H1, Z.eqb_refl. replace (rd =? 1) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

(* From a decoder whose cursor stands where owed_at's step starts, diginet_decoder_next returns that step's code,
   its event passes every check of the pass (fuzz_decode.c:332-334), and its cursor moves to where owed_at's next
   step starts (fuzz_decode.c:337-338). *)
Lemma decoder_step_ok : forall b d len pos status rd ev d',
  Forall (fun x => 0 <= x < 256) b ->
  dd_c d = DgnCursor len pos status ->
  diginet_decoder_next b d dgn_event_zero = (rd, ev, d') ->
  rd = sm_code (ow_m (owed_at b len pos status)) /\
  events_step_ok b (EventsStep (owed_at b len pos status) rd ev) = true /\
  dd_c d' = DgnCursor len (ow_next (owed_at b len pos status)) (ow_status_out (owed_at b len pos status)) /\
  dd_p d' = dd_p d.
Proof.
  intros b d len pos status rd ev d' Hb Hd H.
  unfold diginet_decoder_next in H. rewrite Hd in H. revert H.
  destruct (diginet_msg_next b (DgnCursor len pos status) dgn_msg_zero) as [[r msg] c1] eqn:E1.
  intros H. cbv beta iota zeta in H.
  destruct (diginet_msg_next_step b len pos status dgn_msg_zero r msg c1 Hb E1) as [Hr [Hc Hm]].
  remember (spec_msg_step b len pos status) as m eqn:Em.
  subst c1.
  destruct (Z.eq_dec r 1) as [R1 | R1].
  2: {
    replace (r =? 1) with false in H by (symmetry; apply Z.eqb_neq; exact R1).
    cbn [negb] in H. injection H as H1 H2 H3. subst rd ev d'.
    rewrite (owed_at_nomsg b len pos status m Em) by congruence.
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    apply events_step_ok_nomsg; cbn [ow_m]; [exact Hr | exact R1]. }
  rewrite R1 in Hr, Hm, H. specialize (Hm eq_refl). subst msg.
  assert (Hcode : sm_code m = 1) by (symmetry; exact Hr).
  rewrite Z.eqb_refl in H. cbn [negb] in H.
  assert (Hst : dm_status (msg_of_step m) = sm_status m) by reflexivity.
  assert (Hd1 : dm_d1 (msg_of_step m) = sm_d1 m) by reflexivity.
  rewrite Hst, Hd1 in H.
  revert H. destruct (Z.land (sm_status m) 240 =? 144) eqn:F144; intros H; cbn [negb] in H.
  { (* a key, a touch or a zone key *)
    injection H as H1 H2 H3. subst rd ev d'.
    rewrite (owed_at_event b len pos status m Em Hcode)
      by (intro K; apply spec_kind_fader in K as [K1 _]; apply Z.eqb_eq in F144; lia).
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    rewrite events_step_ok_msg by exact Hcode.
    apply (note_ok b m (msg_of_step m)); [apply msg_fits_step | | apply Z.eqb_eq; exact F144].
    rewrite Em. apply spec_msg_step_d2. exact Hb. }
  revert H. destruct (sm_status m =? 240) eqn:F240; intros H; cbn [negb] in H.
  { (* a sysex *)
    injection H as H1 H2 H3. subst rd ev d'.
    apply Z.eqb_eq in F240.
    rewrite (owed_at_event b len pos status m Em Hcode)
      by (intro K; apply spec_kind_fader in K as [K1 _]; rewrite F240 in K1; cbn in K1; discriminate K1).
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    rewrite events_step_ok_msg by exact Hcode.
    apply (sysex_ok b m (msg_of_step m)); [exact Hb | apply msg_fits_step | exact F240]. }
  revert H. destruct (Z.land (sm_status m) 240 =? 176) eqn:F176; intros H; cbn [negb] in H.
  2: { (* another channel message *)
    injection H as H1 H2 H3. subst rd ev d'.
    rewrite (owed_at_event b len pos status m Em Hcode)
      by (intro K; apply spec_kind_fader in K as [K1 _]; apply Z.eqb_neq in F176; contradiction).
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    rewrite events_step_ok_msg by exact Hcode.
    apply (other_ok b m (msg_of_step m)); [apply msg_fits_step | exact F144 | exact F176 | exact F240]. }
  revert H. destruct (sm_d1 m <? 32) eqn:F32; intros H; cbn [negb] in H.
  2: { (* a control change that is no fader *)
    unfold DIGINET_JOG_CC, DIGINET_ZONE_FIRST in H.
    assert (Hnf : se_kind (spec_event_of b m) <> SPEC_EV_FADER).
    { intro K. apply spec_kind_fader in K as [_ K2]. apply Z.ltb_ge in F32. lia. }
    rewrite (owed_at_event b len pos status m Em Hcode Hnf).
    revert H. destruct (sm_d1 m =? 92) eqn:F92; intros H; cbn [negb] in H.
    { injection H as H1 H2 H3. subst rd ev d'.
      cbn [ow_m ow_next ow_status_out dd_c dd_p].
      split; [exact Hr|]. split; [|split; reflexivity].
      rewrite events_step_ok_msg by exact Hcode.
      apply (jog_ok b m (msg_of_step m)); [apply msg_fits_step | exact F144 | exact F176 | exact F32 | exact F92]. }
    revert H. destruct ((64 <=? sm_d1 m) && (sm_d1 m <? 64 + 24)) eqn:FV; intros H; cbn [negb] in H.
    { injection H as H1 H2 H3. subst rd ev d'.
      cbn [ow_m ow_next ow_status_out dd_c dd_p].
      split; [exact Hr|]. split; [|split; reflexivity].
      rewrite events_step_ok_msg by exact Hcode.
      apply (vpot_ok b m (msg_of_step m));
        [apply msg_fits_step | exact F144 | exact F176 | exact F32 | exact F92 | exact FV]. }
    { injection H as H1 H2 H3. subst rd ev d'.
      cbn [ow_m ow_next ow_status_out dd_c dd_p].
      split; [exact Hr|]. split; [|split; reflexivity].
      rewrite events_step_ok_msg by exact Hcode.
      apply (cc_other_ok b m (msg_of_step m));
        [apply msg_fits_step | exact F144 | exact F176 | exact F32 | exact F92 | exact FV]. } }
  (* a fader *)
  apply Z.eqb_eq in F176. apply Z.ltb_lt in F32.
  revert H.
  destruct (diginet_msg_next b (DgnCursor len (sm_next m) (sm_status_out m)) dgn_msg_zero)
    as [[rl lsb] peek] eqn:E2.
  intros H. cbv beta iota in H.
  remember (spec_msg_step b len (sm_next m) (sm_status_out m)) as ml eqn:Eml.
  destruct (fader_lookahead b len m ml rl lsb peek Hb Eml E2) as [Hcond [Hrl [Hd2l Hpeek]]].
  subst peek. rewrite Hcond in H.
  assert (Hfad : se_kind (spec_event_of b m) = SPEC_EV_FADER)
    by (rewrite spec_event_fader by assumption; reflexivity).
  rewrite (owed_at_fader b len pos status m ml Em Hcode Hfad Eml).
  rewrite (spec_event_fader b m F176 F32).
  revert H.
  destruct ((sm_code ml =? 1) && (Z.land (sm_status ml) 240 =? 176) && (sm_d1 ml =? 32 + sm_d1 m)) eqn:C;
    intros H; cbn [negb] in H.
  - (* the LSB came *)
    assert (Hl1 : rl = 1).
    { rewrite Hrl. apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C _].
      apply Z.eqb_eq. exact C. }
    rewrite (Hd2l Hl1) in H.
    injection H as H1 H2 H3. subst rd ev d'.
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    rewrite events_step_ok_msg by exact Hcode.
    apply fader_ok; first [reflexivity | exact (msg_agrees_of_step m) | exact F240].
  - (* lsb_missing *)
    injection H as H1 H2 H3. subst rd ev d'.
    cbn [ow_m ow_next ow_status_out dd_c dd_p].
    split; [exact Hr|]. split; [|split; reflexivity].
    rewrite events_step_ok_msg by exact Hcode.
    apply fader_ok; first [reflexivity | exact (msg_agrees_of_step m) | exact F240].
Qed.

(* ---- the decoder loop ---- *)

Lemma events_trace_ok : forall fuel b len d pos status,
  Forall (fun x => 0 <= x < 256) b -> dd_c d = DgnCursor len pos status ->
  forallb (events_step_ok b) (events_trace (diginet_decoder_next b) b len fuel d pos status) = true.
Proof.
  induction fuel as [|f IH]; intros b len d pos status Hb Hd; [reflexivity|].
  cbn [events_trace].
  destruct (diginet_decoder_next b d dgn_event_zero) as [[rd ev] d'] eqn:E.
  destruct (decoder_step_ok b d len pos status rd ev d' Hb Hd E) as [_ [Hok [Hc _]]].
  cbn [forallb]. rewrite Hok. cbn [andb].
  destruct (sm_code (ow_m (owed_at b len pos status)) =? 0); [reflexivity|].
  apply IH; assumption.
Qed.

(* No check of the decoder loop of fuzz_decode.c aborts (:324-339), for every body of bytes, every length and every
   personality the decoder is made with. *)
Theorem dgn_events_loop_ok : forall b len p,
  Forall (fun x => 0 <= x < 256) b ->
  events_loop_ok (diginet_decoder_next b) b len (diginet_decoder_init p len) = true.
Proof.
  intros b len p Hb. unfold events_loop_ok. apply events_trace_ok; [exact Hb | reflexivity].
Qed.

(* the harness's decoder: diginet_decoder_init (&d, diginet_personality_of (DESK[sel % 3]), body, len)
   (fuzz_decode.c:324) *)
Corollary dgn_events_loop_ok_desk : forall b len sel,
  Forall (fun x => 0 <= x < 256) b ->
  events_loop_ok (diginet_decoder_next b) b len
    (diginet_decoder_init (diginet_personality_of (desk_of_sel sel)) len) = true.
Proof. intros b len sel Hb. apply dgn_events_loop_ok. exact Hb. Qed.
