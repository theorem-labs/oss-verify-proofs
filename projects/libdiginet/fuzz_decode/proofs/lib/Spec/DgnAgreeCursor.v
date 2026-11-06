(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode. The library's cursor agrees with fuzz/spec.h on every body:
   - diginet_msg_next_step: one call of diginet_msg_next (src/diginet_msg.c:27-103) at a cursor that stands where
     a step of spec_msg_step (fuzz/spec.h:298-363) starts returns the step's code, leaves the cursor at the step's
     next position and status, and on a whole message fills the message the step describes (msg_of_step);
     cursor_step_checks is the same fact in the terms of check_cursor_step_ok and check_cursor_message_ok
     (fuzz/fuzz_decode.c:41-115);
   - spec_msg_step_progress, spec_msg_step_end: a step that is not the end moves forward within the body, and the
     end is exactly a position at or past len;
   - cursor_loop_ok_all: no check of the cursor loop of fuzz/fuzz_decode.c:304-321 aborts, for any body;
   - diginet_body_check_spec, check_refusal_ok_all: diginet_body_check (src/diginet_codec.c:47-64) refuses
     exactly the bodies in which spec_system_at (fuzz/spec.h:264-270) finds F0 13 xx 70, so the check of
     fuzz/fuzz_decode.c:265-276 never aborts.
   A body is a list of bytes, each in [0, 256) (DgnSpec.v). No fact here needs a hypothesis on the body's length:
   in frame mode the body list runs on past len into the frame's padding (fuzz/fuzz_decode.c:295-302). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes ---- *)

Lemma byte_at_range : forall b i, Forall (fun x => 0 <= x < 256) b -> 0 <= byte_at b i < 256.
Proof.
  intros b i Hb. unfold byte_at.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length b)) as [Hl|Hl].
  - rewrite Forall_forall in Hb. apply Hb, nth_In, Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma u8_byte_at : forall b i, Forall (fun x => 0 <= x < 256) b -> u8 (byte_at b i) = byte_at b i.
Proof. intros b i Hb. unfold u8. apply Z.mod_small, byte_at_range, Hb. Qed.

Lemma byte_mod_256 : forall b i, Forall (fun x => 0 <= x < 256) b -> byte_at b i mod 256 = byte_at b i.
Proof. intros b i Hb. apply Z.mod_small, byte_at_range, Hb. Qed.

Lemma zseq_byte : forall x, 0 <= x < 256 -> In x (zseq 256).
Proof.
  intros x Hx. unfold zseq. replace x with (Z.of_nat (Z.to_nat x)) by lia.
  apply in_map. apply in_seq. lia.
Qed.

(* a boolean property of every byte, checked over the 256 of them *)
Lemma byte_forall_zseq : forall p : Z -> bool,
  forallb p (zseq 256) = true -> forall x, 0 <= x < 256 -> p x = true.
Proof. intros p H x Hx. rewrite forallb_forall in H. apply H, zseq_byte, Hx. Qed.

(* the library's test b & 0x80 (diginet_msg.c:63, :89) is the grammar's b < 0x80 on a byte *)
Lemma land_0x80 : forall x, 0 <= x < 256 -> (Z.land x 0x80 =? 0) = (x <? 128).
Proof.
  intros x Hx. apply Bool.eqb_prop.
  exact (byte_forall_zseq (fun y => Bool.eqb (Z.land y 0x80 =? 0) (y <? 128)) ltac:(vm_compute; reflexivity) x Hx).
Qed.

Lemma u8_land_f0 : forall s, u8 (Z.land s 0xf0) = Z.land s 0xf0.
Proof.
  intros s. unfold u8. change 256 with (2 ^ 8).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

(* ---- the library's helpers in the grammar's terms ---- *)

Lemma msg_scan_f7_eq : forall b len fuel i, msg_scan_f7 b len i fuel = scan_f7 b len i fuel.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i; cbn [msg_scan_f7 scan_f7]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma channel_data_len_spec : forall s,
  channel_data_len s = if (Z.land s 240 =? 192) || (Z.land s 240 =? 208) then 1 else 2.
Proof. intros s. unfold channel_data_len; cbv beta zeta. rewrite u8_land_f0. reflexivity. Qed.

Lemma first_high_1 : forall b d, Forall (fun x => 0 <= x < 256) b ->
  first_high b d 0 (Z.to_nat 1) = if 128 <=? byte_at b d then Some 0 else None.
Proof.
  intros b d Hb. change (Z.to_nat 1) with 1%nat. cbn [first_high].
  rewrite Z.add_0_r, (land_0x80 _ (byte_at_range b d Hb)).
  destruct (Z.ltb_spec (byte_at b d) 128), (Z.leb_spec 128 (byte_at b d)); try lia; reflexivity.
Qed.

Lemma first_high_2 : forall b d, Forall (fun x => 0 <= x < 256) b ->
  first_high b d 0 (Z.to_nat 2) =
  if 128 <=? byte_at b d then Some 0 else if 128 <=? byte_at b (d + 1) then Some 1 else None.
Proof.
  intros b d Hb. change (Z.to_nat 2) with 2%nat. cbn [first_high].
  try change (0 + 1) with 1. rewrite Z.add_0_r.
  rewrite (land_0x80 _ (byte_at_range b d Hb)), (land_0x80 _ (byte_at_range b (d + 1) Hb)).
  destruct (Z.ltb_spec (byte_at b d) 128), (Z.leb_spec 128 (byte_at b d));
    destruct (Z.ltb_spec (byte_at b (d + 1)) 128), (Z.leb_spec 128 (byte_at b (d + 1)));
    try lia; reflexivity.
Qed.

(* ---- tactics ---- *)

(* case on every boolean test of an if in the goal, innermost first, keeping each outcome as a hypothesis *)
Ltac split_ifs :=
  repeat (match goal with
          | |- context [if ?x then _ else _] =>
              lazymatch type of x with bool => idtac end;
              lazymatch x with
              | true => fail
              | false => fail
              | context [if _ then _ else _] => fail
              | _ => let E := fresh "E" in destruct x eqn:E
              end
          end; cbv beta iota zeta).

(* boolean comparison outcomes as arithmetic facts *)
Ltac bools :=
  repeat match goal with
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : (_ && _) = false |- _ => apply andb_false_iff in H as [?|?]
  | H : (_ || _) = true |- _ => apply orb_true_iff in H as [?|?]
  | H : (_ || _) = false |- _ => apply orb_false_iff in H as [? ?]
  end.

(* ---- one call of diginet_msg_next is one step of the grammar ---- *)

(* the dgn_msg a whole message of the grammar is, field by field (diginet.h:139-147 against spec.h:291-296) *)
Definition msg_of_step (s : spec_msg) : dgn_msg :=
  {| dm_status := sm_status s; dm_running := sm_running s; dm_d1 := sm_d1 s; dm_d2 := sm_d2 s;
     dm_sysex := sm_sysex_at s; dm_sysex_len := sm_sysex_len s; dm_offset := sm_at s; dm_len := sm_len s |}.

(* a leaf of the case analysis below: the code, the cursor and the message side by side *)
Ltac fin Hb :=
  cbn;
  refine (conj _ (conj _ _));
  [ reflexivity
  | try reflexivity; f_equal; lia
  | let Hr := fresh "Hr" in
    intros Hr;
    first [ discriminate Hr
          | unfold msg_of_step; cbn;
            rewrite ?(u8_byte_at _ _ Hb), ?(byte_mod_256 _ _ Hb);
            try reflexivity; f_equal; lia ] ].

(* the channel-message tail, diginet_msg.c:83-102 against spec.h:339-359 *)
Ltac chan Hb :=
  unfold msg_channel; cbv beta zeta; cbn [dc_len dc_pos dc_status];
  rewrite channel_data_len_spec;
  match goal with |- context [if ?x || ?y then 1 else 2] => destruct (x || y) end;
  [ rewrite (first_high_1 _ _ Hb) | rewrite (first_high_2 _ _ Hb) ];
  cbn; split_ifs; fin Hb.

Lemma msg_next_step_match : forall b len pos status m,
  Forall (fun x => 0 <= x < 256) b ->
  match diginet_msg_next b (DgnCursor len pos status) m with
  | (r, msg, c) =>
      r = sm_code (spec_msg_step b len pos status) /\
      c = DgnCursor len (sm_next (spec_msg_step b len pos status))
                        (sm_status_out (spec_msg_step b len pos status)) /\
      (r = 1 -> msg = msg_of_step (spec_msg_step b len pos status))
  end.
Proof.
  intros b len pos status m Hb.
  unfold diginet_msg_next, spec_msg_step. cbv beta zeta. cbn [dc_len dc_pos dc_status].
  destruct (len <=? pos) eqn:E0; [fin Hb|].
  apply Z.leb_gt in E0.
  pose proof (byte_at_range b pos Hb) as Hl.
  destruct (byte_at b pos =? 240) eqn:E1.
  - (* F0: a system exclusive message, whole or cut short, diginet_msg.c:43-59, spec.h:304-318 *)
    pose proof (msg_scan_f7_ge b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as G.
    pose proof (msg_scan_f7_le b len (Z.to_nat (len - (pos + 1))) (pos + 1) ltac:(lia)) as L.
    rewrite msg_scan_f7_eq in G, L |- *.
    destruct (len <=? scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1)))) eqn:E2.
    + apply Z.leb_le in E2.
      replace (scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) =? len) with true
        by (symmetry; apply Z.eqb_eq; lia).
      fin Hb.
    + apply Z.leb_gt in E2.
      replace (scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) =? len) with false
        by (symmetry; apply Z.eqb_neq; lia).
      fin Hb.
  - apply Z.eqb_neq in E1.
    rewrite (land_0x80 _ Hl).
    destruct (byte_at b pos <? 128) eqn:E2.
    + (* a data byte: refused with no running status, else a running-status message *)
      apply Z.ltb_lt in E2.
      replace (240 <? byte_at b pos) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (128 <=? byte_at b pos) with false by (symmetry; apply Z.leb_gt; lia).
      cbn [negb andb orb].
      destruct (status =? 0) eqn:E3; [fin Hb|].
      chan Hb.
    + (* a status byte: F1..FF refused, 80..EF a channel message *)
      apply Z.ltb_ge in E2.
      cbn [negb andb orb].
      destruct (240 <? byte_at b pos) eqn:E3.
      * apply Z.ltb_lt in E3.
        replace (0xf0 <=? byte_at b pos) with true by (symmetry; apply Z.leb_le; lia).
        fin Hb.
      * apply Z.ltb_ge in E3.
        replace (0xf0 <=? byte_at b pos) with false by (symmetry; apply Z.leb_gt; lia).
        replace (128 <=? byte_at b pos) with true by (symmetry; apply Z.leb_le; lia).
        cbn [negb andb orb].
        chan Hb.
Qed.

(* The per-step cursor lemma. *)
Lemma diginet_msg_next_step : forall b len pos status m r msg c,
  Forall (fun x => 0 <= x < 256) b ->
  diginet_msg_next b (DgnCursor len pos status) m = (r, msg, c) ->
  r = sm_code (spec_msg_step b len pos status) /\
  c = DgnCursor len (sm_next (spec_msg_step b len pos status)) (sm_status_out (spec_msg_step b len pos status)) /\
  (r = 1 -> msg = msg_of_step (spec_msg_step b len pos status)).
Proof.
  intros b len pos status m r msg c Hb E.
  pose proof (msg_next_step_match b len pos status m Hb) as P. rewrite E in P. exact P.
Qed.

Lemma msg_agrees_of_step : forall s, msg_agrees s (msg_of_step s) = true.
Proof.
  intros s. unfold msg_agrees, msg_of_step.
  cbn [dm_offset dm_len dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len].
  rewrite !Z.eqb_refl. destruct (sm_status s =? 240); reflexivity.
Qed.

Lemma check_cursor_step_ok_refl : forall s len,
  check_cursor_step_ok s (sm_code s) (DgnCursor len (sm_next s) (sm_status_out s)) = true.
Proof.
  intros s len. unfold check_cursor_step_ok; cbn [dc_pos dc_status]. rewrite !Z.eqb_refl.
  destruct (sm_code s =? 0), (sm_code s =? SPEC_E_NO_STATUS), (sm_code s =? SPEC_E_STATUS),
    (sm_code s =? SPEC_E_TRUNCATED), (sm_code s =? 1); reflexivity.
Qed.

(* The per-step lemma in the terms of the two checks of one pass of the cursor loop (fuzz_decode.c:314-316). *)
Lemma cursor_step_checks : forall b len pos status m r msg c,
  Forall (fun x => 0 <= x < 256) b ->
  diginet_msg_next b (DgnCursor len pos status) m = (r, msg, c) ->
  check_cursor_step_ok (spec_msg_step b len pos status) r c = true /\
  implb (sm_code (spec_msg_step b len pos status) =? 1)
    (check_cursor_message_ok (spec_msg_step b len pos status) msg) = true.
Proof.
  intros b len pos status m r msg c Hb E.
  destruct (diginet_msg_next_step b len pos status m r msg c Hb E) as [Hr [Hc Hm]].
  subst r c. split; [apply check_cursor_step_ok_refl|].
  destruct (sm_code (spec_msg_step b len pos status) =? 1) eqn:E1; [|reflexivity].
  apply Z.eqb_eq in E1. cbn [implb]. rewrite (Hm E1). unfold check_cursor_message_ok. apply msg_agrees_of_step.
Qed.

(* A step that is not the end moves forward within the body. *)
Lemma spec_msg_step_progress : forall b len pos status,
  sm_code (spec_msg_step b len pos status) <> 0 ->
  pos < sm_next (spec_msg_step b len pos status) <= len.
Proof.
  intros b len pos status. unfold spec_msg_step; cbv beta zeta.
  pose proof (msg_scan_f7_ge b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as G.
  pose proof (msg_scan_f7_le b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as L.
  rewrite msg_scan_f7_eq in G, L.
  split_ifs; cbn; intros Hc; bools; lia.
Qed.

(* The end of the body is exactly a position at or past len. *)
Lemma spec_msg_step_end : forall b len pos status,
  sm_code (spec_msg_step b len pos status) = 0 <-> len <= pos.
Proof.
  intros b len pos status. unfold spec_msg_step; cbv beta zeta.
  split_ifs; unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS; cbn; bools; lia.
Qed.

(* At the end the step leaves the position and the running status as they were. *)
Lemma spec_msg_step_end_fields : forall b len pos status,
  len <= pos ->
  sm_next (spec_msg_step b len pos status) = pos /\ sm_status_out (spec_msg_step b len pos status) = status.
Proof.
  intros b len pos status H. unfold spec_msg_step; cbv beta zeta.
  replace (len <=? pos) with true by (symmetry; apply Z.leb_le, H). cbn. split; reflexivity.
Qed.

(* ---- the cursor loop, fuzz_decode.c:304-321 ---- *)

Lemma cursor_trace_ok : forall b len fuel pos status,
  Forall (fun x => 0 <= x < 256) b ->
  forallb cursor_step_ok
    (cursor_trace (diginet_msg_next b) b len fuel (DgnCursor len pos status) pos status) = true.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros pos status Hb; [reflexivity|].
  cbn [cursor_trace].
  destruct (diginet_msg_next b (DgnCursor len pos status) dgn_msg_zero) as [[r msg] c] eqn:E.
  pose proof (cursor_step_checks b len pos status dgn_msg_zero r msg c Hb E) as [C1 C2].
  destruct (diginet_msg_next_step b len pos status dgn_msg_zero r msg c Hb E) as [_ [Hc _]].
  cbn [forallb]. apply andb_true_intro; split.
  - unfold cursor_step_ok; cbn [cs_m cs_r cs_msg cs_c]. rewrite C1, C2. reflexivity.
  - destruct (sm_code (spec_msg_step b len pos status) =? 0); [reflexivity|].
    subst c. apply IH, Hb.
Qed.

(* No check of the cursor loop aborts, for any body. *)
Theorem cursor_loop_ok_all : forall b len,
  Forall (fun x => 0 <= x < 256) b ->
  cursor_loop_ok (diginet_msg_next b) b len (diginet_cursor_init len) = true.
Proof. intros b len Hb. unfold cursor_loop_ok, diginet_cursor_init. apply cursor_trace_ok, Hb. Qed.

(* ---- the refusal, diginet_codec.c:47-64 against spec.h:264-270 ---- *)

Lemma system_prefix_scan_at : forall b len fuel i,
  0 <= i -> system_prefix_scan b len i fuel = (0 <=? system_at_loop b len i fuel).
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i Hi;
    cbn [system_prefix_scan system_at_loop]; [reflexivity|].
  unfold DIGINET_SYSEX_MAKER, DIGINET_FN_SYSTEM, SPEC_MAKER, SPEC_FN_SYSTEM.
  destruct (i + 3 <? len); [|reflexivity].
  destruct ((byte_at b i =? 240) && (byte_at b (i + 1) =? 19) && (byte_at b (i + 3) =? 112)).
  - symmetry. apply Z.leb_le. exact Hi.
  - apply IH. lia.
Qed.

Lemma system_prefix_scan_found : forall b len fuel i j,
  i <= j -> j + 3 < len -> (Z.to_nat (j - i) < fuel)%nat ->
  byte_at b j = 0xf0 -> byte_at b (j + 1) = DIGINET_SYSEX_MAKER -> byte_at b (j + 3) = DIGINET_FN_SYSTEM ->
  system_prefix_scan b len i fuel = true.
Proof.
  intros b len fuel; induction fuel as [|f IH]; intros i j Hij Hj Hf H0 H1 H3; [lia|].
  cbn [system_prefix_scan].
  replace (i + 3 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct ((byte_at b i =? 0xf0) && (byte_at b (i + 1) =? DIGINET_SYSEX_MAKER) &&
            (byte_at b (i + 3) =? DIGINET_FN_SYSTEM)) eqn:E; [reflexivity|].
  destruct (Z.eq_dec i j) as [<-|Hne].
  - rewrite H0, H1, H3, !Z.eqb_refl in E. discriminate E.
  - apply (IH (i + 1) j); try lia; assumption.
Qed.

(* diginet_msg_next returns 1 with a payload of 3 bytes or more only for a whole F0 .. F7 at the cursor *)
Lemma diginet_msg_next_sysex : forall b c m,
  match diginet_msg_next b c m with
  | (r, m', _) =>
      r = 1 -> 3 <= dm_sysex_len m' ->
      byte_at b (dc_pos c) = 0xf0 /\ dm_sysex m' = dc_pos c + 1 /\
      dc_pos c + 1 + dm_sysex_len m' < dc_len c
  end.
Proof.
  intros b c m. unfold diginet_msg_next; cbv beta zeta.
  destruct (dc_len c <=? dc_pos c) eqn:E0; [cbn; intros Hr; discriminate Hr|].
  destruct (byte_at b (dc_pos c) =? 0xf0) eqn:E1.
  - destruct (dc_len c <=? msg_scan_f7 b (dc_len c) (dc_pos c + 1) (Z.to_nat (dc_len c - (dc_pos c + 1)))) eqn:E2.
    + cbn. intros Hr; discriminate Hr.
    + cbn [dm_sysex dm_sysex_len]. intros _ Hs. apply Z.eqb_eq in E1. apply Z.leb_gt in E2.
      split; [exact E1|split; [reflexivity|lia]].
  - unfold msg_channel; cbv beta zeta.
    repeat match goal with
    | |- context [if ?x then _ else _] => destruct x
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
    end; cbn; intros Hr Hs; try discriminate Hr; lia.
Qed.

Lemma body_check_loop_true : forall fuel b c m,
  0 <= dc_pos c -> body_check_loop b c m fuel = Some true ->
  exists j, dc_pos c <= j /\ j + 3 < dc_len c /\ byte_at b j = 0xf0 /\
            byte_at b (j + 1) = DIGINET_SYSEX_MAKER /\ byte_at b (j + 3) = DIGINET_FN_SYSTEM.
Proof.
  induction fuel as [|f IH]; intros b c m Hpos H; [discriminate H|].
  revert H. cbn [body_check_loop].
  pose proof (diginet_msg_next_progress b c m Hpos) as P.
  pose proof (diginet_msg_next_sysex b c m) as S.
  destruct (diginet_msg_next b c m) as [[r m'] c'] eqn:E.
  unfold moves in P. cbv beta iota zeta in P, S |- *.
  destruct (r =? 0) eqn:R; [intros H; discriminate H|].
  apply Z.eqb_neq in R.
  destruct P as [[P _]|[_ [P1 P2]]]; [contradiction|].
  match goal with |- (if ?x then _ else _) = _ -> _ => destruct x eqn:C end.
  - intros _. bools. subst r.
    destruct (S eq_refl ltac:(lia)) as [S0 [S1 S2]].
    exists (dc_pos c).
    match goal with
    | H4 : byte_at b (dm_sysex m') = _, H5 : byte_at b (dm_sysex m' + 2) = _ |- _ =>
        rewrite S1 in H4, H5; replace (dc_pos c + 1 + 2) with (dc_pos c + 3) in H5 by lia
    end.
    split; [lia|]. split; [lia|]. split; [exact S0|]. split; assumption.
  - intros H. destruct (IH b c' m' ltac:(lia) H) as [j [Hj1 [Hj2 Hj3]]].
    exists j. split; [lia|]. split; [lia|exact Hj3].
Qed.

(* diginet_body_check in the grammar's terms *)
Theorem diginet_body_check_spec : forall b len,
  diginet_body_check b len = (if 0 <=? spec_system_at b len then SPEC_E_REFUSED else SPEC_OK).
Proof.
  intros b len. unfold diginet_body_check, spec_system_at.
  rewrite <- system_prefix_scan_at by lia.
  destruct (body_check_loop b (diginet_cursor_init len) dgn_msg_zero (S (Z.to_nat len))) as [[|]|] eqn:E.
  - destruct (body_check_loop_true _ b (diginet_cursor_init len) dgn_msg_zero ltac:(cbn; lia) E)
      as [j [Hj1 [Hj2 [H0 [H1 H3]]]]].
    cbn [diginet_cursor_init dc_pos dc_len] in Hj1, Hj2.
    rewrite (system_prefix_scan_found b len (Z.to_nat len) 0 j) by first [lia | assumption].
    reflexivity.
  - destruct (system_prefix_scan b len 0 (Z.to_nat len)); reflexivity.
  - destruct (system_prefix_scan b len 0 (Z.to_nat len)); reflexivity.
Qed.

(* The check of fuzz_decode.c:265-276 never aborts, for any body. *)
Theorem check_refusal_ok_all : forall b len, check_refusal_ok b len (diginet_body_check b len) = true.
Proof. intros b len. unfold check_refusal_ok. rewrite diginet_body_check_spec. apply Z.eqb_refl. Qed.
