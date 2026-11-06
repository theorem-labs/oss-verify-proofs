(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: dloop_holds, the decoder loop of LLVMFuzzerTestOneInput (plain image) from its
   head 0x1309c after k passes to its exit 0x13678 (LLVMFuzzerTestOneInput_seg2.v dloop_stmt). One pass is
   dstep_stmt from the head, then dsysex_stmt (0x13228) or dchan_stmt (0x133d0) for a message, up to 0x13180
   with o = owed_at; then memset (&ev, 0, 80), diginet_decoder_next (&d, &ev), check_events_step and, when
   o.m.code is 1, check_events_fields through their contracts, with the check booleans from
   DgnAgreeDecoder.decoder_step_ok; the exit when the code is 0 or steps > len, else the latch
   (s0 = o.next, s7 = o.status_out) back to the head. The loop is an induction on len + 1 - k. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness DgnAgreeCursor DgnAgreeDecoder.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2.
Import ListNotations.
Open Scope Z_scope.

(* ---- cell lists of the frame ---- *)

Section DL.
Variable segs : list Segment.

Lemma dloop_app : forall m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma dloop_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (Ra & Rb & R)].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Rb, R.
  pose proof (cells_bytes_length cs1 W1) as L1.
  pose proof (bytes_at_bound segs _ _ _ B2) as BB2.
  rewrite cells_bytes_length in BB2 by exact W2.
  split.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi. apply R. lia.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply R. lia.
Qed.

Lemma dloop_ro_split : forall m A cs1 cs2, ro_cells segs m A (cs1 ++ cs2) ->
  ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [W B].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; split; assumption.
Qed.

Lemma dloop_ro : forall m A cs, rw_cells segs m A cs -> ro_cells segs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

(* a cell list's meaning is its bytes *)
Lemma dloop_rwc_bytes : forall m A cs cs', rw_cells segs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma dloop_to_CB : forall m A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge segs m A [] cs [] ltac:(rewrite app_nil_r; exact H)) as H'.
  exact H'.
Qed.
End DL.

(* the six pieces of the frame in the decoder loop *)
Lemma dloop_split6 : forall m Sp j0 w8 w10 body OC EC jM DC jC saved,
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ OC ++ EC ++ CB 40 jM :: DC ++ CB 32 jC :: saved) ->
  cells_size OC = 120%nat -> cells_size EC = 80%nat -> cells_size DC = 40%nat ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body) /\ rw_cells rsegs m (Sp + 32) OC /\
  rw_cells rsegs m (Sp + 152) EC /\ rw_cells rsegs m (Sp + 232) [CB 40 jM] /\
  rw_cells rsegs m (Sp + 272) DC /\ rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved).
Proof.
  intros m Sp j0 w8 w10 body OC EC jM DC jC saved H HO HE HD.
  apply dloop_split in H as [H1 H]. change (Z.of_nat (cells_size (fr_head j0 w8 w10 body))) with 32 in H.
  apply dloop_split in H as [H2 H]. rewrite HO in H. replace (Sp + 32 + Z.of_nat 120) with (Sp + 152) in H by lia.
  apply dloop_split in H as [H3 H]. rewrite HE in H. replace (Sp + 152 + Z.of_nat 80) with (Sp + 232) in H by lia.
  change (CB 40 jM :: DC ++ CB 32 jC :: saved) with ([CB 40 jM] ++ DC ++ CB 32 jC :: saved) in H.
  apply dloop_split in H as [H4 H]. change (Z.of_nat (cells_size [CB 40 jM])) with 40 in H.
  replace (Sp + 232 + 40) with (Sp + 272) in H by lia.
  apply dloop_split in H as [H5 H6]. rewrite HD in H6. replace (Sp + 272 + Z.of_nat 40) with (Sp + 312) in H6 by lia.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Lemma dloop_join6 : forall m Sp FH OC EC jM DC jC saved,
  cells_size FH = 32%nat -> cells_size OC = 120%nat -> cells_size EC = 80%nat -> cells_size DC = 40%nat ->
  rw_cells rsegs m Sp FH -> rw_cells rsegs m (Sp + 32) OC ->
  rw_cells rsegs m (Sp + 152) EC -> rw_cells rsegs m (Sp + 232) [CB 40 jM] ->
  rw_cells rsegs m (Sp + 272) DC -> rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved) ->
  rw_cells rsegs m Sp (FH ++ OC ++ EC ++ CB 40 jM :: DC ++ CB 32 jC :: saved).
Proof.
  intros m Sp FH OC EC jM DC jC saved SF SO SE SD H1 H2 H3 H4 H5 H6.
  apply dloop_app; [exact H1|]. rewrite SF.
  apply dloop_app; [exact H2|]. rewrite SO. replace (Sp + Z.of_nat 32 + Z.of_nat 120) with (Sp + 152) by lia.
  apply dloop_app; [exact H3|]. rewrite SE. replace (Sp + 152 + Z.of_nat 80) with (Sp + 232) by lia.
  change (CB 40 jM :: DC ++ CB 32 jC :: saved) with ([CB 40 jM] ++ DC ++ CB 32 jC :: saved).
  apply dloop_app; [exact H4|]. change (Z.of_nat (cells_size [CB 40 jM])) with 40.
  replace (Sp + 232 + 40) with (Sp + 272) by lia.
  apply dloop_app; [exact H5|]. rewrite SD. replace (Sp + 272 + Z.of_nat 40) with (Sp + 312) by lia.
  exact H6.
Qed.

Lemma dloop_exit_frame : forall m Sp FH OC EC jM DC jC saved,
  cells_size FH = 32%nat -> cells_size OC = 120%nat -> cells_size EC = 80%nat -> cells_size DC = 40%nat ->
  rw_cells rsegs m Sp FH -> rw_cells rsegs m (Sp + 32) OC ->
  rw_cells rsegs m (Sp + 152) EC -> rw_cells rsegs m (Sp + 232) [CB 40 jM] ->
  rw_cells rsegs m (Sp + 272) DC -> rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved) ->
  exists jj, rw_cells rsegs m Sp (FH ++ CB 312 jj :: saved).
Proof.
  intros m Sp FH OC EC jM DC jC saved SF SO SE SD H1 H2 H3 H4 H5 H6.
  pose proof (dloop_join6 m Sp FH OC EC jM DC jC saved SF SO SE SD H1 H2 H3 H4 H5 H6) as J.
  replace (FH ++ OC ++ EC ++ CB 40 jM :: DC ++ CB 32 jC :: saved)
    with (FH ++ (OC ++ EC ++ CB 40 jM :: DC ++ [CB 32 jC]) ++ saved) in J
    by (rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity).
  apply rw_cells_merge in J.
  assert (S : cells_size (OC ++ EC ++ CB 40 jM :: DC ++ [CB 32 jC]) = 312%nat).
  { rewrite !cells_size_app. cbn [cells_size csize]. rewrite cells_size_app, SO, SE, SD. reflexivity. }
  rewrite S in J. eexists. exact J.
Qed.

(* the reads of the latch: o.m.code at o, o.next and o.status_out at o + 104 *)
Lemma dloop_owed_code : forall m A p1 p2 o, ro_cells rsegs m A (owed_cells p1 p2 o) ->
  ro_cells rsegs m A [C4 (Z_to_bv 64 (sm_code (ow_m o)))].
Proof.
  intros m A p1 p2 o H.
  assert (E : exists tl, owed_cells p1 p2 o = [C4 (Z_to_bv 64 (sm_code (ow_m o)))] ++ tl) by (eexists; reflexivity).
  destruct E as [tl E]. rewrite E in H. exact (proj1 (dloop_ro_split _ _ _ _ _ H)).
Qed.

Lemma dloop_owed_latch : forall m A p1 p2 o, ro_cells rsegs m A (owed_cells p1 p2 o) ->
  ro_cells rsegs m (A + 104) [C8 (Z_to_bv 64 (ow_next o)); C1 (b8 (ow_status_out o))].
Proof.
  intros m A p1 p2 o H.
  assert (E : owed_cells p1 p2 o =
    (spec_msg_cells (ow_m o) ++ spec_event_cells (ow_e o) ++ [C4 (Z_to_bv 64 (ow_lsb_missing o)); CB 4 p1])
    ++ [C8 (Z_to_bv 64 (ow_next o)); C1 (b8 (ow_status_out o))] ++ [CB 7 p2])
    by (unfold owed_cells; rewrite <- !app_assoc; reflexivity).
  rewrite E in H. apply dloop_ro_split in H as [_ H]. apply dloop_ro_split in H as [H _].
  exact H.
Qed.

Lemma dloop_ev0_bytes : forall body,
  cells_bytes (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero) = repeat (Z_to_bv 8 0) 80.
Proof. intros body. vm_compute. reflexivity. Qed.

Lemma dloop_ev0_wf : forall body, cells_wf (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero).
Proof. intros body. vm_compute. tauto. Qed.

Lemma dloop_scan : forall b len fuel i, i <= len -> i <= scan_f7 b len i fuel <= len.
Proof.
  intros b len fuel i Hi. rewrite <- msg_scan_f7_eq.
  split; [apply msg_scan_f7_ge | apply msg_scan_f7_le; exact Hi].
Qed.

Ltac dloop_fin :=
  cbn [sm_code sm_status sm_sysex_at sm_sysex_len sm_next sm_status_out];
  unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS; repeat split; lia.

(* the fields of one step the loop and the checks' contracts use *)
Lemma dloop_step_facts : forall b len pos st, Forall (fun x => 0 <= x < 256) b -> 0 <= pos <= len -> lp_st st ->
  let m := spec_msg_step b len pos st in
  (sm_code m = 0 \/ sm_code m = 1 \/ sm_code m = -6 \/ sm_code m = -7 \/ sm_code m = -8) /\
  0 <= sm_status m < 256 /\ (sm_status m = 240 -> 0 < sm_sysex_at m < len) /\
  0 <= sm_sysex_len m <= len /\ pos <= sm_next m <= len /\ lp_st (sm_status_out m).
Proof.
  intros b len pos st Hb Hp Hs. unfold lp_st in *. cbv zeta.
  pose proof (byte_at_range b pos Hb) as Hl.
  unfold spec_msg_step; cbv beta zeta.
  destruct (Z.leb_spec len pos) as [E1|E1]; [dloop_fin|].
  destruct (Z.eqb_spec (byte_at b pos) 240) as [E2|E2].
  { pose proof (dloop_scan b len (Z.to_nat (len - (pos + 1))) (pos + 1) ltac:(lia)) as Hi.
    destruct (Z.eqb_spec (scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1)))) len) as [E3|E3]; dloop_fin. }
  destruct (Z.ltb_spec 240 (byte_at b pos)) as [E4|E4]; [dloop_fin|].
  destruct ((byte_at b pos <? 128) && (st =? 0)) eqn:E5; [dloop_fin|].
  apply andb_false_iff in E5.
  destruct (Z.leb_spec 128 (byte_at b pos)) as [E6|E6].
  - destruct ((Z.land (byte_at b pos) 240 =? 192) || (Z.land (byte_at b pos) 240 =? 208)).
    + destruct (Z.ltb_spec len (pos + 1 + 1)); [dloop_fin|].
      destruct (Z.leb_spec 128 (byte_at b (pos + 1))); [dloop_fin|].
      cbn [Z.eqb Pos.eqb andb]. dloop_fin.
    + destruct (Z.ltb_spec len (pos + 1 + 2)); [dloop_fin|].
      destruct (Z.leb_spec 128 (byte_at b (pos + 1))); [dloop_fin|].
      cbn [Z.eqb Pos.eqb andb].
      destruct (Z.leb_spec 128 (byte_at b (pos + 1 + 1))); dloop_fin.
  - assert (Hst : st <> 0) by (destruct E5 as [E5|E5]; [apply Z.ltb_ge in E5; lia | apply Z.eqb_neq in E5; exact E5]).
    destruct ((Z.land st 240 =? 192) || (Z.land st 240 =? 208)).
    + destruct (Z.ltb_spec len (pos + 1)); [dloop_fin|].
      destruct (Z.leb_spec 128 (byte_at b pos)); [dloop_fin|].
      cbn [Z.eqb Pos.eqb andb]. dloop_fin.
    + destruct (Z.ltb_spec len (pos + 2)); [dloop_fin|].
      destruct (Z.leb_spec 128 (byte_at b pos)); [dloop_fin|].
      cbn [Z.eqb Pos.eqb andb].
      destruct (Z.leb_spec 128 (byte_at b (pos + 1))); dloop_fin.
Qed.

(* the kind and length of the event of a message *)
Lemma dloop_kind : forall b m, 0 <= se_kind (spec_event_of b m) <= 13 /\
  (se_kind (spec_event_of b m) = SPEC_EV_SCRIBBLE -> 0 <= se_len (spec_event_of b m) <= 8).
Proof.
  intros b m. unfold spec_event_of, se_other; cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
  cbn [se_kind se_len];
  unfold SPEC_EV_FADER, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON, SPEC_EV_SECTION_BUTTON, SPEC_EV_VPOT, SPEC_EV_JOG,
    SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS, SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER, SPEC_EV_SYSTEM,
    SPEC_EV_OTHER;
  try (split; [lia | intros; lia]).
  all: repeat match goal with H : (_ || _) = false |- _ => apply orb_false_iff in H as [? ?] end.
  all: repeat match goal with H : (_ <? _) = false |- _ => apply Z.ltb_ge in H end.
  all: unfold u8, SPEC_CHARS_MAX in *; rewrite Z.mod_small by lia; split; [lia | intros; lia].
Qed.

(* what the loop and the checks' contracts use of owed_at *)
Lemma dloop_owed_facts : forall b len pos st, Forall (fun x => 0 <= x < 256) b -> 0 <= pos <= len -> lp_st st ->
  let o := owed_at b len pos st in
  ow_m o = spec_msg_step b len pos st /\ 0 <= ow_next o <= len /\ lp_st (ow_status_out o) /\
  0 <= ow_lsb_missing o <= 1 /\ 0 <= se_kind (ow_e o) <= 13 /\
  (se_kind (ow_e o) = SPEC_EV_SCRIBBLE -> 0 <= se_len (ow_e o) <= 8).
Proof.
  intros b len pos st Hb Hp Hs. cbv zeta.
  pose proof (dloop_step_facts b len pos st Hb Hp Hs) as F. cbv zeta in F.
  destruct F as (_ & _ & _ & _ & Fn & Fs).
  unfold owed_at; cbv zeta.
  remember (spec_msg_step b len pos st) as M eqn:EM.
  pose proof (dloop_kind b M) as [K1 K2].
  destruct (negb (sm_code M =? 1)).
  { cbn [ow_m ow_next ow_status_out ow_lsb_missing ow_e se_kind se_len se_zero]. unfold SPEC_EV_SCRIBBLE.
    split; [reflexivity|]. split; [lia|]. split; [exact Fs|]. split; [lia|]. split; [lia|]. intros; lia. }
  destruct (negb (se_kind (spec_event_of b M) =? SPEC_EV_FADER)).
  { cbn [ow_m ow_next ow_status_out ow_lsb_missing ow_e].
    split; [reflexivity|]. split; [lia|]. split; [exact Fs|]. split; [lia|]. split; [exact K1 | exact K2]. }
  pose proof (dloop_step_facts b len (sm_next M) (sm_status_out M) Hb ltac:(lia) Fs) as G. cbv zeta in G.
  destruct G as (_ & _ & _ & _ & Gn & Gs).
  destruct ((sm_code (spec_msg_step b len (sm_next M) (sm_status_out M)) =? 1) &&
    (Z.land (sm_status (spec_msg_step b len (sm_next M) (sm_status_out M))) 240 =? 176) &&
    (sm_d1 (spec_msg_step b len (sm_next M) (sm_status_out M)) =? 32 + sm_d1 M)).
  - cbn [ow_m ow_next ow_status_out ow_lsb_missing ow_e se_with_value se_kind se_len].
    split; [reflexivity|]. split; [lia|]. split; [exact Gs|]. split; [lia|]. split; [exact K1 | exact K2].
  - cbn [ow_m ow_next ow_status_out ow_lsb_missing ow_e].
    split; [reflexivity|]. split; [lia|]. split; [exact Fs|]. split; [lia|]. split; [exact K1 | exact K2].
Qed.

(* memset (&ev, 0, 80) at 0x1318c *)
Lemma dloop_memset_ev : memset_contract ->
  forall (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp : Z) (jE : list byte)
    (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 ->
  rw_cells rsegs m (Sp + 152) [CB 80 jE] -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(Sp + 152, Sp + 232)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (Sp + 152) [CB 80 (repeat (Z_to_bv 8 0) 80)] ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x13190) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Sp + 152))
                        a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13190) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x13190) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Sp + 152))
                     (Z_to_bv 64 0) (Z_to_bv 64 80) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSC gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sp jE Q
    H0 H1 RW MI K.
  eapply evt_cut.
  { apply (MSC (Z_to_bv 64 0x13190) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Sp + 152)) (Z_to_bv 64 0)
      (Z_to_bv 64 80) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jE).
    - rewrite !unsigned_lit by lia. exact RW.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM
    & MI' & RW').
  rewrite !unsigned_lit in MU, RW' by lia. change (0 mod 256) with 0 in RW'. change (Z.to_nat 80) with 80%nat in RW'.
  replace (Sp + 152 + 80) with (Sp + 232) in MU by lia.
  rewrite ret_pc_even by (lia || reflexivity).
  apply K; assumption.
Qed.

(* diginet_decoder_next (&d, &ev) at 0x13198, d = sp + 0x110, ev = sp + 0x98 *)
Lemma dloop_dnext_call : diginet_decoder_next_contract ->
  forall (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo body : Z) (bb ej cpad : list byte)
    (pos : nat) (st : Z) (p : option Z) (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 <= lo -> lo + 160 <= Sp -> body + Z.of_nat (length bb) <= lo ->
  (pos <= length bb)%nat -> lp_st st ->
  rw_cells rsegs m (Sp + 272) (decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) pos st p)) ->
  bytes_at rsegs m body bb -> rw_cells rsegs m (Sp + 152) [CB 80 ej] -> stk rsegs m lo Sp -> mem_inv rsegs m ->
  (forall rd ev d', diginet_decoder_next (map bz bb) (decoder_at (Z.of_nat (length bb)) pos st p) dgn_event_zero =
       (rd, ev, d') ->
   forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mpad : list byte)
     (m' : word -> option byte),
     munch [(Sp + 272, Sp + 312); (Sp + 152, Sp + 232); (Sp - 160, Sp)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo Sp ->
     rw_cells rsegs m' (Sp + 272) (decoder_cells body cpad d') ->
     rw_cells rsegs m' (Sp + 152) (if rd =? 1 then event_cells body mpad ev else [CB 80 ej]) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x1319c) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rd)
                        a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x1319c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x1319c) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Sp + 272))
                     (Z_to_bv 64 (Sp + 152)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DIGINET_DECODER_NEXT) fc None m (seg_rom rsegs)).
Proof.
  intros DNC gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sp lo body
    bb ej cpad pos st p Q H0 H1 L0 L1 L2 Hpos Hst RD BA RE ST MI K.
  destruct (diginet_decoder_next (map bz bb) (decoder_at (Z.of_nat (length bb)) pos st p) dgn_event_zero)
    as [[rd ev] d'] eqn:Eres.
  eapply evt_cut.
  { apply (DNC (Z_to_bv 64 0x1319c) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (Sp + 272) (Sp + 152) body lo bb ej cpad pos st p);
      rewrite ?unsigned_lit by lia; try lia.
    - exact Hst.
    - exact RD.
    - exact BA.
    - exact RE.
    - exact ST.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mpad & m' & -> & MU
    & WM & MI' & ST' & RD' & RE').
  try rewrite Eres in RD'. try rewrite Eres in RE'. try rewrite Eres. cbn [fst snd] in RD', RE' |- *.
  rewrite !unsigned_lit in MU, ST' by lia.
  replace (Sp + 272 + 40) with (Sp + 312) in MU by lia. replace (Sp + 152 + 80) with (Sp + 232) in MU by lia.
  rewrite ret_pc_even by (lia || reflexivity).
  apply (K rd ev d' eq_refl t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mpad m'); assumption.
Qed.

(* check_events_step (body, &o, rd, &ev) at 0x131ac *)
Lemma dloop_ces_call : check_events_step_contract ->
  forall (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo body rd : Z) (ow : owed) (ev : dgn_event)
    (p1 p2 mpad : list byte) (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 <= lo -> lo + 160 <= Sp ->
  check_events_step_ok ow rd ev = true -> -2^31 <= sm_code (ow_m ow) < 2^31 -> 0 <= sm_status (ow_m ow) < 256 ->
  (sm_status (ow_m ow) = 240 -> sm_sysex_at (ow_m ow) <> 0) ->
  ro_cells rsegs m (Sp + 32) (owed_cells p1 p2 ow) -> ro_cells rsegs m (Sp + 152) (event_cells body mpad ev) ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(Sp - 16, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x131b0) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6'
                        a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x131b0) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x131b0) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body)
                     (Z_to_bv 64 (Sp + 32)) (Z_to_bv 64 rd) (Z_to_bv 64 (Sp + 152)) a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CHECK_EVENTS_STEP) fc None m (seg_rom rsegs)).
Proof.
  intros CES gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sp lo body rd
    ow ev p1 p2 mpad Q H0 H1 L0 L1 OK C1 C2 C3 RO RE ST MI K.
  eapply evt_cut.
  { apply (CES (Z_to_bv 64 0x131b0) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body (Sp + 32) (Sp + 152) rd lo ow ev p1 p2 mpad);
      unfold CHECK_EVENTS_STEP_FRAME, OW_SIZE, DE_SIZE; rewrite ?unsigned_lit by lia; try lia; assumption. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU
    & WM & MI' & ST').
  unfold CHECK_EVENTS_STEP_FRAME in MU. rewrite !unsigned_lit in MU, ST' by lia.
  rewrite ret_pc_even by (lia || reflexivity).
  apply K; assumption.
Qed.

(* check_events_fields (body, &o, &ev) at 0x131c4 *)
Lemma dloop_cef_call : check_events_fields_contract ->
  forall (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo body : Z) (bb : list byte) (ow : owed)
    (ev : dgn_event) (p1 p2 mpad : list byte) (Q : machine_state -> Prop),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 <= lo -> lo + 160 <= Sp -> body + Z.of_nat (length bb) <= lo ->
  check_events_fields_ok (map bz bb) ow ev = true ->
  -2^31 <= se_kind (ow_e ow) < 2^31 -> 0 <= sm_status (ow_m ow) < 256 -> 0 <= sm_sysex_len (ow_m ow) < 2^64 ->
  (sm_status (ow_m ow) = 240 -> 0 <= sm_sysex_at (ow_m ow) < Z.of_nat (length bb)) ->
  0 <= ow_lsb_missing ow < 256 -> (se_kind (ow_e ow) = SPEC_EV_SCRIBBLE -> 0 <= se_len (ow_e ow) <= 8) ->
  bytes_at rsegs m body bb ->
  ro_cells rsegs m (Sp + 32) (owed_cells p1 p2 ow) -> ro_cells rsegs m (Sp + 152) (event_cells body mpad ev) ->
  stk rsegs m lo Sp -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(Sp - 48, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x131c8) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6'
                        a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x131c8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x131c8) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body)
                     (Z_to_bv 64 (Sp + 32)) (Z_to_bv 64 (Sp + 152)) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CHECK_EVENTS_FIELDS) fc None m (seg_rom rsegs)).
Proof.
  intros CEF gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sp lo body bb
    ow ev p1 p2 mpad Q H0 H1 L0 L1 L2 OK C1 C2 C3 C4 C5 C6 BA RO RE ST MI K.
  eapply evt_cut.
  { apply (CEF (Z_to_bv 64 0x131c8) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body (Sp + 32) (Sp + 152) lo bb ow ev p1 p2 mpad);
      unfold CHECK_EVENTS_FIELDS_FRAME, OW_SIZE, DE_SIZE; rewrite ?unsigned_lit by lia; try lia; assumption. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU
    & WM & MI' & ST').
  unfold CHECK_EVENTS_FIELDS_FRAME in MU. rewrite !unsigned_lit in MU, ST' by lia.
  rewrite ret_pc_even by (lia || reflexivity).
  apply K; assumption.
Qed.

(* lw of a cell C4 (Z_to_bv 64 z) whose z is a C int *)
Lemma dloop_sx32_int : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  replace (2^31) with 2147483648 in Hz by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* lbu of a cell C1 (b8 z) whose z is a byte *)
Lemma dloop_zxb_b8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact Hz.
Qed.

(* the decoder loop's head after k passes: dloop_stmt's conclusion for one k *)
Definition dloop_head (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w10 : word) (saved : list cell)
    (p : option Z) (k : Z) : Prop :=
  forall (pos status : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31 : word)
    (m : word -> option byte) (oj jE jM cpad jC : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body ++ CB 120 oj :: CB 80 jE :: CB 40 jM ::
    decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat pos) status p) ++ CB 32 jC :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 pos) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) (Z_to_bv 64 k)
           (Z_to_bv 64 status) (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x1309c) fc None m (seg_rom rsegs)).

(* the exit 0x13678 from the six pieces of the frame *)
Lemma dloop_exit : forall x3 x4 F fc m0 Sp lo body bb j0 w10 saved Q,
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (m : word -> option byte) OC EC jM DC jC,
  cells_size OC = 120%nat -> cells_size EC = 80%nat -> cells_size DC = 40%nat ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body) -> rw_cells rsegs m (Sp + 32) OC ->
  rw_cells rsegs m (Sp + 152) EC -> rw_cells rsegs m (Sp + 232) [CB 40 jM] ->
  rw_cells rsegs m (Sp + 272) DC -> rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x13678) fc None m (seg_rom rsegs)).
Proof.
  intros x3 x4 F fc m0 Sp lo body bb j0 w10 saved Q DX r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20
    r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 m OC EC jM DC jC SO SE SD MU WM MI ST BA H1 H2 H3 H4 H5 H6.
  destruct (dloop_exit_frame m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body) OC EC jM DC jC saved eq_refl SO SE SD
    H1 H2 H3 H4 H5 H6) as [jj J].
  exact (DX r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    m jj MU WM MI ST BA J).
Qed.

Lemma dloop_decoder_at : forall body cpad len next so p d',
  dd_c d' = DgnCursor len next so -> dd_p d' = p ->
  decoder_cells body cpad d' = decoder_cells body cpad (decoder_at len (Z.to_nat next) so p).
Proof.
  intros body cpad len next so p [[l n s] pp] Ec Ep. cbn in Ec, Ep. injection Ec as -> -> ->. subst pp.
  unfold decoder_cells, decoder_at. cbn [dd_c dd_p dc_len dc_pos dc_status]. rewrite Nat2Z.id. reflexivity.
Qed.

(* the latch 0x131d0: s0 = o.next, s7 = o.status_out, steps + 1, then the head or the exit *)
Lemma dloop_latch : forall x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q,
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (k : Z) (o : owed) (p1 p2 : list byte) (EC : list cell) (jM cpad jC : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= ow_next o <= Z.of_nat (length bb) -> lp_st (ow_status_out o) ->
  dloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved p (k + 1) ->
  cells_size EC = 80%nat ->
  forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body) ->
  rw_cells rsegs m (Sp + 32) (owed_cells p1 p2 o) ->
  rw_cells rsegs m (Sp + 152) EC -> rw_cells rsegs m (Sp + 232) [CB 40 jM] ->
  rw_cells rsegs m (Sp + 272)
    (decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat (ow_next o)) (ow_status_out o) p)) ->
  rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) (Z_to_bv 64 k)
           x23 (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1) x28 x29 x30 x31)
        F (Z_to_bv 64 0x131d0) fc None m (seg_rom rsegs)).
Proof.
  intros x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o p1 p2 EC jM cpad jC Hk Hn Hs IH SE
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 m MU WM MI ST BA
    H1 H2 H3 H4 H5 H6.
  pose proof SOK as (S0 & S1 & B0 & B1 & BL). pose proof LOK as (L0 & L3 & L4).
  pose proof (dloop_owed_latch m (Sp + 32) p1 p2 o (dloop_ro _ _ _ _ H2)) as RL.
  replace (Sp + 32 + 104) with (Sp + 136) in RL by lia.
  do 4 step.
  rewrite (dloop_zxb_b8 (ow_status_out o)) by (unfold lp_st in Hs; lia).
  destruct (Z_le_gt_dec (k + 1) (Z.of_nat (length bb))) as [Hk1|Hk1].
  - assert (C : negb (bv_ltu (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (k + 1))) = true)
      by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply negb_true_iff, Z.ltb_ge; lia).
    rewrite C; cbv iota.
    pose proof (dloop_to_CB _ _ _ _ H2) as H2'. rewrite owed_cells_size in H2'.
    pose proof (dloop_to_CB _ _ _ _ H3) as H3'. rewrite SE in H3'.
    pose proof (dloop_join6 m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body)
      [CB 120 (cells_bytes (owed_cells p1 p2 o))] [CB 80 (cells_bytes EC)] jM _ jC saved eq_refl eq_refl
      eq_refl (decoder_cells_size _ _ _) H1 H2' H3' H4 H5 H6) as J.
    exact (IH (ow_next o) (ow_status_out o) x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31
      m _ _ jM cpad jC ltac:(lia) Hn Hs MU WM MI ST BA J).
  - assert (C : negb (bv_ltu (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (k + 1))) = false)
      by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply negb_false_iff, Z.ltb_lt; lia).
    rewrite C; cbv iota. step.
    exact (dloop_exit x3 x4 F fc m0 Sp lo body bb j0 w10 saved Q DX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      m _ EC jM _ jC (owed_cells_size _ _ _) SE (decoder_cells_size _ _ _) MU WM MI ST BA H1 H2 H3 H4 H5 H6).
Qed.

(* beq / bne of two 64-bit values that are signed 64-bit integers *)
Lemma dloop_eqb_int64 : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  replace (2^64) with 18446744073709551616 in E by reflexivity.
  replace (2^63) with 9223372036854775808 in Hx, Hy by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* 0x131b0: reload o.m.code, check_events_fields when it is 1, the exit when it is 0, else the latch *)
Lemma dloop_tail : check_events_fields_contract ->
  forall x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q,
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (k : Z) (o : owed) (p1 p2 : list byte) (EC : list cell) (jM cpad jC : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= ow_next o <= Z.of_nat (length bb) -> lp_st (ow_status_out o) ->
  dloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved p (k + 1) ->
  cells_size EC = 80%nat ->
  -2^31 <= sm_code (ow_m o) < 2^31 ->
  (sm_code (ow_m o) = 1 -> exists mpad ev, EC = event_cells body mpad ev /\
     check_events_fields_ok (map bz bb) o ev = true) ->
  -2^31 <= se_kind (ow_e o) < 2^31 -> 0 <= sm_status (ow_m o) < 256 -> 0 <= sm_sysex_len (ow_m o) < 2^64 ->
  (sm_status (ow_m o) = 240 -> 0 <= sm_sysex_at (ow_m o) < Z.of_nat (length bb)) ->
  0 <= ow_lsb_missing o < 256 -> (se_kind (ow_e o) = SPEC_EV_SCRIBBLE -> 0 <= se_len (ow_e o) <= 8) ->
  forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 (Z_to_bv 64 0x103a4) w10 body) ->
  rw_cells rsegs m (Sp + 32) (owed_cells p1 p2 o) ->
  rw_cells rsegs m (Sp + 152) EC -> rw_cells rsegs m (Sp + 232) [CB 40 jM] ->
  rw_cells rsegs m (Sp + 272)
    (decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat (ow_next o)) (ow_status_out o) p)) ->
  rw_cells rsegs m (Sp + 312) (CB 32 jC :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (Sp + 88)) x20 (Z_to_bv 64 body) (Z_to_bv 64 k)
           x23 (Z_to_bv 64 (- Z.of_nat (length bb))) x25 (Z_to_bv 64 247) (Z_to_bv 64 1) x28 x29 x30 x31)
        F (Z_to_bv 64 0x131b0) fc None m (seg_rom rsegs)).
Proof.
  intros CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o p1 p2 EC jM cpad jC Hk Hn Hs IH SE
    Hc Hev C1 C2 C3 C4 C5 C6 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 m
    MU WM MI ST BA H1 H2 H3 H4 H5 H6.
  pose proof SOK as (S0 & S1 & B0 & B1 & BL). pose proof LOK as (L0 & L3 & L4).
  pose proof (dloop_owed_code m (Sp + 32) p1 p2 o (dloop_ro _ _ _ _ H2)) as RC.
  step. rewrite dloop_sx32_int by exact Hc.
  step. rewrite (dloop_eqb_int64 (sm_code (ow_m o)) 1) by lia.
  pose proof (owed_cells_size p1 p2 o) as SO. pose proof (decoder_cells_size body cpad
    (decoder_at (Z.of_nat (length bb)) (Z.to_nat (ow_next o)) (ow_status_out o) p)) as SD.
  destruct (Z.eqb_spec (sm_code (ow_m o)) 1) as [E1|E1].
  - cbn [negb]. cbv iota.
    do 4 step.
    destruct (Hev E1) as (mpad & ev & -> & OKf).
    eapply (dloop_cef_call CEF); [exact S0 | exact S1 | exact L0 | exact L3 | exact L4 | exact OKf | exact C1
      | exact C2 | exact C3 | exact C4 | exact C5 | exact C6 | exact BA | exact (dloop_ro _ _ _ _ H2)
      | exact (dloop_ro _ _ _ _ H3) | exact ST | exact MI | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU' WM' MI' ST'.
    unfold loop_fp in MU. transport_after_call rsegs m m' MU' WM'. clear MU' WM'. fold (loop_fp lo Sp) in MU.
    step. rewrite dloop_sx32_int by exact Hc.
    step. rewrite (dloop_eqb_int64 (sm_code (ow_m o)) 0) by lia.
    replace (sm_code (ow_m o) =? 0) with false by (rewrite E1; reflexivity). cbv iota.
    eapply (dloop_latch x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o p1 p2 _ jM cpad jC
      Hk Hn Hs IH SE); eassumption.
  - cbn [negb]. cbv iota.
    step. rewrite (dloop_eqb_int64 (sm_code (ow_m o)) 0) by lia.
    destruct (Z.eqb_spec (sm_code (ow_m o)) 0) as [E0|E0]; cbv iota.
    + exact (dloop_exit x3 x4 F fc m0 Sp lo body bb j0 w10 saved Q DX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ m _ EC jM _ jC SO SE SD MU WM MI ST BA H1 H2 H3 H4 H5 H6).
    + eapply (dloop_latch x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o p1 p2 _ jM cpad jC
        Hk Hn Hs IH SE); eassumption.
Qed.

Lemma dloop_bytes : forall bb, Forall (fun x => 0 <= x < 256) (map bz bb).
Proof.
  intros bb. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as [y [<- _]].
  pose proof (bz_range y) as H. change (2 ^ 8) with 256 in H. exact H.
Qed.

(* one pass from 0x13180 (o = owed_at complete): memset (&ev, 0, 80), diginet_decoder_next (&d, &ev),
   check_events_step, then dloop_tail *)
Lemma dloop_pass : memset_contract -> diginet_decoder_next_contract -> check_events_step_contract ->
  check_events_fields_contract ->
  forall x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q,
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (k pos status : Z),
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  dloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved p (k + 1) ->
  forall (m1 : word -> option byte) (oj jE jM cpad jC : list byte),
  munch (loop_fp lo Sp) m0 m1 -> wmono rsegs m0 m1 -> stk rsegs m1 lo Sp ->
  dend Q x3 x4 (Z_to_bv 64 k) F fc m1 Sp body bb j0 oj w10
    (CB 80 jE :: CB 40 jM :: decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat pos) status p) ++
     CB 32 jC :: saved)
    (owed_at (bzl bb) (Z.of_nat (length bb)) pos status).
Proof.
  intros MSC DNC CES CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k pos status Hk Hpos Hst IH
    m1 oj jE jM cpad jC MU1 WM1 ST1.
  unfold dend. intros r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r23 r25 r28 r29 r30 r31 m MUa WMa MI BA FR.
  pose proof SOK as (S0 & S1 & B0 & B1 & BL). pose proof LOK as (L0 & L3 & L4).
  pose proof (dloop_bytes bb) as Hb. unfold bzl in *.
  pose proof (dloop_owed_facts (map bz bb) (Z.of_nat (length bb)) pos status Hb Hpos Hst) as OF. cbv zeta in OF.
  destruct OF as (Om & On & Os & Ol & Ok1 & Ok2).
  pose proof (dloop_step_facts (map bz bb) (Z.of_nat (length bb)) pos status Hb Hpos Hst) as SF. cbv zeta in SF.
  destruct SF as (Sc & Ss & Ssx & Sl & Sn & So). rewrite <- Om in Sc, Ss, Ssx, Sl.
  set (o := owed_at (map bz bb) (Z.of_nat (length bb)) pos status) in *.
  assert (MU : munch (loop_fp lo Sp) m0 m).
  { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [|exact MUa].
    unfold sub_fp, loop_fp; cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM1 WMa) as WM.
  assert (ST : stk rsegs m lo Sp).
  { eapply (stk_transport_disjoint rsegs _ m1 m lo Sp ST1 MUa WMa). cbn [disjoint_from]. split; [lia | exact I]. }
  clear MU1 WM1 ST1 MUa WMa.
  destruct (dloop_split6 m Sp j0 (Z_to_bv 64 0x103a4) w10 body (owed_cells (ow_p1 oj) (ow_p2 oj) o) [CB 80 jE] jM
    (decoder_cells body cpad (decoder_at (Z.of_nat (length bb)) (Z.to_nat pos) status p)) jC saved FR
    (owed_cells_size _ _ _) eq_refl (decoder_cells_size _ _ _)) as (H1 & H2 & H3 & H4 & H5 & H6).
  clear FR.
  pose proof (owed_cells_size (ow_p1 oj) (ow_p2 oj) o) as SO.
  assert (SH : cells_size (fr_head j0 (Z_to_bv 64 0x103a4) w10 body) = 32%nat) by reflexivity.
  unfold loop_fp in MU.
  (* memset (&ev, 0, 80) *)
  do 4 step.
  eapply (dloop_memset_ev MSC); [exact S0 | exact S1 | exact H3 | exact MI |].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 H3'.
  transport_after_call rsegs m m2 MU2 WM2. clear MU2 WM2.
  (* diginet_decoder_next (&d, &ev) *)
  do 3 step.
  eapply (dloop_dnext_call DNC) with (pos := Z.to_nat pos); [exact S0 | exact S1 | exact L0 | exact L3 | exact L4
    | lia | exact Hst | exact H5
    | exact BA | exact H3' | exact ST | exact MI2 |].
  intros rd ev d' Eres t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' mpad m3 MU3 WM3 MI3 ST3
    H5' H3''.
  assert (Hd0 : dd_c (decoder_at (Z.of_nat (length bb)) (Z.to_nat pos) status p) =
    DgnCursor (Z.of_nat (length bb)) pos status) by (cbn; rewrite Z2Nat.id by lia; reflexivity).
  destruct (decoder_step_ok (map bz bb) _ _ _ _ rd ev d' Hb Hd0 Eres) as (Hrd & Hok & Hdc & Hdp).
  fold o in Hrd, Hok, Hdc. cbn [dd_p decoder_at] in Hdp.
  rewrite (dloop_decoder_at body cpad _ _ _ p d' Hdc Hdp) in H5'.
  clear ST.
  transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3.
  (* check_events_step (body, &o, rd, &ev) *)
  do 5 step.
  unfold events_step_ok in Hok. cbn [es_o es_rd es_ev] in Hok. apply andb_true_iff in Hok as [Hok1 Hok2].
  assert (Hc : -2^31 <= sm_code (ow_m o) < 2^31) by lia.
  assert (C3 : sm_status (ow_m o) = 240 -> sm_sysex_at (ow_m o) <> 0) by (intros E; specialize (Ssx E); lia).
  revert H3''. destruct (Z.eqb_spec rd 1) as [R1|R1]; intros H3''.
  - eapply (dloop_ces_call CES) with (ow := o) (p1 := ow_p1 oj) (p2 := ow_p2 oj); [exact S0 | exact S1 | exact L0
      | exact L3 | exact Hok1 | exact Hc | exact Ss | exact C3 | exact (dloop_ro _ _ _ _ H2)
      | exact (dloop_ro _ _ _ _ H3'') | exact ST3 | exact MI3 |].
    intros t0''' t1''' t2''' a0''' a1''' a2''' a3''' a4''' a5''' a6''' a7''' t3''' t4''' t5''' t6''' m4 MU4 WM4 MI4 ST4.
    clear ST3. transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4.
    fold (loop_fp lo Sp) in MU.
    eapply (dloop_tail CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o (ow_p1 oj) (ow_p2 oj)
      (event_cells body mpad ev) jM cpad jC Hk On Os IH eq_refl Hc); try eassumption.
    + intros _. exists mpad, ev. split; [reflexivity|]. rewrite <- Hrd, R1 in Hok2. exact Hok2.
    + lia.
    + lia.
    + intros E; specialize (Ssx E); lia.
    + lia.
  - assert (H3e : rw_cells rsegs m3 (Sp + 152) (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero)).
    { apply (dloop_rwc_bytes rsegs _ _ _ _ H3'' (dloop_ev0_wf body)). rewrite dloop_ev0_bytes.
      cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity. }
    assert (Hok0 : check_events_step_ok o rd dgn_event_zero = true).
    { unfold check_events_step_ok. rewrite <- Hrd, Z.eqb_refl.
      replace (rd =? 1) with false by (symmetry; apply Z.eqb_neq; exact R1). reflexivity. }
    eapply (dloop_ces_call CES) with (ow := o) (p1 := ow_p1 oj) (p2 := ow_p2 oj); [exact S0 | exact S1 | exact L0
      | exact L3 | exact Hok0 | exact Hc | exact Ss | exact C3 | exact (dloop_ro _ _ _ _ H2)
      | exact (dloop_ro _ _ _ _ H3e) | exact ST3 | exact MI3 |].
    intros t0''' t1''' t2''' a0''' a1''' a2''' a3''' a4''' a5''' a6''' a7''' t3''' t4''' t5''' t6''' m4 MU4 WM4 MI4 ST4.
    clear ST3 H3''. transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4.
    fold (loop_fp lo Sp) in MU.
    eapply (dloop_tail CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k o (ow_p1 oj) (ow_p2 oj)
      (event_cells body (repeat (Z_to_bv 8 0) 4) dgn_event_zero) jM cpad jC Hk On Os IH eq_refl Hc);
      try eassumption.
    + intros E. exfalso. apply R1. rewrite Hrd. exact E.
    + lia.
    + lia.
    + intros E; specialize (Ssx E); lia.
    + lia.
Qed.

(* the composition of the loop's footprint with a pass's set-up *)
Lemma dloop_munch_mid : forall lo Sp m0 m1 m2, lo + 160 <= Sp ->
  munch (loop_fp lo Sp) m0 m1 -> munch [(Sp + 32, Sp + 152)] m1 m2 -> munch (loop_fp lo Sp) m0 m2.
Proof.
  intros lo Sp m0 m1 m2 H M1 M2. eapply munch_trans; [exact M1|]. eapply munch_weaken; [|exact M2].
  unfold sub_fp, loop_fp; cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

Lemma dloop_stk_mid : forall lo Sp m1 m2, stk rsegs m1 lo Sp -> munch [(Sp + 32, Sp + 152)] m1 m2 ->
  wmono rsegs m1 m2 -> stk rsegs m2 lo Sp.
Proof.
  intros lo Sp m1 m2 ST MU WM. apply (stk_transport_disjoint rsegs _ m1 m2 lo Sp ST MU WM).
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* every pass, by induction on len + 1 - k *)
Lemma dloop_ind : memset_contract -> memcpy_contract -> diginet_decoder_next_contract ->
  check_events_step_contract -> check_events_fields_contract ->
  dstep_stmt -> dsysex_stmt -> dchan_stmt ->
  forall x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q,
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  dexit Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  forall (n : nat) (k : Z), Z.to_nat (Z.of_nat (length bb) + 1 - k) = n ->
  dloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved p k.
Proof.
  intros MSC MCC DNC CES CEF DS DSY DCH x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX n.
  induction n as [|n IHn]; intros k Hn; unfold dloop_head;
    intros pos status x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31 m oj jE jM cpad jC
      Hk Hpos Hst MU WM MI ST BA FR.
  { exfalso. lia. }
  pose proof (IHn (k + 1) ltac:(lia)) as IH. clear IHn.
  pose proof LOK as (L0 & L3 & L4).
  assert (Hst' : 0 <= status < 240) by (unfold lp_st in Hst; lia).
  assert (Loj : length oj = 120%nat).
  { pose proof (proj1 (proj1 FR)) as WF. apply cells_wf_app in WF. destruct WF as [_ [WF _]]. exact WF. }
  eapply (DS MSC); [exact SOK | exact Hpos | exact Hst' | exact BA | exact FR | exact MI | | | ].
  - intros _. exact (dloop_pass MSC DNC CES CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k pos status
      Hk Hpos Hst IH m oj jE jM cpad jC MU WM ST).
  - intros Hc1 Hs240. unfold dmid.
    intros r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r25 r28 r29 r30 r31 m' MU' WM' MI' BA' _ FR'.
    apply (DSY MSC MCC r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 k) r25 r28 r29 r30 r31
      F fc m' Sp body pos status bb j0 oj w10 _ Q SOK Hpos Hst' Hc1 (proj2 (Z.eqb_eq _ _) Hs240) Loj BA'
      ltac:(discriminate) FR' MI').
    exact (dloop_pass MSC DNC CES CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k pos status
      Hk Hpos Hst IH m' oj jE jM cpad jC (dloop_munch_mid lo Sp m0 m m' L3 MU MU') (wmono_trans rsegs _ _ _ WM WM')
      (dloop_stk_mid lo Sp m m' ST MU' WM')).
  - intros Hc1 Hs240. unfold dmid.
    intros r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r25 r28 r29 r30 r31 m' MU' WM' MI' BA' Hr25 FR'.
    apply (DCH MSC MCC r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 k) r25 r28 r29 r30 r31
      F fc m' Sp body pos status bb j0 oj w10 _ Q SOK Hpos Hst' Hc1 (proj2 (Z.eqb_neq _ _) Hs240) Loj BA'
      (fun _ => Hr25 ltac:(discriminate)) FR' MI').
    exact (dloop_pass MSC DNC CES CEF x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX k pos status
      Hk Hpos Hst IH m' oj jE jM cpad jC (dloop_munch_mid lo Sp m0 m m' L3 MU MU') (wmono_trans rsegs _ _ _ WM WM')
      (dloop_stk_mid lo Sp m m' ST MU' WM')).
Qed.

Theorem dloop_holds : dloop_stmt.
Proof.
  unfold dloop_stmt.
  intros MSC MCC DNC CES CEF DS DSY DCH x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK _ DX k.
  exact (dloop_ind MSC MCC DNC CES CEF DS DSY DCH x3 x4 F fc m0 Sp lo body bb j0 w10 saved p Q SOK LOK DX
    (Z.to_nat (Z.of_nat (length bb) + 1 - k)) k eq_refl).
Qed.
