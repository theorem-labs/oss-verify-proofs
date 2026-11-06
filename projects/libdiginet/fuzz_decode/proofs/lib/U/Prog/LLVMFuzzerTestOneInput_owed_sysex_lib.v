(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the pieces shared by the walk of the system exclusive part of the inlined
   spec_event_of (spec.h:428-499) in LLVMFuzzerTestOneInput on the UBSan image, 0x1302c-0x130c0 and the cases of the
   jump table at 0x103a4 (LLVMFuzzerTestOneInput_owed_sysex.v and LLVMFuzzerTestOneInput_owed_sysex_*.v):
   - sx_mem, the memory of the decoder loop at a cut of the segment (the frame, the body and the cells of struct owed
     with the event e), and sx_close: at 0x131cc such a state hands the owed (m, e, 0, m.next, m.status_out) to
     owed_k;
   - at_sx, the state at the entry of a case of the jump table (0x130c4 ring, 0x13268 meter, 0x13230 LEDs, 0x132f0
     counter, 0x13344 scribble): a0 = pl = s + 3, a1 = s = body + m.sysex_at, a2 = m.sysex_len,
     a3 = pn = m.sysex_len - 3, and the event OTHER with the device byte s[1] (spec.h:434); sx_env, the facts on
     the frame and the message every case reads (a system exclusive of the maker SPEC_MAKER, at least 3 bytes);
   - owed_tail_sx: no event of this part of spec_event_of is a fader, so owed_tail is the owed of the message;
   - the equation of spec_event_of on each path through spec.h:428-499 (seo_sx_short, seo_sx_maker, seo_sx_other,
     seo_ring, seo_meter, seo_leds, seo_counter, seo_scribble, seo_system);
   - the values the walk computes: seqz of a pointer (0x13040, seqz_pos), a byte fact checked on its 256 values
     (enum256, for the rotation of fn at 0x1308c-0x1309c), the sign-extending 32-bit arithmetic of the loops
     (swrap32_small, swrap32_neg, unsigned_neg);
   - the tactics: sx_fin (the hand-over to owed_k at 0x131cc), sx_mem_solve (sx_mem from the walk's hypotheses),
     rd_step (a lbu of a body byte), fold_closed_z (the closed values of the jump through the table as literals),
     sx_env_facts. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout
  LLVMFuzzerTestOneInput_owed_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---- the state at a cut ---- *)

(* the memory of the decoder loop with the event e in o.e: the frame and the body as at_ev1 has them *)
Definition sx_mem (m0 m : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg) (E : spec_event)
    (p1 p2 j56 : list byte) : Prop :=
  munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m0 m /\
  wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo Sp /\ bytes_at rsegs m body bb /\
  rw_cells rsegs m (Sp + 0x18) (spec_msg_cells M) /\
  rw_cells rsegs m (Sp + 0x50) (spec_event_cells E) /\
  rw_cells rsegs m (Sp + 0x78) [C4 (Z_to_bv 64 0)] /\
  rw_cells rsegs m (Sp + 0x7c) [CB 4 p1] /\
  rw_cells rsegs m (Sp + 0x80) [C8 (Z_to_bv 64 (sm_next M))] /\
  rw_cells rsegs m (Sp + 0x88) [C1 (b8 (sm_status_out M))] /\
  rw_cells rsegs m (Sp + 0x89) [CB 7 p2] /\
  rw_cells rsegs m (Sp + 0x150) [CB 56 j56] /\
  rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)].

(* 0x131cc with the event e in o.e: the owed of the message, with lsb_missing = 0 *)
Lemma sx_close : forall (Q : machine_state -> Prop) (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg) (E : spec_event)
    (p1 p2 j56 : list byte)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word),
  sx_mem m0 m Sp lo body bb M E p1 p2 j56 ->
  owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb)) (Owed M E 0 (sm_next M) (sm_status_out M)) ->
  evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
       (Z_to_bv 64 (Z.of_nat (length bb))) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
       (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1)
       (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
       F (Z_to_bv 64 0x131cc) fc None m (seg_rom rsegs)).
Proof.
  intros Q gp tp x23 F fc m0 m Sp lo body bb M E p1 p2 j56
    y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31
    (MU & WM & MI & ST & BA & HM & HE & HL & HP1 & HN & HS & HP2 & H150 & H10) K.
  unfold owed_k in K. apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
  apply (owed_join _ _ _ _ _ _ _ p1 p2); assumption.
Qed.

(* the entry of a case of the jump table: a0 = pl, a1 = s, a2 = m.sysex_len, a3 = pn; the event is OTHER with the
   device byte s[1] *)
Definition at_sx (Q : machine_state -> Prop) (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg) (pc : Z) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word)
         (m : word -> option byte) (p1 p2 j56 : list byte),
    y10 = Z_to_bv 64 (body + sm_sysex_at M + 3) -> y11 = Z_to_bv 64 (body + sm_sysex_at M) ->
    y12 = Z_to_bv 64 (sm_sysex_len M) -> y13 = Z_to_bv 64 (sm_sysex_len M - 3) ->
    sx_mem m0 m Sp lo body bb M (se_other (byte_at (map bz bb) (sm_sysex_at M + 1))) p1 p2 j56 ->
    evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
         (Z_to_bv 64 (Z.of_nat (length bb))) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
         (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1)
         (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
         F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the facts every case reads: the body, the frame and the payload s .. s + n - 1 of the message, n >= 3 *)
Definition sx_env (Sp lo body : Z) (bb : list byte) (M : spec_msg) : Prop :=
  seg_env Sp lo body bb /\ msg_ok (Z.of_nat (length bb)) M /\ sm_code M = 1 /\ sm_status M = 240 /\
  3 <= sm_sysex_len M /\ byte_at (map bz bb) (sm_sysex_at M) = 19.

(* ---- the model ---- *)

(* spec.h:428-499 has no fader: o is the owed of the message (fuzz_decode.c:136-137) *)
Lemma owed_tail_sx : forall b len M, Z.land (sm_status M) 240 <> 144 -> Z.land (sm_status M) 240 <> 176 ->
  owed_tail b len M = Owed M (spec_event_of b M) 0 (sm_next M) (sm_status_out M).
Proof.
  intros b len M H1 H2. apply owed_tail_nf. unfold spec_event_of.
  replace (Z.land (sm_status M) 240 =? 144) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.land (sm_status M) 240 =? 176) with false by (symmetry; apply Z.eqb_neq; exact H2).
  cbv beta iota zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [se_kind se_other];
    unfold SPEC_EV_OTHER, SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS, SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER,
      SPEC_EV_SYSTEM; lia.
Qed.

(* the comparisons of two literals in the goal, evaluated *)
Ltac zlit_cmp :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => is_Zlit x; is_Zlit y;
      let v := eval vm_compute in (Z.eqb x y) in change (Z.eqb x y) with v
  | |- context [Z.ltb ?x ?y] => is_Zlit x; is_Zlit y;
      let v := eval vm_compute in (Z.ltb x y) in change (Z.ltb x y) with v
  end;
  cbv beta iota delta [negb orb andb].

(* spec_event_of for a status 0xf0, to the tests of spec.h:431 *)
Ltac seo_prep H :=
  unfold spec_event_of; rewrite H; cbv zeta;
  unfold SPEC_MAKER, SPEC_FN_RING, SPEC_FN_METER, SPEC_FN_LEDS, SPEC_FN_COUNTER, SPEC_FN_SCRIBBLE, SPEC_FN_SYSTEM,
    SPEC_CHARS_MAX, SPEC_DIGITS;
  replace (Z.land 240 240) with 240 by reflexivity; zlit_cmp.

(* spec.h:431: fewer than 3 bytes *)
Lemma seo_sx_short : forall b M, sm_status M = 240 -> sm_sysex_len M < 3 -> spec_event_of b M = se_other 0.
Proof.
  intros b M H Hn. seo_prep H.
  replace (sm_sysex_len M <? 3) with true by (symmetry; apply Z.ltb_lt; exact Hn). reflexivity.
Qed.

(* spec.h:431: another maker *)
Lemma seo_sx_maker : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M ->
  byte_at b (sm_sysex_at M) <> 19 -> spec_event_of b M = se_other 0.
Proof.
  intros b M H Hn Hmk. seo_prep H.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn).
  replace (byte_at b (sm_sysex_at M) =? 19) with false by (symmetry; apply Z.eqb_neq; exact Hmk).
  reflexivity.
Qed.

(* spec.h:499: a function this model does not decode (0x50, 0x60, or not a multiple of 0x10 below 0x80) *)
Lemma seo_sx_other : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) <> 0 -> byte_at b (sm_sysex_at M + 2) <> 16 ->
  byte_at b (sm_sysex_at M + 2) <> 32 -> byte_at b (sm_sysex_at M + 2) <> 48 ->
  byte_at b (sm_sysex_at M + 2) <> 64 -> byte_at b (sm_sysex_at M + 2) <> 112 ->
  spec_event_of b M = se_other (byte_at b (sm_sysex_at M + 1)).
Proof.
  intros b M H Hn Hmk F0 F1 F2 F3 F4 F7. seo_prep H. rewrite Hmk. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn).
  rewrite (proj2 (Z.eqb_neq _ _) F0), (proj2 (Z.eqb_neq _ _) F1), (proj2 (Z.eqb_neq _ _) F2),
    (proj2 (Z.eqb_neq _ _) F3), (proj2 (Z.eqb_neq _ _) F4), (proj2 (Z.eqb_neq _ _) F7).
  reflexivity.
Qed.

(* spec.h:438-452, fn = SPEC_FN_RING *)
Lemma seo_ring : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 0 ->
  spec_event_of b M =
    (if negb (sm_sysex_len M - 3 =? 3) then se_other (byte_at b (sm_sysex_at M + 1))
     else {| se_kind := 7; se_strip := Z.land (byte_at b (sm_sysex_at M + 3)) 63; se_button := 0; se_zone := 0;
             se_on := 0; se_right := 0; se_addr := 0; se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
             se_dots := 0; se_value := 0;
             se_mask := ring_mask (byte_at b (sm_sysex_at M + 3)) (byte_at b (sm_sysex_at M + 3 + 1))
                          (byte_at b (sm_sysex_at M + 3 + 2));
             se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}).
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* spec.h:453-464, fn = SPEC_FN_METER *)
Lemma seo_meter : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 16 ->
  spec_event_of b M =
    (if negb (sm_sysex_len M - 3 =? 3) then se_other (byte_at b (sm_sysex_at M + 1))
     else {| se_kind := 8; se_strip := Z.land (byte_at b (sm_sysex_at M + 3)) 31; se_button := 0; se_zone := 0;
             se_on := 0; se_right := Z.land (Z.shiftr (byte_at b (sm_sysex_at M + 3)) 5) 1;
             se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
             se_dots := 0; se_value := 0;
             se_mask := u16 (Z.lor (Z.shiftl (Z.land (byte_at b (sm_sysex_at M + 3 + 1)) 127) 7)
                                   (Z.land (byte_at b (sm_sysex_at M + 3 + 2)) 127));
             se_delta := 0;
             se_segments := s8 (spec_segments (u16 (Z.lor (Z.shiftl (Z.land (byte_at b (sm_sysex_at M + 3 + 1)) 127) 7)
                                                           (Z.land (byte_at b (sm_sysex_at M + 3 + 2)) 127))));
             se_text := repeat 0 8; se_seg := repeat 0 8 |}).
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* spec.h:465-473, fn = SPEC_FN_LEDS *)
Lemma seo_leds : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 32 ->
  spec_event_of b M =
    (if negb (sm_sysex_len M - 3 =? 2) then se_other (byte_at b (sm_sysex_at M + 1))
     else {| se_kind := 9; se_strip := byte_at b (sm_sysex_at M + 3); se_button := 0; se_zone := 0; se_on := 0;
             se_right := 0; se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1);
             se_len := 0; se_dots := 0; se_value := 0; se_mask := byte_at b (sm_sysex_at M + 3 + 1); se_delta := 0;
             se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}).
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* spec.h:483-492, fn = SPEC_FN_COUNTER *)
Lemma seo_counter : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 48 ->
  spec_event_of b M =
    (if negb (sm_sysex_len M - 3 =? 10) then se_other (byte_at b (sm_sysex_at M + 1))
     else {| se_kind := 11; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
             se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
             se_dots := byte_at b (sm_sysex_at M + 3 + 1); se_value := 0; se_mask := 0; se_delta := 0;
             se_segments := 0; se_text := repeat 0 8;
             se_seg := map (fun k => byte_at b (sm_sysex_at M + 3 + 2 + 8 - 1 - k)) (zseq 8) |}).
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* spec.h:474-482, fn = SPEC_FN_SCRIBBLE *)
Lemma seo_scribble : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 64 ->
  spec_event_of b M =
    (if (sm_sysex_len M - 3 <? 3) || (8 <? sm_sysex_len M - 3 - 2)
     then se_other (byte_at b (sm_sysex_at M + 1))
     else {| se_kind := 10; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
             se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1);
             se_len := u8 (sm_sysex_len M - 3 - 2); se_dots := 0; se_value := 0; se_mask := 0; se_delta := 0;
             se_segments := 0;
             se_text := map (fun k => if k <? u8 (sm_sysex_len M - 3 - 2)
                                      then byte_at b (sm_sysex_at M + 3 + 2 + k) else 0) (zseq 8);
             se_seg := repeat 0 8 |}).
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* spec.h:493-495, fn = SPEC_FN_SYSTEM *)
Lemma seo_system : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M -> byte_at b (sm_sysex_at M) = 19 ->
  byte_at b (sm_sysex_at M + 2) = 112 ->
  spec_event_of b M =
    {| se_kind := 12; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0; se_addr := 0;
       se_device := byte_at b (sm_sysex_at M + 1); se_len := 0; se_dots := 0; se_value := 0; se_mask := 0;
       se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}.
Proof.
  intros b M H Hn Hmk Hfn. seo_prep H. rewrite Hmk, Hfn. zlit_cmp.
  replace (sm_sysex_len M <? 3) with false by (symmetry; apply Z.ltb_ge; exact Hn). reflexivity.
Qed.

(* ---- values ---- *)

(* 0x13040: seqz of a pointer that is not NULL *)
Lemma seqz_pos : forall a, 0 < a < 2 ^ 64 -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec a 1); [lia | reflexivity].
Qed.

(* a fact about one byte, checked on its 256 values *)
Lemma enum256 : forall P : Z -> bool, forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. apply H.
  replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia.
Qed.

(* the byte i of the body as a number *)
Lemma bat_range : forall bb i, 0 <= byte_at (map bz bb) i < 256.
Proof. intros bb i. apply byte_at_range, bytes_ok_bz. Qed.

(* bv_swrap 32 of a value already in [-2^31, 2^31) *)
Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite Z.mod_small by lia. lia.
Qed.

(* the 64-bit form of a small negative value, read back in 32 bits plus c (the addiw and addw of the loops) *)
Lemma swrap32_neg : forall x c, 0 <= x < 2 ^ 30 -> - 2 ^ 30 <= c < 2 ^ 30 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (- x)) + c) = c - x.
Proof.
  intros x c Hx Hc. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  destruct (Z.eq_dec x 0) as [->|N].
  - change ((- 0) mod 2 ^ 64) with 0. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (- x) (2 ^ 64) (-1) (2 ^ 64 - x)) by lia.
    replace (2 ^ 64 - x + c + 2 ^ 31) with ((c - x + 2 ^ 31) + 2 ^ 32 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* bv_unsigned of a small negative value *)
Lemma unsigned_neg : forall x, 0 < x < 2 ^ 63 -> bv_unsigned (Z_to_bv 64 (- x)) = 2 ^ 64 - x.
Proof.
  intros x Hx. rewrite unsigned_lit_wrap.
  rewrite <- (Z.mod_unique (- x) (2 ^ 64) (-1) (2 ^ 64 - x)) by lia. reflexivity.
Qed.

(* ---- tactics ---- *)

Lemma sx_mem_intro : forall (m0 m : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg)
    (E : spec_event) (p1 p2 j56 : list byte),
  munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
  rw_cells rsegs m (Sp + 0x18) (spec_msg_cells M) ->
  rw_cells rsegs m (Sp + 0x50) (spec_event_cells E) ->
  rw_cells rsegs m (Sp + 0x78) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (Sp + 0x7c) [CB 4 p1] ->
  rw_cells rsegs m (Sp + 0x80) [C8 (Z_to_bv 64 (sm_next M))] ->
  rw_cells rsegs m (Sp + 0x88) [C1 (b8 (sm_status_out M))] ->
  rw_cells rsegs m (Sp + 0x89) [CB 7 p2] ->
  rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
  rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
  sx_mem m0 m Sp lo body bb M E p1 p2 j56.
Proof.
  intros. unfold sx_mem. repeat (split; [assumption|]). assumption.
Qed.

(* the sx_mem of the context, its event cells and the message's as the walk has unfolded them *)
Ltac sx_mem_goal :=
  first [ eassumption | unfold spec_msg_cells; assumption | rewrite ev_cells_unfold; assumption
        | match goal with |- ?G => fail 1000 "sx_mem: no hypothesis for" G end ].
Ltac sx_mem_solve := eapply sx_mem_intro; sx_mem_goal.

(* at 0x131cc, hand the owed of K's event to K *)
Ltac sx_fin K := eapply sx_close; [ eapply sx_mem_intro | exact K ]; sx_mem_goal.

(* a lbu of the body byte i: the step with rd_body for it *)
Ltac rd_step i :=
  lazymatch goal with
  | BA : bytes_at rsegs ?mm ?bd ?bs |- _ =>
      let HR := fresh "HR" in pose proof (rd_body mm bd bs i BA ltac:(lia)) as HR; step; clear HR
  end.

(* the closed arguments of Z_to_bv 64 in the goal as literals (the jump through the table reads its address) *)
Ltac fold_closed_z :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
      let v := eval vm_compute in e in is_Zlit v; change e with v
  end.

(* the facts of sx_env as hypotheses *)
Ltac sx_env_facts SXE :=
  let Hlo := fresh "Hlo" in let HloSp := fresh "HloSp" in let HSp16 := fresh "HSp16" in
  let HSp47 := fresh "HSp47" in let Hbody := fresh "Hbody" in let Hbb := fresh "Hbb" in
  let Hcode := fresh "Hcode" in let Hsta := fresh "Hsta" in let Hd1 := fresh "Hd1" in let Hd2 := fresh "Hd2" in
  let Hso := fresh "Hso" in let Hnx := fresh "Hnx" in let Hmsg := fresh "Hmsg" in let Hc1 := fresh "Hc1" in
  let E240 := fresh "E240" in let Hn3 := fresh "Hn3" in let Hmk := fresh "Hmk" in
  let Hnxl := fresh "Hnxl" in let Hsx0 := fresh "Hsx0" in let Hsn0 := fresh "Hsn0" in let Hsxn := fresh "Hsxn" in
  destruct SXE as ((Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb) &
                   (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg) & Hc1 & E240 & Hn3 & Hmk);
  destruct (Hmsg Hc1) as (Hnxl & Hsx0 & Hsn0 & Hsxn); clear Hmsg.
