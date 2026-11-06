(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the pieces shared by the walk of the inlined owed_at (fuzz_decode.c:127-150,
   with spec_event_of of fuzz/spec.h:392-499 inlined in it) in LLVMFuzzerTestOneInput on the UBSan image, the first
   half of the decoder loop's body from the loop head 0x12f10 to 0x131cc (LLVMFuzzerTestOneInput_owed.v):
   - rw_cells_app (a cell list at A is its two halves), rwc_bytes (a cell list may be reshaped by its bytes), and
     the byte forms of the stores and loads the segment makes (le1_lit, zxb_b8, rd_body);
   - msg_ok, the facts about a DgnSpec.v spec_msg_step result that the walk reads (msg_ok_step): the byte fields
     are bytes, the code is a small int, next is a size_t, and the payload of a message lies in the body;
   - owed_tail, the part of owed_at after spec_msg_step (owed_at_tail: owed_at is spec_msg_step then owed_tail);
   - owed_k, the state at 0x131cc that the segment hands to the rest of the loop (the continuation of every
     segment lemma), and owed_join, which puts the three parts of struct owed back together;
   - sms_call, mset_call and mcpy_call: the three callee contracts (lib/U/Prog/spec_msg_step_c.v, memset_c.v,
     memcpy_c.v) with every address of their post written as a Z, so that the caller's own cells and body bytes
     transport across the call. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import spec_msg_step_c memset_c memcpy_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- cells ---- *)

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, bytes_at_app, cells_size_app, Nat2Z.inj_add.
  split.
  - intros [[[W1 W2] [B1 B2]] (H0 & H1 & HW)].
    rewrite cells_bytes_length in B2 by exact W1.
    split.
    + split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply HW. lia.
  - intros [[[W1 B1] (H0 & H1 & HW1)] [[W2 B2] (H2 & H3 & HW2)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [Hl|Hl].
    + apply HW1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply HW2. lia.
Qed.

(* a cell list's meaning is its bytes: reshape it freely *)
Lemma rwc_bytes : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma rw_cells_cons : forall segs m A c cs,
  rw_cells segs m A (c :: cs) -> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs H. apply (rw_cells_app segs m A [c] cs) in H. cbn [cells_size] in H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

(* CB n bs at A is CB k (firstn k bs) at A and CB (n - k) (skipn k bs) at A + k *)
Lemma rw_cells_cut : forall segs m A n k bs, (k <= n)%nat ->
  rw_cells segs m A [CB n bs] ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros segs m A n k bs Hk H.
  assert (L : length bs = n) by (destruct H as [[[Hl _] _] _]; exact Hl).
  assert (H2 : rw_cells segs m A [CB k (firstn k bs); CB (n - k) (skipn k bs)]).
  { apply (rwc_bytes segs m A [CB n bs]); [exact H | | ].
    - cbn [cells_wf cell_wf]. rewrite firstn_length_le, length_skipn by lia. lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity. }
  apply rw_cells_cons in H2. cbn [csize] in H2. exact H2.
Qed.

(* ---- bytes ---- *)

Lemma b8_mod : forall x y, x mod 256 = y mod 256 -> b8 x = b8 y.
Proof.
  intros x y E. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact E.
Qed.

(* sb of a register Z_to_bv 64 z stores the byte b8 z *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply b8_mod.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_eq z (2 ^ 64)) by lia.
  replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + (- (2 ^ 56 * (z / 2 ^ 64))) * 256) by lia.
  apply Z.mod_add. lia.
Qed.

(* lbu of a cell b8 z, z a byte *)
Lemma zxb_b8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz.
Qed.

(* the body as DgnSpec.v reads it: every element a byte *)
Definition bytes_ok (b : list Z) : Prop := Forall (fun x => 0 <= x < 256) b.

Lemma byte_at_range : forall b i, bytes_ok b -> 0 <= byte_at b i < 256.
Proof.
  intros b i H. unfold byte_at. unfold bytes_ok in H.
  destruct (nth_in_or_default (Z.to_nat i) b 0) as [Hin|E].
  - rewrite Forall_forall in H. apply H. exact Hin.
  - rewrite E. lia.
Qed.

Lemma bytes_ok_bz : forall bb, bytes_ok (map bz bb).
Proof.
  intros bb. unfold bytes_ok. rewrite Forall_map. apply Forall_forall. intros x _. unfold bz.
  pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  exact R.
Qed.

(* byte i of the body, read at body + i *)
Lemma rd_body : forall m body bb i, bytes_at rsegs m body bb -> 0 <= i < Z.of_nat (length bb) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (body + i)) 1 = Some [b8 (byte_at (map bz bb) i)].
Proof.
  intros m body bb i H Hi.
  change (Z_to_bv 64 (body + i)) with (wa (body + i)).
  replace (body + i) with (body + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read rsegs m body bb (Z.to_nat i) 1 H ltac:(lia)).
  f_equal. unfold byte_at.
  assert (L : (Z.to_nat i < length bb)%nat) by lia.
  clear H Hi. revert L. generalize (Z.to_nat i) as k. intros k L.
  revert k L. induction bb as [|x bb IH]; intros [|k] L; cbn [length] in L; try lia.
  - cbn. f_equal. unfold b8, bz. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  - cbn [skipn map nth]. apply IH. lia.
Qed.

(* ---- spec_msg_step ---- *)

(* spec.h:311-313: the scan stops at or after where it starts, and inside the body *)
Lemma scan_f7_range : forall b len f i,
  i <= scan_f7 b len i f /\ (i <= len -> scan_f7 b len i f <= len).
Proof.
  intros b len f. induction f as [|f IH]; intros i; cbn [scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 247)) eqn:E; [|lia].
  apply andb_true_iff in E. destruct E as [E _]. apply Z.ltb_lt in E.
  specialize (IH (i + 1)). lia.
Qed.

(* what the walk reads of a spec_msg_step result: the code is an int in [-8, 1] (the lw of 0x12f44 and 0x12fa4 is
   its sign extension), the byte fields are bytes, next is a size_t (and in the body for a message), and a message's
   payload (sysex_at, sysex_len) lies in the body *)
Definition msg_ok (len : Z) (M : spec_msg) : Prop :=
  -8 <= sm_code M <= 1 /\
  0 <= sm_status M < 256 /\ 0 <= sm_d1 M < 256 /\ 0 <= sm_d2 M < 256 /\ 0 <= sm_status_out M < 256 /\
  0 <= sm_next M < 2 ^ 64 /\
  (sm_code M = 1 -> sm_next M <= len /\ 0 <= sm_sysex_at M /\ 0 <= sm_sysex_len M /\
                    sm_sysex_at M + sm_sysex_len M < len).

Lemma msg_ok_step : forall b len pos st, bytes_ok b -> 0 <= len < 2 ^ 64 -> 0 <= pos < 2 ^ 64 -> 0 <= st < 256 ->
  msg_ok len (spec_msg_step b len pos st).
Proof.
  intros b len pos st Hb Hlen Hpos Hst.
  pose proof (byte_at_range b pos Hb) as L0.
  pose proof (byte_at_range b (pos + 1) Hb) as L1.
  pose proof (byte_at_range b (pos + 1 + 1) Hb) as L2.
  pose proof (scan_f7_range b len (Z.to_nat (len - (pos + 1))) (pos + 1)) as [S1 S2].
  unfold spec_msg_step, msg_ok, SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS. cbv zeta.
  repeat match goal with
  | |- context [if ?c then _ else _] => destruct c eqn:?
  end; cbn -[Z.land byte_at scan_f7]; lia.
Qed.

(* ---- owed_at ---- *)

(* fuzz_decode.c:136-149: owed_at after spec_msg_step, for a message M *)
Definition owed_tail (b : list Z) (len : Z) (M : spec_msg) : owed :=
  let e := spec_event_of b M in
  if negb (se_kind e =? SPEC_EV_FADER) then Owed M e 0 (sm_next M) (sm_status_out M)
  else
    let lsb := spec_msg_step b len (sm_next M) (sm_status_out M) in
    if (sm_code lsb =? 1) && (Z.land (sm_status lsb) 240 =? 176) && (sm_d1 lsb =? 32 + sm_d1 M)
    then
      Owed M (se_with_value e (u16 (Z.lor (se_value e) (u16 (Z.land (Z.shiftr (sm_d2 lsb) 4) 7)))))
        0 (sm_next lsb) (sm_status_out lsb)
    else Owed M e 1 (sm_next M) (sm_status_out M).

Lemma owed_at_tail : forall b len pos st,
  owed_at b len pos st =
  (if negb (sm_code (spec_msg_step b len pos st) =? 1)
   then Owed (spec_msg_step b len pos st) se_zero 0 (sm_next (spec_msg_step b len pos st))
          (sm_status_out (spec_msg_step b len pos st))
   else owed_tail b len (spec_msg_step b len pos st)).
Proof. reflexivity. Qed.

(* a step whose event is not a fader keeps o.next and o.status_out and lsb_missing = 0 *)
Lemma owed_tail_nf : forall b len M, se_kind (spec_event_of b M) <> 1 ->
  owed_tail b len M = Owed M (spec_event_of b M) 0 (sm_next M) (sm_status_out M).
Proof.
  intros b len M H. unfold owed_tail. cbv zeta.
  replace (negb (se_kind (spec_event_of b M) =? SPEC_EV_FADER)) with true
    by (symmetry; apply negb_true_iff, Z.eqb_neq; exact H).
  reflexivity.
Qed.

(* spec.h:397-411, the note family *)
Lemma seo_note : forall b M, Z.land (sm_status M) 240 = 144 ->
  spec_event_of b M =
    (if (24 <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? 29)
     then {| se_kind := 4; se_strip := 0; se_button := sm_d1 M; se_zone := Z.land (sm_d2 M) 63;
             se_on := Z.land (Z.shiftr (sm_d2 M) 6) 1; se_right := 0; se_addr := 0; se_device := 0;
             se_len := 0; se_dots := 0; se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0;
             se_text := repeat 0 8; se_seg := repeat 0 8 |}
     else {| se_kind := (if sm_d1 M =? 9 then 2 else 3); se_strip := Z.land (sm_d2 M) 63;
             se_button := sm_d1 M; se_zone := 0; se_on := Z.land (Z.shiftr (sm_d2 M) 6) 1;
             se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0;
             se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
             se_seg := repeat 0 8 |}).
Proof. intros b M H. unfold spec_event_of. rewrite H. reflexivity. Qed.

Lemma owed_tail_note : forall b len M, Z.land (sm_status M) 240 = 144 ->
  owed_tail b len M = Owed M (spec_event_of b M) 0 (sm_next M) (sm_status_out M).
Proof.
  intros b len M H. apply owed_tail_nf. rewrite (seo_note b M H).
  destruct ((24 <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? 29)); cbn [se_kind];
    [lia | destruct (sm_d1 M =? 9); lia].
Qed.

(* spec.h:412-427, the control change family *)
Lemma seo_cc : forall b M, Z.land (sm_status M) 240 = 176 ->
  spec_event_of b M =
    (if sm_d1 M <? 32
     then {| se_kind := 1; se_strip := sm_d1 M; se_button := 0; se_zone := 0; se_on := 0;
             se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0;
             se_value := u16 (Z.shiftl (sm_d2 M) 3); se_mask := 0; se_delta := 0; se_segments := 0;
             se_text := repeat 0 8; se_seg := repeat 0 8 |}
     else if sm_d1 M =? 92
     then {| se_kind := 6; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
             se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0; se_mask := 0;
             se_delta := s16 (sm_d2 M - 64); se_segments := 0; se_text := repeat 0 8;
             se_seg := repeat 0 8 |}
     else if (64 <=? sm_d1 M) && (sm_d1 M <? 88)
     then {| se_kind := 5; se_strip := u8 (sm_d1 M - 64); se_button := 0; se_zone := 0; se_on := 0;
             se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0; se_value := 0;
             se_mask := 0; se_delta := s16 (sm_d2 M - 64); se_segments := 0; se_text := repeat 0 8;
             se_seg := repeat 0 8 |}
     else se_other 0).
Proof.
  intros b M H. unfold spec_event_of. rewrite H.
  replace (176 =? 144) with false by reflexivity. cbv iota. reflexivity.
Qed.

(* spec.h:412-417 with the lookahead of fuzz_decode.c:139-149: the fader *)
Lemma owed_tail_fader : forall b len M, Z.land (sm_status M) 240 = 176 -> sm_d1 M < 32 ->
  owed_tail b len M =
    (let e := {| se_kind := 1; se_strip := sm_d1 M; se_button := 0; se_zone := 0; se_on := 0;
                 se_right := 0; se_addr := 0; se_device := 0; se_len := 0; se_dots := 0;
                 se_value := u16 (Z.shiftl (sm_d2 M) 3); se_mask := 0; se_delta := 0;
                 se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |} in
     let lsb := spec_msg_step b len (sm_next M) (sm_status_out M) in
     if (sm_code lsb =? 1) && (Z.land (sm_status lsb) 240 =? 176) && (sm_d1 lsb =? 32 + sm_d1 M)
     then Owed M (se_with_value e (u16 (Z.lor (se_value e) (u16 (Z.land (Z.shiftr (sm_d2 lsb) 4) 7)))))
            0 (sm_next lsb) (sm_status_out lsb)
     else Owed M e 1 (sm_next M) (sm_status_out M)).
Proof.
  intros b len M H1 H2. unfold owed_tail. rewrite (seo_cc b M H1).
  replace (sm_d1 M <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* the other three control changes (jog, V-Pot, OTHER) have no lookahead *)
Lemma owed_tail_cc : forall b len M, Z.land (sm_status M) 240 = 176 -> 32 <= sm_d1 M ->
  owed_tail b len M = Owed M (spec_event_of b M) 0 (sm_next M) (sm_status_out M).
Proof.
  intros b len M H1 H2. apply owed_tail_nf. rewrite (seo_cc b M H1).
  replace (sm_d1 M <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (sm_d1 M =? 92); [cbn [se_kind]; lia|].
  destruct ((64 <=? sm_d1 M) && (sm_d1 M <? 88)); cbn [se_kind se_other];
    try unfold SPEC_EV_OTHER; lia.
Qed.

(* spec.h:428-429, neither family and not a system exclusive *)
Lemma seo_plain : forall b M, Z.land (sm_status M) 240 <> 144 -> Z.land (sm_status M) 240 <> 176 ->
  sm_status M <> 240 -> spec_event_of b M = se_other 0.
Proof.
  intros b M H1 H2 H3. unfold spec_event_of.
  replace (Z.land (sm_status M) 240 =? 144) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.land (sm_status M) 240 =? 176) with false by (symmetry; apply Z.eqb_neq; exact H2).
  replace (negb (sm_status M =? 240)) with true
    by (symmetry; apply negb_true_iff, Z.eqb_neq; exact H3).
  reflexivity.
Qed.

(* 0x13000-0x13004 and 0x13288-0x13290: `slli k, x, 57` then `srli k, k, 63` is bit 6 of a byte x *)
Lemma b01_eq : forall x y, 0 <= x < 2 -> 0 <= y < 2 -> Z.testbit x 0 = Z.testbit y 0 -> x = y.
Proof.
  intros x y Hx Hy H.
  assert (Dx : x = 0 \/ x = 1) by lia. assert (Dy : y = 0 \/ y = 1) by lia.
  destruct Dx as [->| ->]; destruct Dy as [->| ->]; cbn in H; congruence.
Qed.

Lemma shl_shr_bit : forall d s k, 0 <= d < 256 -> 0 <= k < 8 -> s + k = 63 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl d s))) 63 = Z.land (Z.shiftr d k) 1.
Proof.
  intros d s k Hd Hk Hs.
  assert (R : 0 <= bv_unsigned (Z_to_bv 64 (Z.shiftl d s)) < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (Z.shiftl d s))) as X.
    unfold bv_modulus in X. change (2 ^ Z.of_N 64) with (2 ^ 64) in X. lia. }
  apply b01_eq.
  - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 63 * 2) with (2 ^ 64). lia.
  - rewrite Z.land_comm. change 2 with (2 ^ 1).
    apply land_lt_pow2; [lia | apply Z.shiftr_nonneg; lia].
  - rewrite Z.shiftr_spec by lia. rewrite Z.add_0_l.
    rewrite unsigned_lit_wrap. change (2 ^ 64) with (2 ^ Z.of_nat 64).
    rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_low by lia.
    rewrite andb_true_r. rewrite Z.shiftl_spec by lia.
    rewrite Z.land_spec, Z.shiftr_spec, Z.add_0_l by lia.
    change (Z.testbit 1 0) with true. rewrite andb_true_r. f_equal. lia.
Qed.


(* ---- the state at 0x131cc ---- *)

(* what the segment hands on at 0x131cc for the owed o: memory changed only in o, lsb and spec_msg_step's frame
   below sp; o's 120 bytes at sp + 0x18; s0, s1 (len), s2 (body), s3, s4, s7 .. s11 as the loop keeps them *)
Definition owed_k (Q : machine_state -> Prop) (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body len : Z) (o : owed) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word)
         (m' : word -> option byte) (p1 p2 j56' : list byte),
    munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m0 m' ->
    wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
    rw_cells rsegs m' (Sp + 0x18) (owed_cells p1 p2 o) ->
    rw_cells rsegs m' (Sp + 0x150) [CB 56 j56'] ->
    rw_cells rsegs m' (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
         (Z_to_bv 64 len) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
         (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1)
         (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
         F (Z_to_bv 64 0x131cc) fc None m' (seg_rom rsegs)).

(* the frame and the body of the decoder loop (the premises of the segment) *)
Definition seg_env (Sp lo body : Z) (bb : list byte) : Prop :=
  0 <= lo /\ lo + 8192 <= Sp /\ Sp mod 16 = 0 /\ Sp + 496 <= 2 ^ 47 /\
  4096 <= body /\ body + Z.of_nat (length bb) <= lo.

(* the two inner cuts of the segment, both inside the `if (o.m.code == 1)` arm of owed_at:
   - at 0x12f5c, the event just zeroed by the second memset (o.e = se_zero, o.lsb_missing = 0);
   - at pc (0x12f70 the control change, 0x12ff4 the note, 0x1302c the rest), the event of spec.h:395
     (kind = OTHER) and a0 = o.m.status.
   In both, o.m is the message M, o.next and o.status_out are M's, s5 = M.next and s6 = M.status_out. *)
Definition at_ev0 (Q : machine_state -> Prop) (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
         (m : word -> option byte) (p1 p2 j56 : list byte),
    munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m0 m ->
    wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
    rw_cells rsegs m (Sp + 0x18) (spec_msg_cells M) ->
    rw_cells rsegs m (Sp + 0x50) (spec_event_cells se_zero) ->
    rw_cells rsegs m (Sp + 0x78) [C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (Sp + 0x7c) [CB 4 p1] ->
    rw_cells rsegs m (Sp + 0x80) [C8 (Z_to_bv 64 (sm_next M))] ->
    rw_cells rsegs m (Sp + 0x88) [C1 (b8 (sm_status_out M))] ->
    rw_cells rsegs m (Sp + 0x89) [CB 7 p2] ->
    rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
    rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
         (Z_to_bv 64 (Z.of_nat (length bb))) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
         (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (sm_next M))
         (Z_to_bv 64 (sm_status_out M)) x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13)
         (Z_to_bv 64 0x90) y28 y29 y30 y31)
         F (Z_to_bv 64 0x12f5c) fc None m (seg_rom rsegs)).

Definition at_ev1 (Q : machine_state -> Prop) (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb : list byte) (M : spec_msg) (pc : Z) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
         (m : word -> option byte) (p1 p2 j56 : list byte),
    munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m0 m ->
    wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
    rw_cells rsegs m (Sp + 0x18) (spec_msg_cells M) ->
    rw_cells rsegs m (Sp + 0x50) (spec_event_cells (se_other 0)) ->
    rw_cells rsegs m (Sp + 0x78) [C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (Sp + 0x7c) [CB 4 p1] ->
    rw_cells rsegs m (Sp + 0x80) [C8 (Z_to_bv 64 (sm_next M))] ->
    rw_cells rsegs m (Sp + 0x88) [C1 (b8 (sm_status_out M))] ->
    rw_cells rsegs m (Sp + 0x89) [CB 7 p2] ->
    rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
    rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
         (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (sm_status M)) y11 y12 y13 y14 y15 y16 y17
         (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (sm_next M))
         (Z_to_bv 64 (sm_status_out M)) x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13)
         (Z_to_bv 64 0x90) y28 y29 y30 y31)
         F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma rwc_eq : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros m A cs cs' H ->. exact H. Qed.

(* 0x12f44-0x12f48 and 0x12fa4-0x12fa8: the `lw` of a spec_msg code sign-extends it, and the `bne` against 1
   is the model's test (the code is one of 1, 0, -6, -7, -8) *)
Lemma sx32_code : forall c, -8 <= c <= 1 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c Hc.
  assert (D : c = -8 \/ c = -7 \/ c = -6 \/ c = -5 \/ c = -4 \/ c = -3 \/ c = -2 \/ c = -1 \/ c = 0 \/ c = 1)
    by lia.
  destruct D as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma code_br : forall c, -8 <= c <= 1 ->
  negb (bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 1)) = negb (c =? 1).
Proof.
  intros c Hc.
  assert (D : c = -8 \/ c = -7 \/ c = -6 \/ c = -5 \/ c = -4 \/ c = -3 \/ c = -2 \/ c = -1 \/ c = 0 \/ c = 1)
    by lia.
  destruct D as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* two adjacent cell lists are one *)
Lemma rw_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

(* struct owed from its parts: o.m at sp + 0x18, o.e at sp + 0x50, o.lsb_missing at sp + 0x78, the two padding
   runs at sp + 0x7c and sp + 0x89, o.next at sp + 0x80 and o.status_out at sp + 0x88 *)
Lemma owed_join : forall m Sp M E l nx so p1 p2,
  rw_cells rsegs m (Sp + 0x18) (spec_msg_cells M) ->
  rw_cells rsegs m (Sp + 0x50) (spec_event_cells E) ->
  rw_cells rsegs m (Sp + 0x78) [C4 (Z_to_bv 64 l)] ->
  rw_cells rsegs m (Sp + 0x7c) [CB 4 p1] ->
  rw_cells rsegs m (Sp + 0x80) [C8 (Z_to_bv 64 nx)] ->
  rw_cells rsegs m (Sp + 0x88) [C1 (b8 so)] ->
  rw_cells rsegs m (Sp + 0x89) [CB 7 p2] ->
  rw_cells rsegs m (Sp + 0x18) (owed_cells p1 p2 (Owed M E l nx so)).
Proof.
  intros m Sp M E l nx so p1 p2 H1 H2 H3 H4 H5 H6 H7.
  pose proof (rw_join m (Sp + 0x88) (Sp + 0x89) _ _ H6 H7 ltac:(cbn [cells_size csize]; lia)) as J6.
  pose proof (rw_join m (Sp + 0x80) (Sp + 0x88) _ _ H5 J6 ltac:(cbn [cells_size csize]; lia)) as J5.
  pose proof (rw_join m (Sp + 0x7c) (Sp + 0x80) _ _ H4 J5 ltac:(cbn [cells_size csize]; lia)) as J4.
  pose proof (rw_join m (Sp + 0x78) (Sp + 0x7c) _ _ H3 J4 ltac:(cbn [cells_size csize]; lia)) as J3.
  pose proof (rw_join m (Sp + 0x50) (Sp + 0x78) _ _ H2 J3
    ltac:(rewrite spec_event_cells_size; lia)) as J2.
  pose proof (rw_join m (Sp + 0x18) (Sp + 0x50) _ _ H1 J2 ltac:(rewrite spec_msg_cells_size; lia)) as J1.
  unfold owed_cells. cbn [ow_m ow_e ow_lsb_missing ow_next ow_status_out].
  cbn [app] in J1. exact J1.
Qed.

(* the 120 bytes of struct owed, as the walk uses them: o.m, the memset region (o.e and o.lsb_missing), the
   padding at 100, o.next, o.status_out, the padding at 113 *)
Lemma owed_split : forall m Sp j, rw_cells rsegs m (Sp + 0x18) [CB 120 j] ->
  exists j56 j44 j4 j8 j1 j7,
    rw_cells rsegs m (Sp + 0x18) [CB 56 j56] /\ rw_cells rsegs m (Sp + 0x50) [CB 44 j44] /\
    rw_cells rsegs m (Sp + 0x7c) [CB 4 j4] /\ rw_cells rsegs m (Sp + 0x80) [CB 8 j8] /\
    rw_cells rsegs m (Sp + 0x88) [CB 1 j1] /\ rw_cells rsegs m (Sp + 0x89) [CB 7 j7].
Proof.
  intros m Sp j H.
  pose proof (rw_cells_split_CB rsegs m (Sp + 0x18) [] 120 j [] [56; 44; 4; 8; 1; 7]%nat H eq_refl) as H2.
  cbn [app mk_CB_cells] in H2.
  apply rw_cells_cons in H2. destruct H2 as [A1 H2]. cbn [csize] in H2.
  replace (Sp + 0x18 + Z.of_nat 56) with (Sp + 0x50) in H2 by lia.
  apply rw_cells_cons in H2. destruct H2 as [A2 H2]. cbn [csize] in H2.
  replace (Sp + 0x50 + Z.of_nat 44) with (Sp + 0x7c) in H2 by lia.
  apply rw_cells_cons in H2. destruct H2 as [A3 H2]. cbn [csize] in H2.
  replace (Sp + 0x7c + Z.of_nat 4) with (Sp + 0x80) in H2 by lia.
  apply rw_cells_cons in H2. destruct H2 as [A4 H2]. cbn [csize] in H2.
  replace (Sp + 0x80 + Z.of_nat 8) with (Sp + 0x88) in H2 by lia.
  apply rw_cells_cons in H2. destruct H2 as [A5 H2]. cbn [csize] in H2.
  replace (Sp + 0x88 + Z.of_nat 1) with (Sp + 0x89) in H2 by lia.
  do 6 eexists. repeat (split; [eassumption|]). eassumption.
Qed.

(* the memsets' zero bytes as the zero event and a zero int *)
Lemma ev_zero : forall m A, rw_cells rsegs m A [CB 40 (repeat (b8 0) 40)] ->
  rw_cells rsegs m A (spec_event_cells se_zero).
Proof.
  intros m A H. apply (rwc_bytes rsegs m A _ _ H);
    [vm_compute; repeat first [exact I | reflexivity | split] | vm_compute; reflexivity].
Qed.

Lemma int_zero : forall m A, rw_cells rsegs m A [CB 4 (repeat (b8 0) 4)] -> rw_cells rsegs m A [C4 (Z_to_bv 64 0)].
Proof.
  intros m A H. apply (rwc_bytes rsegs m A _ _ H);
    [vm_compute; repeat first [exact I | reflexivity | split] | vm_compute; reflexivity].
Qed.

(* the 44 bytes memset at o.e: the zero event and o.lsb_missing = 0 *)
Lemma mset44 : forall m A, rw_cells rsegs m A [CB 44 (repeat (b8 0) 44)] ->
  rw_cells rsegs m A (spec_event_cells se_zero) /\ rw_cells rsegs m (A + 40) [C4 (Z_to_bv 64 0)].
Proof.
  intros m A H.
  assert (H2 : rw_cells rsegs m A [CB 40 (repeat (b8 0) 40); CB 4 (repeat (b8 0) 4)]).
  { apply (rwc_bytes rsegs m A _ _ H);
      [vm_compute; repeat first [exact I | reflexivity | split] | vm_compute; reflexivity]. }
  apply rw_cells_cons in H2. destruct H2 as [H2a H2b]. cbn [csize] in H2b.
  split; [apply ev_zero; exact H2a|]. replace (A + Z.of_nat 40) with (A + 40) in H2b by lia.
  apply int_zero. exact H2b.
Qed.

(* ---- the three callees, with Z addresses in the post ---- *)

(* spec_msg_step (b, len, pos, st, mp) at 0x13464, the caller's sp = Sp: the contract of
   lib/U/Prog/spec_msg_step_c.v with bv_unsigned sp read off *)
Lemma sms_call : spec_msg_step_contract ->
  forall (lo : Z) (bs junk : list byte)
         (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b len pos st mp Sp : Z),
    b <> 0 -> 0 <= len <= Z.of_nat (length bs) -> 0 <= pos < 2 ^ 64 -> 0 <= st < 256 ->
    bytes_at rsegs m b bs -> mp mod 8 = 0 -> rw_cells rsegs m mp [CB 56 junk] ->
    mp + 56 <= b \/ b + Z.of_nat (length bs) <= mp ->
    stk rsegs m lo Sp -> 0 <= Sp < 2 ^ 64 -> lo + 48 <= Sp ->
    mp + 56 <= Sp - 48 \/ Sp <= mp -> b + Z.of_nat (length bs) <= Sp - 48 \/ Sp <= b ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(mp, mp + 56); (Sp - 48, Sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo Sp /\
         rw_cells rsegs m' mp (spec_msg_cells (spec_msg_step (map bz bs) len pos st)))
      (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 len) (Z_to_bv 64 pos)
               (Z_to_bv 64 st) (Z_to_bv 64 mp) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SPEC_MSG_STEP) fc None m (seg_rom rsegs)).
Proof.
  intros SMS lo bs junk ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b len pos st mp Sp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  eapply evt_mono.
  - eapply (SMS ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m b len pos st mp lo bs junk);
      unfold SPEC_MSG_STEP_FRAME; rewrite ?(unsigned_lit Sp) by lia; assumption.
  - intros ms' PO. unfold SPEC_MSG_STEP_FRAME in PO. rewrite ?(unsigned_lit Sp) in PO by lia. exact PO.
Qed.

(* memset (A, 0, n) at 0x1c29c *)
Lemma mset_call : memset_contract ->
  forall (junk : list byte)
         (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n : Z),
    0 <= A < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    rw_cells rsegs m A [CB (Z.to_nat n) junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(A, A + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET junk ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp
    F fc m A n HA Hn FR MI.
  eapply evt_mono.
  - eapply (MSET ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk);
      rewrite ?(unsigned_lit A), ?(unsigned_lit n) by lia; assumption.
  - intros ms' PO. unfold memset_post in PO.
    rewrite ?(unsigned_lit A), ?(unsigned_lit n), ?(unsigned_lit 0) in PO by lia.
    change (Z_to_bv 8 (0 mod 256)) with (b8 0) in PO. exact PO.
Qed.

(* memcpy (A, src at S, n) at 0x1be98 *)
Lemma mcpy_call : memcpy_contract ->
  forall (src junk : list byte)
         (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S n : Z),
    0 <= A < 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> length src = Z.to_nat n ->
    bytes_at rsegs m S src -> rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
    S + n <= A \/ A + n <= S -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(A, A + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' A [CB (Z.to_nat n) src] /\ bytes_at rsegs m' S src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 memcpy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY src junk ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp
    F fc m A S n HA HS Hn Hl BA FR HD MI.
  eapply evt_mono.
  - eapply (MCPY ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
      rewrite ?(unsigned_lit A), ?(unsigned_lit S), ?(unsigned_lit n) by lia; assumption.
  - intros ms' PO. unfold memcpy_post in PO.
    rewrite ?(unsigned_lit A), ?(unsigned_lit S), ?(unsigned_lit n) in PO by lia. exact PO.
Qed.

(* ---- the event's cells, field by field (every offset of DgnLayout.spec_event_cells) ---- *)

Lemma ev_cells_unfold : forall E, spec_event_cells E =
  [ C4 (Z_to_bv 64 (se_kind E));
    C1 (b8 (se_strip E)); C1 (b8 (se_button E)); C1 (b8 (se_zone E)); C1 (b8 (se_on E));
    C1 (b8 (se_right E)); C1 (b8 (se_addr E)); C1 (b8 (se_device E)); C1 (b8 (se_len E));
    C1 (b8 (se_dots E)); C1 (b8 0);
    C2 (Z_to_bv 64 (se_value E)); C2 (Z_to_bv 64 (se_mask E)); C2 (Z_to_bv 64 (se_delta E));
    C1 (b8 (se_segments E));
    C1 (b8 (nth 0 (se_text E) 0)); C1 (b8 (nth 1 (se_text E) 0)); C1 (b8 (nth 2 (se_text E) 0));
    C1 (b8 (nth 3 (se_text E) 0)); C1 (b8 (nth 4 (se_text E) 0)); C1 (b8 (nth 5 (se_text E) 0));
    C1 (b8 (nth 6 (se_text E) 0)); C1 (b8 (nth 7 (se_text E) 0));
    C1 (b8 (nth 0 (se_seg E) 0)); C1 (b8 (nth 1 (se_seg E) 0)); C1 (b8 (nth 2 (se_seg E) 0));
    C1 (b8 (nth 3 (se_seg E) 0)); C1 (b8 (nth 4 (se_seg E) 0)); C1 (b8 (nth 5 (se_seg E) 0));
    C1 (b8 (nth 6 (se_seg E) 0)); C1 (b8 (nth 7 (se_seg E) 0));
    CB 3 [b8 0; b8 0; b8 0] ].
Proof. reflexivity. Qed.

(* ---- the comparisons the segment makes ---- *)

Lemma land_b : forall x k, 0 <= x < 256 -> 0 <= k -> 0 <= Z.land x k < 256.
Proof. intros x k Hx Hk. change 256 with (2 ^ 8) in *. apply land_lt_pow2; lia. Qed.

Lemma land_w : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k -> 0 <= Z.land x k < 2 ^ 64.
Proof. intros x k Hx Hk. apply land_lt_pow2; lia. Qed.

Lemma shiftr_b : forall x k, 0 <= x < 256 -> 0 <= k -> 0 <= Z.shiftr x k < 256.
Proof.
  intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with x; [apply Z.div_le_upper_bound; [lia|]|lia].
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). nia.
Qed.

(* a 64-bit compare of two values that do not wrap *)
Lemma beq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bleu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_leu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <=? b).
Proof. intros a b Ha Hb. unfold bv_leu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* a 64-bit compare whose left side is a subtraction that may wrap below zero (the `addi x, y, -k`
   of a range test): the wrapped value is at least 2^64 - 2^32, above every constant here *)
Lemma modw_cases : forall a, - 2 ^ 32 < a < 2 ^ 32 ->
  (0 <= a -> a mod 2 ^ 64 = a) /\ (a < 0 -> a mod 2 ^ 64 = a + 2 ^ 64).
Proof.
  intros a Ha. split; intros H.
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique a (2 ^ 64) (-1) (a + 2 ^ 64)) by lia. reflexivity.
Qed.

Lemma addw_ltu : forall a b c, 0 <= a < 2 ^ 32 -> - 2 ^ 32 < b <= 0 -> 0 <= c < 2 ^ 32 ->
  bv_ltu (Z_to_bv 64 (a + b)) (Z_to_bv 64 c) = (0 <=? a + b) && (a + b <? c).
Proof.
  intros a b c Ha Hb Hc. unfold bv_ltu. rewrite (unsigned_lit c) by lia. rewrite unsigned_lit_wrap.
  destruct (modw_cases (a + b) ltac:(lia)) as [Hp Hn].
  destruct (Z_le_gt_dec 0 (a + b)) as [H|H].
  - rewrite Hp by lia. replace (0 <=? a + b) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. reflexivity.
  - rewrite Hn by lia. replace (0 <=? a + b) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [andb]. destruct (Z.ltb_spec (a + b + 2 ^ 64) c); [exfalso; lia | reflexivity].
Qed.

Lemma addw_leu : forall a b c, 0 <= a < 2 ^ 32 -> - 2 ^ 32 < b <= 0 -> 0 <= c < 2 ^ 32 ->
  bv_leu (Z_to_bv 64 c) (Z_to_bv 64 (a + b)) = negb ((0 <=? a + b) && (a + b <? c)).
Proof.
  intros a b c Ha Hb Hc. unfold bv_leu. rewrite (unsigned_lit c) by lia. rewrite unsigned_lit_wrap.
  destruct (modw_cases (a + b) ltac:(lia)) as [Hp Hn].
  destruct (Z_le_gt_dec 0 (a + b)) as [H|H].
  - rewrite Hp by lia. replace (0 <=? a + b) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. destruct (Z.ltb_spec (a + b) c) as [Hl|Hl]; cbn [negb];
      destruct (Z.leb_spec c (a + b)); first [reflexivity | exfalso; lia].
  - rewrite Hn by lia. replace (0 <=? a + b) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [andb negb]. destruct (Z.leb_spec c (a + b + 2 ^ 64)); [reflexivity | exfalso; lia].
Qed.


(* the same for a wider field: `slli k, x, s` then `srli k, k, r` with r + w = 64 and s + k + w = 64 *)
Lemma shl_shr_bits : forall d s k w r, 0 <= d < 256 -> 0 <= k -> 0 < w -> 0 <= s -> s + k + w = 64 ->
  r + w = 64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl d s))) r = Z.land (Z.shiftr d k) (Z.ones w).
Proof.
  intros d s k w r Hd Hk Hw Hs0 Hs Hr.
  replace r with (64 - w) by lia.
  rewrite unsigned_lit_wrap. rewrite <- (Z.land_ones _ 64) by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia. rewrite !Z.land_spec.
  rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i w).
  - rewrite (Z.ones_spec_low 64 (i + (64 - w))) by lia.
    rewrite (Z.ones_spec_low w i) by lia. rewrite !andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64 (i + (64 - w))) by lia.
    rewrite (Z.ones_spec_high w i) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma shl57_shr61 : forall d, 0 <= d < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl d 57))) 61 = Z.land (Z.shiftr d 4) 7.
Proof. intros d Hd. rewrite (shl_shr_bits d 57 4 3 61) by lia. reflexivity. Qed.

(* a bound for the fader's `or` *)
Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n ->
  0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high n a k), (Z_testbit_high n b k) by lia. reflexivity.
Qed.

(* 0x13188: `seqz x, y` after `addi y, z, -k` *)
Lemma sltiu1_addw : forall a b, 0 <= a < 2 ^ 32 -> - 2 ^ 32 < b <= 0 ->
  v_sltiu (Z_to_bv 64 (a + b)) 1 = Z_to_bv 64 (if a + b =? 0 then 1 else 0).
Proof.
  intros a b Ha Hb. unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (modw_cases (a + b) ltac:(lia)) as [Hp Hn].
  destruct (Z_le_gt_dec 0 (a + b)) as [H|H].
  - rewrite Hp by lia. destruct (Z.eqb_spec (a + b) 0) as [E|E].
    + rewrite E. reflexivity.
    + destruct (Z.ltb_spec (a + b) 1); [exfalso; lia | reflexivity].
  - rewrite Hn by lia. destruct (Z.eqb_spec (a + b) 0) as [E|E]; [exfalso; lia|].
    destruct (Z.ltb_spec (a + b + 2 ^ 64) 1); [exfalso; lia | reflexivity].
Qed.

(* `andi x, x, 0xff` after such a subtraction *)
Lemma land255_addw : forall a b, 0 <= a < 2 ^ 32 -> - 2 ^ 32 < b <= 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (a + b))) 255 = (a + b) mod 256.
Proof.
  intros a b Ha Hb. rewrite unsigned_lit_wrap.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
Qed.

(* the `lh` of a value the segment has just stored, below 2^15 *)
Lemma sx16_small : forall z, 0 <= z < 2 ^ 15 -> sx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx16. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with (2 ^ 16).
  change (2 ^ 16 `div` 2) with (2 ^ 15). unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite Z.mod_small by lia. lia.
Qed.

(* ---- branch conditions ---- *)

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
