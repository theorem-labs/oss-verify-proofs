(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the cut of the UBSan walk of diginet_decoder_next (lib/U/Prog/
   diginet_decoder_next_c.v) into its entry part and its decode part.
   - The entry part runs from 0x13fe4 through the call of diginet_msg_next on d->c (0x1401c), the result test
     (0x14028), memset (ev, 0, 80) (0x14038), the alignment check of ev (0x1403c) and memcpy (ev + 40, &m, 40)
     (0x14050), to 0x14054 (DN_DECODE). There the event is the model's zeroed event with the message
     (de_set_msg msg dgn_event_zero, kind not yet written), the message is at sp' + 0x48 (sp' = sp - 144), and s0 = ev,
     s1 = 1, s2 = d.
   - The decode part runs from DN_DECODE to 0x1429c (DN_RET, `mv a0, s1` and the epilogue), which every path of
     diginet_decode.c:115-157 reaches with s1 = 1: the note (0x14068), the sysex (0x140a4, the jump table at
     0x14128), the control changes (0x141d0) and the other statuses.
   rw_cells_split / rw_cells_join (lib/U/Prog/DgnCellsU.v, re-exported here) cut an rw_cells region at a cell
   boundary for a callee whose footprint is part of a bigger object.
   dn_seg_cont is what a decode-part lemma hands on at DN_RET: the memory changed only in the decoder, the event and
   the 72 bytes below the message (the fader's LSB message at sp' and peek cursor at sp' + 0x28), with the event and
   the decoder as the model's step gives them. msg_next_one gives the facts of the model's message and cursor when
   diginet_msg_next returns 1. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Export DgnCellsU.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout diginet_decoder_next_c.
Import ListNotations.
Open Scope Z_scope.

Definition DN_DECODE : Z := 0x14054.
Definition DN_RET : Z := 0x1429c.

(* the state at DN_RET a decode-part lemma reaches: s1 = 1, sp = spf, s3..s11, gp, tp, F, fc as at DN_DECODE;
   ra, s0, s2, a0..a7, t0..t6 any (the epilogue reloads ra, s0, s1, s2 from the frame) *)
Definition dn_seg_cont (Q : machine_state -> Prop) (spf : Z)
    (gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (d ev body : Z) (bb cpad mpad : list byte) (dc : dgn_decoder) : Prop :=
  forall (ra s0 s2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m' : word -> option byte),
    munch [(d, d + 40); (ev, ev + 80); (spf, spf + 72)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' ev (event_cells body mpad (dn_e bb dc)) ->
    rw_cells rsegs m' d (decoder_cells body cpad (dn_d bb dc)) ->
    evt rsegs Q
      (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 s0 (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DN_RET) fc None m' (seg_rom rsegs)).

(* the premises a decode-part lemma starts from at DN_DECODE (the entry part establishes them) *)
Definition dn_seg_pre (m : word -> option byte) (spf d ev body : Z) (bb cpad mpad junk : list byte)
    (dc : dgn_decoder) (msg : dgn_msg) (c1 : dgn_cursor) : Prop :=
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) /\
  d <> 0 /\ ev <> 0 /\ d mod 8 = 0 /\ ev mod 8 = 0 /\ spf mod 16 = 0 /\ body <> 0 /\
  dc_len (dd_c dc) = Z.of_nat (length bb) /\
  0 <= dc_pos (dd_c dc) <= dc_len (dd_c dc) /\
  st_ok (dc_status (dd_c dc)) /\
  bytes_at rsegs m body bb /\
  rw_cells rsegs m d (decoder_cells body cpad {| dd_c := c1; dd_p := dd_p dc |}) /\
  rw_cells rsegs m ev (event_cells body mpad (de_set_msg msg dgn_event_zero)) /\
  rw_cells rsegs m (spf + 72) (dmsg_cells body mpad msg) /\
  rw_cells rsegs m spf [CB 72 junk] /\
  (d + 40 <= ev \/ ev + 80 <= d) /\
  (d + 40 <= body \/ body + Z.of_nat (length bb) <= d) /\
  (ev + 80 <= body \/ body + Z.of_nat (length bb) <= ev) /\
  (d + 40 <= spf \/ spf + 144 <= d) /\
  (ev + 80 <= spf \/ spf + 144 <= ev) /\
  (body + Z.of_nat (length bb) <= spf \/ spf + 144 <= body) /\
  mem_inv rsegs m.

(* ---- facts of the model's message when diginet_msg_next returns 1 ---- *)

Lemma byte_at_map_range : forall (bb : list byte) i, 0 <= byte_at (map bv_unsigned bb) i < 256.
Proof.
  intros bb i. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length bb)) as [H|H].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact H).
    rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bb (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
  - rewrite nth_overflow by (rewrite length_map; exact H). lia.
Qed.

Lemma land80_high : forall x, 0 <= x < 256 -> Z.land x 0x80 <> 0 -> 0x80 <= x.
Proof.
  intros x Hx H. destruct (Z.ltb_spec x 0x80) as [L|L]; [|exact L].
  exfalso. apply H. change 0x80 with (2 ^ 7). apply zb_land_pow2_small; lia.
Qed.

Lemma u8_range : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

(* what the decode part reads of the message and what the fader's peek call needs of the cursor *)
Definition msg_one_facts (len : Z) (c : dgn_cursor) (msg : dgn_msg) (c1 : dgn_cursor) : Prop :=
  0 <= dm_status msg < 256 /\ 0 <= dm_d1 msg < 256 /\ 0 <= dm_d2 msg < 256 /\
  (dm_status msg = 0xf0 ->
     1 <= dm_sysex msg /\ 0 <= dm_sysex_len msg /\ dm_sysex msg + dm_sysex_len msg < len) /\
  (dm_status msg <> 0xf0 -> 0x80 <= dm_status msg < 0xf0) /\
  dc_len c1 = dc_len c /\ dc_pos c < dc_pos c1 <= dc_len c /\ st_ok (dc_status c1).

Lemma msg_channel_one : forall b c m0 status data_at running msg c1,
  (forall i, 0 <= byte_at b i < 256) ->
  0x80 <= status < 0xf0 -> dc_pos c <= data_at ->
  msg_channel b c m0 status data_at running = (1, msg, c1) ->
  msg_one_facts (dc_len c) c msg c1.
Proof.
  intros b c m0 status data_at running msg c1 HB HS HD H. unfold msg_channel in H; cbv zeta in H.
  pose proof (channel_data_len_range status) as Hn.
  destruct (dc_len c <? data_at + channel_data_len status) eqn:E1; [discriminate|].
  apply Z.ltb_ge in E1.
  destruct (first_high b data_at 0 (Z.to_nat (channel_data_len status))); [discriminate|].
  injection H as <- <-. unfold msg_one_facts; cbn [dm_status dm_d1 dm_d2 dm_sysex dm_sysex_len dc_len dc_pos dc_status].
  pose proof (HB data_at). pose proof (u8_range (if 1 <? channel_data_len status then byte_at b (data_at + 1) else 0)).
  unfold st_ok. repeat split; try lia.
Qed.

Lemma msg_next_one : forall (bb : list byte) c m0 msg c1,
  dc_len c = Z.of_nat (length bb) -> 0 <= dc_pos c -> st_ok (dc_status c) ->
  diginet_msg_next (map bv_unsigned bb) c m0 = (1, msg, c1) ->
  msg_one_facts (dc_len c) c msg c1.
Proof.
  intros bb c m0 msg c1 HL HP HS H.
  pose proof (byte_at_map_range bb) as HB.
  unfold diginet_msg_next in H; cbv zeta in H.
  destruct (dc_len c <=? dc_pos c) eqn:E0; [discriminate|]. apply Z.leb_gt in E0.
  destruct (byte_at (map bv_unsigned bb) (dc_pos c) =? 0xf0) eqn:E1.
  - pose proof (msg_scan_f7_ge (map bv_unsigned bb) (dc_len c) (Z.to_nat (dc_len c - (dc_pos c + 1)))
                  (dc_pos c + 1)) as G.
    destruct (dc_len c <=? msg_scan_f7 (map bv_unsigned bb) (dc_len c) (dc_pos c + 1)
                (Z.to_nat (dc_len c - (dc_pos c + 1)))) eqn:E2; [discriminate|].
    apply Z.leb_gt in E2. injection H as <- <-.
    unfold msg_one_facts; cbn [dm_status dm_d1 dm_d2 dm_sysex dm_sysex_len dc_len dc_pos dc_status].
    unfold st_ok. repeat split; try lia.
  - destruct (negb (Z.land (byte_at (map bv_unsigned bb) (dc_pos c)) 0x80 =? 0)) eqn:E2.
    + destruct (0xf0 <=? byte_at (map bv_unsigned bb) (dc_pos c)) eqn:E3; [discriminate|].
      apply Z.leb_gt in E3. apply negb_true_iff, Z.eqb_neq in E2.
      pose proof (land80_high _ (HB (dc_pos c)) E2).
      refine (msg_channel_one _ _ _ _ _ _ _ _ HB _ _ H); lia.
    + destruct (dc_status c =? 0) eqn:E3; [discriminate|]. apply Z.eqb_neq in E3.
      refine (msg_channel_one _ _ _ _ _ _ _ _ HB _ _ H); unfold st_ok in HS; lia.
Qed.
