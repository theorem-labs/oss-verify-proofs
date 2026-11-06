(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the segment of LLVMFuzzerTestOneInput on the UBSan image that is the inlined
   owed_at (fuzz_decode.c:127-150, with spec_event_of of fuzz/spec.h:392-499 inlined in it), the first half of
   the decoder loop's body, from the loop head 0x12f10 to 0x131cc. It is put together from
     _owed_head.v   0x12f10-0x12f5c  spec_msg_step (&o.m), o.next, o.status_out, the two memsets, code != 1;
     _owed_chan.v   0x12f5c-0x12f6c  e.kind = OTHER and the switch on status & 0xf0;
     _owed_note.v   0x12ff4-0x13028, 0x13184-0x13198  the note family;
     _owed_cc.v     0x12f70-0x12ff0, 0x13164-0x131c8  the control change family, with the fader's LSB
                    lookahead (the second spec_msg_step call, at sp + 0x150);
     _owed_sysex.v  0x1302c-0x130c0 and the eight cases of the jump table at 0x103a4.
   Every path ends at 0x131cc with the 120 bytes at sp + 0x18 holding DgnLayout.owed_cells of
   DgnDecHarness.owed_at. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout spec_msg_step_c memset_c
  memcpy_c LLVMFuzzerTestOneInput_owed_lib LLVMFuzzerTestOneInput_owed_head LLVMFuzzerTestOneInput_owed_chan
  LLVMFuzzerTestOneInput_owed_note LLVMFuzzerTestOneInput_owed_cc LLVMFuzzerTestOneInput_owed_sysex.
Import ListNotations.
Open Scope Z_scope.

Theorem owed_evt :
  spec_msg_step_contract -> memset_contract -> memcpy_contract ->
  forall (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sp lo body pos status : Z) (bb j120 j56 : list byte) (Q : machine_state -> Prop),
    0 <= lo -> lo + 8192 <= Sp -> Sp mod 16 = 0 -> Sp + 496 <= 2 ^ 47 ->
    4096 <= body -> body + Z.of_nat (length bb) <= lo ->
    0 <= pos < 2 ^ 64 -> 0 <= status < 2 ^ 64 ->
    stk rsegs m lo Sp -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
    rw_cells rsegs m (Sp + 0x18) [CB 120 j120] ->
    rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
    rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word)
            (m' : word -> option byte) (p1 p2 j56' : list byte),
       munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m m' ->
       wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
       rw_cells rsegs m' (Sp + 0x18)
         (owed_cells p1 p2 (owed_at (map bz bb) (Z.of_nat (length bb)) pos (status mod 256))) ->
       rw_cells rsegs m' (Sp + 0x150) [CB 56 j56'] ->
       rw_cells rsegs m' (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
       evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
            (Z_to_bv 64 (Z.of_nat (length bb))) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
            (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1)
            (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
            F (Z_to_bv 64 0x131cc) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
        (Z_to_bv 64 status) x11 (Z_to_bv 64 pos) x13 x14 x15 x16 x17 (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50))
        (Z_to_bv 64 (2 ^ 64 - 1)) x21 x22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13) (Z_to_bv 64 0x90)
        x28 x29 x30 x31)
        F (Z_to_bv 64 0x12f10) fc None m (seg_rom rsegs)).
Proof.
  intros SMS MSET MCPY x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp F fc m
    Sp lo body pos status bb j120 j56 Q Hlo HloSp HSp16 HSp47 Hbody Hbb Hpos Hst ST MI BA H18 H150 H10 K.
  assert (ENV : seg_env Sp lo body bb) by (unfold seg_env; repeat split; lia).
  pose proof (msg_ok_step (map bz bb) (Z.of_nat (length bb)) pos (status mod 256) (bytes_ok_bz bb)
    ltac:(lia) ltac:(lia) ltac:(lia)) as MOK.
  remember (spec_msg_step (map bz bb) (Z.of_nat (length bb)) pos (status mod 256)) as M eqn:HMdef.
  rewrite (owed_at_tail (map bz bb) (Z.of_nat (length bb)) pos (status mod 256)) in K.
  rewrite <- HMdef in K.
  apply (head_evt SMS MSET x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp F fc m
    Sp lo body pos status bb j120 j56 M Q HMdef ENV Hpos Hst ST MI BA H18 H150 H10).
  - intros Hne.
    replace (negb (sm_code M =? 1)) with true in K
      by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Hne).
    cbv iota in K. unfold owed_k. exact K.
  - intros He1.
    replace (negb (sm_code M =? 1)) with false in K
      by (symmetry; apply negb_false_iff, Z.eqb_eq; exact He1).
    cbv iota in K.
    apply (chan_evt gp tp x23 F fc m Sp lo body bb M Q ENV MOK).
    + intros H144. apply (note_evt gp tp x23 F fc m Sp lo body bb M Q ENV MOK H144). exact K.
    + intros H176. apply (cc_evt SMS gp tp x23 F fc m Sp lo body bb M Q ENV MOK H176). exact K.
    + intros H144 H176.
      apply (sysex_evt MCPY gp tp x23 F fc m Sp lo body bb M Q ENV MOK He1 H144 H176). exact K.
Qed.
