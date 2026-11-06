(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_events_fields (fuzz/fuzz_decode.c:187-263) in fuzz_decode.plain.
   Address 0x13870, size 544 bytes. Stack frame: 48 bytes (ra, s0..s4). It dispatches the kinds
   7..11 through the jump table at 0x103c4 (5 words, read from the image), calls bcmp (0x1bc6c, the
   kit's bcmp_contract) for the counter's 8 digits (0x13a1c) and for a scribble write's characters
   (0x13a78), and calls nothing else but the `jal abort` at 0x13a8c.
   Arguments: a0 is the address b of the body bytes bb, a1 the address o of the harness's struct
   owed ow, a2 the address e of the struct diginet_event ev. The caller is LLVMFuzzerTestOneInput
   (0x131c4); o and e are in its frame and the event is the one diginet_decoder_next filled from the
   body at b. The model reads the body as DgnLib.v does: the list Z map bz bb.
   Preconditions:
   - DgnDecHarness.check_events_fields_ok (map bz bb) ow ev holds;
   - the kind of ow's event is a C int, in [-2^31, 2^31);
   - the status of ow's message is a byte, in [0, 256), and its payload length is a size_t, in
     [0, 2^64); when the status is F0 the payload offset is a place in bb (the maker test of
     fuzz_decode.c:190 reads b[sysex_at]);
   - ow's lsb_missing is in [0, 256) (it is 0 or 1; fuzz_decode.c:208 compares it with the event's
     uint8_t lsb_missing);
   - a scribble write's length is at most 8 (SPEC_CHARS_MAX, spec.h:368: memcmp at
     fuzz_decode.c:247 reads that many of the 8 bytes of e->text);
   - the bytes bb at b are readable (bytes_at), the 120 bytes at o are owed_cells p1 p2 ow and the
     80 bytes at e are event_cells b mpad ev (ro_cells);
   - the stack from lo to sp is writable (stk), lo + 48 <= sp, and neither the body nor a struct is
     in the 48 bytes below sp;
   - mem_inv holds.
   Result: the function returns to ra, which is the statement that none of the tests of
   fuzz_decode.c:196-262 branches to the abort. It writes only the 48 bytes below sp. It keeps ra,
   sp, gp, tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_EVENTS_FIELDS : Z := 0x13870.
Definition CHECK_EVENTS_FIELDS_FRAME : Z := 48.

Definition check_events_fields_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b o e lo : Z) (bb : list byte) (ow : owed) (ev : dgn_event) (p1 p2 mpad : list byte),
    check_events_fields_ok (map bz bb) ow ev = true ->
    -2^31 <= se_kind (ow_e ow) < 2^31 ->
    0 <= sm_status (ow_m ow) < 256 ->
    0 <= sm_sysex_len (ow_m ow) < 2^64 ->
    (sm_status (ow_m ow) = 240 -> 0 <= sm_sysex_at (ow_m ow) < Z.of_nat (length bb)) ->
    0 <= ow_lsb_missing ow < 256 ->
    (se_kind (ow_e ow) = SPEC_EV_SCRIBBLE -> 0 <= se_len (ow_e ow) <= 8) ->
    bytes_at rsegs m b bb ->
    ro_cells rsegs m o (owed_cells p1 p2 ow) ->
    ro_cells rsegs m e (event_cells b mpad ev) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_EVENTS_FIELDS_FRAME <= bv_unsigned sp ->
    b + Z.of_nat (length bb) <= bv_unsigned sp - CHECK_EVENTS_FIELDS_FRAME \/ bv_unsigned sp <= b ->
    o + OW_SIZE <= bv_unsigned sp - CHECK_EVENTS_FIELDS_FRAME \/ bv_unsigned sp <= o ->
    e + DE_SIZE <= bv_unsigned sp - CHECK_EVENTS_FIELDS_FRAME \/ bv_unsigned sp <= e ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_EVENTS_FIELDS_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 o) (Z_to_bv 64 e)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_EVENTS_FIELDS) fc None m (seg_rom rsegs)).
