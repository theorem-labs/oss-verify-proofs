(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of diginet_decoder_next in fuzz_decode.plain.
   Source: src/diginet_decode.c:20-158 at 835f336c (decode_note and decode_sysex are inlined). It
   calls diginet_msg_next (0x13b34) on d->c (0x13eb0) and, for a fader, on a copy of it (0x14084);
   memset (0x1c0a4) on the first 40 bytes of the event (0x13ecc); memcpy (0x1bca0) of its message to
   ev->msg (0x13edc) and of a scribble's characters to ev->text (0x14274); diginet_meter_segments
   (0x13df8) for a meter (0x141ec). None of them uses the stack. The sysex switch is a jump table of
   8 words at 0x103e4 (read-only data).
   Address 0x13e80, size 1028 bytes. Stack frame: 160 bytes (the message m at sp - 80, the peek cursor
   at sp - 112, the message lsb at sp - 152, ra and s0..s3 at sp - 8 .. sp - 40).
   Arguments: a0 is the address d of a struct diginet_decoder (40 bytes), a1 the address ev of a struct
   diginet_event (80 bytes). The caller is LLVMFuzzerTestOneInput: its decoder and its event, both in
   its stack frame.
   Preconditions:
   - d and ev are not 0;
   - the decoder at d is dd as decoder_cells gives it (DgnLayout.v), for the body at the address body
     whose bytes are bb, the cursor length the length of bb, the position pos <= the length of bb, the
     running status st 0 or a channel status 80..EF (st_ok), any personality p and any 7 cursor padding
     bytes cpad;
   - the bytes bb at body are readable (bytes_at);
   - the 80 bytes ej at ev are writable (rw_cells);
   - the stack from lo to sp is writable (stk), and lo + 160 <= sp;
   - the 40 bytes at d, the 80 bytes at ev, the bytes at body and the 160 bytes below sp do not
     overlap;
   - mem_inv holds.
   Result: let (r, e, dd') be diginet_decoder_next (map bz bb) dd dgn_event_zero (DgnLib.v). a0 is r:
   1, 0, -6, -7 or -8. The decoder at d is dd' (its cursor padding cpad and its p as they were). When r
   is 1 the event at ev is e as event_cells gives it, with the 4 padding bytes of ev->msg some bytes
   mpad (the function copies them from its uninitialised message); else the 80 bytes at ev are ej.
   The function writes only the 40 bytes at d, the 80 bytes at ev and the 160 bytes below sp. It
   writes a1..a7 and t0..t6. It keeps ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr,
   and the stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_DECODER_NEXT : Z := 0x13e80.

(* the decoder at the cursor position pos with running status st over a body of len bytes *)
Definition decoder_at (len : Z) (pos : nat) (st : Z) (p : option Z) : dgn_decoder :=
  {| dd_c := {| dc_len := len; dc_pos := Z.of_nat pos; dc_status := st |}; dd_p := p |}.

Definition diginet_decoder_next_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (d ev body lo : Z) (bb ej cpad : list byte) (pos : nat) (st : Z) (p : option Z),
    let len := Z.of_nat (length bb) in
    let dd := decoder_at len pos st p in
    let res := diginet_decoder_next (map bz bb) dd dgn_event_zero in
    d <> 0 -> ev <> 0 ->
    (pos <= length bb)%nat -> st_ok st ->
    rw_cells rsegs m d (decoder_cells body cpad dd) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m ev [CB 80 ej] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp ->
    d + 40 <= ev \/ ev + 80 <= d ->
    d + 40 <= body \/ body + len <= d ->
    ev + 80 <= body \/ body + len <= ev ->
    d + 40 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= d ->
    ev + 80 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= ev ->
    body + len <= bv_unsigned sp - 160 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (mpad : list byte) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (fst res))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp - 160, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' d (decoder_cells body cpad (snd res)) /\
         rw_cells rsegs m' ev (if fst (fst res) =? 1 then event_cells body mpad (snd (fst res)) else [CB 80 ej]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 ev) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_DECODER_NEXT) fc None m (seg_rom rsegs)).
