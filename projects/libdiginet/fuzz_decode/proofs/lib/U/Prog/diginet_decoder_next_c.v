(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the contract of diginet_decoder_next (src/diginet_decode.c:107-158, with
   decode_note :20-35 and decode_sysex :37-105 inlined) on the UBSan image, at 0x13fe4 (1176 bytes: 294 words, the
   last the unimp at 0x14478), over lib/Spec/DgnLib.v's diginet_decoder_next.
   Arguments: a0 = d, the address of a struct diginet_decoder (DgnLayout.v decoder_cells over the model's decoder
   dc and the bytes bb at body); a1 = ev, the address of a struct diginet_event (80 bytes). The one caller is
   LLVMFuzzerTestOneInput 0x131e4 (d = sp + 0x108, ev = sp + 0x90, which it zeroes first at 0x131d0-0x131d8).
   The function keeps ra, s0, s1, s2 in a 144-byte frame below sp (0x13fe4-0x13ff4), with its message m at
   sp - 0x48, the fader's peek cursor at sp - 0x68 and the LSB message at sp - 0x90 (frame offsets 0x48, 0x28 and 0
   from the lowered sp); it calls diginet_msg_next
   (0x1401c on d->c, 0x14228 on the peek cursor), memset (ev, 0, 80) (0x14038), memcpy (ev + 40, &m, 40) (0x14050),
   diginet_meter_segments (0x143a0) and memcpy for the scribble text (0x14460).
   - d or ev NULL returns DIGINET_E_ARG (0x13ffc, 0x14004 to 0x1429c, diginet_decode.c:110-111); the model has no
     NULL objects (DgnLib.v header): d <> 0 and ev <> 0 are premises.
   - The cursor is what the msg_next contract reads: its len is the length of bb, pos <= len, status none or a
     channel status (st_ok); body <> 0 (the msg_next check of body, and every body the harness passes is a block
     or a pointer into it). sp is 16-aligned (the psABI), so the three stack objects are 8-aligned.
   - When diginet_msg_next does not return 1 the event is left as it was (0x14028 to 0x1429c): the post keeps the
     80 bytes ej; else the event is event_cells of the model's event, whose msg padding mpad is the 4 padding bytes
     of m (not written by diginet_msg_next, copied by the memcpy).
   The UBSan check sites of the function itself, each a branch to the unimp at 0x14478, and what makes each
   unreachable:
   - 0x1400c `andi a0, a0, 7` / 0x14010 `bnez`: d misaligned: d mod 8 = 0;
   - 0x1403c `andi a0, s0, 7` / 0x14040 `bnez`: ev misaligned: ev mod 8 = 0;
   - 0x140c0 `beqz a1` (s == NULL at the load s[0]), 0x140d4 `beq a1, -1` (s + 1 wraps), 0x140e4 / 0x140ec (s + 3,
     s + 2 wrap), 0x1415c `beq a0, -1` and 0x14194 `bltu a7, a0` (pl + 1, pl + 2 in the ring loop), 0x1432c
     (pl + 1, LEDs), 0x14380 `bltu a0, a3` (pl + 2, meter), 0x143c8 `beq a0, -1` (pl + 1), 0x143f8 `beqz a4`
     (pl + 2, the digit loop's source) and 0x143fc `bltu a5, a2` (ev + 29 + 8, the seg stores) of the counter,
     0x1444c (pl + 2, scribble), 0x14468 (ev + 20 + len, the text's NUL): s = body + the payload offset
     of a sysex message, which lies inside bb with its F7 after it, and ev + 80 <= 2^64 by rw_cells: no premise of
     their own.
   The callees' check sites are their contracts'.
   Result: a0 is the model's result, sign-extended; the decoder holds decoder_cells of the model's decoder (the
   cursor's 7 padding bytes cpad are kept: the peek copy-back at 0x14278-0x14284 writes back the bytes 0x14200-
   0x1420c read); memory changes only in the 40 bytes at d, the 80 bytes at ev and the frame; s0..s11, ra, sp, gp,
   tp are kept; a1..a7 and t0..t6 are written. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
Open Scope Z_scope.

Definition DIGINET_DECODER_NEXT : Z := 0x13fe4.
Definition DIGINET_DECODER_NEXT_FRAME : Z := 144.

(* the model's step over the bytes bb from the decoder dc: its result, event and decoder. The event argument of
   the model is dgn_event_zero: when the result is 1 the model's event does not depend on it (diginet_decode.c:115
   zeroes it), and otherwise the post keeps the event's bytes. *)
Definition dn_step (bb : list byte) (dc : dgn_decoder) : Z * dgn_event * dgn_decoder :=
  diginet_decoder_next (map bv_unsigned bb) dc dgn_event_zero.
Definition dn_r (bb : list byte) (dc : dgn_decoder) : Z := fst (fst (dn_step bb dc)).
Definition dn_e (bb : list byte) (dc : dgn_decoder) : dgn_event := snd (fst (dn_step bb dc)).
Definition dn_d (bb : list byte) (dc : dgn_decoder) : dgn_decoder := snd (dn_step bb dc).

Definition diginet_decoder_next_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (d ev body lo : Z) (bb cpad ej : list byte) (dc : dgn_decoder),
    d <> 0 -> ev <> 0 ->
    (* UBSan only: 0x1400c / 0x14010 and 0x1403c / 0x14040, the alignment checks of d and ev *)
    d mod 8 = 0 -> ev mod 8 = 0 ->
    bv_unsigned sp mod 16 = 0 ->
    body <> 0 ->
    dc_len (dd_c dc) = Z.of_nat (length bb) ->
    0 <= dc_pos (dd_c dc) <= dc_len (dd_c dc) ->
    st_ok (dc_status (dd_c dc)) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m d (decoder_cells body cpad dc) ->
    rw_cells rsegs m ev [CB 80 ej] ->
    d + 40 <= ev \/ ev + 80 <= d ->
    d + 40 <= body \/ body + Z.of_nat (length bb) <= d ->
    ev + 80 <= body \/ body + Z.of_nat (length bb) <= ev ->
    stk rsegs m lo (bv_unsigned sp) ->
    (* the lowest of the three objects the frame holds, the fader's LSB message at sp - 0x90, is at the frame base,
       and diginet_msg_next's contract asks for a non-NULL address; stk alone allows lo = 0 and sp = 144. Without
       this premise the statement is false, not merely unprovable: with that message at 0, diginet_msg_next returns
       -1 at its own NULL check (0x13bf4), the walk skips the LSB merge and the cursor copy-back, and the model
       merges them. The stack of a real run lies far above 0 (the harness's lo is at least alloc_ceiling). *)
    0 < lo ->
    lo + DIGINET_DECODER_NEXT_FRAME <= bv_unsigned sp ->
    d + 40 <= bv_unsigned sp - DIGINET_DECODER_NEXT_FRAME \/ bv_unsigned sp <= d ->
    ev + 80 <= bv_unsigned sp - DIGINET_DECODER_NEXT_FRAME \/ bv_unsigned sp <= ev ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - DIGINET_DECODER_NEXT_FRAME \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (mpad : list byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (dn_r bb dc)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 40); (ev, ev + 80);
                (bv_unsigned sp - DIGINET_DECODER_NEXT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' d (decoder_cells body cpad (dn_d bb dc)) /\
         length mpad = 4%nat /\
         rw_cells rsegs m' ev (if dn_r bb dc =? 1 then event_cells body mpad (dn_e bb dc) else [CB 80 ej]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 ev) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_DECODER_NEXT) fc None m (seg_rom rsegs)).
