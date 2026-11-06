(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/U/Prog into libdiginet/fuzz_decode (module path and addresses only: entry 0x141a0 -> 0x13bec, every other pc -0x5b4, the caller list of this image) *)
(* Contract of diginet_msg_next in fuzz_decode.ubsan, relocated from fuzz_frame.ubsan's
   lib/U/Prog/diginet_msg_next_c.v (frozen text; module path and addresses changed, nothing
   else). The code is byte-identical in the two images and lies 0x5b4 lower here, so every pc
   of the frame text is moved by -0x5b4 and checked against this image's bytes.
   Source: src/diginet_msg.c:27-103 at 835f336c. The binary inlines channel_data_len; it
   tests (status & 0xe0) == 0xc0 (DgnLib.chan_n_land).
   Address 0x13bec, size 480 bytes. No stack frame and no call.
   Arguments: a0 is the address c of a struct diginet_cursor, a1 the address mp of a struct
   diginet_msg (40 bytes). The callers are diginet_body_check (0x13e64), diginet_decoder_next
   (0x1401c on the decoder's cursor, 0x14228 on its peek cursor) and LLVMFuzzerTestOneInput
   (0x12e48); each gives the cursor and the message in its own frame or decoder.
   Preconditions:
   - c and mp are not 0, and both are 8-aligned; body is not 0;
   - the cursor holds body, the length of bb, pos and st (rw_cells, cursor_cells), with
     pos <= the length of bb and st 0 or a channel status 80..EF (st_ok);
   - the bytes bb at body are readable (bytes_at);
   - the 40 bytes mj at mp are writable (rw_cells);
   - the 25 bytes at c, the 40 bytes at mp and the bytes at body do not overlap;
   - mem_inv holds.
   Result: let r be msg_step bb pos st. a0 is mr_code r: 1, 0, -6, -7 or -8. The function
   writes c->pos = mr_pos r and c->status = mr_st r. It writes the fields of the message as
   msg_cells gives them: nothing when r is the end; else m->offset, m->d1, m->d2, m->sysex
   (body + mr_sysex r for a sysex, else 0) and m->sysex_len, and m->status, m->running and
   m->len when r writes them (writes_status, writes_running, writes_len). It does not write
   the bytes 4..7 of the message.
   The function writes only the 25 bytes at c and the 40 bytes at mp. It writes a2..a7 and
   t0..t3 (the statement lets a1 change too, as the plain one does). It keeps all other
   registers.
   UBSan checks: ten branches to the trap at 0x13dc8 (unimp):
   - 0x13bfc: c & 7 is not 0; 0x13c30: mp & 7 is not 0 (the alignment of the two structs).
     The premises c mod 8 = 0 and mp mod 8 = 0 keep them from firing;
   - 0x13c14, 0x13c24, 0x13c28: b + start wraps past 2^64, or b is 0, when pos < len. The
     premise body <> 0 and bytes_at (body + length bb <= 2^64, start < length bb) keep them
     from firing;
   - 0x13c6c (b + i in the F7 scan), 0x13c8c (b + start + 1, m->sysex), 0x13d48 (b + data_at
     + i), 0x13d68 (b + data_at), 0x13d9c (b + data_at + 1): each index is less than
     length bb there, so with body + length bb <= 2^64 nothing wraps.
   On pos >= len the function returns 0 at 0x13cb4 before any check of body.
   Differences from the plain statement: the premises c mod 8 = 0, mp mod 8 = 0 and
   body <> 0. Every caller's cursor and message are at 8-aligned addresses (frame slots, or
   the decoder's first field), and its body is not 0.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_MSG_NEXT : Z := 0x13bec.

(* The 40 bytes of the struct diginet_msg at mp after the step r over the body at the address
   body; mj are the 40 bytes before the call. Layout: status 0, running 1, d1 2, d2 3,
   padding 4..7, sysex 8, sysex_len 16, offset 24, len 32. The same cells as in
   Prog/diginet_msg_next_c.v. *)
Definition msg_cells (body : Z) (mj : list byte) (r : msg_res) : list cell :=
  if is_end r then [CB 40 mj]
  else
    [ C1 (if writes_status (mr_kind r) then b8 (mr_status r) else nth 0 mj (b8 0));
      C1 (if writes_running (mr_kind r) then b8 (mr_running r) else nth 1 mj (b8 0));
      C1 (b8 (mr_d1 r));
      C1 (b8 (mr_d2 r));
      CB 4 (firstn 4 (skipn 4 mj));
      C8 (Z_to_bv 64 (if writes_sysex (mr_kind r) then body + Z.of_nat (mr_sysex r) else 0));
      C8 (Z_to_bv 64 (Z.of_nat (mr_sysex_len r)));
      C8 (Z_to_bv 64 (Z.of_nat (mr_start r)));
      if writes_len (mr_kind r) then C8 (Z_to_bv 64 (Z.of_nat (mr_len r))) else CB 8 (skipn 32 mj) ].

Definition diginet_msg_next_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    c <> 0 -> mp <> 0 -> c mod 8 = 0 -> mp mod 8 = 0 -> body <> 0 ->
    (pos <= length bb)%nat -> st_ok st ->
    rw_cells rsegs m c (cursor_cells body (Z.of_nat (length bb)) pos st) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m mp [CB 40 mj] ->
    c + 25 <= mp \/ mp + 40 <= c ->
    c + 25 <= body \/ body + Z.of_nat (length bb) <= c ->
    mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mr_code (msg_step bb pos st)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(c, c + 25); (mp, mp + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' c (cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                                (mr_st (msg_step bb pos st))) /\
         rw_cells rsegs m' mp (msg_cells body mj (msg_step bb pos st)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 mp) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_MSG_NEXT) fc None m (seg_rom rsegs)).
