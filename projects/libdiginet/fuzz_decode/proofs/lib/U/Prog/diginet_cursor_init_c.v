(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/U/Prog into libdiginet/fuzz_decode (module path and addresses only: entry 0x14170 -> 0x13bbc, every other pc -0x5b4, the caller list of this image) *)
(* Contract of diginet_cursor_init in fuzz_decode.ubsan, relocated from fuzz_frame.ubsan's
   lib/U/Prog/diginet_cursor_init_c.v (frozen text; module path and addresses changed, nothing
   else). The code is byte-identical in the two images and lies 0x5b4 lower here, so every pc
   of the frame text is moved by -0x5b4 and checked against this image's bytes.
   Source: src/diginet_msg.c:10-18 at 835f336c.
   Address 0x13bbc, size 48 bytes. No stack frame and no call.
   Arguments: a0 is the address c of a struct diginet_cursor, a1 the address body, a2 the
   length len. The callers are diginet_body_check (0x13e40), diginet_decoder_init (0x13fb4) and
   LLVMFuzzerTestOneInput (0x12e04); each gives a cursor in its own frame or in its decoder and
   its own two arguments.
   Preconditions: c is not 0 and c is 8-aligned. The 25 bytes cj at c (body, len, pos, status)
   are writable (rw_cells). mem_inv holds.
   Result: the function writes c->body = body, c->len = len (0 when body is 0), c->pos = 0
   and c->status = 0, as cursor_cells gives them. It does not write the 7 padding bytes after
   c->status. It writes a2 and a3, and it keeps a0 and a1.
   The function writes only the 25 bytes at c. It keeps all other registers.
   UBSan checks: one branch to the trap at 0x13be8 (unimp), at 0x13bc4: c & 7 is not 0 (the
   alignment of struct diginet_cursor, 0x13bc0 andi a3, a0, 7). The premise c mod 8 = 0 keeps it
   from firing.
   Difference from the plain statement: the premise c mod 8 = 0. Every caller's cursor is at an
   8-aligned address (a frame slot, or the decoder's first field).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_CURSOR_INIT : Z := 0x13bbc.

(* The 25 bytes body, len, pos, status of a struct diginet_cursor; the same cells as in
   Prog/diginet_cursor_init_c.v. *)
Definition cursor_cells (body len : Z) (pos : nat) (st : Z) : list cell :=
  [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].

Definition diginet_cursor_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c body len : Z) (cj : list byte),
    c <> 0 -> c mod 8 = 0 ->
    0 <= body < 2^64 -> 0 <= len < 2^64 ->
    rw_cells rsegs m c [CB 25 cj] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 body) a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(c, c + 25)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' c (cursor_cells body (if body =? 0 then 0 else len) 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 body) (Z_to_bv 64 len)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_CURSOR_INIT) fc None m (seg_rom rsegs)).
