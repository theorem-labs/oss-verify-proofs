(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_announce_parse_c.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images; the caller named is fuzz_frame's (its pcs dropped) *)
(* Contract of diginet_announce_parse in fuzz_transport.ubsan, the twin of
   Prog/diginet_announce_parse_c.v (fuzz_transport.plain).
   Source: src/diginet_frame.c:138-151 at 835f336c. The binary calls copy_strz (0x185e0,
   src/diginet_frame.c:130-136) two times; copy_strz uses no stack. Its walk takes the
   copy_strz contract (U/Prog/copy_strz_c.v) as a hypothesis. It tests (cmd & 0xfe) == 0xe0
   (DgnSpec.ann_cmd_land).
   Address 0x18520, size 192 bytes. Stack frame: 32 bytes (addi sp, sp, -0x20 at 0x18520; ra,
   s0, s1 saved at sp - 8 .. sp - 24).
   Arguments: a0 is the address f of a struct diginet_frame, a1 the address ap of a struct
   diginet_announce (40 bytes). In fuzz_frame the caller is check_announce; it gives the frame that
   diginet_frame_parse filled and an announce in its stack frame.
   Preconditions:
   - f and ap are not 0, and both are 8-aligned; body is in 1 .. 2^64 - 1;
   - these bytes are readable (bytes_at): f + 30, f->h.cmd: the byte cmd; f + 32, f->body: the
     8 bytes of the address body; f + 40, f->body_len: the 8 bytes of the length of bb; the
     bytes bb at body;
   - the 40 bytes aj at ap are writable (rw_cells);
   - the 40 bytes at ap do not overlap the bytes f + 30 .. f + 47 or the bytes at body;
   - the stack from lo to sp is writable (stk), and lo + 32 <= sp; the bytes f + 30 .. f + 47,
     the bytes at body and the 40 bytes at ap are not in the 32 bytes below sp;
   - mem_inv holds.
   Result: a0 is ann_code cmd (length bb): -9 (NOT_ANNOUNCE) for a command other than e0 and
   e1, else -4 (LENGTH) for a body under 33 bytes, else 0. On 0 the function writes ap as
   ann_cells gives it: version (bytes 0..9) is ann_version, name (bytes 10..19) is ann_name,
   unknown (byte 24) is body and unknown_len (byte 32) is 15. In each string field copy_strz
   writes the k = strz_len bytes of the string and a NUL after them; it does not write the
   bytes k+1..9 of the field. It does not write the bytes 20..23. On a code that is not 0 it
   writes no byte at ap.
   The function writes only the 40 bytes at ap and the 32 bytes below sp. It writes a1..a7.
   It keeps all other registers, and the stack from lo to sp stays writable.
   UBSan checks: branches to the trap at 0x185dc (unimp):
   - 0x18548: f & 7 is not 0, on every path past the two tests for 0; 0x1857c: ap & 7 is not
     0, on the path of code 0 (the alignment of the two structs). The premises f mod 8 = 0
     and ap mod 8 = 0 keep them from firing;
   - 0x18590 and 0x185ac: f->body is 0, before each copy_strz (code 0, so length bb >= 33).
     The premise 0 < body keeps them from firing;
   - 0x18598 (body + 15) and 0x185b4 (body + 24): the pointer wraps past 2^64. On code 0,
     bytes_at gives body + 33 <= 2^64, so neither branch is taken.
   copy_strz's own checks need its source not 0 and the 9 bytes at body + 15 and at body + 24
   readable: both are in bb when length bb >= 33.
   Differences from the plain statement: the 32-byte stack frame (the stk premise, the
   disjointness from the 32 bytes below sp, the stack in munch, and stk after the call), the
   premises f mod 8 = 0 and ap mod 8 = 0, 0 < body in place of 0 <= body, and a7 written
   (copy_strz writes it). The caller gives its local frame struct and its local announce (both
   8-aligned) and body = buf + 30.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_ANNOUNCE_PARSE : Z := 0x18520.
(* addi sp, sp, -0x20 at 0x18520; copy_strz uses no stack. *)
Definition ANN_STACK : Z := 32.

(* The struct diginet_announce after a parse that answered 0, for the body bb at the address
   body; aj are the 40 bytes before the call. The same cells as in
   Prog/diginet_announce_parse_c.v. *)
Definition ann_cells (body : Z) (bb aj : list byte) : list cell :=
  [ CB 10 (ann_version bb (firstn 10 aj));            (*  0 version[10] *)
    CB 10 (ann_name bb (firstn 10 (skipn 10 aj)));    (* 10 name[10] *)
    CB 4 (firstn 4 (skipn 20 aj));                    (* 20 not written *)
    C8 (Z_to_bv 64 body);                             (* 24 unknown *)
    C8 (Z_to_bv 64 15) ].                             (* 32 unknown_len *)

Definition diginet_announce_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (f ap cmd body lo : Z) (bb aj : list byte),
    f <> 0 -> ap <> 0 -> f mod 8 = 0 -> ap mod 8 = 0 ->
    0 <= cmd < 2^8 -> 0 < body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m ap [CB 40 aj] ->
    ap + 40 <= f + 30 \/ f + 48 <= ap ->
    ap + 40 <= body \/ body + Z.of_nat (length bb) <= ap ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ANN_STACK <= bv_unsigned sp ->
    f + 48 <= bv_unsigned sp - ANN_STACK \/ bv_unsigned sp <= f + 30 ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - ANN_STACK \/ bv_unsigned sp <= body ->
    ap + 40 <= bv_unsigned sp - ANN_STACK \/ bv_unsigned sp <= ap ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ann_code cmd (Z.of_nat (length bb))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - ANN_STACK, bv_unsigned sp); (ap, ap + 40)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' ap
           (if ann_code cmd (Z.of_nat (length bb)) =? 0 then ann_cells body bb aj else [CB 40 aj]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_ANNOUNCE_PARSE) fc None m (seg_rom rsegs)).
