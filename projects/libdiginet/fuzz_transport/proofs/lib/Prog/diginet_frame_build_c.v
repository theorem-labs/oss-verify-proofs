(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_build_c.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images; the caller named is fuzz_frame's (its pcs dropped) *)
(* Contract of diginet_frame_build in fuzz_transport.plain.
   Source: src/diginet_frame.c:93-127 at 835f336c. The binary inlines wr16, wr32 and
   diginet_sum16. It calls diginet_body_check (0x17c38), memcpy (0x1f910) and memset
   (0x1fd14).
   Address 0x178d8, size 516 bytes. Stack frame: 96 bytes; with diginet_body_check, 240.
   Arguments: a0 is the address out of the buffer, a1 its size cap (the length of oj), a2 the
   address dst of the destination MAC, a3 the address src of the source MAC, a4 the address hp
   of a struct diginet_header, a5 the address body, a6 the length of the bytes bb at body, a7
   the sum mode (0 DIGINET_SUM_BODY, 1 DIGINET_SUM_ZERO). In fuzz_frame the caller is check_round_trip; it
   gives an allocation of the frame length (or one byte less), the MACs and the body in the
   input, and a header in its stack frame.
   Preconditions:
   - 0 < out < 2^64 (so the register a0 is not 0); dst, src, hp and body are not 0; mode is 0 or 1;
   - the 6 bytes dmac at dst and the 6 bytes smac at src are readable (bytes_at);
   - the 12 bytes at hp + 4 are the little-endian send_counter, ack_counter and retry, then
     cmd and num_commands (bytes_at). The function does not read h->numbytes or h->sum;
   - the bytes bb at body are readable (bytes_at);
   - the cap bytes oj at out are writable (rw_cells);
   - the bytes at out do not overlap the bytes at dst, src, hp + 4 and body;
   - the stack from lo to sp is writable (stk), and lo + 240 <= sp; the bytes at out, dst,
     src, hp + 4 and body are not in the 240 bytes below sp;
   - mem_inv holds.
   Result: a0 is build_code bb cap: -4 (LENGTH) for a body past 1484 bytes, else -10
   (REFUSED) when system_at bb, else -5 (SPACE) when cap is less than frame_len, else
   frame_len, the larger of 60 and 30 + the body length. On frame_len the function writes the
   first frame_len bytes at out with build_frame (the sum of the body in mode 0, zero in mode
   1); DgnLib.frame_build_ok gives the library's own bytes. On a code under 0 it writes no
   byte at out.
   The function writes only the cap bytes at out and the 240 bytes below sp. It keeps ra, sp,
   gp, tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_FRAME_BUILD : Z := 0x178d8.

(* The cap bytes at out after the call; oj are the bytes before it. *)
Definition build_out (dmac smac : list byte) (send ack retry cmd ncmds : Z) (bb : list byte)
    (mode : Z) (oj : list byte) : list byte :=
  let n := build_code bb (Z.of_nat (length oj)) in
  if 0 <=? n then build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) ++ skipn (Z.to_nat n) oj
  else oj.

Definition diginet_frame_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out dst src hp body mode lo send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte),
    0 < out < 2^64 -> dst <> 0 -> src <> 0 -> hp <> 0 -> body <> 0 ->
    mode = 0 \/ mode = 1 ->
    0 <= send < 2^32 -> 0 <= ack < 2^32 -> 0 <= retry < 2^16 -> 0 <= cmd < 2^8 -> 0 <= ncmds < 2^8 ->
    0 <= hp < 2^64 ->
    length dmac = 6%nat -> bytes_at rsegs m dst dmac ->
    length smac = 6%nat -> bytes_at rsegs m src smac ->
    bytes_at rsegs m (hp + 4)
      (Z_to_le_bytes 4 send ++ Z_to_le_bytes 4 ack ++ Z_to_le_bytes 2 retry ++ [b8 cmd; b8 ncmds]) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m out [CB (length oj) oj] ->
    out + Z.of_nat (length oj) <= dst \/ dst + 6 <= out ->
    out + Z.of_nat (length oj) <= src \/ src + 6 <= out ->
    out + Z.of_nat (length oj) <= hp + 4 \/ hp + 16 <= out ->
    out + Z.of_nat (length oj) <= body \/ body + Z.of_nat (length bb) <= out ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 240 <= bv_unsigned sp ->
    out + Z.of_nat (length oj) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= out ->
    dst + 6 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= dst ->
    src + 6 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= src ->
    hp + 16 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= hp + 4 ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (build_code bb (Z.of_nat (length oj))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' out [CB (length oj) (build_out dmac smac send ack retry cmd ncmds bb mode oj)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 (Z.of_nat (length oj)))
               (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 hp) (Z_to_bv 64 body)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 mode)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_BUILD) fc None m (seg_rom rsegs)).
