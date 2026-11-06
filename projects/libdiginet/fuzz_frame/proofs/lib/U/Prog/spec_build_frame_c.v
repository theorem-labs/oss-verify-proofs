(* Contract of spec_build_frame (static) in fuzz_frame.ubsan. fuzz_frame.plain inlines this
   function into check_round_trip, so it has no plain twin; its caller here takes this
   contract as a hypothesis.
   Source: fuzz/spec.h:228-247 at 835f336c (spec_put16, spec_put32 and spec_sum inlined).
   Address 0x136a8, size 668 bytes. Stack frame: 96 bytes (addi sp, sp, -0x60 at 0x136a8; ra and
   s0..s10 saved). It calls memset (0x1c1a0) and memcpy (0x1bd9c) two times, and when len is
   not 0 it ends with a tail call to memcpy (0x13904: j, after the frame is popped) for the
   body; neither uses stack. Its walk takes their contracts (U/Prog/memset_c.v, memcpy_c.v) as
   hypotheses.
   Arguments (the compiler's own convention for this local function, 11 arguments): a0 out,
   a1 dst, a2 src, a3 send and a4 ack (each sign-extended from bit 31, sx32: the caller loads
   them with lw), a5 retry, a6 cmd, a7 ncmds (zero-extended: lhu, lbu), t3 body, t4 len, the
   length of the bytes bb at body, and t5 zero_sum. The caller is check_round_trip (0x133a8
   with zero_sum 0, 0x133f4 with zero_sum 1); it gives the block want of n_want bytes, the
   fields w->dst, w->src, w->send, w->ack, w->retry, w->cmd, w->ncmds, w->body and
   w->body_len of its spec_frame. The function returns no value the caller reads (a0 is out + 30
   from the tail call to memcpy, or 2^64 - 30 when len is 0).
   Preconditions:
   - send < 2^32, ack < 2^32, retry < 2^16, cmd < 2^8, ncmds < 2^8, all at least 0;
     zero_sum is 0 or 1; body is not 0;
   - the 6 bytes dmac at dst and the 6 bytes smac at src are readable (bytes_at);
   - the bytes bb at body are readable (bytes_at);
   - the bytes oj at out are writable (rw_cells), and their number is frame_len (length bb),
     the larger of 60 and 30 + the body length (the n of spec.h:232);
   - the bytes at out do not overlap the bytes at dst, src and body;
   - the stack from lo to sp is writable (stk), and lo + 96 <= sp; the bytes at out, dst, src
     and body are not in the 96 bytes below sp;
   - mem_inv holds.
   Result: the bytes at out are build_frame dmac smac send ack retry cmd ncmds bb (zero_sum
   = 1): the MACs, 88 5F, put16 (16 + len), put16 of 0 or of the sum of bb (the binary adds
   in 64 bits and stores the low 16 bits: spec_sum, DgnSpec.spec_sum_eq), put32 send,
   put32 ack, put16 retry, cmd, ncmds, then bb, then the zeros of the memset up to frame_len.
   The function writes only the bytes at out and the 96 bytes below sp. It keeps ra, sp, gp,
   tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   UBSan checks: branches to the trap at 0x13940 (unimp):
   - 0x13738, 0x13750, 0x13764, 0x13774, 0x1378c, 0x13798, 0x137f8, 0x13804, 0x13818,
     0x13828, 0x13838, 0x13844, 0x13858, 0x13868, 0x13878, 0x13884, 0x13898, 0x138a4,
     0x138b0, 0x138c0: the pointer-overflow checks of out + 6 .. out + 30. rw_cells gives
     out + frame_len <= 2^64 with frame_len >= 60, so none of them is taken;
   - 0x137bc, 0x137c8, 0x137cc, each turn of the sum loop (len not 0 and zero_sum 0) before
     it reads body[i]: body + i wraps past 2^64, or body is 0. bytes_at gives
     body + len <= 2^64 with i < len, and body is not 0, so none of them is taken.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition SPEC_BUILD_FRAME : Z := 0x136a8.
(* addi sp, sp, -0x60 at 0x136a8; memset and memcpy use no stack. *)
Definition SBF_STACK : Z := 96.

Definition spec_build_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out dst src body zs lo send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte),
    0 <= send < 2^32 -> 0 <= ack < 2^32 -> 0 <= retry < 2^16 -> 0 <= cmd < 2^8 -> 0 <= ncmds < 2^8 ->
    zs = 0 \/ zs = 1 ->
    body <> 0 ->
    length dmac = 6%nat -> bytes_at rsegs m dst dmac ->
    length smac = 6%nat -> bytes_at rsegs m src smac ->
    bytes_at rsegs m body bb ->
    Z.of_nat (length oj) = frame_len (length bb) ->
    rw_cells rsegs m out [CB (length oj) oj] ->
    out + Z.of_nat (length oj) <= dst \/ dst + 6 <= out ->
    out + Z.of_nat (length oj) <= src \/ src + 6 <= out ->
    out + Z.of_nat (length oj) <= body \/ body + Z.of_nat (length bb) <= out ->
    stk rsegs m lo (bv_unsigned sp) -> lo + SBF_STACK <= bv_unsigned sp ->
    out + Z.of_nat (length oj) <= bv_unsigned sp - SBF_STACK \/ bv_unsigned sp <= out ->
    dst + 6 <= bv_unsigned sp - SBF_STACK \/ bv_unsigned sp <= dst ->
    src + 6 <= bv_unsigned sp - SBF_STACK \/ bv_unsigned sp <= src ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - SBF_STACK \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - SBF_STACK, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' out [CB (length oj) (build_frame dmac smac send ack retry cmd ncmds bb (zs =? 1))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 dst) (Z_to_bv 64 src)
               (sx32 (Z_to_bv 64 send)) (sx32 (Z_to_bv 64 ack)) (Z_to_bv 64 retry) (Z_to_bv 64 cmd)
               (Z_to_bv 64 ncmds) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 zs) t6)
          F (Z_to_bv 64 SPEC_BUILD_FRAME) fc None m (seg_rom rsegs)).
