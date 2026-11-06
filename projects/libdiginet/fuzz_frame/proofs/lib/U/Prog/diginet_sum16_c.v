(* Contract of diginet_sum16 in fuzz_frame.ubsan. fuzz_frame.plain inlines this function into
   diginet_frame_parse and diginet_frame_build, so it has no plain twin; its callers here take
   this contract as a hypothesis.
   Source: src/diginet_frame.c:42-48 at 835f336c.
   Address 0x13944, size 80 bytes. No stack frame and no call.
   Arguments: a0 is the address p, a1 the length of the bytes bb at p. The callers are
   diginet_frame_parse (0x13bb4: f->body = buf + 30 and f->body_len) and diginet_frame_build
   (0x13d9c, in the mode DIGINET_SUM_BODY: its body and body_len).
   Preconditions: p is not 0. The bytes bb at p are readable (bytes_at).
   Result: a0 is lib_sum16 bb, the sum of the bytes of bb cut to 16 bits (the binary adds in
   64 bits, then keeps the low 16 bits: slli 0x30, srli 0x30). The function writes a1..a6. It
   writes no memory.
   It keeps all other registers, the memory and the stack.
   UBSan checks: three branches to the trap at 0x13990 (unimp), each turn of the loop before it
   reads p[i]:
   - 0x13958: p + i < p (the pointer p + i wraps past 2^64);
   - 0x13964: p is not 0 and p + i is 0, or p is 0 and p + i is not 0;
   - 0x13968: p is 0.
   The loop runs only for i < length bb. bytes_at gives p + length bb <= 2^64, so p + i does not
   wrap, and p is not 0; no branch is taken. For bb = [] the function returns at 0x13948 before
   the loop.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_SUM16 : Z := 0x13944.

Definition diginet_sum16_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte),
    p <> 0 ->
    bytes_at rsegs m p bb ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lib_sum16 bb)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SUM16) fc None m (seg_rom rsegs)).
