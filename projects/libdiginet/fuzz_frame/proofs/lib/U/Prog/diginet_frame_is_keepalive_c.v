(* Contract of diginet_frame_is_keepalive in fuzz_frame.ubsan, the twin of
   Prog/diginet_frame_is_keepalive_c.v (fuzz_frame.plain).
   Source: src/diginet_frame.c:55-58 at 835f336c.
   Address 0x139d8, size 64 bytes. No stack frame and no call.
   Argument: a0 is the address f of a struct diginet_frame (64 bytes). The caller is
   check_parse_fields (0x131b8); it gives the frame that diginet_frame_parse filled.
   Preconditions: f is not 0 and f is 8-aligned. body is in 1 .. 2^64 - 1. These bytes are
   readable (bytes_at):
   - f + 30, f->h.cmd: the byte cmd;
   - f + 32, f->body: the 8 bytes of the address body;
   - f + 40, f->body_len: the 8 bytes of blen, the length of bb;
   - the bytes bb at body.
   Result: a0 is 1 when cmd is 0, blen is 1 and the byte bb[0] is 0 (keepalive_of cmd blen bb),
   else 0. The function writes a1 and a2. It writes no memory.
   It keeps all other registers, the memory and the stack.
   UBSan checks: two branches to the trap at 0x13a14 (unimp):
   - 0x139e0: f & 7 is not 0 (the alignment of struct diginet_frame). The premise f mod 8 = 0
     keeps it from firing;
   - 0x139fc: f->body is 0 when the function reads f->body[0] (cmd 0 and blen 1). The premise
     0 < body keeps it from firing.
   Differences from the plain statement: the premise f mod 8 = 0, and 0 < body in place of
   0 <= body. The caller gives f = its local frame struct (8-aligned) and body = buf + 30.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_FRAME_IS_KEEPALIVE : Z := 0x139d8.

Definition diginet_frame_is_keepalive_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f cmd body : Z) (bb : list byte),
    f <> 0 -> f mod 8 = 0 ->
    0 <= cmd < 2^8 -> 0 < body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)) a1' a2'
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_IS_KEEPALIVE) fc None m (seg_rom rsegs)).
