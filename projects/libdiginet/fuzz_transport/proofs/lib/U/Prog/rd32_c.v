(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/rd32_c.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Contract of rd32 (static) in fuzz_transport.ubsan. fuzz_transport.plain inlines this function into
   diginet_frame_parse, so it has no plain twin; its caller here takes this contract as a
   hypothesis.
   Source: src/diginet_frame.c:12-15 at 835f336c.
   Address 0x1821c, size 68 bytes. No stack frame and no call.
   Argument: a0 is the address p. The caller is diginet_frame_parse, at 0x1814c (p = buf + 18,
   h->send_counter) and 0x18160 (p = buf + 22, h->ack_counter).
   Preconditions: the 4 bytes l at p are readable (bytes_at).
   Result: a0 is the big-endian value be32 l 0 of the 4 bytes, as a uint32_t return value is
   in RV64: sign-extended from bit 31 (sx32; slliw at 0x18240). The caller stores its low 32
   bits (sw). The function writes a1, a2 and a3. It writes no memory.
   It keeps all other registers, the memory and the stack.
   UBSan checks: two branches to the trap at 0x1825c (unimp), the pointer-overflow checks of
   p + 1 .. p + 3: 0x18220 (p = 2^64 - 1) and 0x1822c (p + 3 wraps to 0 or 1). bytes_at of the
   4 bytes gives p + 4 <= 2^64, so neither branch is taken.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition RD32 : Z := 0x1821c.

Definition rd32_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (l : list byte),
    length l = 4%nat ->
    bytes_at rsegs m p l ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sx32 (Z_to_bv 64 (be32 l 0))) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RD32) fc None m (seg_rom rsegs)).
