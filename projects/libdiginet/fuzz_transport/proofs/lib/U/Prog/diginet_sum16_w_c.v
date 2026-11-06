(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_sum16_w_c.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Wide contract of diginet_sum16 in fuzz_transport.ubsan (0x17f60), for a caller that gives p = 0
   with no bytes. diginet_frame_build calls diginet_sum16 (body, body_len) in the mode
   DIGINET_SUM_BODY (0x183b8), and a caller of diginet_frame_build can give body = NULL and
   body_len = 0.
   Source: src/diginet_frame.c:42-48 at 835f336c.
   Difference from U/Prog/diginet_sum16_c.v: the premise p <> 0 becomes p <> 0 \/ length bb = 0.
   All other premises and the result are the same; diginet_sum16_contract_of_w
   (U/Prog/diginet_sum16_w.v) shows that this contract gives the narrow one.
   The empty path: a1 = 0, so 0x17f64 (beqz a1) goes to 0x17fa0 before the loop, and a0 is the
   low 16 bits of a2 = 0, which is lib_sum16 []. The three trap branches (0x17f74, 0x17f80,
   0x17f84, to the unimp at 0x17fac) are in the loop, so this path does not reach them.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_sum16_c.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_sum16_contract_w : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte),
    p <> 0 \/ length bb = 0%nat ->
    bytes_at rsegs m p bb ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lib_sum16 bb)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SUM16) fc None m (seg_rom rsegs)).
