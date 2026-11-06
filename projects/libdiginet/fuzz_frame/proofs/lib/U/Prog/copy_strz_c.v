(* Contract of copy_strz (static) in fuzz_frame.ubsan. fuzz_frame.plain inlines this function
   into diginet_announce_parse, so it has no plain twin; its caller here takes this contract as
   a hypothesis.
   Source: src/diginet_frame.c:130-136 at 835f336c. The binary is the function for dst_size 10
   and n 9, the only values its caller gives (sizeof a->version, sizeof a->name; 9): the loop
   stops at i = 9 (0x13ffc).
   Address 0x13fc4, size 100 bytes. No stack frame and no call.
   Arguments: a0 is the address dst of a 10-byte field, a1 the address src. The caller is
   diginet_announce_parse, at 0x13f88 (dst = a->version, src = f->body + 15) and 0x13fa4
   (dst = a->name, src = f->body + 24).
   Preconditions:
   - src is not 0; the 9 bytes s at src are readable (bytes_at);
   - the 10 bytes old at dst are writable (rw_cells);
   - the 10 bytes at dst and the 9 bytes at src do not overlap;
   - mem_inv holds.
   Result: the function writes the field as DgnSpec.copy_strz 10 9 s old gives it: the
   k = copy_len 10 9 s bytes of s before its first NUL (at most 9), then a NUL; it does not
   write the bytes k+1..9. It writes a0 and a2..a7, and it keeps a1.
   The function writes only the 10 bytes at dst. It keeps all other registers.
   UBSan checks: five branches to the trap at 0x14024 (unimp):
   - 0x13fd4: src + i < src (src + i wraps past 2^64), each turn before it reads src[i];
   - 0x13fe0: src is not 0 and src + i is 0, or src is 0 and src + i is not 0;
   - 0x13fe4: src is 0;
   - 0x13ff0: dst + i wraps past 2^64, before it writes dst[i];
   - 0x14014: dst + k wraps past 2^64, before it writes the NUL.
   The function reads src[i] only for i < 9, and writes dst[i] only for i <= 9. bytes_at gives
   src + 9 <= 2^64 and rw_cells gives dst + 10 <= 2^64, so nothing wraps, and src is not 0; no
   branch is taken.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition COPY_STRZ : Z := 0x13fc4.

Definition copy_strz_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst src : Z) (s old : list byte),
    src <> 0 ->
    length s = 9%nat -> bytes_at rsegs m src s ->
    rw_cells rsegs m dst [CB 10 old] ->
    dst + 10 <= src \/ src + 9 <= dst ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 src) a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(dst, dst + 10)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' dst [CB 10 (copy_strz 10 9 s old)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 COPY_STRZ) fc None m (seg_rom rsegs)).
