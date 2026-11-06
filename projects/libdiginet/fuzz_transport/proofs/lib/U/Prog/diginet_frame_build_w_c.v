(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_build_w_c.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Wide contract of diginet_frame_build in fuzz_transport.ubsan (0x18260), for the calls of a
   caller that gives body = NULL with body_len = 0, and a sum mode that is any int (an enum
   diginet_sum_mode read from memory).
   Source: src/diginet_frame.c:93-127 at 835f336c. Its walk takes the wide contracts of
   diginet_body_check (U/Prog/diginet_body_check_w_c.v) and diginet_sum16
   (U/Prog/diginet_sum16_w_c.v) and the contracts of memcpy and memset (U/Prog/memcpy_c.v,
   memset_c.v) as hypotheses.
   Differences from U/Prog/diginet_frame_build_c.v:
   - the premise body <> 0 becomes body <> 0 \/ length bb = 0;
   - the premise mode = 0 \/ mode = 1 becomes -2^31 <= mode < 2^31 (a7 = Z_to_bv 64 mode, the
     int sign-extended to 64 bits);
   - the result is build_code_w and the bytes at out are build_out_w: for a mode other than 0
     or 1 the result is -1 (DIGINET_E_ARG) and no byte at out changes; for mode 0 or 1 they are
     build_code and build_out (diginet_frame_build_contract_of_w,
     U/Prog/diginet_frame_build_w.v, shows that this contract gives the narrow one).
   All other premises are the same.
   The order of the tests in the binary: out, dst, src, hp against 0 (0x18294 .. 0x182ac), then
   body_len != 0 && body == 0 (0x182c0 .. 0x182cc), then the mode at 0x182d8 (bltu 1, a7: a7
   above 1 as unsigned, which for -2^31 <= mode < 2^31 is mode other than 0 and 1), then
   body_len > 1484 at 0x182e0. So a bad mode gives -1 before DIGINET_E_LENGTH, before the call
   of diginet_body_check and before every trap branch (the first is at 0x18338).
   The path with body = NULL and body_len = 0 (mode 0 or 1): the test at 0x182cc is not taken
   (body_len is 0); diginet_body_check (NULL, 0) answers 0 (its wide contract); the frame
   length is 60; past cap >= 60 (0x18318) the trap branches on out + 6 .. out + 30 and the
   one on hp & 3 (0x183dc) are those of the narrow path and are not taken (cap >= 60 and
   out + cap <= 2^64; hp mod 4 = 0); in mode 0, diginet_sum16 (NULL, 0) answers 0 (its wide
   contract); 0x184a4 (beqz body_len) skips the trap branch 0x184ac and the memcpy of the body;
   0x184cc (out + 30 wraps) is not taken, and memset (out + 30, 0, 30) writes the padding.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_build_c.
Import ListNotations.
Open Scope Z_scope.

(* The result for any mode: -1 (DIGINET_E_ARG) for a mode other than DIGINET_SUM_BODY (0) and
   DIGINET_SUM_ZERO (1), else build_code. *)
Definition build_code_w (bb : list byte) (cap mode : Z) : Z :=
  if orb (mode =? 0) (mode =? 1) then build_code bb cap else -1.

(* The cap bytes at out after the call; oj are the bytes before it. *)
Definition build_out_w (dmac smac : list byte) (send ack retry cmd ncmds : Z) (bb : list byte)
    (mode : Z) (oj : list byte) : list byte :=
  let n := build_code_w bb (Z.of_nat (length oj)) mode in
  if 0 <=? n then build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) ++ skipn (Z.to_nat n) oj
  else oj.

Definition diginet_frame_build_contract_w : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out dst src hp body mode lo send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte),
    0 < out < 2^64 -> dst <> 0 -> src <> 0 -> hp <> 0 -> body <> 0 \/ length bb = 0%nat ->
    -2^31 <= mode < 2^31 ->
    hp mod 4 = 0 ->
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
    bv_unsigned sp mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> 0 < lo -> lo + 240 <= bv_unsigned sp ->
    out + Z.of_nat (length oj) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= out ->
    dst + 6 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= dst ->
    src + 6 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= src ->
    hp + 16 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= hp + 4 ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (build_code_w bb (Z.of_nat (length oj)) mode))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' out [CB (length oj) (build_out_w dmac smac send ack retry cmd ncmds bb mode oj)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 (Z.of_nat (length oj)))
               (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 hp) (Z_to_bv 64 body)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 mode)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_BUILD) fc None m (seg_rom rsegs)).
