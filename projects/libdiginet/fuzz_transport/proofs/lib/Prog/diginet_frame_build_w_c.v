(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_build_w_c.v at b8f2ecf2c3ff0406d93584348ebba6e5957c14ce to fuzz_transport's images *)
(* Wide contract of diginet_frame_build in fuzz_transport.plain.
   Source: src/diginet_frame.c:93-127 at 835f336c. Address 0x178d8 (diginet_frame_build_c.v).
   It is diginet_frame_build_contract with two premises made wider, for the callers send_control
   and send_data, which give body = NULL with body_len = 0 and a sum mode they load from memory:
   - body is not 0, or the body is empty (src/diginet_frame.c:98, body_len && !body);
   - mode is any int (-2^31 <= mode < 2^31). The register a7 holds mode sign-extended to 64 bits,
     as the calling convention gives an int argument. The binary tests bltu 1, a7 at 0x17934:
     it continues only when a7 is 0 or 1 as a 64-bit value, that is when mode is 0 or 1; else
     it returns -1 (DIGINET_E_ARG, src/diginet_frame.c:100-101).
   Result: a0 is build_code_w bb cap mode: -1 when mode is not 0 or 1, else build_code bb cap.
   The two DIGINET_E_ARG tests come before the length test (0x17958), so a mode other than 0 and
   1 gives -1 for every body. On a code under 0 the function writes no byte at out
   (build_out_w is then oj); for mode 0 or 1 build_out_w is build_out. All other premises and
   the result are those of diginet_frame_build_contract.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_build_c.
Import ListNotations.
Open Scope Z_scope.

(* The code diginet_frame_build returns for any int mode: DIGINET_E_ARG (-1) unless mode is
   DIGINET_SUM_BODY (0) or DIGINET_SUM_ZERO (1). *)
Definition build_code_w (bb : list byte) (cap mode : Z) : Z :=
  if (mode =? 0) || (mode =? 1) then build_code bb cap else -1.

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
