(* Contract of diginet_frame_parse in fuzz_frame.ubsan, the twin of
   Prog/diginet_frame_parse_c.v (fuzz_frame.plain).
   Source: src/diginet_frame.c:60-91 at 835f336c. The binary inlines rd16. It calls memcpy
   (0x1bd9c) two times, rd32 (0x13c00) two times and diginet_sum16 (0x13944) one time; none of
   them uses stack. Its walk takes their contracts (U/Prog/memcpy_c.v, rd32_c.v,
   diginet_sum16_c.v) as hypotheses.
   Address 0x13a18, size 488 bytes. Stack frame: 48 bytes (addi sp, sp, -0x30 at 0x13a18).
   Arguments: a0 is the address buf of the frame, a1 its length len, a2 the address f of a
   struct diginet_frame (64 bytes). The caller is LLVMFuzzerTestOneInput; it gives its copy of
   the input, the input size and its local frame struct.
   Preconditions:
   - 0 < buf and buf + len < 2^64 (so the register a0 is not 0, and buf + 30 does not wrap);
     f is not 0 and f is 8-aligned;
   - the len bytes b at buf are readable (bytes_at);
   - the 64 bytes fj at f are writable (rw_cells);
   - the 64 bytes at f, the bytes at buf and the 48 bytes below sp do not overlap;
   - the stack from lo to sp is writable (stk), and lo + 48 <= sp;
   - mem_inv holds.
   Result: a0 is fr_code b: 0, or -2, -3, -4. On 0 the function writes the 64 bytes at f as
   parse_cells gives them: dst and src (the bytes 0..5 and 6..11 of b), the EtherType,
   numbytes, sum, the two counters, retry, cmd, ncmds, body (buf + 30), body_len, pad_len,
   body_sum and sum_matches, as the libdiginet model (DgnSpec, DgnLib) reads them. It does not write the bytes 14, 15 and
   59..63 of f. On a code that is not 0 it writes no byte of f.
   The function writes only the 64 bytes at f and the 48 bytes below sp. It keeps ra, sp, gp,
   tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   UBSan checks: branches to the trap at 0x13bfc (unimp):
   - 0x13ac4: f & 7 is not 0 (the alignment of struct diginet_frame), on the path of code 0.
     The premise f mod 8 = 0 keeps it from firing;
   - 0x13a60, 0x13a68, 0x13a8c, 0x13a98, 0x13adc, 0x13b04, 0x13b0c, 0x13b28, 0x13b3c,
     0x13b50, 0x13b58, 0x13b74, 0x13b84: the pointer-overflow checks of buf + 12 .. buf + 29
     (and of h = buf + 14 plus 2 .. 15). They come after the test len >= 30 (0x13a50), and
     buf + len < 2^64, so none of them is taken;
   - 0x13b94: buf + 30 wraps past 2^64 (buf > 2^64 - 31), the check of f->body = buf + 30.
     The plain premise buf < 2^64 lets buf + 30 = 2^64 when len = 30; the premise
     buf + len < 2^64 keeps it from firing.
   Differences from the plain statement: buf + len < 2^64 in place of buf < 2^64, and the
   premise f mod 8 = 0. The caller gives a heap block far below 2^64 for buf and its local
   frame struct (8-aligned) for f.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_FRAME_PARSE : Z := 0x13a18.

(* The struct diginet_frame after a parse of the frame bytes b at buf that answered 0. fj are
   the 64 bytes before the call. The same cells as in Prog/diginet_frame_parse_c.v. *)
Definition parse_cells (buf : Z) (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b);                                          (*  0 dst *)
    CB 6 (fr_src b);                                          (*  6 src *)
    C2 (Z_to_bv 64 (fr_ethertype b));                         (* 12 ethertype *)
    CB 2 (firstn 2 (skipn 14 fj));                            (* 14 not written *)
    C2 (Z_to_bv 64 (fr_numbytes b));                          (* 16 h.numbytes *)
    C2 (Z_to_bv 64 (fr_sum b));                               (* 18 h.sum *)
    C4 (Z_to_bv 64 (fr_send b));                              (* 20 h.send_counter *)
    C4 (Z_to_bv 64 (fr_ack b));                               (* 24 h.ack_counter *)
    C2 (Z_to_bv 64 (fr_retry b));                             (* 28 h.retry *)
    C1 (b8 (fr_cmd b));                                       (* 30 h.cmd *)
    C1 (b8 (fr_ncmds b));                                     (* 31 h.num_commands *)
    C8 (Z_to_bv 64 (buf + 30));                               (* 32 body *)
    C8 (Z_to_bv 64 (fr_body_len b));                          (* 40 body_len *)
    C8 (Z_to_bv 64 (fr_pad_len b));                           (* 48 pad_len *)
    C2 (Z_to_bv 64 (fr_body_sum b));                          (* 56 body_sum *)
    C1 (b8 (if fr_sum b =? fr_body_sum b then 1 else 0));     (* 58 sum_matches *)
    CB 5 (skipn 59 fj) ].                                     (* 59 not written *)

Definition diginet_frame_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f lo : Z) (b fj : list byte),
    0 < buf -> buf + Z.of_nat (length b) < 2^64 -> f <> 0 -> f mod 8 = 0 ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m f [CB 64 fj] ->
    f + 64 <= buf \/ buf + Z.of_nat (length b) <= f ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    buf + Z.of_nat (length b) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= buf ->
    f + 64 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= f ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fr_code b)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp); (f, f + 64)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' f (if fr_code b =? 0 then parse_cells buf b fj else [CB 64 fj]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 f)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_PARSE) fc None m (seg_rom rsegs)).
