(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame: module paths, FrameSpec -> DgnSpec DgnLib, entry 0x13b84 -> 0x13cec, the header's image, addresses and caller. *)
(* Contract of diginet_body_check in fuzz_decode.plain.
   Source: src/diginet_codec.c:47-64 at 835f336c. It calls diginet_cursor_init (0x13b10) one
   time and diginet_msg_next (0x13b34) in a loop; both use no stack.
   Address 0x13cec, size 268 bytes. Stack frame: 144 bytes (the cursor at sp - 96, the
   message at sp - 136).
   Arguments: a0 is the address body, a1 the length of the bytes bb at body. The caller is
   check_refusal; it gives the body the harness decodes.
   Preconditions:
   - body is not 0;
   - the bytes bb at body are readable (bytes_at);
   - the stack from lo to sp is writable (stk), and lo + 144 <= sp;
   - the bytes at body are not in the 144 bytes below sp;
   - mem_inv holds.
   Result: a0 is body_check bb: -10 (REFUSED) when the cursor finds a sysex F0 13 xx 70 .. F7
   or the prefix scan finds F0 13 xx 70, else 0. By DgnLib.body_check_spec this is -10
   exactly when system_at bb.
   The function writes only the 144 bytes below sp. It keeps ra, sp, gp, tp, s0..s11, the
   floating-point registers and fcsr, and the stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_BODY_CHECK : Z := 0x13cec.

Definition diginet_body_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_BODY_CHECK) fc None m (seg_rom rsegs)).
