(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the contract of diginet_decoder_init (src/diginet_decode.c:11-18) on the UBSan
   image, at 0x13f84 (24 words, the last the unimp at 0x13fe0), over lib/Spec/DgnLib.v's diginet_decoder_init.
   Arguments: a0 = d, the address of a struct diginet_decoder (40 bytes, DgnLayout.v decoder_cells); a1 = p, the
   pointer of a personality (DgnLayout.v personality_ptr of the model's option); a2 = body; a3 = len. The one caller
   is LLVMFuzzerTestOneInput 0x12edc (d = sp + 0x108, p = the result of diginet_personality_of at 0x12ec8, body and
   len the harness's body).
   The function saves ra, s0 and s1 in a 32-byte frame below sp (0x13f84-0x13f90), calls diginet_cursor_init
   (d, body, len) (0x13fb4), and, when p is NULL, diginet_personality_of (DIGINET_DESK_CONTROL24) (0x13fbc-0x13fc4);
   it stores the pointer at d + 32 (0x13fc8) and returns.
   - d == NULL returns at once (0x13f94 `beqz a0` to the epilogue, diginet_decode.c:14-15); the model has no NULL
     decoder (DgnLib.v header), so d <> 0 is a premise.
   - The cursor's len is len only when body is not NULL (diginet_msg.c:15); the model's diginet_cursor_init is len
     (DgnLib.v: every body the harness passes is a block or a pointer into it), so body <> 0 is a premise.
   - p is NULL or a personalities entry (the model's None, Some 0, Some 1: what diginet_personality_of returns).
   The UBSan check site: 0x13f9c `andi a0, a0, 7` / 0x13fa0 `bnez` to the unimp at 0x13fe0, d misaligned for the
   store of d->p: d mod 8 = 0. The callees' own check sites are their contracts'.
   Result: the 25 cursor bytes and the pointer at d hold decoder_cells of the model's decoder; the 7 padding bytes of
   the cursor keep their bytes (the cursor_init contract writes 25 bytes); memory changes only in the 40 bytes at d
   and in the frame; s0..s11, ra, sp, gp, tp are kept; a0..a7 and t0..t6 are written. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
Open Scope Z_scope.

Definition DIGINET_DECODER_INIT : Z := 0x13f84.
Definition DIGINET_DECODER_INIT_FRAME : Z := 32.

Definition diginet_decoder_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (d body len lo : Z) (p : option Z) (dj : list byte),
    d <> 0 ->
    (* UBSan only: 0x13f9c / 0x13fa0, the alignment check of d *)
    d mod 8 = 0 ->
    body <> 0 ->
    0 <= body < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    p = None \/ p = Some 0 \/ p = Some 1 ->
    rw_cells rsegs m d [CB 40 dj] ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_DECODER_INIT_FRAME <= bv_unsigned sp ->
    d + 40 <= bv_unsigned sp - DIGINET_DECODER_INIT_FRAME \/ bv_unsigned sp <= d ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 40); (bv_unsigned sp - DIGINET_DECODER_INIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' d (decoder_cells body (firstn 7 (skipn 25 dj)) (diginet_decoder_init p len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (personality_ptr p)) (Z_to_bv 64 body)
               (Z_to_bv 64 len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_DECODER_INIT) fc None m (seg_rom rsegs)).
