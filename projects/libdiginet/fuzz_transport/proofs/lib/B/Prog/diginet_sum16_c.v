(* Modified by Theorem Labs, 2026-10: diginet_sum16 of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_mac_is_digidesign_c.v: a function image A inlines (into diginet_frame_parse and diginet_frame_build), stated in that file's leaf form with a second Z argument in a1 (n, the length of the bytes bb at p), the result DgnSpec.lib_sum16 bb, t0 and a1 .. a7 changed, and the facts of the range [p, p + n) under the condition bb <> [] (the code reads nothing when n = 0), as lib/A/Prog/diginet_announce_parse_c.v states facts under the condition of the access; shape donor of the premises: the UBSan image's contract lib/U/Prog/diginet_sum16_c.v (p <> 0 for the null check 0x81e68, bytes_at of bb for the checks 0x81e58 and 0x81e64). *)
(* diginet_sum16 on fuzz_transport.asan-ubsan (image B, 41113a03c82f): entry 0x8afd8, 144 bytes, frame 16 bytes.
   Image A (fuzz_transport.asan) has no out-of-line copy of this function (no symbol diginet_sum16 there): it inlines
   it into diginet_frame_parse and diginet_frame_build, so this file has no image-A twin.
   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/diginet_sum16_c.v (file sha256 a9b34da4218e;
   donor not released): the 144 code bytes are equal to fuzz_frame.asan-ubsan's (2574b26fc98e, the image of the donor's
   lib/B, entry 0x81e30) up to pc-relative words (compared word by word with capstone on the two symbol-bearing
   files: 36 words, the 2 that differ are the GOT-word load at 0x8afec and the error-path call), and so are the
   callers diginet_frame_parse (1340 bytes, 335 words, the 27 that differ are its GOT-word load and its calls) and
   diginet_frame_build (1492 bytes, 373 words, the 29 that differ are its GOT-word load and its calls), so the
   statement is fuzz_frame's with the module paths, the entry, every pc (+ 0x91a8), the cells GOT_CELL_K / CELL_K,
   the error entry's name and address and the callers' callers changed; each changed number was read again off the
   symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's section-table fields and
   the build-id note, and the 144 code bytes of this function are equal in both files).

   Contract. The argument a0 is p, the address of the bytes bb, and p is not 0 when bb is not empty; a1 is n, the
   length of bb. The stack
   holds the frame [sp - 16, sp), the frame is in application memory, and the two cells GOT_CELL_K and CELL_K hold
   their values (asan_cells) outside the frame. When bb is not empty, the n bytes [p, p + n) are outside the frame and
   addressable (their shadow bytes mark them usable). The result in a0 is lib_sum16 bb (the libdiginet model), the sum of the
   bytes of bb cut to 16 bits. The function changes t0, a1, a2, a3, a4, a5, a6, a7 and the bytes of its own frame. It
   keeps all other registers and all other memory.

   The callers: diginet_frame_parse at 0x8b54c (a0 = buf + 30, set at 0x8b508; a1 = numbytes - 16, set at 0x8b524:
   f->body and f->body_len; src/diginet_frame.c:88) and diginet_frame_build at 0x8b9cc (a0 = body, a1 = body_len, set
   at 0x8b9c4-0x8b9c8; only in mode 0, `beqz s5` at 0x8b9b4; src/diginet_frame.c:116). diginet_frame_parse gives a p
   that is not 0: buf + 30 lies in the received bytes (its caller diginet_session_rx passes buf = its second argument,
   s8, which it tests for 0 at 0x878b0 before the call at 0x878d0). diginet_frame_build can give p = 0 with n = 0:
   its premise is the wide plain contract's body <> 0 \/ body_len = 0 (lib/Prog/diginet_frame_build_w_c.v), and its
   caller send_control passes body = 0, body_len = 0 (a5 = a6 = 0 at 0x87078 / 0x8707c) with mode =
   s->cfg.sum_mode, which can be 0; diginet_frame_build passes them on unchanged. When bb is not empty both give
   p <> 0 (diginet_frame_build: body_len <> 0 with body = 0 returns -1 at 0x8b87c - 0x8b888 before the call).

   Facts read off the twin (symbol diginet_sum16, value 0x8afd8, size 144, 36 words):
   - 0x8afd8 `addi sp,sp,-16`: the frame is 16 bytes. 0x8afdc stores ra (8 bytes) at sp - 8, 0x8b058 loads it back,
     0x8b05c restores sp, 0x8b060 returns.
   - 0x8afe0 sets a3 (the sum) to 0. 0x8afe4: when a1 = 0 the code goes to 0x8b050 at once: it reads no byte, no
     shadow byte and no cell, and returns a0 = 0 = lib_sum16 [].
   - 0x8afec loads 8 bytes at GOT_CELL_K 0xa3cf0 (the address CELL_K 0xac678); 0x8aff0 loads 8 bytes at CELL_K (the
     value 0x7fff8000) into a4. asan_cells gives both values. 0x8aff4 sets a5 = (p <> 0); 0x8aff8 / 0x8affc set
     a6 = a2 = p.
   - The loop, one turn for each i < n (a2 = a6 = p + i, a1 = n - i at the loop head 0x8b000):
     - UBSan check 1 (p + i, src/diginet_frame.c:46): 0x8b000 `bltu a2,a0` goes to the unimp word at 0x8b064 when
       p + i < p (the pointer wraps). Not taken: bytes_at rsegs m p bb gives p + n <= 2^64, so p + i < 2^64.
     - UBSan check 2 (the null rule of p + i): 0x8b004-0x8b00c `seqz a7,a2`, `xor a7,a5,a7`, `beqz a7` go to the unimp
       word when (p <> 0) = (p + i = 0). Not taken: bb is not empty in the loop, so p <> 0 by the premise, and p + i
       does not wrap, so p + i <> 0.
     - UBSan check 3 (p = 0): 0x8b010 `beqz a0` goes to the unimp word. Not taken: bb is not empty in the loop, so
       p <> 0 by the premise.
     - 0x8b014-0x8b01c load the shadow byte k of p + i at ((p + i) >> 3) + 0x7fff8000 (signed, `lb`). When k <> 0
       (0x8b020), 0x8b040-0x8b044 compare (p + i) mod 8 (t0 = (p + i) & 7) with k: the code goes back to the byte
       load when (p + i) mod 8 < k, else it calls __asan_report_load1 (0x59504, DgnTransportBAddr.v
       TB___asan_report_load1) at 0x8b04c (a0 = p + i, 0x8b048). The premise `addressable m p n` gives k = 0 or
       (p + i) mod 8 < k <= 7, so the code reaches no error-path call.
     - 0x8b024 loads the byte at p + i (a6); 0x8b028-0x8b034: a1 = a1 - 1, a2 = a2 + 1, a3 = a3 + the byte,
       a6 = a6 + 1; 0x8b038 `bnez a1` starts the next turn, else 0x8b03c goes to 0x8b050.
   - 0x8b050-0x8b054 `slli a0,a3,0x30`, `srli a0,a0,0x30`: a0 = a3 mod 2^16. a3 is the sum of the bytes of bb mod
     2^64 (64-bit adds), so a0 = sum_bytes bb mod 2^16 = lib_sum16 bb (the libdiginet model: (sum mod 2^32) mod 2^16).
   - The error paths: one __asan_report_load1 call (0x8b04c) and the unimp word 0x8b064 (the target of the three
     UBSan branches 0x8b000, 0x8b00c, 0x8b010); none is reached.
   - Registers written: a0 (the result) and a3 on every run; when n <> 0 also a1 (counted down to 0), a2, a4, a5, a6,
     a7, and t0 (only at 0x8b040, when a shadow byte is not 0). Memory written: the 8 bytes at sp - 8.

   Premise choice. The facts of [p, p + n) (p <> 0, off_stk, addressable) are stated under the condition bb <> [],
   the condition under which the code reads the range or tests p (0x8afe4): with n = 0 the code reads nothing at p
   and reaches none of the three UBSan checks, and a caller with an empty body need not place [p, p) anywhere, nor
   give a p that is not 0 (diginet_frame_build's call with p = 0, n = 0 above; the UBSan image's contract states
   p <> 0 without the condition). bytes_at is unconditional, as the UBSan image's contract states it: bytes_at of
   bb = [] asks only 0 <= p <= 2^64. The premises give all n bytes: the code reads each byte of bb on every run with
   n <> 0.

   Form: fuzz_frame's lib/B/Prog/diginet_sum16_c.v, after lib/A/Prog/diginet_mac_is_digidesign_c.v (registers, stk,
   app_mem, asan_cells, off_stk of the cells, addressable, the post) and lib/A/Prog/diginet_announce_parse_c.v (facts
   under the condition of the access). There is no shadow_rw premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_SUM16 : Z := 0x8afd8.
Definition DIGINET_SUM16_FRAME : Z := 16.

Definition diginet_sum16_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte) (lo : Z),
    (bb <> [] -> p <> 0) ->
    bytes_at rsegs m p bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SUM16_FRAME <= bv_unsigned sp ->
    (bb <> [] -> off_stk sp DIGINET_SUM16_FRAME p (Z.of_nat (length bb))) ->
    app_mem (bv_unsigned sp - DIGINET_SUM16_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SUM16_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SUM16_FRAME CELL_K 8 ->
    (bb <> [] -> addressable m p (Z.of_nat (length bb))) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (lib_sum16 bb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SUM16_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length bb))) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SUM16) fc None m (seg_rom rsegs)).
