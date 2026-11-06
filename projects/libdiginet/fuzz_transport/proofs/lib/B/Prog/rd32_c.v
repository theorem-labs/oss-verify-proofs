(* Modified by Theorem Labs, 2026-10: rd32 of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_mac_is_digidesign_c.v: a function image A inlines (into diginet_frame_parse), stated in that file's leaf form (a Z argument p in a0, a list l of 4 or more bytes at p, no condition on the byte values) with the 4 bytes [p, p + 4) in place of mac's 3, no null premise (the code has no null test), the result sx32 (Z_to_bv 64 (be32 l 0)) (DgnSpec.be32, sign-extended from bit 31 by `slliw` at 0x82608) and a1 .. a7 changed; shape donor of the premises: the UBSan image's contract lib/U/Prog/rd32_c.v (bytes_at of the 4 bytes for the two UBSan checks 0x825b4 and 0x825d8, and its result form). *)
(* rd32 on fuzz_transport.asan-ubsan (image B, 41113a03c82f): entry 0x8b734, 228 bytes, frame 16 bytes. Image A
   (fuzz_transport.asan) has no out-of-line copy of this function (no symbol rd32 there): it inlines it into
   diginet_frame_parse, so this file has no image-A twin.
   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/rd32_c.v (file sha256 dd853b028b8f; donor not
   released): the 228 code bytes are equal to fuzz_frame.asan-ubsan's (2574b26fc98e, the image of the donor's
   lib/B, entry 0x8258c) up to pc-relative words (compared word by word with capstone on the two symbol-bearing
   files: 57 words, the 5 that differ are the GOT-word load at 0x8b740 and the 4 error-path calls), and so is the
   caller diginet_frame_parse (1340 bytes, 335 words, the 27 that differ are its GOT-word load and its calls), so
   the statement is fuzz_frame's with the module paths, the entry, every pc (+ 0x91a8), the cells GOT_CELL_K /
   CELL_K and the error entry's name and address changed; each changed number was read again off the symbol-bearing
   twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's section-table fields and the build-id
   note, and the 228 code bytes of this function are equal in both files).

   Contract. The argument a0 is p, the address of the bytes l, a list of 4 or more bytes. The 4 bytes [p, p + 4) are
   outside the function's frame and are addressable (their shadow bytes mark them usable). The stack holds the frame
   [sp - 16, sp), the frame is in application memory, and the two cells GOT_CELL_K and CELL_K hold their values
   (asan_cells) outside the frame. The result in a0 is the big-endian value be32 l 0 (the libdiginet model) of the bytes 0..3 of
   l, as the code leaves it in the 64-bit register: sign-extended from bit 31, sx32 (Z_to_bv 64 (be32 l 0)). The
   function changes a1, a2, a3, a4, a5, a6, a7 and the bytes of its own frame. It keeps all other registers and all
   other memory.

   The caller: diginet_frame_parse at 0x8b3d8 (a0 = buf + 18, set at 0x8b3d4: h->send_counter;
   src/diginet_frame.c:80) and at 0x8b400 (a0 = buf + 22, set at 0x8b3fc: h->ack_counter; src/diginet_frame.c:81).
   It stores the low 32 bits of the result (`sw` at 0x8b3f4 for the first call).

   Facts read off the twin (symbol rd32, value 0x8b734, size 228, 57 words):
   - 0x8b734 `addi sp,sp,-16`: the frame is 16 bytes. 0x8b738 stores ra (8 bytes) at sp - 8, 0x8b7cc loads it back,
     0x8b7d0 restores sp, 0x8b7d4 returns.
   - 0x8b740 loads 8 bytes at GOT_CELL_K 0xa3cf0 (the address CELL_K 0xac678); 0x8b744 loads 8 bytes at CELL_K (the
     value 0x7fff8000) into a3. asan_cells gives both values.
   - Byte 0: 0x8b748-0x8b750 load the shadow byte k0 of p at (p >> 3) + 0x7fff8000 (signed, `lb`); 0x8b770 loads the
     byte at p into a4.
   - UBSan check 1 (p + 1, src/diginet_frame.c:14): 0x8b758 `li a1,-1`, 0x8b75c `beq a0,a1` goes to the unimp word at
     0x8b7d8 when p = 2^64 - 1. Not taken: bytes_at rsegs m p l with 4 <= length l gives p + 4 <= 2^64.
   - Byte 1: 0x8b760-0x8b76c load the shadow byte k1 of p + 1; 0x8b794 loads the byte at p + 1 into a5.
   - UBSan check 2 (p + 3): 0x8b778-0x8b780 `addi a1,a0,3`, `li a2,2`, `bltu a1,a2` go to the unimp word at 0x8b7d8
     when p + 3 wraps to 0 or 1 (p >= 2^64 - 3). Not taken: the same bound p + 4 <= 2^64.
   - Byte 2: 0x8b784-0x8b790 load the shadow byte k2 of p + 2 into a6; 0x8b7a8 loads the byte at p + 2 into a0.
   - Byte 3: 0x8b79c-0x8b7a4 load the shadow byte k3 of p + 3; 0x8b7b4 loads the byte at p + 3 into a1.
   - The value: 0x8b7b0 `slliw a2,a4,0x18` puts byte 0 at bits 24..31 and copies bit 31 into bits 32..63;
     0x8b7b8-0x8b7c8 put byte 1 at bits 16..23, byte 2 at bits 8..15 and byte 3 at bits 0..7 and `or` the four:
     a0 = sx32 (Z_to_bv 64 (be32 l 0)).
   - The error path: when a shadow byte k is not 0 (`bnez` at 0x8b754, 0x8b774, 0x8b798, 0x8b7ac), the code compares
     (a mod 8) with k (0x8b7dc-0x8b7e0, 0x8b7e8-0x8b7ec, 0x8b7f8-0x8b7fc, 0x8b808-0x8b80c). It goes back to the byte
     load when (a mod 8) < k, else it calls __asan_report_load1 (0x59504, DgnTransportBAddr.v
     TB___asan_report_load1) at 0x8b7e4, 0x8b7f4, 0x8b804 or 0x8b814. The premise `addressable m p 4` gives, for each
     of the 4 bytes, k = 0 or (a mod 8) < k <= 7, so the code reaches no error-path call. Each byte load comes after
     the check of its own shadow byte.
   - The error paths: four __asan_report_load1 calls and the unimp word 0x8b7d8 (the target of the two UBSan
     branches); none is reached.
   - Registers written: a0 (the result), a1, a2, a3, a4, a5, a6, and a7 (only at 0x8b7f8). Memory written: the 8
     bytes at sp - 8.

   Premise choice. The premises give all 4 bytes [p, p + 4), with no condition: the code reads the 4 bytes and their
   shadow bytes on every run. There is no p <> 0 premise: the code has no null test (its two UBSan checks are
   pointer-overflow checks). The length premise is `(4 <= length l)%nat` (the form of diginet_mac_is_digidesign's
   `(3 <= length l)%nat`; the UBSan image's contract states `length l = 4%nat`): the caller can pass the input bytes
   from buf + 18 (or buf + 22) on, and be32 l 0 reads only the bytes 0..3 of l. bytes_at of these 4 or more bytes
   gives p + 4 <= 2^64, which keeps both UBSan checks from firing.

   Form: fuzz_frame's lib/B/Prog/rd32_c.v, after lib/A/Prog/diginet_mac_is_digidesign_c.v (registers, stk, app_mem,
   asan_cells, off_stk of the cells, addressable, the post). There is no shadow_rw premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition RD32 : Z := 0x8b734.
Definition RD32_FRAME : Z := 16.

Definition rd32_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (l : list byte) (lo : Z),
    (4 <= length l)%nat ->
    bytes_at rsegs m p l ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RD32_FRAME <= bv_unsigned sp ->
    off_stk sp RD32_FRAME p 4 ->
    app_mem (bv_unsigned sp - RD32_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RD32_FRAME GOT_CELL_K 8 ->
    off_stk sp RD32_FRAME CELL_K 8 ->
    addressable m p 4 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sx32 (Z_to_bv 64 (be32 l 0))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RD32_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RD32) fc None m (seg_rom rsegs)).
