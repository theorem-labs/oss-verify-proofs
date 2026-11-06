(* Modified by Theorem Labs, 2026-10: copy_strz of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_cursor_init_c.v: a function image A inlines (into diginet_announce_parse; dst_size 10 and n 9 folded in), stated in that file's writing-leaf form (the arguments dst and src in a0 and a1, the written range [dst, dst + 10) in the post's munch, the written cells in the post) with the written bytes' old value as lib/A/Prog/diginet_announce_parse_c.v states it (rw_cells of [CB 10 old]), the read range [src, src + 9) (bytes_at of 9 or more bytes s, off_stk, addressable), the overlap premise, the post's cells [CB 10 (DgnSpec.copy_strz 10 9 s old)], and t0, t1, t2, a0 .. a7, t3, t4 changed; shape donor of the premises: the UBSan image's contract lib/U/Prog/copy_strz_c.v (src <> 0 for the null check 0x82df4, bytes_at of s and rw_cells of dst for the pointer-overflow checks 0x82de4, 0x82df0, 0x82e10, 0x82e68, the overlap premise). *)
(* copy_strz on fuzz_transport.asan-ubsan (image B, 41113a03c82f): entry 0x8bf5c, 244 bytes, own frame 16 bytes.
   Image A (fuzz_transport.asan) has no out-of-line copy of this function (no symbol copy_strz there): it inlines it
   into diginet_announce_parse, so this file has no image-A twin.
   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/copy_strz_c.v (file sha256 d932b72ba333; donor
   not released): the 244 code bytes are equal to fuzz_frame.asan-ubsan's (2574b26fc98e, the image of the donor's
   lib/B, entry 0x82db4) up to pc-relative words (compared word by word with capstone on the two symbol-bearing
   files: 61 words, the 4 that differ are the GOT-word load at 0x8bf6c and the 3 error-path calls), and so is the
   caller diginet_announce_parse (368 bytes, 92 words, the 7 that differ are its GOT-word load and its 6 error-path
   calls), so the statement is fuzz_frame's with the module paths, the entry, every pc (+ 0x91a8), the cells
   GOT_CELL_K / CELL_K, the error entries' names and addresses and the caller's caller changed; each changed number
   was read again off the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 244 code bytes of this function are equal in both files).
   The source function takes dst_size and n; image B's copy has dst_size = 10 and
   n = 9 folded in (its only caller passes these values: the loop stops at i = 9, 0x8bfe0-0x8bfe8), so its arguments
   are dst and src only.
   Contract. a0 = dst, the address of a 10-byte field; a1 = src, with src <> 0. The caller is diginet_announce_parse:
   at 0x8bee0 (a0 = ap, set at 0x8bedc; a1 = body + 15, set at 0x8bed8: ap->version from f->body + 15;
   src/diginet_frame.c:148) and at 0x8bf04 (a0 = ap + 10, set at 0x8befc; a1 = body + 24, set at 0x8bf00: ap->name
   from f->body + 24; src/diginet_frame.c:149), where ap (its second argument, s0 = a1 at 0x8be00) is on_announce's
   local struct diginet_announce `a` (on_announce's call at 0x87e6c passes a1 = s10 = s3 + 32, set at 0x87d74: the 40
   bytes at offset 32 of its class-3 side-stack frame from __asan_stack_malloc_3 at 0x87d3c, or of the 32-aligned
   area it carves on the real stack when that call is skipped or returns 0, 0x87d54-0x87d58). Before each call
   diginet_announce_parse passes its own UBSan checks of body (0x8becc body = 0, 0x8bed4 body + 15 wraps; 0x8bef0,
   0x8bef8 for body + 24; each goes to its unimp word at 0x8bf28), so src is not 0.
   Premises: src <> 0; s is a list of 9 or more bytes at src (bytes_at); the 10 bytes at dst are writable and hold
   old (rw_cells); [dst, dst + 10) and [src, src + 9) do not overlap; the frame lies in the stack below sp (stk) and in
   application memory (app_mem of both ends); [src, src + 9), [dst, dst + 10) and the cells GOT_CELL_K and CELL_K lie
   outside the frame; the cells hold their values (asan_cells); [src, src + 9) and [dst, dst + 10) are addressable in
   the shadow map.
   Result: the 10 bytes at dst become DgnSpec.copy_strz 10 9 s old: the k = copy_len 10 9 s bytes of s before its
   first 0 byte (at most 9), then a 0 byte; the bytes k + 1 .. 9 keep old. The function writes no other byte outside
   its frame. It changes t0, t1, t2, a0 .. a7, t3 and t4 and keeps every other register. No result register is
   stated: the function returns nothing (at the return a0 = dst + k and a1 holds the shadow byte of dst + k).
   Facts read off the twin (symbol copy_strz, value 0x8bf5c, size 244, 61 words):
     - 0x8bf5c addi sp,sp,-16; 0x8bf60 stores ra at sp - 8; 0x8c02c loads it back; 0x8c030 addi sp,sp,16;
       0x8c034 ret.
     - 0x8bf64 sets a5 = i = 0. 0x8bf6c loads 8 bytes at GOT_CELL_K 0xa3cf0 (the address CELL_K 0xac678); 0x8bf70
       loads 8 bytes at CELL_K (the shadow base 0x7fff8000) into a4. 0x8bf74 a6 = 2^64 - 1 - dst (`not`); 0x8bf78
       a7 = (src <> 0); 0x8bf7c-0x8bf88 t0 = a2 = src and t1 = a3 = dst (each then steps with i).
     - The loop, from the head 0x8bf8c, for i = 0 .. 8:
       - UBSan check 1 (src + i, src/diginet_frame.c:133): 0x8bf8c `bltu a2,a1` goes to the unimp word at 0x8c038 when
         src + i < src (the pointer wraps). Not taken: bytes_at of s (9 or more bytes) gives src + 9 <= 2^64.
       - UBSan check 2 (the null rule of src + i): 0x8bf90-0x8bf98 `seqz t2,a2`, `xor t2,a7,t2`, `beqz t2` go to the
         unimp word when (src <> 0) = (src + i = 0). Not taken: src <> 0, and src + i does not wrap, so src + i <> 0.
       - UBSan check 3 (src = 0): 0x8bf9c `beqz a1` goes to the unimp word. Not taken: the premise src <> 0.
       - 0x8bfa0-0x8bfa8 load the shadow byte k of src + i (signed, `lb`). When k <> 0 (0x8bfac), 0x8bff0-0x8bff4
         compare (src + i) mod 8 with k: the code jumps back to the byte load 0x8bfb0 (0x8bff8) when (src + i) mod 8
         < k, else it calls __asan_report_load1 (0x59504, DgnTransportBAddr.v TB___asan_report_load1) at 0x8c04c (a0 =
         src + i, 0x8c048). addressable m src 9 gives
         k = 0 or (src + i) mod 8 < k <= 7, so the call is not reached.
       - 0x8bfb0 loads the byte c at src + i. When c = 0 (0x8bfb4) the code goes to 0x8c00c, which sets t2 = k = i.
       - UBSan check 4 (dst + i, before dst[i] = c, src/diginet_frame.c:134): 0x8bfb8 `bltu a6,a5` goes to the unimp
         word when 2^64 - 1 - dst < i, that is dst + i >= 2^64. Not taken: rw_cells of the 10 bytes at dst gives
         dst + 10 <= 2^64, and i <= 8.
       - 0x8bfbc-0x8bfc4 load the shadow byte k' of dst + i (signed). When k' <> 0 (0x8bfc8), 0x8bffc-0x8c000 compare
         (dst + i) mod 8 with k': the code goes on to the store when (dst + i) mod 8 < k', else it calls
         __asan_report_store1 (0x59824, TB___asan_report_store1) at 0x8c008 (a0 = dst + i, 0x8c004). addressable
         m dst 10 keeps the call unreached.
       - 0x8bfcc i = i + 1; 0x8bfd0 stores c at dst + i (the old i); 0x8bfd4-0x8bfe4 step a3, t1, a2 and t0 by 1 and
         set t2 = 9; 0x8bfe8 `bne a5,t2` starts the next turn, else (i = 9) 0x8bfec goes to 0x8c010 with t2 = k = 9.
     - So k is the number of bytes of s before its first 0 byte, at most 9: nz_run (firstn 9 s) = copy_len 10 9 s.
     - UBSan check 5 (dst + k, before dst[k] = 0, src/diginet_frame.c:135): 0x8c010 `bltu a6,t2` goes to the unimp
       word when dst + k >= 2^64. Not taken: k <= 9 and dst + 10 <= 2^64.
     - 0x8c014 a0 = dst + k; 0x8c018-0x8c020 load the shadow byte k'' of dst + k into a1 (signed). When k'' <> 0
       (0x8c024), 0x8c03c-0x8c040 compare (dst + k) mod 8 with k'': the code goes on to the store when (dst + k) mod 8
       < k'', else it calls __asan_report_store1 at 0x8c044. addressable m dst 10 keeps the call unreached.
     - 0x8c028 stores the byte 0 at dst + k.
     - So the code reads a prefix of [src, src + 9), up to and with its first 0 byte (all 9 bytes when none is 0),
       and the shadow byte of each byte it reads; it stores the bytes [dst, dst + k] after reading the shadow byte of
       each, and it stores no byte of [dst + k + 1, dst + 10).
     - The error paths: three calls (__asan_report_load1 0x8c04c, __asan_report_store1 0x8c008 and 0x8c044) and the
       unimp word 0x8c038 (the target of the five UBSan branches 0x8bf8c, 0x8bf98, 0x8bf9c, 0x8bfb8, 0x8c010); none is
       reached.
     - The stores to [dst, dst + k] change no byte the code reads later: no byte of [src, src + 9) (the overlap
       premise), no shadow byte ([dst, dst + 10) is addressable, so in application memory, and a shadow byte is not),
       no cell (the cells are read once, before the loop) and not the saved ra (off_stk of dst). The frame store at
       sp - 8 changes no shadow byte (app_mem of the frame ends), no byte of [src, src + 9) and no cell (off_stk).
     - Registers written: t0, t1, t2 and a0 .. a7 on every run; t3 when the code reaches 0x8bfbc (a byte other than
       0 was read) or 0x8bff0 (a shadow byte of src + i is not 0); t4 only at 0x8bffc. Memory written: the 8 bytes at
       sp - 8 and [dst, dst + k].
   Premise choice. The premises give all 9 bytes [src, src + 9) and all 10 bytes [dst, dst + 10), with no condition
   on the values of the bytes, although the code reads src only up to its first 0 byte and stores dst only up to
   dst + k: the caller's facts for [body + 15, body + 33) and for the 40 bytes of ap do not depend on the values
   (image A's lib/A/Prog/diginet_announce_parse_c.v states them so), as diginet_mac_is_digidesign_c.v gives all 3
   bytes of mac. The
   length premise is `(9 <= length s)%nat` (the form of
   diginet_mac_is_digidesign_c.v's `(3 <= length l)%nat`; the UBSan image's contract states `length s = 9%nat`): the
   caller can pass s = skipn 15 bb (and skipn 24 bb) for the body bytes bb, and the post's copy_strz 10 9 s old is then
   DgnSpec.ann_version bb old (ann_name bb old), the field of the plain contract; copy_strz 10 9 reads only the
   bytes 0 .. 8 of s. The overlap premise names only the 9 bytes the code may read. The UBSan image's contract states
   mem_inv before and after the call; this leaf form states wmono and stk in its place, as diginet_cursor_init_c.v.
   Form: fuzz_frame's lib/B/Prog/copy_strz_c.v, after lib/A/Prog/diginet_cursor_init_c.v (a writing leaf: the
   arguments in a0 / a1, the written range in munch, the written cells in the post, the kept registers) and
   lib/A/Prog/diginet_announce_parse_c.v (rw_cells of the written bytes with their old value). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition COPY_STRZ : Z := 0x8bf5c.
Definition COPY_STRZ_FRAME : Z := 16.

Definition copy_strz_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s old : list byte) (dst src lo : Z),
    a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 src ->
    src <> 0 ->
    (9 <= length s)%nat -> bytes_at rsegs m src s ->
    rw_cells rsegs m dst [CB 10 old] ->
    dst + 10 <= src \/ src + 9 <= dst ->
    stk rsegs m lo (bv_unsigned sp) -> lo + COPY_STRZ_FRAME <= bv_unsigned sp ->
    off_stk sp COPY_STRZ_FRAME src 9 ->
    off_stk sp COPY_STRZ_FRAME dst 10 ->
    app_mem (bv_unsigned sp - COPY_STRZ_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp COPY_STRZ_FRAME GOT_CELL_K 8 -> off_stk sp COPY_STRZ_FRAME CELL_K 8 ->
    addressable m src 9 ->
    addressable m dst 10 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - COPY_STRZ_FRAME, bv_unsigned sp); (dst, dst + 10)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' dst [CB 10 (DgnSpec.copy_strz 10 9 s old)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 COPY_STRZ) fc None m (seg_rom rsegs)).
