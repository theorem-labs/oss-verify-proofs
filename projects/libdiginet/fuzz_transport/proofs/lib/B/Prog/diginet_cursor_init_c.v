(* diginet_cursor_init in fuzz_transport.asan-ubsan (image B, 41113a03c82f): entry 0x8c554, size 0xb8, own frame 16
   bytes. RELOCATED from libdiginet/fuzz_decode's image-B statement lib/B/Prog/diginet_cursor_init_c.v
   (file sha256 af23e3297742; donor not released; it carries no notice line, and libdiginet/fuzz_frame's image-B copy,
   lib/B/Prog/diginet_cursor_init_c.v, file sha256 f6d7d6aa1c5e, is the same text with fuzz_frame's numbers): the 184
   code bytes are equal to fuzz_decode.asan-ubsan's (1c8e7ec20682, the image of the donor's lib/B, entry 0x82270) up
   to pc-relative words (compared word by word with capstone on the two symbol-bearing files: 46 words, the 6 that
   differ are the GOT-word pair at 0x8c568-0x8c56c and the 4 error-path calls), so the statement is fuzz_decode's
   with the module paths, the entry, every pc (+ 0xa2e4), the cells GOT_CELL_K / CELL_K, the error entries' names
   and the caller changed; each changed number was read again off the symbol-bearing twin (e217cb0a84f1; its loaded
   bytes equal the pin's but the ELF header's section-table fields and the build-id note, and the 184 code bytes of
   this function are equal in both files).
   Image B's text has one premise more than image A's (lib/A/Prog/diginet_cursor_init_c.v), as in fuzz_decode and
   fuzz_frame: c mod 8 = 0, forced by this code's UBSan alignment check of c (below), which goes to the unimp word
   when c is not 8-aligned.
   Contract. a0 = c, the address of a struct diginet_cursor, with c <> 0 and c a multiple of 8; a1 = body; a2 = len.
   The caller is diginet_body_check (the call at 0x8c254, a0 = s5, set at 0x8c244; src/diginet_codec.c:52); c is its
   local cursor: s5 = s8 + 32 (0x8c1a4), where s8 is the side-stack frame __asan_stack_malloc_2 (0x3d9f8, called at
   0x8c16c) returns, 192 bytes requested from __asan_stack_malloc_2 (the model's class-2 frame is 256 bytes), or,
   when that call is skipped or returns 0, the 32-aligned area (sp - 192) & -32 it carves on the real stack
   (0x8c180-0x8c184): frame + 32 of a 64-aligned class-2 frame (as
   fuzz_decode's and fuzz_frame's image-B texts state for the runtime's class-2 frames) or of a 32-aligned area, so
   c mod 8 = 0.
   Premises: c mod 8 = 0 (image B's UBSan check); the 25 bytes at c are writable (wr_at), outside this frame
   (off_stk) and addressable in the shadow map; the frame lies in the stack below sp (stk) and in application memory
   (app_mem of both ends); the runtime cells hold their values (asan_cells), and GOT_CELL_K and CELL_K lie outside the
   frame.
   Result: the function writes c->body = body, c->len = len (0 when body = 0), c->pos = 0 and c->status = 0: the
   cells cursor_cells of lib/Prog/diginet_cursor_init_c.v. It writes no other byte outside its frame (not the 7
   padding bytes after c->status). It changes a0..a5 and keeps every other register. The plain image keeps a0 and
   a1; this code does not (at the return a0 = c + 24 and a1 holds the shadow byte of c + 24), so no result register
   is stated.
   Facts read off the twin (symbol diginet_cursor_init, value 0x8c554, size 184, 46 words; with the UBSan check
   (3 words: 0x8c560, 0x8c564, 0x8c5e8) taken out, the code is image A's word for word up to relocation):
     - 0x8c554 addi sp,sp,-16 (no side-stack frame); 0x8c558 stores ra at sp - 8; 0x8c5dc loads it back; 0x8c5e0
       addi sp,sp,16; 0x8c5e4 ret.
     - 0x8c55c: when a0 = 0 the code goes to 0x8c5dc and writes nothing. The premise c <> 0 keeps this exit
       unreached.
     - 0x8c560 `andi a3,a0,7`, 0x8c564 `bnez a3` to the `unimp` word at 0x8c5e8: the UBSan alignment check of c
       (c->body, src/diginet_msg.c:14). The premise c mod 8 = 0 keeps the branch not taken.
     - 0x8c56c loads 8 bytes at GOT_CELL_K 0xa3cf0 (the address CELL_K 0xac678); 0x8c570 loads 8 bytes at CELL_K
       (the shadow base 0x7fff8000).
     - Before each store at a, the instrumented check loads the shadow byte at (a >> 3) + 0x7fff8000 and compares:
       0x8c57c lbu, shadow byte of c; when not 0, the error path (a call of __asan_report_store8 (0x59a04,
         DgnTransportBAddr.v TB___asan_report_store8) at 0x8c5f8); 0x8c584 stores the 8 bytes of body at c.
       0x8c594 lbu, shadow byte of c + 8; when not 0, the error path (__asan_report_store8 at 0x8c600);
         0x8c59c-0x8c5a4 compute len, or 0 when body = 0 (seqz, addi -1, and); 0x8c5ac stores it at c + 8.
       0x8c5b8 lbu, shadow byte of c + 16; when not 0, the error path (__asan_report_store8 at 0x8c608);
         0x8c5c0 stores 8 zero bytes at c + 16.
       0x8c5d0 lb, shadow byte k of c + 24; when k <> 0 and not ((c + 24) mod 8 < k) (0x8c5ec-0x8c5f0), the error
         path (a call of __asan_report_store1 (0x59824, TB___asan_report_store1) at 0x8c5f4); 0x8c5d8 stores one
         zero byte at c + 24.
     - addressable m c 25 keeps the four error paths unreached. For the 8-byte store at c + 8i (i < 3), the byte
       c + 8i + 7 - (c mod 8) lies in [c, c + 25) and in the 8-byte granule of c + 8i; its shadow_ok, with address
       mod 8 = 7, gives shadow byte 0. For the 1-byte store, shadow_ok (c + 24) k is the compare.
     - The stores to [c, c + 25) do not change the shadow bytes the later checks load: [c, c + 25) is application
       memory (addressable) and shadow bytes are not. The frame store at sp - 8 changes neither (app_mem of the frame
       ends) nor the two cells (off_stk).
   Form: fuzz_decode's lib/B/Prog/diginet_cursor_init_c.v (a writing leaf: wr_at of the written range, the range in
   munch, the written bytes in the post; the kept registers; image B's UBSan premise). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c.
Import ListNotations.
Open Scope Z_scope.
(* The plain contract's cell list cursor_cells, by its qualified name only (it does not depend on the image). *)
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.

Definition DIGINET_CURSOR_INIT : Z := 0x8c554.
Definition DIGINET_CURSOR_INIT_FRAME : Z := 16.

Definition diginet_cursor_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c body len lo : Z),
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 body -> a2 = Z_to_bv 64 len ->
    0 <= c < 2^64 -> c <> 0 -> 0 <= body < 2^64 -> 0 <= len < 2^64 ->
    (* Image B's UBSan premise: 0x8c560 `andi a3,a0,7` / 0x8c564 `bnez a3` trap (unimp at 0x8c5e8) on a c that is
       not 8-aligned. *)
    c mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_CURSOR_INIT_FRAME <= bv_unsigned sp ->
    wr_at rsegs m c 25 ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME c 25 ->
    app_mem (bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME GOT_CELL_K 8 -> off_stk sp DIGINET_CURSOR_INIT_FRAME CELL_K 8 ->
    addressable m c 25 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5'
                       a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME, bv_unsigned sp); (c, c + 25)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' c (PCur.cursor_cells body (if body =? 0 then 0 else len) 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_CURSOR_INIT) fc None m (seg_rom rsegs)).
