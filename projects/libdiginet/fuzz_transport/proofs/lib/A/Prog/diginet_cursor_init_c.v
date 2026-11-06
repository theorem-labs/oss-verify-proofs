(* Modified by Theorem Labs, 2026-10: the writing-leaf contract form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_decode_c.v, stated for diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan); module paths changed; the arguments, the result and the written cells are those of lib/Prog/diginet_cursor_init_c.v. *)
(* diginet_cursor_init in fuzz_transport.asan (image A, e89be137db17): entry 0x8c94c, size 0xac, own frame 16
   bytes. RELOCATED from libdiginet/fuzz_frame's image-A statement lib/A/Prog/diginet_cursor_init_c.v
   (file sha256 d2f682927139; donor not released): the 172 code bytes are equal to fuzz_frame.asan's (67d7e481d74e,
   entry 0x83224) up to pc-relative words (5 pc-relative words differ, no other), so the statement is fuzz_frame's
   with the module paths, the entry, every pc (+ 0x9728), the cells
   and the error entries' names changed; each changed number was read again off the symbol-bearing twin
   (86efc3a80314; its loaded bytes equal the pin's, and the 172 code bytes of this function are equal in both files).
   Contract. a0 = c, the address of a struct diginet_cursor, with c <> 0; a1 = body; a2 = len. The caller is
   diginet_body_check (the call at 0x8c688, a0 = s5); c is its local cursor inside its side-stack frame (class 2, 192
   bytes, as in fuzz_frame).
   Premises: the 25 bytes at c are writable (wr_at), outside this frame (off_stk) and addressable in the shadow map;
   the frame lies in the stack below sp (stk) and in application memory (app_mem of both ends); the runtime cells
   hold their values (asan_cells), and GOT_CELL_K and CELL_K lie outside the frame.
   Result: the function writes c->body = body, c->len = len (0 when body = 0), c->pos = 0 and c->status = 0: the
   cells cursor_cells of lib/Prog/diginet_cursor_init_c.v. It writes no other byte outside its frame (not the 7
   padding bytes after c->status). It changes a0..a5 and keeps every other register. The plain image keeps a0 and
   a1; this code does not (at the return a0 = c + 24 and a1 holds the shadow byte of c + 24), so no result register
   is stated.
   Facts read off the twin (symbol diginet_cursor_init, value 0x8c94c, size 172, 43 words):
     - 0x8c94c sp = sp - 16 (no side-stack frame); 0x8c950 stores ra at sp - 8; 0x8c9cc loads it back; 0x8c9d0
       sp = sp + 16; 0x8c9d4 returns.
     - 0x8c954: when a0 = 0 the code goes to 0x8c9cc and writes nothing. The premise c <> 0 keeps this exit
       unreached.
     - 0x8c95c loads 8 bytes at GOT_CELL_K 0xa4090 (the address CELL_K 0xac9f8); 0x8c960 loads 8 bytes at CELL_K
       (the shadow base 0x7fff8000).
     - Before each store at a, the instrumented check loads the shadow byte at (a >> 3) + 0x7fff8000 and compares:
       0x8c96c, the unsigned shadow byte of c; when not 0, the error path (a call of __asan_report_store8 (0x599c8,
         DgnTransportAddr.v TS___asan_report_store8) at 0x8c9e4); 0x8c974 stores the 8 bytes of body at c.
       0x8c984, the unsigned shadow byte of c + 8; when not 0, the error path (__asan_report_store8 at 0x8c9ec);
         0x8c98c-0x8c994 compute len, or 0 when body = 0 (a1 = (body = 0), a1 = a1 - 1, a2 = a1 & len); 0x8c99c
         stores it at c + 8.
       0x8c9a8, the unsigned shadow byte of c + 16; when not 0, the error path (__asan_report_store8 at 0x8c9f4);
         0x8c9b0 stores 8 zero bytes at c + 16.
       0x8c9c0, the signed shadow byte k of c + 24; when k <> 0 and not ((c + 24) mod 8 < k) (0x8c9d8-0x8c9dc), the
         error path (a call of __asan_report_store1 (0x597e8, TS___asan_report_store1) at 0x8c9e0); 0x8c9c8 stores
         one zero byte at c + 24.
     - addressable m c 25 keeps the four error paths unreached. For the 8-byte store at c + 8i (i < 3), the byte
       c + 8i + 7 - (c mod 8) lies in [c, c + 25) and in the 8-byte granule of c + 8i; its shadow_ok, with address
       mod 8 = 7, gives shadow byte 0. For the 1-byte store, shadow_ok (c + 24) k is the compare. c need not be
       8-aligned.
     - The stores to [c, c + 25) do not change the shadow bytes the later checks load: [c, c + 25) is application
       memory (addressable) and shadow bytes are not. The frame store at sp - 8 changes neither (app_mem of the frame
       ends) nor the two cells (off_stk).
   Form: fuzz_frame's diginet_cursor_init_c.v (a writing leaf: wr_at of the written range, the range in munch, the
   written bytes in the post; the kept registers). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c.
Import ListNotations.
Open Scope Z_scope.
(* The plain contract's cell list cursor_cells, by its qualified name only (it does not depend on the image). *)
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.

Definition DIGINET_CURSOR_INIT : Z := 0x8c94c.
Definition DIGINET_CURSOR_INIT_FRAME : Z := 16.

Definition diginet_cursor_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c body len lo : Z),
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 body -> a2 = Z_to_bv 64 len ->
    0 <= c < 2^64 -> c <> 0 -> 0 <= body < 2^64 -> 0 <= len < 2^64 ->
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
