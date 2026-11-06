(* Modified by Theorem Labs, 2026-10: diginet_announce_parse's image-A contract, in the form of libreac/fuzz_decode's
   lib/A/Prog/reac_decode_c.v. *)
(* diginet_announce_parse in fuzz_transport.asan (image A, e89be137db17): entry 0x8c238 =
   transport_sigma TS_diginet_announce_parse, 0x24c bytes, own frame 16 bytes.
   RELOCATED from libdiginet/fuzz_frame's image-A statement lib/A/Prog/diginet_announce_parse_c.v
   (file sha256 0d119003b2f9; donor not released): the 588 code bytes are equal to fuzz_frame.asan's (67d7e481d74e,
   entry 0x82bbc) up to pc-relative words (13 pc-relative words differ, no other; re-read here word by word on the
   two symbol-bearing twins: 147 words, the 13 that differ are the
   GOT-word load at 0x8c250 and the 12 error-path calls). So the statement is fuzz_frame's with the module paths, the
   entry, every pc (+ 0x967c), the cells GOT_CELL_K / CELL_K, the error entries' addresses and the caller changed;
   each changed number was read again off the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's).
   The function stores into no harness global and reads none: f and ap lie in its callers' frames (below), and the
   body bytes in the buffer diginet_session_rx parsed (receive's heap block or diginet_session_poll's local buffer),
   so fuzz_frame's form F is kept unchanged.
   Arguments: a0 = f, the address of a struct diginet_frame; a1 = ap, the address of a struct diginet_announce
   (40 bytes). The caller is on_announce (the call at 0x87c88, return address 0x87c8c): f is its own second argument
   (diginet_session_rx's local struct diginet_frame, 64 bytes at offset 32 of diginet_session_rx's class-1 side-stack
   frame (__asan_stack_malloc_1 at 0x8760c), or of the frame it carves on the real stack when that call is skipped or
   returns 0 (0x87624 - 0x8763c)), ap its local `a`, the 40 bytes at offset 256 of its class-4 side-stack frame
   (__asan_stack_malloc_4 at 0x87ae8), or of the frame it carves on the real stack when that call is skipped or
   returns 0 (0x87b00 - 0x87b18).
   Result and written bytes: those of the plain contract lib/Prog/diginet_announce_parse_c.v (module PAnn below; it
   is not imported). a0 = ann_code cmd (length bb). When that code is 0 (ann_ok), the 40 bytes at ap become
   PAnn.ann_cells body bb aj: version (bytes 0..9) is copy_strz of the body bytes from 15, name (bytes 10..19) is
   copy_strz of the body bytes from 24, bytes 20..23 keep aj, unknown (byte 24) is body, unknown_len (byte 32) is 15.
   For any other code the function writes no byte outside its own frame.
   Premises: f and ap are not 0; the byte cmd at f + 30, the address body at f + 32 and the length of bb at f + 40
   (bytes_at); the bytes bb at body; the frame [sp - 16, sp) inside the stack range [lo, sp), with both ends in
   application memory; [f + 30, f + 48) and the runtime cells outside the frame; asan_cells m; f + 30 addressable;
   when cmd is e0 or e1, [f + 40, f + 48) addressable; when the code is 0: [body + 15, body + 33) outside the frame
   and addressable, [f + 32, f + 40) addressable, and the 40 bytes at ap writable with the old bytes aj (rw_cells),
   outside the frame, apart from [f + 30, f + 48) and from [body + 15, body + 33), and addressable.
   What the code does (measured on the symbol-bearing twin, symbol diginet_announce_parse, value 0x8c238, size 588):
   - 0x8c238 sp = sp - 16; 0x8c23c stores ra at sp - 8; 0x8c414 loads it back; 0x8c418 sp = sp + 16; 0x8c41c returns.
   - 0x8c244 / 0x8c248: a0 = 0 or a1 = 0 returns -1 (set at 0x8c240). Not reached: f and ap are not 0.
   - 0x8c250 loads 8 bytes at GOT_CELL_K 0xa4090 (it holds CELL_K); 0x8c254 loads 8 bytes at CELL_K 0xac9f8 (it
     holds 0x7fff8000).
   - Before each data load or store at x outside its frame, the code loads the shadow byte k at
     (x >> 3) + 0x7fff8000. A 1-byte access goes on when k = 0 or (x & 7) < k (k signed); an 8-byte access goes on
     only when k = 0. Else the code calls the error path: __asan_report_load1 (0x594c8), __asan_report_load8
     (0x596a8), __asan_report_store1 (0x597e8) or __asan_report_store8 (0x599c8) (the TS___asan_report_ rows of
     DgnTransportAddr.v).
   - 0x8c26c loads cmd at f + 30 (shadow byte 0x8c264, error path at 0x8c42c). (cmd & 0xfe) <> 0xe0 returns -9
     (0x8c278, 0x8c2a4).
   - 0x8c290 loads the length at f + 40 (shadow byte 0x8c288, error path at 0x8c450). A length under 33 (unsigned)
     returns -4 (0x8c298, 0x8c29c).
   - 0x8c2d4 loads body at f + 32 (shadow byte 0x8c2b8, error path at 0x8c454); 0x8c2e0 stores it at ap + 24
     (shadow byte 0x8c2cc, error path at 0x8c45c); 0x8c2f4 stores 15 at ap + 32 (shadow byte 0x8c2e8, error path at
     0x8c464).
   - 0x8c2fc-0x8c338: for i = 0 .. 8 it loads the byte at body + 15 + i (0x8c310; shadow byte 0x8c308, error path at
     0x8c474), stops at a 0 byte (0x8c314), else stores the byte at ap + i (0x8c334; shadow byte 0x8c324, error path
     at 0x8c358). 0x8c374 then stores 0 at ap + k1, k1 = strz_len (skipn 15 bb) <= 9 (shadow byte 0x8c36c, error
     path at 0x8c43c).
   - 0x8c380 loads body at f + 32 again (shadow byte loaded again at 0x8c378, error path at 0x8c468).
   - 0x8c38c-0x8c3c8: the same for j = 0 .. 8, from body + 24 + j (0x8c3a0; shadow byte 0x8c398, error path at
     0x8c480; stop at 0x8c3a4) to ap + 10 + j (0x8c3c4; shadow byte 0x8c3b4, error path at 0x8c3ec). 0x8c40c stores 0
     at ap + 10 + k2, k2 = strz_len (skipn 24 bb) <= 9 (shadow byte 0x8c400, error path at 0x8c448); the result is 0
     (0x8c408).
   So on code 0 it stores [ap, ap + k1], [ap + 10, ap + 10 + k2] and [ap + 24, ap + 40); it stores no byte of
   [ap + k1 + 1, ap + 10), [ap + 11 + k2, ap + 20) or [ap + 20, ap + 24). It reads a prefix of [body + 15, body + 24)
   and of [body + 24, body + 33), each up to and with its first 0 byte. On -9 and -4 it stores nothing outside its
   frame.
   The 12 error-path calls are not reached: __asan_report_load1 at 0x8c42c by addressable (f + 30) 1;
   __asan_report_load8 at 0x8c450 by addressable (f + 40) 8 (8 usable bytes from f + 40 hold the last byte of the
   8-byte group of f + 40, so its shadow byte is 0); __asan_report_load8 at 0x8c454 / 0x8c468 by addressable (f + 32)
   8; __asan_report_load1 at 0x8c474 / 0x8c480 by addressable (body + 15) 18; __asan_report_store8 at 0x8c45c /
   0x8c464 and __asan_report_store1 at 0x8c358 / 0x8c43c / 0x8c3ec / 0x8c448 by addressable ap 40 (k1, k2 <= 9).
   It can write a0..a7, t0, t1 and t2 (t2 only at 0x8c34c); it keeps all other registers.
   Template: reac_decode_c.v:26-60 (a writing leaf: the written buffer's facts under the condition of the write, the
   frame and the written range in the post's munch, the written bytes). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_announce_parse_c.
Import ListNotations.
Open Scope Z_scope.

(* The plain contract, for its cell list ann_cells (which does not depend on the image). *)
Module PAnn := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_announce_parse_c.

Definition DIGINET_ANNOUNCE_PARSE : Z := 0x8c238.
Definition DIGINET_ANNOUNCE_PARSE_FRAME : Z := 16.

(* The code is 0: cmd is e0 or e1 and bb has 33 bytes or more (DgnSpec.ann_code). Only then does the function read
   the body field and the body, and write the 40 bytes at ap. *)
Definition ann_ok (cmd : Z) (bb : list byte) : bool := ann_code cmd (Z.of_nat (length bb)) =? 0.

Definition diginet_announce_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bb aj : list byte)
         (f ap cmd body lo : Z),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 ap ->
    0 < f < 2^64 -> 0 < ap < 2^64 ->
    0 <= cmd < 2^8 -> 0 < body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_ANNOUNCE_PARSE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (f + 30) 18 ->
    (ann_ok cmd bb = true -> off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (body + 15) 18) ->
    (ann_ok cmd bb = true ->
       rw_cells rsegs m ap [CB 40 aj] /\
       (ap + 40 <= f + 30 \/ f + 48 <= ap) /\
       (ap + 40 <= body + 15 \/ body + 33 <= ap) /\
       off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME ap 40) ->
    app_mem (bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    addressable m (f + 30) 1 ->
    (ann_cmd cmd = true -> addressable m (f + 40) 8) ->
    (ann_ok cmd bb = true -> addressable m (f + 32) 8) ->
    (ann_ok cmd bb = true -> addressable m (body + 15) 18) ->
    (ann_ok cmd bb = true -> addressable m ap 40) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ann_code cmd (Z.of_nat (length bb))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if ann_ok cmd bb
          then munch [(bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME, bv_unsigned sp); (ap, ap + 40)] m m' /\
               rw_cells rsegs m' ap (PAnn.ann_cells body bb aj)
          else munch [(bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_ANNOUNCE_PARSE) fc None m (seg_rom rsegs)).
