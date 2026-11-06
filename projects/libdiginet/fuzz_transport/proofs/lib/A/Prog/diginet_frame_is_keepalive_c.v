(* Modified by Theorem Labs, 2026-10: the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_c.v (and check_braid_c.v for arguments given as Z values), restated for diginet_frame_is_keepalive of libdiginet/fuzz_frame's image A with the result and read bytes of proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_is_keepalive_c.v; module paths changed; no shadow_rw premise. *)
(* Contract of diginet_frame_is_keepalive in fuzz_transport.asan (image A, e89be137db17). Entry 0x8b63c, 0xc0
   bytes. It takes a frame of 16 bytes, [sp - 16, sp). On the paths the premises allow it calls no function.
   RELOCATED from libdiginet/fuzz_frame's image-A statement lib/A/Prog/diginet_frame_is_keepalive_c.v
   (file sha256 bb258893582a; donor not released): the 192 code bytes are equal to fuzz_frame.asan's (67d7e481d74e,
   entry 0x81fc0) up to pc-relative words (6 pc-relative words differ, no other), so the statement is fuzz_frame's
   with the module paths, the entry, every pc (+ 0x967c), the cells
   and the error entries' names changed; each changed number was read again off the symbol-bearing twin
   (86efc3a80314; its loaded bytes equal the pin's, and the 192 code bytes of this function are equal in both files).
   Argument: a0 is the address f (0 < f < 2^64) of a struct diginet_frame (64 bytes). The caller is on_data (the call
   at 0x88b9c, a0 = s4; transport/src/diginet_session.c:255); f is the frame on_data was handed (diginet_session_rx's
   struct diginet_frame that diginet_frame_parse filled), and body points into the received bytes. The bytes are read
   through bytes_at and addressable of raw memory, so the premises hold wherever f and body lie.
   Premises:
   - as the plain contract (lib/Prog/diginet_frame_is_keepalive_c.v): these bytes are readable (bytes_at): f + 30, the
     byte cmd; f + 32, the 8 bytes of the address body; f + 40, the 8 bytes of blen = length bb; the bytes bb at body;
   - the stack window [lo, sp) is readable (stk) and holds the frame (lo + 16 <= sp); both ends of the frame are in
     application memory (app_mem);
   - asan_cells m: among others, the 8 bytes at GOT_CELL_K (0xa4090) hold CELL_K (0xac9f8) and the 8 bytes at CELL_K
     hold 0x7fff8000;
   - each range the code loads is outside the frame (off_stk) and its bytes are marked usable (addressable), under the
     condition under which the code loads it: GOT_CELL_K 8, CELL_K 8 and f + 30 (1 byte) always; f + 40 (8 bytes) when
     cmd = 0; f + 32 (8 bytes) and body (1 byte) when cmd = 0 and blen = 1.
   Result: a0 = 1 when keepalive_of cmd blen bb (cmd = 0, blen = 1 and bb[0] = 0), else 0. The function writes a1, a2,
   a3, a4 and the bytes of its frame (munch); it keeps all other registers, and the window stays readable (stk).
   Facts read off the twin (symbol diginet_frame_is_keepalive, value 0x8b63c, size 192, 48 words):
   - 0x8b63c sp = sp - 16 (no side-stack frame); 0x8b640 stores ra at sp - 8; 0x8b6c8 loads it back; 0x8b6cc restores
     sp; 0x8b6d0 returns.
   - 0x8b644: a0 = 0 jumps to 0x8b6c8 and returns 0. Not taken: 0 < f.
   - 0x8b64c loads the 8 bytes at GOT_CELL_K; 0x8b650 loads the 8 bytes at CELL_K: a2 = 0x7fff8000.
   - 0x8b660 loads (signed) the shadow byte k of f + 30 at ((f + 30) >> 3) + 0x7fff8000. When k <> 0 (0x8b664),
     0x8b6d4-0x8b6d8 go back to 0x8b668 when ((f + 30) & 7) < k, else 0x8b6e0 calls __asan_report_load1 (0x594c8,
     DgnTransportAddr.v TS___asan_report_load1; the error path). 0x8b668 loads cmd; cmd <> 0 (0x8b66c) returns 0
     (0x8b6c4).
   - 0x8b67c loads the shadow byte of f + 40; when it is not 0 (0x8b680), 0x8b6f4 calls __asan_report_load8 (0x596a8,
     TS___asan_report_load8). 0x8b684 loads blen; blen <> 1 (0x8b68c) returns 0 (0x8b6c4).
   - 0x8b69c loads the shadow byte of f + 32; when it is not 0 (0x8b6a0), 0x8b6f8 calls __asan_report_load8. 0x8b6a4
     loads body.
   - 0x8b6b0 loads (signed) the shadow byte k of body. When k <> 0 (0x8b6b4), 0x8b6e4-0x8b6e8 go back to 0x8b6b8 when
     (body & 7) < k, else 0x8b6ec calls __asan_report_load1. 0x8b6b8 loads bb[0]; 0x8b6bc sets a0 to 1 when bb[0] = 0,
     else 0.
   The addressable premise of each loaded range keeps its error path unreached: for the 1-byte loads at a, the shadow
   byte k is 0 or a mod 8 < k <= 7; for the 8-byte loads at a, the 8 bytes run to the end of a's 8-byte granule, so
   k = 0.
   Form: fuzz_frame's diginet_frame_is_keepalive_c.v (read-only leaf with an early exit, arguments as Z values). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_FRAME_IS_KEEPALIVE : Z := 0x8b63c.
Definition DIGINET_FRAME_IS_KEEPALIVE_FRAME : Z := 16.

Definition diginet_frame_is_keepalive_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f cmd body lo : Z) (bb : list byte),
    0 < f < 2^64 ->
    0 <= cmd < 2^8 -> 0 <= body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_FRAME_IS_KEEPALIVE_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    app_mem (bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 30) 1 ->
    addressable m (f + 30) 1 ->
    (cmd = 0 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 40) 8 /\ addressable m (f + 40) 8) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 32) 8 /\ addressable m (f + 32) 8 /\
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME body 1 /\ addressable m body 1) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_IS_KEEPALIVE) fc None m (seg_rom rsegs)).
