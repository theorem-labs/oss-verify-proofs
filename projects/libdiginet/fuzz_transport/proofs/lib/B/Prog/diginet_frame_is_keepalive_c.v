(* Modified by Theorem Labs, 2026-10: the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_c.v (and check_braid_c.v for arguments given as Z values), restated for diginet_frame_is_keepalive of libdiginet/fuzz_frame's image A with the result and read bytes of proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_is_keepalive_c.v; module paths changed; no shadow_rw premise. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A statement text lib/A/Prog/diginet_frame_is_keepalive_c.v: Img0 / AsanCells / AsanKA are lib/B's, the entry and every address in the comments are fuzz_frame.asan-ubsan's, ONE premise more than image A's text, image B's UBSan premise `f mod 8 = 0` (the trap 0x81f8c `andi a1,a0,7` / 0x81f90 `bnez a1`, unimp at 0x82024), and `0 < body < 2^64` in place of image A's `0 <= body < 2^64` (the trap 0x81ff4 `beqz a0`, unimp at 0x82024), in the shape of the UBSan image's lib/U/Prog/diginet_frame_is_keepalive_c.v. *)
(* Contract of diginet_frame_is_keepalive in fuzz_transport.asan-ubsan (image B, 41113a03c82f). Entry 0x8b128,
   0xd0 bytes. It takes a frame of 16 bytes, [sp - 16, sp). On the paths the premises allow it calls no function.
   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/diginet_frame_is_keepalive_c.v
   (file sha256 c4f8716552b6; donor not released): the 208 code bytes are equal to fuzz_frame.asan-ubsan's
   (2574b26fc98e, the image of the donor's lib/B, entry 0x81f80) up to pc-relative words (compared word by word with
   capstone on the two symbol-bearing files: 52 words, the 5 that differ are the GOT-word load at 0x8b140 and the
   4 error-path calls), so the statement is fuzz_frame's with the module paths, the entry, every pc (+ 0x91a8), the
   cells GOT_CELL_K / CELL_K, the error entries' names and addresses and the caller changed; each changed number was
   read again off the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 208 code bytes of this function are equal in both files).
   Image B's text differs from image A's (lib/A/Prog/diginet_frame_is_keepalive_c.v) in two premises, both forced by
   the two UBSan checks of this code (below), each of which goes to the unimp word when its premise fails: f mod 8 = 0
   more, and body <> 0 added to the premise of the path cmd = 0 and blen = 1, the only path that reaches the body
   check (0x8b19c). 0 <= body < 2^64 is image A's. (fuzz_frame's image-B text states 0 < body for every path; that
   is stronger than the code needs.)
   Argument: a0 is the address f (0 < f < 2^64, f mod 8 = 0) of a struct diginet_frame (64 bytes). The caller is
   on_data (the call at 0x88d2c, a0 = s4, set at 0x88d28; transport/src/diginet_session.c:255); f is the frame
   on_data was handed (its second argument, s4 = a1 at 0x88a94; diginet_session_rx's struct diginet_frame that
   diginet_frame_parse filled), and body points into the received bytes (body = buf + 30, the cell at f + 32 of
   lib/Prog/diginet_frame_parse_c.v, so body <> 0). on_data's own UBSan check of f (0x88b3c a1 = s4 & 7; 0x88b80
   a1 <> 0 goes to its unimp word at 0x88f88; transport/src/diginet_session.c:242) lies on every path from its entry
   to the call, and on_data writes s4 only at 0x88a94 and in its epilogue (0x88f60), so f mod 8 = 0 holds at the
   call. The bytes are read through bytes_at and addressable of raw memory, so the other premises hold wherever f
   and body lie.
   Premises:
   - f mod 8 = 0 (image B's UBSan check of f);
   - as the plain contract (lib/Prog/diginet_frame_is_keepalive_c.v): these bytes are readable (bytes_at): f + 30, the
     byte cmd; f + 32, the 8 bytes of the address body; f + 40, the 8 bytes of blen = length bb; the bytes bb at body;
   - the stack window [lo, sp) is readable (stk) and holds the frame (lo + 16 <= sp); both ends of the frame are in
     application memory (app_mem);
   - asan_cells m: among others, the 8 bytes at GOT_CELL_K (0xa3cf0) hold CELL_K (0xac678) and the 8 bytes at CELL_K
     hold 0x7fff8000;
   - each range the code loads is outside the frame (off_stk) and its bytes are marked usable (addressable), under the
     condition under which the code loads it: GOT_CELL_K 8, CELL_K 8 and f + 30 (1 byte) always; f + 40 (8 bytes) when
     cmd = 0; f + 32 (8 bytes) and body (1 byte) when cmd = 0 and blen = 1, and then also body <> 0 (image B's UBSan
     check of body, reached only on that path).
   Result: a0 = 1 when keepalive_of cmd blen bb (cmd = 0, blen = 1 and bb[0] = 0), else 0. The function writes a1, a2,
   a3, a4 and the bytes of its frame (munch); it keeps all other registers, and the window stays readable (stk).
   Facts read off the twin (symbol diginet_frame_is_keepalive, value 0x8b128, size 208, 52 words; with the two UBSan
   check branches and the alignment test taken out, the code is image A's word for word up to relocation, as in
   fuzz_frame):
   - 0x8b128 sp = sp - 16 (no side-stack frame); 0x8b12c stores ra at sp - 8; 0x8b1c0 loads it back; 0x8b1c4 restores
     sp; 0x8b1c8 returns.
   - 0x8b130: a0 = 0 jumps to 0x8b1c0 and returns 0. Not taken: 0 < f.
   - UBSan check 1 (f->h.cmd, src/diginet_frame.c:57): 0x8b134 a1 = f & 7; 0x8b138 a1 <> 0 goes to the unimp word at
     0x8b1cc. Not taken: f mod 8 = 0.
   - 0x8b140 loads the 8 bytes at GOT_CELL_K; 0x8b144 loads the 8 bytes at CELL_K: a2 = 0x7fff8000.
   - 0x8b154 loads (signed) the shadow byte k of f + 30 at ((f + 30) >> 3) + 0x7fff8000. When k <> 0 (0x8b158),
     0x8b1d0-0x8b1d4 go back to 0x8b15c when ((f + 30) & 7) < k, else 0x8b1dc calls __asan_report_load1 (the error
     path). 0x8b15c loads cmd; cmd <> 0 (0x8b160) returns 0 (0x8b1bc).
   - 0x8b170 loads the shadow byte of f + 40; when it is not 0 (0x8b174), 0x8b1f0 calls __asan_report_load8. 0x8b178
     loads blen; blen <> 1 (0x8b180) returns 0 (0x8b1bc).
   - 0x8b190 loads the shadow byte of f + 32; when it is not 0 (0x8b194), 0x8b1f4 calls __asan_report_load8. 0x8b198
     loads body.
   - UBSan check 2 (f->body[0], cmd = 0 and blen = 1; src/diginet_frame.c:57): 0x8b19c body = 0 goes to the unimp word
     at 0x8b1cc. It is reached only on the path cmd = 0 and blen = 1. Not taken: body <> 0, which the premise of that
     path gives.
   - 0x8b1a8 loads (signed) the shadow byte k of body. When k <> 0 (0x8b1ac), 0x8b1e0-0x8b1e4 go back to 0x8b1b0 when
     (body & 7) < k, else 0x8b1e8 calls __asan_report_load1. 0x8b1b0 loads bb[0]; 0x8b1b4 sets a0 to 1 when bb[0] = 0,
     else 0.
   The addressable premise of each loaded range keeps its error path unreached: for the 1-byte loads at a, the shadow
   byte k is 0 or a mod 8 < k <= 7; for the 8-byte loads at a, the 8 bytes run to the end of a's 8-byte granule, so
   k = 0. The error-path calls are __asan_report_load1 (0x59504, DgnTransportBAddr.v TB___asan_report_load1) at
   0x8b1dc and 0x8b1e8 and __asan_report_load8 (0x596e4, TB___asan_report_load8) at 0x8b1f0 and 0x8b1f4; the two
   UBSan checks branch to the one unimp word at 0x8b1cc.
   Form: fuzz_frame's lib/B/Prog/diginet_frame_is_keepalive_c.v (read-only leaf with an early exit, arguments as Z
   values; image B's two UBSan premises). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_FRAME_IS_KEEPALIVE : Z := 0x8b128.
Definition DIGINET_FRAME_IS_KEEPALIVE_FRAME : Z := 16.

Definition diginet_frame_is_keepalive_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f cmd body lo : Z) (bb : list byte),
    0 < f < 2^64 ->
    (* Image B's UBSan premises: 0x8b134 `andi a1,a0,7` / 0x8b138 `bnez a1` trap (unimp at 0x8b1cc) on an f that is
       not 8-aligned, here; and 0x8b19c `beqz a0` traps (unimp at 0x8b1cc) on body = 0 before the load of bb[0], on
       the path cmd = 0 and blen = 1 only, so body <> 0 is stated under that condition, in the premise of that path's
       ranges below; 0 <= body is image A's. *)
    f mod 8 = 0 ->
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
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME body 1 /\ addressable m body 1 /\ body <> 0) ->
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
