(* Modified by Theorem Labs, 2026-10: the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_c.v and check_braid_c.v, stated for diginet_mac_is_digidesign on fuzz_frame.asan with the result of lib/Prog/diginet_mac_is_digidesign_c.v. *)
(* diginet_mac_is_digidesign on fuzz_transport.asan (image A, e89be137db17): entry 0x8b590, 172 bytes, frame 16
   bytes.
   RELOCATED from libdiginet/fuzz_frame's image-A statement lib/A/Prog/diginet_mac_is_digidesign_c.v
   (file sha256 9d9be1b8d5c7; donor not released): the 172 code bytes are equal to fuzz_frame.asan's (67d7e481d74e,
   entry 0x81f14) up to pc-relative words (4 pc-relative words differ, no other), so the statement is fuzz_frame's
   with the module paths, the entry, every pc (+ 0x967c), the cells
   GOT_CELL_K / CELL_K and the error entry's address changed; each changed number was read again off the
   symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 172 code bytes of this function are
   equal in both files).

   Contract. The argument a0 is mac, the address of a MAC, and mac is not 0. l is a list of 3 or more bytes at mac.
   The 3 bytes [mac, mac + 3) are outside the function's frame and are addressable (their shadow bytes mark them
   usable). The stack holds the frame [sp - 16, sp), the frame is in application memory, and the two cells
   GOT_CELL_K and CELL_K hold their values (asan_cells) outside the frame. The result in a0 is 1 when the bytes 0, 1,
   2 of l are 00 a0 7e (DgnSpec.oui_of l), else 0: the result of the plain contract
   lib/Prog/diginet_mac_is_digidesign_c.v. The function changes a1, a2, a3, a4 and the bytes of its own frame. It
   keeps all other registers and all other memory.

   Facts read off the twin (symbol diginet_mac_is_digidesign, value 0x8b590, size 172, 43 words):
   - 0x8b590 sp = sp - 16: the frame is 16 bytes. No side-stack frame. 0x8b594 stores ra (8 bytes) at sp - 8, 0x8b608
     loads it back, 0x8b60c restores sp, 0x8b610 returns.
   - 0x8b598: when a0 = 0 the function returns at once with a0 = 0. The premise mac <> 0 keeps this branch from being
     taken; without it the result would not be oui_of l.
   - 0x8b5a0 loads 8 bytes at GOT_CELL_K 0xa4090 (the address CELL_K 0xac9f8); 0x8b5a4 loads 8 bytes at CELL_K (the
     value 0x7fff8000). asan_cells gives both values.
   - Byte 0: 0x8b5b0 loads the shadow byte of mac at (mac >> 3) + 0x7fff8000; 0x8b5b8 loads the byte at mac. When it
     is not 00, the code sets a0 to 0 (0x8b604) and returns.
   - Byte 1: 0x8b5cc loads the shadow byte of mac + 1; 0x8b5d4 loads the byte at mac + 1. When it is not a0, the code
     sets a0 to 0 (0x8b604) and returns.
   - Byte 2: 0x8b5ec loads the shadow byte of mac + 2; 0x8b5f4 loads the byte at mac + 2; 0x8b5f8-0x8b5fc set a0 to 1
     when it is 7e, else to 0. So the code reads 1, 2 or 3 bytes of [mac, mac + 3) and the shadow byte of each.
   - The error path: when a shadow byte k is not 0, the code compares (a mod 8) with k (0x8b618, 0x8b624, 0x8b634). It
     goes back to the byte load when (a mod 8) < k, else it calls __asan_report_load1 (0x594c8,
     DgnTransportAddr.v TS___asan_report_load1) at 0x8b61c, 0x8b62c or 0x8b638. The premise `addressable m mac 3`
     gives, for each of the 3 bytes, k = 0 or (a mod 8) < k <= 7, so the code reaches no error-path call.
   - Registers written: a0 (the result), a1, a2, a3, and a4 (only at 0x8b620). Memory written: the 8 bytes at sp - 8.

   Premise choice. The premises give all 3 bytes [mac, mac + 3), with no condition on the values of the bytes,
   although the code reads byte 1 only when byte 0 is 00 and byte 2 only when byte 1 is a0. The caller
   diginet_session_rx (the call at 0x878d0, a0 = s7; transport/src/diginet_session.c:286) passes f.src: 6 bytes inside
   its local struct diginet_frame f. The caller has the facts for these bytes whatever their values, so a condition on
   the values would not make the caller's work smaller. The length premise is `(3 <= length l)%nat`: the caller can
   pass the 6 bytes of f.src, the l of the plain contract. The bytes are read through bytes_at and addressable of raw
   memory, so the premises hold wherever the caller's f lies (its machine frame or its side-stack frame).

   Form: fuzz_frame's diginet_mac_is_digidesign_c.v (registers, stk, app_mem, asan_cells, off_stk of the cells, the
   post; a Z argument in a0, premises with no condition). There is no shadow_rw premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_MAC_IS_DIGIDESIGN : Z := 0x8b590.
Definition DIGINET_MAC_IS_DIGIDESIGN_FRAME : Z := 16.

Definition diginet_mac_is_digidesign_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mac : Z) (l : list byte) (lo : Z),
    mac <> 0 ->
    (3 <= length l)%nat ->
    bytes_at rsegs m mac l ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_MAC_IS_DIGIDESIGN_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME mac 3 ->
    app_mem (bv_unsigned sp - DIGINET_MAC_IS_DIGIDESIGN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME CELL_K 8 ->
    addressable m mac 3 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if oui_of l then 1 else 0)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_MAC_IS_DIGIDESIGN_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mac) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_MAC_IS_DIGIDESIGN) fc None m (seg_rom rsegs)).
