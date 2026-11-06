(* Modified by Theorem Labs, 2026-10: the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_c.v without its shadow_rw premise (as reac_frame_is_reac_F_nosh.v) and of check_braid_F_c.v, stated for diginet_mac_is_digidesign on fuzz_frame.asan. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A statement text lib/A/Prog/diginet_mac_is_digidesign_F_c.v: Img0 / AsanCells / AsanKA / diginet_mac_is_digidesign_c are lib/B's, the addresses in the comments are fuzz_frame.asan-ubsan's; no premise more than image A's text (the two UBSan checks 0x81ef4 / 0x81f1c, unimp at 0x81f60, test registers only and are refuted by the bytes_at bound, lib/B/Prog/diginet_mac_is_digidesign_c.v); the footprint ranges are image A's. *)
(* Footprint form of diginet_mac_is_digidesign_contract (diginet_mac_is_digidesign_c.v; image B, entry 0x8b068,
   frame 16 bytes), RELOCATED from libdiginet/fuzz_frame lib/B/Prog/diginet_mac_is_digidesign_F_c.v
   (file sha256 d49c866bde86; donor not released) with the numbers of diginet_mac_is_digidesign_c.v changed: the
   same premises, then one rng premise for each memory range the code reads or writes, and the run as an ExecF.evtF
   run under RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the store of ra at sp - 8 (0x8b06c) and its load (0x8b0f0);
     - GOT_CELL_K 0xa3cf0 and CELL_K 0xac678: one 8-byte load each (0x8b078, 0x8b07c);
     - the bytes [mac, mac + 3): 1-byte loads at 0x8b090, 0x8b0b4, 0x8b0dc;
     - their shadow bytes [shadow_addr mac, shadow_addr (mac + 2)]: 1-byte loads at 0x8b088, 0x8b0ac, 0x8b0d4. The
       range [mac, mac + 3) need not be 8-aligned, so its shadow range is 1 or 2 bytes.
   The code reads the cells, the bytes and the shadow bytes only when a0 <> 0; the premise mac <> 0 makes that
   condition true, so these rng premises have no condition. The rng premises for the bytes and the shadow bytes
   cover all 3 bytes, with no condition on the values of the bytes, as the addressable premise does: the code reads
   byte 1 only when byte 0 is 00 and byte 2 only when byte 1 is a0, but the caller's range f.src (6 bytes inside
   diginet_session_rx's local struct diginet_frame f) and its shadow bytes are in the caller's footprint whatever the
   values. The two UBSan checks (0x8b098-0x8b09c and 0x8b0c0-0x8b0c4, branches to the unimp word at 0x8b108) compare
   registers only, so they add no range, and they are not taken (diginet_mac_is_digidesign_c.v). The error-path calls
   (__asan_report_load1 at 0x8b104, 0x8b118, 0x8b124) are not reached (diginet_mac_is_digidesign_c.v), so no range is
   given for them. There is no shadow_rw premise.
   Form: fuzz_frame's lib/B/Prog/diginet_mac_is_digidesign_F_c.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_mac_is_digidesign_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - DIGINET_MAC_IS_DIGIDESIGN_FRAME) DIGINET_MAC_IS_DIGIDESIGN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG mac 3 ->
    ExecF.rng RNG (shadow_addr mac) (shadow_addr (mac + 3 - 1) - shadow_addr mac + 1) ->
    ExecF.evtF rsegs RNG
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
