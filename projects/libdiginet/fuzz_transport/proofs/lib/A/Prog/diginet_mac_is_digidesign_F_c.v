(* Modified by Theorem Labs, 2026-10: the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_c.v without its shadow_rw premise (as reac_frame_is_reac_F_nosh.v) and of check_braid_F_c.v, stated for diginet_mac_is_digidesign on fuzz_frame.asan. *)
(* Footprint form of diginet_mac_is_digidesign_contract (diginet_mac_is_digidesign_c.v; image A, entry 0x8b590,
   frame 16 bytes), RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_mac_is_digidesign_F_c.v
   (file sha256 905686628882; donor not released) with the numbers of diginet_mac_is_digidesign_c.v changed: the
   same premises, then one rng premise for each memory range the code reads or writes, and the run as an ExecF.evtF
   run under RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the store of ra at sp - 8 (0x8b594) and its load (0x8b608);
     - GOT_CELL_K 0xa4090 and CELL_K 0xac9f8: one 8-byte load each (0x8b5a0, 0x8b5a4);
     - the bytes [mac, mac + 3): 1-byte loads at 0x8b5b8, 0x8b5d4, 0x8b5f4;
     - their shadow bytes [shadow_addr mac, shadow_addr (mac + 2)]: 1-byte loads at 0x8b5b0, 0x8b5cc, 0x8b5ec. The
       range [mac, mac + 3) need not be 8-aligned, so its shadow range is 1 or 2 bytes.
   The code reads the cells, the bytes and the shadow bytes only when a0 <> 0; the premise mac <> 0 makes that
   condition true, so these rng premises have no condition. The rng premises for the bytes and the shadow bytes
   cover all 3 bytes, with no condition on the values of the bytes, as the addressable premise does: the code reads
   byte 1 only when byte 0 is 00 and byte 2 only when byte 1 is a0, but the caller's range f.src (6 bytes inside
   diginet_session_rx's local struct diginet_frame f) and its shadow bytes are in the caller's footprint whatever the
   values. The error-path calls (__asan_report_load1 at 0x8b61c, 0x8b62c, 0x8b638) are not reached
   (diginet_mac_is_digidesign_c.v), so no range is given for them. There is no shadow_rw premise.
   Form: fuzz_frame's diginet_mac_is_digidesign_F_c.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA diginet_mac_is_digidesign_c.
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
