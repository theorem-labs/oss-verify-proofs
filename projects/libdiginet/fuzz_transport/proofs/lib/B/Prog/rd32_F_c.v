(* Modified by Theorem Labs, 2026-10: rd32 of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_mac_is_digidesign_F_c.v: the premises of rd32_c.v, then the footprint ranges of rd32's code (the frame, the two cells, the 4 bytes [p, p + 4) and their shadow bytes, all without condition); shape donor of the premises: the UBSan image's contract lib/U/Prog/rd32_c.v. *)
(* Footprint form of rd32_contract (rd32_c.v; image B, entry 0x8b734, frame 16 bytes), RELOCATED from
   libdiginet/fuzz_frame lib/B/Prog/rd32_F_c.v (file sha256 82de98f14320; donor not released) with the numbers of
   rd32_c.v changed: the same premises, then one rng premise for each memory range the code reads or writes, and the
   run as an ExecF.evtF run under RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the store of ra at sp - 8 (0x8b738) and its load (0x8b7cc);
     - GOT_CELL_K 0xa3cf0 and CELL_K 0xac678: one 8-byte load each (0x8b740, 0x8b744);
     - the bytes [p, p + 4): 1-byte loads at 0x8b770, 0x8b794, 0x8b7a8, 0x8b7b4;
     - their shadow bytes [shadow_addr p, shadow_addr (p + 3)]: 1-byte loads at 0x8b750, 0x8b76c, 0x8b790, 0x8b7a4.
       The range [p, p + 4) need not be 8-aligned, so its shadow range is 1 or 2 bytes.
   The code has no early return: it reads the cells, the 4 bytes and their 4 shadow bytes on every run, so these rng
   premises have no condition. The two UBSan checks (0x8b758-0x8b75c and 0x8b778-0x8b780, branches to the unimp word
   at 0x8b7d8) compare registers only, so they add no range, and they are not taken (rd32_c.v). The error-path calls
   (__asan_report_load1 at 0x8b7e4, 0x8b7f4, 0x8b804, 0x8b814) are not reached (rd32_c.v), so no range is given for
   them. There is no shadow_rw premise.
   Form: fuzz_frame's lib/B/Prog/rd32_F_c.v, after lib/A/Prog/diginet_mac_is_digidesign_F_c.v (rng of the frame,
   the cells, the bytes and the shadow range, with no condition). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA rd32_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition rd32_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - RD32_FRAME) RD32_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG p 4 ->
    ExecF.rng RNG (shadow_addr p) (shadow_addr (p + 4 - 1) - shadow_addr p + 1) ->
    ExecF.evtF rsegs RNG
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
