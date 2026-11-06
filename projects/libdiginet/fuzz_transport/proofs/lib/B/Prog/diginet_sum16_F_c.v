(* Modified by Theorem Labs, 2026-10: diginet_sum16 of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_mac_is_digidesign_F_c.v: the premises of diginet_sum16_c.v, then the footprint ranges of diginet_sum16's code (the frame without condition; the two cells, [p, p + n) and its shadow bytes under the condition bb <> [], as lib/A/Prog/diginet_announce_parse_F_c.v states a range under the condition of its access); shape donor of the premises: the UBSan image's contract lib/U/Prog/diginet_sum16_c.v. *)
(* Footprint form of diginet_sum16_contract (diginet_sum16_c.v; image B, entry 0x8afd8, frame 16 bytes), RELOCATED
   from libdiginet/fuzz_frame lib/B/Prog/diginet_sum16_F_c.v (file sha256 d76b39618c5e; donor not released) with
   the numbers of diginet_sum16_c.v changed: the same premises, then one rng premise for each memory range the code
   reads or writes, under the condition under which the code touches it, and the run as an ExecF.evtF run under RNG
   (every data access of every step lies in RNG). The ranges (n = length bb):
     - the frame [sp - 16, sp): the store of ra at sp - 8 (0x8afdc) and its load (0x8b058), on every run;
     - GOT_CELL_K 0xa3cf0 and CELL_K 0xac678: one 8-byte load each (0x8afec, 0x8aff0);
     - the bytes [p, p + n): one 1-byte load per loop turn (0x8b024);
     - their shadow bytes [shadow_addr p, shadow_addr (p + n - 1)]: one 1-byte load per loop turn (0x8b01c). The
       range [p, p + n) need not be 8-aligned, so its shadow range is the shadow byte of each 8-byte group it meets.
   The code reaches the cell loads and the loop only when n <> 0 (`beqz a1` at 0x8afe4 returns at once), so the
   rng premises of the cells, the bytes and the shadow bytes have the condition bb <> []; with n <> 0 the loop reads
   every byte of [p, p + n) and its shadow byte. The three UBSan checks (0x8b000, 0x8b00c, 0x8b010, branches to the
   unimp word at 0x8b064) compare registers only, so they add no range, and they are not taken (diginet_sum16_c.v).
   The error-path call (__asan_report_load1 at 0x8b04c) is not reached (diginet_sum16_c.v), so no range is given for
   it. There is no shadow_rw premise.
   Form: fuzz_frame's lib/B/Prog/diginet_sum16_F_c.v, after lib/A/Prog/diginet_mac_is_digidesign_F_c.v (rng of the
   frame, the cells, the bytes and the shadow range) and lib/A/Prog/diginet_announce_parse_F_c.v (rng premises under
   the condition of the access). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_sum16_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_sum16_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte) (lo : Z),
    (bb <> [] -> p <> 0) ->
    bytes_at rsegs m p bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SUM16_FRAME <= bv_unsigned sp ->
    (bb <> [] -> off_stk sp DIGINET_SUM16_FRAME p (Z.of_nat (length bb))) ->
    app_mem (bv_unsigned sp - DIGINET_SUM16_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SUM16_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SUM16_FRAME CELL_K 8 ->
    (bb <> [] -> addressable m p (Z.of_nat (length bb))) ->
    (* the frame: ra stored at sp - 8 and loaded back *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_SUM16_FRAME) DIGINET_SUM16_FRAME ->
    (* the two asan_cells cells, read when n <> 0 *)
    (bb <> [] -> ExecF.rng RNG GOT_CELL_K 8) ->
    (bb <> [] -> ExecF.rng RNG CELL_K 8) ->
    (* the n bytes at p and their shadow bytes, read when n <> 0 *)
    (bb <> [] -> ExecF.rng RNG p (Z.of_nat (length bb))) ->
    (bb <> [] ->
       ExecF.rng RNG (shadow_addr p) (shadow_addr (p + Z.of_nat (length bb) - 1) - shadow_addr p + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (lib_sum16 bb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SUM16_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length bb))) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SUM16) fc None m (seg_rom rsegs)).
