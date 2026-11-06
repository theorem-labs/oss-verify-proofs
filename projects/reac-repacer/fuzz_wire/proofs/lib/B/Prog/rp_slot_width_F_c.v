(* rp_slot_width_F_c: the footprint contract of rp_slot_width in image B (fuzz_wire.asan-ubsan), in the form of
   reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_F_c.v. STATEMENT only (no proof).

   The C (src/repace_wire.c rp_slot_width, modelled by lib/Prog/rp_slot_width_c.v rp_slot_width_model): -1 unless the
   frame is 50 bytes or more and its two type bytes f[16] / f[17] are zero; otherwise rp_frame_channels of (long)n,
   and -1 again unless that width holds the slot.
   The code (image B, entry 0x8151c, 0xd0 bytes):
     +0x0   `addi sp, sp, -0x10`, `sd ra, 8(sp)`, `sd s0, 0(sp)`: the frame [sp - 16, sp), the only memory it writes;
     +0x1c  `bltu a1, a3` (a3 = 50) returns -1 before any load;
     +0x20  `beqz a2` and +0x28 `bgeu a2, a3` (a3 = -16) and +0x58 `bltu a3, a2` (a3 = -18) are the UBSan checks of
            f and of f + 16 / f + 17; each branches to the `unimp` at 0x815c8. Image A's text has none of them;
     +0x2c..+0x34 reads the shadow base through the GOT word 0x98878 (-> the cell 0xa07f8);
     +0x38..+0x74 loads f[16] and f[17] (`lbu` at +0x4c / +0x70), each behind the shadow byte of its address
            ((a >> 3) + the base, `lb` at +0x44 / +0x68), which branches to __asan_report_load1 (0x57e5c) at
            0x815d8 / 0x815e8 when the byte is not addressable;
     +0x7c  `jal rp_frame_channels` (0x813a0), which itself calls reac_frame_clean_len (0x818e8, no frame of its own);
     +0x80..+0x98 the slot bound, then the epilogue (+0x9c..+0xa8).
   So the run writes only [sp - 16, sp); below that only rp_frame_channels's own 16-byte frame is used, and the
   footprint RNG holds: the two frames, the two runtime cells, the two frame bytes with their shadow bytes, and the
   three read-only words the callee chain reads (0x10300 and 0x103b0 in reac_frame_clean_len, 0x10328 in
   rp_frame_channels), whose positions and values rp_frame_channels's own footprint contract needs at the same RNG. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_frame_channels_F_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PRFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_F_c.

(* The entry of rp_slot_width in image B, its own frame, and its stack window: the frame plus the 16 bytes of
   rp_frame_channels's frame below it (RP_FRAME_CHANNELS_FRAME, lib/B/Prog/rp_frame_channels_c.v; reac_frame_clean_len,
   which rp_frame_channels calls, has no frame). *)
Definition RP_SLOT_WIDTH : Z := 0x8151c.
Definition RP_SLOT_WIDTH_FRAME : Z := 16.
Definition RP_SLOT_WIDTH_STK : Z := RP_SLOT_WIDTH_FRAME + RP_FRAME_CHANNELS_FRAME.

(* The two frame bytes this function loads: f[16] and f[17] (repace_wire.c is_audio). *)
Definition RP_SW_OFF : Z := 16.
Definition RP_SW_LEN : Z := 2.

(* The constant words the callee chain reads: A_M = 0x10300 and A_T = 0x103b0 (reac_frame_clean_len's two constants,
   `ld` at 0x818f4 and 0x818fc; lib/B/Prog/reac_frame_clean_len_c.v) and A_K36 = 0x10328 (the reciprocal of 36, `ld`
   at 0x813c4 in rp_frame_channels; lib/B/Prog/rp_frame_channels_c.v). All three lie in the first PT_LOAD
   [0x10000, 0x2ef5c), which is read-only. In image B, 0x10300 and 0x103b0 are the two rows of lib/B/Prog/WireCg.v
   WIRE_RO_RD (unowned, read through the read-only view wire_rom_view_rd), and 0x10328 is an owned static of the
   record and wire_cells' row 20 (WireCg.v WIRE_RO_FCH). A footprint contract fixes only the memory m, so their values
   are premises below (bytes_at in m, the form of rp_frame_channels_F_c.v): the caller proves them from its view, and
   without them an overlay on any of the three words changes the result. *)
Definition WIRE_RFC_CONSTS : list (Z * Z) := [(A_M, 8); (A_K36, 8); (A_T, 8)].

Definition rp_slot_width_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* The values of the three constant words (rp_frame_channels_F_c.v's first three premises, verbatim): the callee
       chain's footprint contract asks for them at the call, and nothing else here fixes them. *)
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_SLOT_WIDTH_STK <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_SLOT_WIDTH_STK) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_SLOT_WIDTH_STK GOT_CELL_K 8 ->
    off_stk sp RP_SLOT_WIDTH_STK CELL_K 8 ->
    (* The frame is read only on the n >= 50 path (+0x1c returns -1 below it), so every premise about it is that
       path's, as lib/Prog/rp_slot_width_c.v states them. *)
    (50 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_SLOT_WIDTH_STK (bv_unsigned a0) (Z.of_nat (length bs)) /\
       addressable m (bv_unsigned a0 + RP_SW_OFF) RP_SW_LEN) ->
    (* Image B's UBSan premises, all three on the n >= 50 path: 0x8153c `beqz a2` traps (unimp at 0x815c8) on
       f == NULL, 0x81544 `bgeu a2, a3` (a3 = -16) on f + 16 wrapping, and 0x81574 `bltu a3, a2` (a3 = -18) on
       f + 17 wrapping. Image A's text lacks them. *)
    (50 <= bv_unsigned a1 -> bv_unsigned a0 <> 0 /\ bv_unsigned a0 + 18 <= 2 ^ 64) ->
    ExecF.rng RNG (bv_unsigned sp - RP_SLOT_WIDTH_STK) RP_SLOT_WIDTH_STK ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    (* the callee chain's constant words: separated from this call's stack window, and inside RNG. The separation
       is the form rp_frame_channels_F_c.v states for each of them (off_stk at its own frame), at this window,
       which is the wider one. *)
    Forall (fun r => off_stk sp RP_SLOT_WIDTH_STK (fst r) (snd r)) WIRE_RFC_CONSTS ->
    Forall (fun r => ExecF.rng RNG (fst r) (snd r)) WIRE_RFC_CONSTS ->
    (50 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + RP_SW_OFF) RP_SW_LEN) ->
    (50 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + RP_SW_OFF))
         (shadow_addr (bv_unsigned a0 + RP_SW_OFF + RP_SW_LEN - 1) - shadow_addr (bv_unsigned a0 + RP_SW_OFF) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_SLOT_WIDTH_STK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_SLOT_WIDTH) fc None m (seg_rom rsegs)).

(* The statement the walk will prove (close row H_PROG_RSW_F), in the form of rp_frame_channels_F_c.v's
   rp_frame_channels_F_holds_stmt: rp_frame_channels's footprint contract gives rp_slot_width's. The two report
   branches (__asan_report_load1 at 0x815d8 and 0x815e8) are refuted by the addressability of f[16] / f[17], and the
   three UBSan traps at 0x815c8 by the premises on f, so neither a report nor a trap entry is a hypothesis here. *)
Definition rp_slot_width_F_holds_stmt : Prop :=
  PRFC.rp_frame_channels_contract_F -> rp_slot_width_contract_F.
