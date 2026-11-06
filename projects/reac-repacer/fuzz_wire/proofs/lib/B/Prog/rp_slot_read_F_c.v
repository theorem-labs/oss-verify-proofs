(* rp_slot_read_F_c: the footprint contract of rp_slot_read in image B (fuzz_wire.asan-ubsan), in the form of
   reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_F_c.v. STATEMENT only (no proof).

   The C (src/repace_wire.c rp_slot_read, modelled by lib/Prog/rp_slot_read_c.v rp_slot_read_model / rp_slot_bytes):
   rp_slot_width of (f, n, slot); when that width is negative it returns 0 and writes nothing, otherwise it reads the
   12 samples of the slot through the braid map behind REAC_AUDIO_OFFSET = 50 and writes v[0..11] (48 bytes), 1.
   The code (image B, entry 0x815ec, 0x250 bytes):
     +0x0   `addi sp, sp, -0x60`, `sd ra, 0x58(sp)` .. `sd s7, 0x18(sp)`: the frame [sp - 96, sp); the three 8-byte
            slots at sp + 0, 8, 16 are the braid offsets (reac_braid_pos's pos[3]);
     +0x30  reads the shadow base through the GOT word 0x98878 (-> the cell 0xa07f8);
     +0x44  `jal rp_slot_width` (0x8151c), whose own window is 32 bytes below this frame;
     +0x48  `bltz a0` returns 0 (+0x204) when the width is negative, before any access to f or v;
     +0x4c  `beqz s2` and +0x54 `bltu a1, s2` (a1 = -51) are the UBSan checks of f and f + 50, and the loop carries
            the UBSan checks of the braid arithmetic (`mul` / `mulw` and `add` / `addw` compared at +0x9c..+0xb4), of
            the pos[] slot addresses sp + 8 / sp + 16 (+0xd0, +0xd8, +0xec, +0xf8), of each braid address
            (`bltu t5, ...` at +0x10c, +0x114, +0x11c, t5 = ~(f + 50)) and of v (+0x164 `bltu a1, s0`: v + 4s
            wrapping; +0x170 `beqz s6`: v + 4s NULL against v; +0x174 `beqz t6`: v NULL or not 4-byte aligned, t6
            formed at +0x68..+0x8c); each branches to the `unimp` at 0x81820. Image A's text has none of them;
     +0x120..+0x184 the three braid bytes per sample (`lbu` / `lb` at +0x144, +0x15c, +0x184), each behind the
            shadow byte of its address (`lb` at +0x12c, +0x140, +0x158), which branches to __asan_report_load1
            (0x57e5c) at 0x81828 / 0x81830 / 0x81838;
     +0x1b4 `sw a2, 0(s4)` writes v[s], behind the shadow byte that branches to __asan_report_store4 (0x582bc) at
            0x817e4. The 48 bytes of v are the only memory it writes outside its own frame.
   So the footprint RNG holds: the two frames and rp_slot_width's below them, the two runtime cells, the frame bytes
   and v with their shadow bytes, and the read-only words the callee chain reads. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import rp_slot_width_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c rp_slot_read_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.

(* The entry of rp_slot_read in image B, its own frame, and its stack window: the frame plus rp_slot_width's
   32-byte window below it. *)
Definition RP_SLOT_READ : Z := 0x815ec.
Definition RP_SLOT_READ_FRAME : Z := 96.
Definition RP_SLOT_READ_STK : Z := RP_SLOT_READ_FRAME + RP_SLOT_WIDTH_STK.
(* REAC_SAMPLES_PER_PKT = 12 int32_t. *)
Definition RP_SLOT_READ_VLEN : Z := 48.
(* REAC_AUDIO_OFFSET: the braid bytes start 50 bytes into the frame. *)
Definition RP_AUDIO_OFF : Z := 50.

Definition rp_slot_read_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* The values of the three constant words the callee chain reads (rp_frame_channels_F_c.v's first three premises,
       verbatim; rp_slot_width_F_c.v WIRE_RFC_CONSTS). *)
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_SLOT_READ_STK <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_SLOT_READ_STK) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    (* The stack window is kept off EVERY runtime cell, not only the two this function reads: its nine register saves
       (+0x4..+0x24) come before `jal rp_slot_width` (+0x44), whose contract takes asan_cells at the call. The 19
       cells of AsanCells.asan_cells span [GOT_CELL_K, MIDEND + 8) = [0x98878, 0xa14f8) (GOT_CELL_K the lowest, MIDEND
       the highest), and this one premise implies the separation from GOT_CELL_K and CELL_K the reads need (the
       caller form of libreac/fuzz_decode's reac_decode_F_c.v). *)
    off_stk sp RP_SLOT_READ_STK GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (* The frame, as lib/Prog/rp_slot_read_c.v states it, plus the shadow of every byte the braid loads read, and f
       non-NULL: rp_slot_read hands f to rp_slot_width before the width is known, and there image B's UBSan check
       0x8153c `beqz a2` traps (unimp at 0x815c8) on f == NULL for every n >= 50. *)
    (RP_AUDIO_OFF <= bv_unsigned a1 ->
       bv_unsigned a1 <= Z.of_nat (length bs) /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a0) (Z.of_nat (length bs)) /\
       addressable m (bv_unsigned a0) (Z.of_nat (length bs)) /\
       bv_unsigned a0 <> 0) ->
    (* v is written only when the width is not negative. *)
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       wr_at rsegs m (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       (bv_unsigned a3 + RP_SLOT_READ_VLEN <= bv_unsigned a0 \/
        bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a3) /\
       addressable m (bv_unsigned a3) RP_SLOT_READ_VLEN) ->
    (* Image B's UBSan premises on the reading path: 0x81640 `bltu a1, s2` (a1 = -51) traps (unimp at 0x81820) on
       f + 50 wrapping, and 0x81760 `beqz t6` traps on every sample unless v is non-NULL and 4-byte aligned. 0x81638
       `beqz s2` (f == NULL) is refuted by f <> 0 above (a width that is not negative needs n >= 50). The other checks
       need no premise: the arithmetic checks of the loop and the three braid address checks are refuted by the width's
       own bounds (2 <= width <= 40, lib/Prog/rp_slot_width_c.v) and by the frame law 52 + 36 * width <= n; the four
       pos[] slot checks by app_mem (sp - 1); +0x164 and +0x170 by v <> 0 and wr_at's v + 48 <= 2 ^ 64. Image A's text
       lacks all of them. *)
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       bv_unsigned a0 + RP_AUDIO_OFF + 1 <= 2 ^ 64 /\ bv_unsigned a3 <> 0 /\ bv_unsigned a3 mod 4 = 0) ->
    ExecF.rng RNG (bv_unsigned sp - RP_SLOT_READ_STK) RP_SLOT_READ_STK ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    (* the callee chain's constant words, separated from this call's stack window and inside RNG *)
    Forall (fun r => off_stk sp RP_SLOT_READ_STK (fst r) (snd r)) WIRE_RFC_CONSTS ->
    Forall (fun r => ExecF.rng RNG (fst r) (snd r)) WIRE_RFC_CONSTS ->
    (RP_AUDIO_OFF <= bv_unsigned a1 ->
       ExecF.rng RNG (bv_unsigned a0) (Z.of_nat (length bs)) /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0))
         (shadow_addr (bv_unsigned a0 + Z.of_nat (length bs) - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       ExecF.rng RNG (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a3))
         (shadow_addr (bv_unsigned a3 + RP_SLOT_READ_VLEN - 1) - shadow_addr (bv_unsigned a3) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (PSR.rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if 0 <=? PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)
          then munch [(bv_unsigned sp - RP_SLOT_READ_STK, bv_unsigned sp);
                      (bv_unsigned a3, bv_unsigned a3 + RP_SLOT_READ_VLEN)] m m' /\
               bytes_at rsegs m' (bv_unsigned a3)
                 (PSR.rp_slot_bytes bs (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_signed a2))
          else munch [(bv_unsigned sp - RP_SLOT_READ_STK, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_SLOT_READ) fc None m (seg_rom rsegs)).

(* The statement the walk will prove (close row H_PROG_RSR_F), in the form of rp_frame_channels_F_c.v's
   rp_frame_channels_F_holds_stmt: rp_slot_width's footprint contract gives rp_slot_read's. The three load report
   branches (0x81828, 0x81830, 0x81838) and the store report branch (0x817e4) are refuted by the addressability of
   the frame and of v, and the UBSan traps at 0x81820 by the premises on f and v and by the width's own bounds, so
   neither a report nor a trap entry is a hypothesis here. *)
Definition rp_slot_read_F_holds_stmt : Prop :=
  rp_slot_width_contract_F -> rp_slot_read_contract_F.
