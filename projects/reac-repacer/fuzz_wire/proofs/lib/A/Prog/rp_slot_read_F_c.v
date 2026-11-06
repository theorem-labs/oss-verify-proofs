(* rp_slot_read_F_c: the footprint contract of rp_slot_read in image A (fuzz_wire.asan), in the form of
   reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_F_c.v. STATEMENT only (no proof).

   The C (src/repace_wire.c rp_slot_read, modelled by lib/Prog/rp_slot_read_c.v rp_slot_read_model / rp_slot_bytes):
   rp_slot_width of (f, n, slot); when that width is negative it returns 0 and writes nothing, otherwise it reads the
   12 samples of the slot through the braid map behind REAC_AUDIO_OFFSET = 50 and writes v[0..11] (48 bytes), 1.
   The code (image A, entry 0x8160c, 0x1b0 bytes):
     +0x0   `addi sp, sp, -0x30`, `sd ra, 0x28(sp)` .. `sd s4, 0(sp)`: the frame [sp - 48, sp), the whole of which is
            the saved registers (image B's larger frame also holds the braid offsets in memory);
     +0x24..+0x2c reads the shadow base through the GOT word 0x987e8 (-> the cell 0xa0778);
     +0x38  `jal rp_slot_width` (0x81554), whose own window is 32 bytes below this frame;
     +0x3c  `bltz a0` returns 0 (+0x16c) when the width is negative, before any access to f or v;
     +0x94..+0xf0 the three braid bytes per sample (shadow `lb` at +0xa0 / +0xbc / +0xd4, byte loads at +0xc0 / +0xd8
            / +0xf0), each behind the shadow byte of its address, which branches to __asan_report_load1 (0x580bc) at
            0x817b0 / 0x817b8 / 0x817a4;
     +0xe4..+0xf4 the shadow byte of v[s] (`lb` at +0xec), whose slow path (+0x154..+0x15c, the 4-byte test
            (v & 7) + 3 < shadow) branches to __asan_report_store4 (0x5851c) at 0x8176c; +0x11c `sw a1, 0(s0)` writes
            v[s]. The 48 bytes of v are the only memory it writes outside its own frame.
   Image A is the ASan-only build: it has no UBSan check and no `unimp`, so it needs none of image B's twin's UBSan
   premises. In particular nothing in it (or in rp_slot_width) tests f or v against 0 or tests v's alignment: f and v
   enter only as the addresses of the braid loads and of the 12 stores, the ASan test of each store is refuted by the
   addressability of v byte by byte whatever v's alignment, and the machine's `sw` needs no alignment
   (lib/Prog/rp_slot_read.v proves the plain build's store loop, `sw` to v + 4 s, with no alignment premise on v).
   So the footprint RNG holds: this frame and rp_slot_width's below it, the two runtime cells, the frame bytes and v
   with their shadow bytes, and the constant words the callee chain reads, whose values the contract fixes (its first
   three premises, as rp_slot_width_F_c.v takes them). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c
  rp_slot_width_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c rp_slot_read_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.

(* The entry of rp_slot_read in image A, its own frame, and its stack window: the frame plus rp_slot_width's
   32-byte window below it. *)
Definition RP_SLOT_READ : Z := 0x8160c.
Definition RP_SLOT_READ_FRAME : Z := 48.
Definition RP_SLOT_READ_STK : Z := RP_SLOT_READ_FRAME + RP_SLOT_WIDTH_STK.
(* REAC_SAMPLES_PER_PKT = 12 int32_t. *)
Definition RP_SLOT_READ_VLEN : Z := 48.
(* REAC_AUDIO_OFFSET: the braid bytes start 50 bytes into the frame. *)
Definition RP_AUDIO_OFF : Z := 50.

Definition rp_slot_read_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* the callee chain's three constant words hold their image values (rp_frame_channels_F_c.v's premises) *)
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_SLOT_READ_STK <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_SLOT_READ_STK) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    (* The stack window is kept off EVERY runtime cell, not only the two this function reads: its six register saves
       (+0x4..+0x18) come before `jal rp_slot_width` (+0x38), whose contract takes asan_cells at the call. The 19
       cells of AsanCells.asan_cells span [GOT_CELL_K, MIDEND + 8) = [0x987e8, 0xa1478) (GOT_CELL_K the lowest, MIDEND
       the highest), and this one premise implies the separation from GOT_CELL_K and CELL_K the reads need (the
       caller form of libreac/fuzz_decode's reac_decode_F_c.v). *)
    off_stk sp RP_SLOT_READ_STK GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (* The frame, as lib/Prog/rp_slot_read_c.v states it, plus the shadow of every byte the braid loads read. *)
    (RP_AUDIO_OFF <= bv_unsigned a1 ->
       bv_unsigned a1 <= Z.of_nat (length bs) /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a0) (Z.of_nat (length bs)) /\
       addressable m (bv_unsigned a0) (Z.of_nat (length bs))) ->
    (* v is written only when the width is not negative. *)
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       wr_at rsegs m (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       (bv_unsigned a3 + RP_SLOT_READ_VLEN <= bv_unsigned a0 \/
        bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a3) /\
       addressable m (bv_unsigned a3) RP_SLOT_READ_VLEN) ->
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

(* The statement the walk will prove: rp_slot_width's footprint contract gives rp_slot_read's (callers chain by
   `<callee>_contract_F -> <fn>_contract_F`, as rp_frame_channels_F_c.v's rp_frame_channels_F_holds_stmt). The callee's
   three bytes_at premises are this contract's first three (this frame's stores avoid them: WIRE_RFC_CONSTS off_stk).
   The three load report branches (0x817a4, 0x817b0, 0x817b8) and the store report branch (0x8176c) are refuted by the
   addressability of f's bytes and of v. Image A has no UBSan trap, so no trap premise appears, where image B's twin
   carries its UBSan premises (of f and of v). *)
Definition rp_slot_read_F_holds_stmt : Prop :=
  rp_slot_width_contract_F -> rp_slot_read_contract_F.
