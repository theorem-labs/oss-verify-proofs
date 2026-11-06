(* rp_slot_width_F_c: the footprint contract of rp_slot_width in image A (fuzz_wire.asan), in the form of
   reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_F_c.v. STATEMENT only (no proof).

   The C (src/repace_wire.c rp_slot_width, modelled by lib/Prog/rp_slot_width_c.v rp_slot_width_model): -1 unless the
   frame is 50 bytes or more and its two type bytes f[16] / f[17] are zero; otherwise rp_frame_channels of (long)n,
   and -1 again unless that width holds the slot.
   The code (image A, entry 0x81554, 0xb8 bytes):
     +0x0   `addi sp, sp, -0x10`, `sd ra, 8(sp)`, `sd s0, 0(sp)`: the frame [sp - 16, sp), the only memory it writes;
     +0x1c  `bltu a1, a3` (a3 = 50) returns -1 before any load;
     +0x20..+0x28 reads the shadow base through the GOT word 0x987e8 (-> the cell 0xa0778);
     +0x2c..+0x60 loads f[16] and f[17] (shadow `lb` at +0x38 / +0x54, byte `lbu` at +0x40 / +0x5c), each behind
            the shadow byte of its address ((a >> 3) + the base), which branches to __asan_report_load1 (0x580bc) at
            0x815f8 / 0x81608 when the byte is not addressable;
     +0x68  `jal rp_frame_channels` (0x8136c), which itself calls reac_frame_clean_len (0x81854, no frame of its own);
     +0x6c..+0x84 the slot bound (the full 64-bit slot register: `or`, `slti`, `slt`), +0x88..+0x94 the epilogue.
   Image A is the ASan-only build: it has no UBSan check and no `unimp`, so it needs none of image B's twin's UBSan
   premises. In particular nothing in it tests f against 0: f enters only as the address of the two loads, and their
   addressability (with the RNG premise of [f + 16, f + 18)) is all the run needs of it.
   So the run writes only [sp - 16, sp); below that only rp_frame_channels's own 16-byte frame is used, and the
   footprint RNG holds: the two frames, the two runtime cells, the two frame bytes with their shadow bytes, and the
   three constant words the callee chain reads. The callee chain's result depends on the bytes of those three words
   (the machine reads the overlay m before the image, lib/Lib/Mem.v mrd), so the contract fixes them, in the form
   lib/A/Prog/rp_frame_channels_F_c.v takes them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_frame_channels_F_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PRFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_frame_channels_F_c.

(* The entry of rp_slot_width in image A, its own frame, and its stack window: the frame plus the 16 bytes of
   rp_frame_channels's frame below it (lib/A/Prog/rp_frame_channels_c.v RP_FRAME_CHANNELS_FRAME; reac_frame_clean_len,
   which rp_frame_channels calls, has no frame). *)
Definition RP_SLOT_WIDTH : Z := 0x81554.
Definition RP_SLOT_WIDTH_FRAME : Z := 16.
Definition RP_SLOT_WIDTH_STK : Z := RP_SLOT_WIDTH_FRAME + RP_FRAME_CHANNELS_FRAME.

(* The two frame bytes this function loads: f[16] and f[17] (repace_wire.c is_audio). *)
Definition RP_SW_OFF : Z := 16.
Definition RP_SW_LEN : Z := 2.

(* The constant words the callee chain reads: A_M = 0x10300 and A_T = 0x103b0 (reac_frame_clean_len's two constants,
   `ld` at 0x81860 and 0x81868; lib/A/Prog/reac_frame_clean_len_c.v), the two rows of lib/A/Prog/WireCg.v WIRE_RO_RD,
   and A_K36 = 0x10328 (the reciprocal of 36, `ld` at 0x81390 in rp_frame_channels; lib/A/Prog/rp_frame_channels_c.v),
   which in this image is an owned static of the record and reaches a walk as the constant cell WireCg.v
   WIRE_RO_FCH, not as a read-only byte. Their values are the contract's first three premises; their positions, here,
   give the separation from the stack window and the RNG premises. *)
Definition WIRE_RFC_CONSTS : list (Z * Z) := [(A_M, 8); (A_K36, 8); (A_T, 8)].

Definition rp_slot_width_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* the callee chain's three constant words hold their image values (rp_frame_channels_F_c.v's premises) *)
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

(* The statement the walk will prove: rp_frame_channels's footprint contract gives rp_slot_width's (callers chain by
   `<callee>_contract_F -> <fn>_contract_F`, as rp_frame_channels_F_c.v's rp_frame_channels_F_holds_stmt). The callee's
   three bytes_at premises are this contract's first three (its frame stores avoid them: WIRE_RFC_CONSTS off_stk). The
   two report branches (__asan_report_load1 at 0x815f8 and 0x81608) are refuted by the addressability of f[16] /
   f[17]. Image A has no UBSan trap, so no trap premise appears, where image B's twin carries its UBSan premises. *)
Definition rp_slot_width_F_holds_stmt : Prop :=
  PRFC.rp_frame_channels_contract_F -> rp_slot_width_contract_F.
