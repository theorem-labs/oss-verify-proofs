(* is_tagged_reac_F_c: the footprint contract of image B's is_tagged_reac (fuzz_wire.asan-ubsan 0x8103c), as a
   STATEMENT only (no proof), in the form of libreac/fuzz_decode's released lib/B/Prog/reac_frame_is_reac_F_c.v without
   its shadow_rw premise (as fuzz_decode's reac_frame_is_reac_F_nosh.v and reac-repacer/fuzz_uci's
   lib/B/Prog/rp_hot_clamp_F_c.v state it), with image B's UBSan premise `bv_unsigned a0 <> 0`.
   The C (src/repace_wire.c:23-26 is_tagged_reac): f[12] == 0x81 && f[13] == 0x00 && f[16] == 0x88 && f[17] == 0x19. It is a
   separate function in this image (the plain and the asan images put its code inside its callers): rp_copy_untag calls
   it, rp_ds_accept jumps to it. Its model is lib/Prog/rp_copy_untag_c.v cu_tagged. It takes no length: both callers
   have checked n >= 18 first, so the premise is the 18 bytes it can read.
   The code (listing of image B, offsets from the entry):
     +0x0   `addi sp, sp, -16` (frame IS_TAGGED_REAC_FRAME = 16), +0x4 `sd ra, 8(sp)`, and +0xbc `ld ra, 8(sp)` back;
            it stores nothing else;
     +0x14 .. +0x1c  `auipc` / `ld` of the GOT word 0x98878 (GOT_CELL_K), then `ld a2, 0(a1)` (CELL_K: the shadow base);
     before each of its four byte loads (+0x34 f[12], +0x5c f[13], +0x80 f[16], +0xa8 f[17]) it loads the shadow byte
            of the address at (a >> 3) + ASAN_K (+0x2c, +0x54, +0x78, +0xa0) and continues when it is 0 or (a mod 8)
            is below it (the slow path +0xcc, +0xdc, +0xec, +0xfc); otherwise it calls __asan_report_load1 (0x57e5c)
            at +0xd8, +0xe8, +0xf8, +0x104, the error path;
     +0x3c `bne` (f[12] <> 0x81), +0x60 `bnez` (f[13] <> 0), +0x88 `bne` (f[16] <> 0x88) return 0 (+0xb8); +0xac /
            +0xb0 `addi a0, a0, -25` / `seqz` return f[17] = 0x19;
     it uses a1 .. a4 besides a0 and calls nothing else.
   Its UBSan checks branch to `unimp` at +0xc8: +0x8 `beqz a0` (f = NULL), +0x10 `bgeu a0, a1` (a1 = -12: f + 12
   wraps), +0x44 (-14: f + 13), +0x68 (-17: f + 16), +0x90 (-18: f + 17) `bltu a1, a0`. `bv_unsigned a0 <> 0` refutes
   the first; the addressable premise of [f + 16, f + 18) (its end at most APPMEM_END) refutes the others.
   The run is an ExecF.evtF run under a footprint RNG: every data access of every step lies in RNG. So RNG holds the
   stack frame, the two cells, the bytes [f + 12, f + 14) and [f + 16, f + 18), and their shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
Open Scope Z_scope.
Module PCU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.

(* The entry (the unstripped twin's symbol is_tagged_reac) and the frame (+0x0 `addi sp, sp, -16`). *)
Definition IS_TAGGED_REAC : Z := 0x8103c.
Definition IS_TAGGED_REAC_FRAME : Z := 16.

(* The result in a0: 1 when the four bytes are the tag, else 0. *)
Definition is_tagged_result (bs : list byte) : Z := if PCU.cu_tagged bs then 1 else 0.

Definition is_tagged_reac_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* Image B's UBSan premise: +0x8 `beqz a0, +0xc8` traps (unimp at +0xc8) on f == NULL. *)
    bv_unsigned a0 <> 0 ->
    (18 <= length bs)%nat -> bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + IS_TAGGED_REAC_FRAME <= bv_unsigned sp ->
    off_stk sp IS_TAGGED_REAC_FRAME (bv_unsigned a0) 18 ->
    app_mem (bv_unsigned sp - IS_TAGGED_REAC_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp IS_TAGGED_REAC_FRAME GOT_CELL_K 8 ->
    off_stk sp IS_TAGGED_REAC_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 12) 2 ->
    addressable m (bv_unsigned a0 + 16) 2 ->
    ExecF.rng RNG (bv_unsigned sp - IS_TAGGED_REAC_FRAME) IS_TAGGED_REAC_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 12) 2 ->
    ExecF.rng RNG (bv_unsigned a0 + 16) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
      (shadow_addr (bv_unsigned a0 + 13) - shadow_addr (bv_unsigned a0 + 12) + 1) ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 16))
      (shadow_addr (bv_unsigned a0 + 17) - shadow_addr (bv_unsigned a0 + 16) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (is_tagged_result bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - IS_TAGGED_REAC_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IS_TAGGED_REAC) fc None m (seg_rom rsegs)).
