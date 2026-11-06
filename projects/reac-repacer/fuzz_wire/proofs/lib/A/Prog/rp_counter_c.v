(* The evt contract of reac-repacer/fuzz_wire's rp_counter in image A, in the form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_c.v (entry, frame, the ASan runtime cells and addressability premises, no shadow_rw premise) with the read-only buffer premise of libreac/fuzz_decode's released lib/A/Prog/reac_frame_counter_c.v, over the plain contract's model (lib/Prog/rp_counter_c.v counter_result). *)
(* rp_counter_c: rp_counter of fuzz_wire.asan (0x812f4 = wire_sigma WS_rp_counter, lib/A/Prog/WirePAddr.v), a leaf.
   The C (src/repace_wire.c:69-72): return (unsigned)(f[14] | (f[15] << 8)).
   The code (DIS of image A, 0x812f4 .. 0x8136c):
     +0x0   `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)` ... +0x4c `ld ra, 8(sp)`, +0x50 `addi sp, sp, 0x10`, +0x54 `ret`
            (frame [sp - 16, sp); `sd ra` is the only store, so it writes nothing outside its frame);
     +0x8   `auipc a1, 0x17`, +0xc `ld a1, 0x4ec(a1)`: the shadow base's GOT word (0x987e8, GOT_CELL_K), +0x10
            `ld a2, 0(a1)`: the shadow base cell (CELL_K);
     +0x14..+0x24 the shadow byte of f + 14, (a >> 3) + base, `bnez` to +0x58 (the partial-granule test, then
            `jal __asan_report_load1` at +0x64);
     +0x28..+0x34 the shadow byte of f + 15; +0x38 `lbu a0, 14(a0)` = f[14]; +0x3c `bnez` to +0x68 (then
            `jal __asan_report_load1` at +0x74); +0x40 `lbu a1, 0(a1)` = f[15]; +0x44 `slli a1, a1, 8`, +0x48 `or`.
   It calls nothing but the two __asan_report_load1 sinks, which addressable refutes. It writes a0 .. a4 only
   (a4 on the partial-granule path +0x58). Unlike libreac's reac_frame_counter (a uint16_t, truncated by
   `slli/srli a0, a0, 0x30`), the result is the unsigned of the two bytes, with no truncation: counter_result. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

(* The entry (symbol rp_counter of the unstripped twin) and the frame (`addi sp, sp, -0x10` at the entry). *)
Definition RP_COUNTER : Z := 0x812f4.
Definition RP_COUNTER_FRAME : Z := 16.

Definition rp_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp RP_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - RP_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_COUNTER_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 14) 2 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (PRC.counter_result bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COUNTER) fc None m (seg_rom rsegs)).
