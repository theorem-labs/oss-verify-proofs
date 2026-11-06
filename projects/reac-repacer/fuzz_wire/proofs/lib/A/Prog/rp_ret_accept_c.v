(* The evt contract of reac-repacer/fuzz_wire's rp_ret_accept in image A, in the form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_c.v (entry, frame, the ASan runtime cells and addressability premises, no shadow_rw premise) with the read-only buffer premise of libreac/fuzz_decode's released lib/A/Prog/reac_frame_is_reac_c.v, over the plain contract's model (lib/Prog/rp_ret_accept_c.v ret_accept_result). *)
(* rp_ret_accept_c: rp_ret_accept of fuzz_wire.asan (0x80fe0 = wire_sigma WS_rp_ret_accept, lib/A/Prog/WirePAddr.v), a
   leaf. The C (src/repace_wire.c:45-48): return n >= 14 && is_reac(f), is_reac(f) = f[12] == 0x88 && f[13] == 0x19.
   The code (DIS of image A, 0x80fe0 .. 0x8106c):
     +0x0   `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)` ... +0x64 `ld ra, 8(sp)`, +0x68 `addi sp, sp, 0x10`, +0x6c `ret`
            (frame [sp - 16, sp); `sd ra` is the only store, so it writes nothing outside its frame);
     +0x8   `li a2, 14`, +0xc `bltu a1, a2` to +0x60 (`li a0, 0`): n < 14 returns 0 before any other load;
     +0x10  `auipc a1, 0x17`, +0x14 `ld a1, 0x7f8(a1)`: the shadow base's GOT word (0x987e8, GOT_CELL_K), +0x18
            `ld a2, 0(a1)`: the shadow base cell (CELL_K);
     +0x1c..+0x2c the shadow byte of f + 12, (a >> 3) + base, `bnez` to +0x70 (the partial-granule test, then
            `jal __asan_report_load1` at +0x7c); +0x30 `lbu a1, 0(a1)` = f[12]; +0x38 `bne` 0x88 to +0x60 (returns 0);
     +0x3c..+0x4c the shadow byte of f + 13, `bnez` to +0x80 (then `jal __asan_report_load1` at +0x88); +0x50
            `lbu a0, 0(a0)` = f[13]; +0x54 `addi a0, a0, -25`, +0x58 `seqz a0, a0` (f[13] == 0x19).
   It calls nothing but the two __asan_report_load1 sinks, which addressable refutes. It writes a0 .. a4 only
   (a4 on the partial-granule path +0x70). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

(* The entry (symbol rp_ret_accept of the unstripped twin) and the frame (`addi sp, sp, -0x10` at the entry). *)
Definition RP_RET_ACCEPT : Z := 0x80fe0.
Definition RP_RET_ACCEPT_FRAME : Z := 16.

(* The frame is read only when n >= 14 (the `bltu` at +0xc comes before every load but the frame's), so the buffer
   premise, the cells, the stack separation and the shadow premise are taken under that condition. *)
Definition rp_ret_accept_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_RET_ACCEPT_FRAME <= bv_unsigned sp ->
    (14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_RET_ACCEPT_FRAME (bv_unsigned a0) 14 /\
       app_mem (bv_unsigned sp - RP_RET_ACCEPT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_RET_ACCEPT_FRAME GOT_CELL_K 8 /\
       off_stk sp RP_RET_ACCEPT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0 + 12) 2) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_RET_ACCEPT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_RET_ACCEPT) fc None m (seg_rom rsegs)).
