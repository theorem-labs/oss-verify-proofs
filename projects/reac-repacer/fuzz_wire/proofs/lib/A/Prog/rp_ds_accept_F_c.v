(* rp_ds_accept_F_c: the footprint contract of rp_ds_accept of fuzz_wire.asan, a leaf, as a STATEMENT only (no
   proof).
   The C (src/repace_wire.c:50-55): `if (n < 18) return 0; return is_reac(f) || is_tagged_reac(f);` (the model
   lib/Prog/rp_ds_accept_c.v ds_accept_result of n and the frame bytes bs).
   The code (DIS of image A, entry RP_DS_ACCEPT, 63 words):
     - +0x0 `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)`, `ld ra, 8(sp)` at +0x8c (stack frame [sp - 16, sp)); it stores
       nothing else;
     - +0xc `bltu a1, a2, +0x88` (a2 = 18): n < 18 returns 0 (`mv a0, zero` at +0x88) before any other access;
     - +0x10 / +0x14 `auipc a1, 0x17` / `ld a1, 0x76c(a1)` loads the GOT word GOT_CELL_K, +0x18 `ld a2, 0(a1)` the
       shadow base at CELL_K;
     - it loads the frame bytes f[12] (+0x30), f[13] (+0x58 on the tagged path, +0xb0 on the untagged one), f[16]
       (+0x74) and f[17] (+0xb0), each after a load of its shadow byte (a >> 3) + ASAN_K (+0x28, +0x50, +0x6c, +0xa8)
       whose non-zero value branches to __asan_report_load1 (`jal` at +0xcc, +0xd8, +0xe8, +0xf8) unless the granule
       holds the byte; is_tagged_reac is inlined (+0x3c .. +0x84, and the tail +0x9c .. +0xbc, which is_reac's f[13]
       test also runs, entered at +0x98). It calls nothing else.
   So RNG holds the stack frame and, when 18 <= n, the two cells, the bytes [f + 12, f + 18) and their shadow bytes.
   The report branches are refuted by `addressable m (f + 12) 6`. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.

(* rp_ds_accept's entry in fuzz_wire.asan (`addi sp, sp, -0x10` at 0x8106c) and its frame. *)
Definition RP_DS_ACCEPT : Z := 0x8106c.
Definition RP_DS_ACCEPT_FRAME : Z := 16.

Definition rp_ds_accept_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_DS_ACCEPT_FRAME <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_DS_ACCEPT_FRAME (bv_unsigned a0) 18 /\
       app_mem (bv_unsigned sp - RP_DS_ACCEPT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_DS_ACCEPT_FRAME GOT_CELL_K 8 /\
       off_stk sp RP_DS_ACCEPT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0 + 12) 6) ->
    ExecF.rng RNG (bv_unsigned sp - RP_DS_ACCEPT_FRAME) RP_DS_ACCEPT_FRAME ->
    (18 <= bv_unsigned a1 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned a0 + 12) 6 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 6 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (PDA.ds_accept_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_DS_ACCEPT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_DS_ACCEPT) fc None m (seg_rom rsegs)).
