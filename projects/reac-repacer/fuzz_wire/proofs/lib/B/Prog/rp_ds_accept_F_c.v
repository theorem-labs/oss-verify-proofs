(* rp_ds_accept_F_c: the footprint contract of rp_ds_accept of fuzz_wire.asan-ubsan, a leaf, as a STATEMENT only (no
   proof).
   The C (src/repace_wire.c:50-55): `if (n < 18) return 0; return is_reac(f) || is_tagged_reac(f);` (the model
   lib/Prog/rp_ds_accept_c.v ds_accept_result of n and the frame bytes bs).
   The code (DIS of image B, entry RP_DS_ACCEPT, 46 words):
     - +0x0 `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)`, `ld ra, 8(sp)` at +0x14 and +0x88 (stack frame [sp - 16, sp));
       it stores nothing else;
     - +0xc `bgeu a1, a2, +0x20` (a2 = 18): n < 18 returns 0 (`li a0, 0` at +0x10) before any other access;
     - its UBSan checks of f branch to `unimp` at +0x94 (0x81018): f = 0 (+0x20 `beqz a0`), f + 12 wraps (+0x28
       `bgeu a0, a1`, a1 = -12), f + 13 wraps (+0x5c `bltu a1, a0`, a1 = -14);
     - +0x2c / +0x30 `auipc a1, 0x18` / `ld a1, -0x738(a1)` loads the GOT word GOT_CELL_K, +0x34 `ld a2, 0(a1)` the
       shadow base at CELL_K;
     - it loads f[12] (+0x4c) and f[13] (+0x74), each after a load of its shadow byte (a >> 3) + ASAN_K (+0x44, +0x6c)
       whose non-zero value branches to __asan_report_load1 (`jal` at +0xa4, +0xb4) unless the granule holds the byte;
       f[12] = 0x88 and f[13] = 0x19 return 1 (+0x80);
     - otherwise +0x88 / +0x8c restore ra and sp and +0x90 `j is_tagged_reac` (0x8103c) TAIL-JUMPS to is_tagged_reac
       with ra, sp and a0 = f as at entry. is_tagged_reac (66 words) stores only `sd ra, 8(sp)` into the same frame
       [sp - 16, sp), traps f = 0 and the wraps of f + 12, f + 13, f + 16, f + 17 (unimp at 0x81104), loads the same
       two cells, and loads f[12], f[13], f[16], f[17], each after its shadow byte (report sinks at 0x81114, 0x81124,
       0x81134, 0x81140); it returns to ra with a0 = is_tagged_reac(f).
   Neither calls anything else. So RNG holds the stack frame and, when 18 <= n, the two cells, the bytes
   [f + 12, f + 18) and their shadow bytes. The report branches are refuted by `addressable m (f + 12) 6`, the UBSan
   traps by `bv_unsigned a0 <> 0` and by the same addressable (f + 18 <= APPMEM_END). The walk takes is_tagged_reac's
   footprint contract (lib/B/Prog/is_tagged_reac_F_c.v) at the tail jump (lib/B/Prog/rp_ds_accept_cg.v
   wire_rp_ds_accept_holds_stmt). That contract asks asan_cells of the memory after the `sd ra` at +0x4, so the frame
   lies off the whole cell region [GOT_CELL_K, MIDEND + 8) (every row of asan_cells is inside it), as the released
   chained caller proofs/libreac/fuzz_decode/lib/B/Prog/reac_decode_c.v states it for its callee. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.

(* rp_ds_accept's entry in fuzz_wire.asan-ubsan (`addi sp, sp, -0x10` at 0x80f84) and its frame. *)
Definition RP_DS_ACCEPT : Z := 0x80f84.
Definition RP_DS_ACCEPT_FRAME : Z := 16.

Definition rp_ds_accept_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_DS_ACCEPT_FRAME <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (* Image B's UBSan premise: 0x80fa4 `beqz a0, 0x81018` traps (unimp at 0x81018) on f == NULL. *)
       bv_unsigned a0 <> 0 /\
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_DS_ACCEPT_FRAME (bv_unsigned a0) 18 /\
       app_mem (bv_unsigned sp - RP_DS_ACCEPT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_DS_ACCEPT_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) /\
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
