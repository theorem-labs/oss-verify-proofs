(* Modified by Theorem Labs: reac-repacer/fuzz_wire's rp_fwd_class in image A, in the footprint form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_F_c.v (itself the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_c.v at recipes commit 88154566652a without its shadow_rw premise). As reac_frame_is_reac_F_c.v, the buffer premises are taken under the guard of the function's own early exit (n >= 18), past which alone it reads the frame; the model is lib/Prog/rp_fwd_class_c.v fwd_class_result. Every address measured on fuzz_wire.asan. *)
(* rp_fwd_class_F_c: rp_fwd_class of fuzz_wire.asan (0x80ec4 = wire_sigma WS_rp_fwd_class), a leaf: its footprint
   contract, as a STATEMENT (no proof). The run is an ExecF.evtF run under a footprint RNG: every data access of every
   step lies in RNG.
   The C (src/repace_wire.c:34-43 rp_fwd_class (f, n, bcast_only)): RP_FWD_DROP (0) when n < 18, when f is not a REAC
   frame (f[12] = 0x88, f[13] = 0x19) and, when bcast_only, when f[0] <> 0xff; else RP_FWD_AUDIO (1) when
   f[16] = f[17] = 0, else RP_FWD_CTRL (2): lib/Prog/rp_fwd_class_c.v fwd_class_result n bcast_only of its bytes.
   The code (DIS of image A; 0x80ec4, 0x11c bytes):
     - `addi sp, sp, -0x10`, `sd ra, 8(sp)` ... `ld ra, 8(sp)` (frame [sp - 16, sp)): its only store;
     - 0x80ed0 `bltu a1, a3` (a3 = 18) returns 0 before any other data access when n < 18;
     - past it: it loads the GOT word GOT_CELL_K (0x987e8: `auipc a1, 0x18` / `ld a1, -0x6ec(a1)` at 0x80ed4 /
       0x80ed8) and the shadow base at CELL_K (0xa0778, the GOT word's value, __asan_shadow_memory_dynamic_address)
       (0x80edc), and before each `lbu` of f[12], f[13], f[0] (only when bcast_only <> 0: `beqz a2` at 0x80f20),
       f[16], f[17] it loads that byte's shadow byte, (a >> 3) + base, branching to __asan_report_load1 (0x580bc;
       calls at 0x80fa4, 0x80fb4, 0x80fc0, 0x80fd0, 0x80fdc) when the byte is not addressable. It calls nothing else.
   So, past the guard, RNG holds the frame, the two cells, the 18 bytes [f, f + 18) and their shadow bytes
   [shadow_addr f, shadow_addr (f + 17)]; addressable refutes each report. It changes a0 (the result) and a1 .. a5
   (a5 at the shadow tests 0x80f98 .. 0x80fd4). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.

(* Its entry (= wire_sigma WS_rp_fwd_class), its frame (`addi sp, sp, -0x10` at the entry) and the bytes of f it may
   read past its guard, [f, f + 18): f[0], f[12], f[13], f[16], f[17]. *)
Definition RP_FWD_CLASS : Z := 0x80ec4.
Definition RP_FWD_CLASS_FRAME : Z := 16.
Definition RP_FWD_CLASS_SPAN : Z := 18.

Definition rp_fwd_class_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_FWD_CLASS_FRAME <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_FWD_CLASS_FRAME (bv_unsigned a0) RP_FWD_CLASS_SPAN /\
       app_mem (bv_unsigned sp - RP_FWD_CLASS_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_FWD_CLASS_FRAME GOT_CELL_K 8 /\
       off_stk sp RP_FWD_CLASS_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0) RP_FWD_CLASS_SPAN) ->
    ExecF.rng RNG (bv_unsigned sp - RP_FWD_CLASS_FRAME) RP_FWD_CLASS_FRAME ->
    (18 <= bv_unsigned a1 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (18 <= bv_unsigned a1 -> ExecF.rng RNG CELL_K 8) ->
    (18 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0) RP_FWD_CLASS_SPAN) ->
    (18 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0))
         (shadow_addr (bv_unsigned a0 + RP_FWD_CLASS_SPAN - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (PFC.fwd_class_result (bv_unsigned a1) (bv_unsigned a2) bs)) a1' a2' a3' a4' a5'
                       a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FWD_CLASS_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_FWD_CLASS) fc None m (seg_rom rsegs)).
