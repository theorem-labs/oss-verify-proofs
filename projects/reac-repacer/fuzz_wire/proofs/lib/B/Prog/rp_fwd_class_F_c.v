(* rp_fwd_class_F_c: rp_fwd_class of fuzz_wire.asan-ubsan (0x80d9c = wire_sigma WS_rp_fwd_class), a leaf: its
   footprint contract, as a STATEMENT (no proof). The run is an ExecF.evtF run under a footprint RNG: every data access
   of every step lies in RNG.
   The C (src/repace_wire.c:34-43 rp_fwd_class (f, n, bcast_only)): RP_FWD_DROP (0) when n < 18, when f is not a REAC
   frame (f[12] = 0x88, f[13] = 0x19) and, when bcast_only, when f[0] <> 0xff; else RP_FWD_AUDIO (1) when
   f[16] = f[17] = 0, else RP_FWD_CTRL (2): lib/Prog/rp_fwd_class_c.v fwd_class_result n bcast_only of its bytes.
   The code (DIS of image B; 0x80d9c, 0x144 bytes):
     - `addi sp, sp, -0x10`, `sd ra, 8(sp)` ... `ld ra, 8(sp)` (frame [sp - 16, sp)): its only store;
     - 0x80da8 `bltu a1, a3` (a3 = 18) returns 0 before any other data access when n < 18;
     - past it: 0x80dac `beqz a0` traps on f = NULL, and 0x80db4, 0x80de8, 0x80e40, 0x80e64 trap when f + 12, f + 13,
       f + 16, f + 17 wrap (`unimp` at 0x80e94); it loads the GOT word GOT_CELL_K (0x98878: `auipc a1, 0x18` /
       `ld a1, -0x540(a1)` at 0x80db8 / 0x80dbc) and the shadow base at CELL_K (0xa07f8, the GOT word's value,
       __asan_shadow_memory_dynamic_address) (0x80dc0), and before each `lbu` of f[12], f[13], f[0] (only when
       bcast_only <> 0: `beqz a2` at 0x80e0c), f[16], f[17] it loads that byte's shadow byte, (a >> 3) + base,
       branching to __asan_report_load1 (0x57e5c; calls at 0x80ea4, 0x80eb4, 0x80ec0, 0x80ed0, 0x80edc) when the
       byte is not addressable. It calls nothing else.
   So, past the guard, RNG holds the frame, the two cells, the 18 bytes [f, f + 18) and their shadow bytes
   [shadow_addr f, shadow_addr (f + 17)]; addressable refutes each report and (f + 18 <= APPMEM_END) each wrap, and
   f <> NULL the NULL trap. It changes a0 (the result) and a1 .. a5 (a5 at the shadow tests 0x80e98 .. 0x80ed4). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.

(* Its entry (= wire_sigma WS_rp_fwd_class), its frame (`addi sp, sp, -0x10` at the entry) and the bytes of f it may
   read past its guard, [f, f + 18): f[0], f[12], f[13], f[16], f[17]. *)
Definition RP_FWD_CLASS : Z := 0x80d9c.
Definition RP_FWD_CLASS_FRAME : Z := 16.
Definition RP_FWD_CLASS_SPAN : Z := 18.

Definition rp_fwd_class_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_FWD_CLASS_FRAME <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (* Image B's UBSan premise: 0x80dac `beqz a0, 0x80e94` traps (unimp at 0x80e94) on f == NULL past the guard;
          image A's text lacks it. *)
       bv_unsigned a0 <> 0 /\
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
