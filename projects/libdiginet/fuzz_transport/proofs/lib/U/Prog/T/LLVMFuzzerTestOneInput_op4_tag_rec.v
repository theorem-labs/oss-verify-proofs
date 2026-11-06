(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the tagged arm from 0x143f0 (the three calls done) to the latch
   0x14574: the record of the command when want = 0 (fuzz_transport.c:1108-1118: g_cmd[serial] = {PENDING, key,
   display, len, bytes}, then g_q[at] = serial with g_cmd[g_q[at]].st = REPLACED, or the append g_q[g_nq++] = serial),
   g_ncmd++ (:1120), settle(0) (:1121) and the latch. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs LLVMFuzzerTestOneInput_op4_tag_lib.
Import ListNotations.
Open Scope Z_scope.

(* The machine at 0x143f0 (`bnez s7`): s0 = serial = g_ncmd B1, s1 = 1, s2 = &g_cmd[serial], s3 / s6 the cursor
   after the take (its address, the take's n), s4 = at as a 32-bit value, s5 = &g_cmd, s7 = want, s8 / s9 / s11 as at
   the loop head, s10 free; the world B5 (the one check_latest_submit left), sp+0x10 = the cursor's n before the
   take, sp+0x18 = (int)before, the struct at sp+0x60 = cmd_struct cbytes len display key. *)
Definition t4r_at (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops before : Z) (c3 : fuzz_in) (B1 : list byte) (display key : Z) (jhi : list byte)
    (at_ : Z) (B5 : list byte) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) (m : word -> option byte)
         (jio : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 (g_ncmd B1)) (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cmd + g_ncmd B1 * 40))
                 (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                 (Z_to_bv 64 (at_ mod 2 ^ 32)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cmd)) (Z_to_bv 64 (t4_n D c3))
                 (Z_to_bv 64 (t4_want B1 D c3 at_))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 s10 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x143f0) fc None m (seg_rom rsegs) /\
    llvm_mem data D regs0 m0 Sp lo B5 m
      (le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ le8 (Z_to_bv 64 (bv_swrap 32 before))) jio
      (t4_cs B1 D c3 display key ++ jhi).

(* 0x143f0 .. the latch. The premises are t4_split's (tag_lib.v) for this stretch, and the facts the arm's
   earlier stretches know. *)
Definition t4r_rec_stmt : Prop :=
  forall data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 B6 B8 F fc ms,
    0 <= ops < OPS_MAX -> llvm_cursor D c3 -> 0 <= display <= 1 -> 0 <= key < 2 ^ 32 ->
    0 <= g_ncmd B1 < CMDS_MAX -> length jhi = 8%nat -> (at_ = -1 \/ 0 <= at_ < CMDS_MAX) ->
    (if t4_want B1 D c3 at_ =? SPEC_OK
     then t4_rec B5 (g_ncmd B1) key display (t4_len D c3) (t4_cb B1 D c3) at_
     else Some B5) = Some B6 ->
    settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 = Some (B8, tt) ->
    t4r_at data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 F fc ms ->
    evt rsegs (llvm_latch data D regs0 m0 Sp lo ops (t4_c5 D c3) B8 F fc) ms.
