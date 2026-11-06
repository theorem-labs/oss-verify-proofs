(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushS21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1512c : bv 32 := 0x00050663.
Lemma F_1512c : fetch_word Plain.M.loaded_segments (0x15230 : word) = Some W_1512c.
Proof. vm_refl. Qed.
Lemma D_1512c : decode_any W_1512c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15130 : bv 32 := 0x00852503.
Lemma F_15130 : fetch_word Plain.M.loaded_segments (0x15234 : word) = Some W_15130.
Proof. vm_refl. Qed.
Lemma D_15130 : decode_any W_15130 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15134 : bv 32 := 0x00008067.
Lemma F_15134 : fetch_word Plain.M.loaded_segments (0x15238 : word) = Some W_15134.
Proof. vm_refl. Qed.
Lemma D_15134 : decode_any W_15134 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1516c : bv 32 := 0x00050663.
Lemma F_1516c : fetch_word Plain.M.loaded_segments (0x15270 : word) = Some W_1516c.
Proof. vm_refl. Qed.
Lemma D_1516c : decode_any W_1516c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15170 : bv 32 := 0x03853503.
Lemma F_15170 : fetch_word Plain.M.loaded_segments (0x15274 : word) = Some W_15170.
Proof. vm_refl. Qed.
Lemma D_15170 : decode_any W_15170 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15174 : bv 32 := 0x00008067.
Lemma F_15174 : fetch_word Plain.M.loaded_segments (0x15278 : word) = Some W_15174.
Proof. vm_refl. Qed.
Lemma D_15174 : decode_any W_15174 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151ac : bv 32 := 0x00050663.
Lemma F_151ac : fetch_word Plain.M.loaded_segments (0x152b0 : word) = Some W_151ac.
Proof. vm_refl. Qed.
Lemma D_151ac : decode_any W_151ac = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b0 : bv 32 := 0x03053503.
Lemma F_151b0 : fetch_word Plain.M.loaded_segments (0x152b4 : word) = Some W_151b0.
Proof. vm_refl. Qed.
Lemma D_151b0 : decode_any W_151b0 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b4 : bv 32 := 0x00008067.
Lemma F_151b4 : fetch_word Plain.M.loaded_segments (0x152b8 : word) = Some W_151b4.
Proof. vm_refl. Qed.
Lemma D_151b4 : decode_any W_151b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1522c : bv 32 := 0xfd010113.
Lemma F_1522c : fetch_word Plain.M.loaded_segments (0x15330 : word) = Some W_1522c.
Proof. vm_refl. Qed.
Lemma D_1522c : decode_any W_1522c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15230 : bv 32 := 0x02113423.
Lemma F_15230 : fetch_word Plain.M.loaded_segments (0x15334 : word) = Some W_15230.
Proof. vm_refl. Qed.
Lemma D_15230 : decode_any W_15230 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15234 : bv 32 := 0x02813023.
Lemma F_15234 : fetch_word Plain.M.loaded_segments (0x15338 : word) = Some W_15234.
Proof. vm_refl. Qed.
Lemma D_15234 : decode_any W_15234 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15238 : bv 32 := 0x00913c23.
Lemma F_15238 : fetch_word Plain.M.loaded_segments (0x1533c : word) = Some W_15238.
Proof. vm_refl. Qed.
Lemma D_15238 : decode_any W_15238 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1523c : bv 32 := 0x01213823.
Lemma F_1523c : fetch_word Plain.M.loaded_segments (0x15340 : word) = Some W_1523c.
Proof. vm_refl. Qed.
Lemma D_1523c : decode_any W_1523c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15240 : bv 32 := 0x06050063.
Lemma F_15240 : fetch_word Plain.M.loaded_segments (0x15344 : word) = Some W_15240.
Proof. vm_refl. Qed.
Lemma D_15240 : decode_any W_15240 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15244 : bv 32 := 0x00050493.
Lemma F_15244 : fetch_word Plain.M.loaded_segments (0x15348 : word) = Some W_15244.
Proof. vm_refl. Qed.
Lemma D_15244 : decode_any W_15244 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15248 : bv 32 := 0x00058913.
Lemma F_15248 : fetch_word Plain.M.loaded_segments (0x1534c : word) = Some W_15248.
Proof. vm_refl. Qed.
Lemma D_15248 : decode_any W_15248 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1524c : bv 32 := 0x00c10593.
Lemma F_1524c : fetch_word Plain.M.loaded_segments (0x15350 : word) = Some W_1524c.
Proof. vm_refl. Qed.
Lemma D_1524c : decode_any W_1524c = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15250 : bv 32 := 0x00810613.
Lemma F_15250 : fetch_word Plain.M.loaded_segments (0x15354 : word) = Some W_15250.
Proof. vm_refl. Qed.
Lemma D_15250 : decode_any W_15250 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15254 : bv 32 := 0x00410693.
Lemma F_15254 : fetch_word Plain.M.loaded_segments (0x15358 : word) = Some W_15254.
Proof. vm_refl. Qed.
Lemma D_15254 : decode_any W_15254 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15258 : bv 32 := 0xef8ff0ef.
Lemma F_15258 : fetch_word Plain.M.loaded_segments (0x1535c : word) = Some W_15258.
Proof. vm_refl. Qed.
Lemma D_15258 : decode_any W_15258 = Some (Jal 1 2094840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1525c : bv 32 := 0x00412503.
Lemma F_1525c : fetch_word Plain.M.loaded_segments (0x15360 : word) = Some W_1525c.
Proof. vm_refl. Qed.
Lemma D_1525c : decode_any W_1525c = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15260 : bv 32 := 0x02000593.
Lemma F_15260 : fetch_word Plain.M.loaded_segments (0x15364 : word) = Some W_15260.
Proof. vm_refl. Qed.
Lemma D_15260 : decode_any W_15260 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15264 : bv 32 := 0x12b50463.
Lemma F_15264 : fetch_word Plain.M.loaded_segments (0x15368 : word) = Some W_15264.
Proof. vm_refl. Qed.
Lemma D_15264 : decode_any W_15264 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1538c : bv 32 := 0x00000513.
Lemma F_1538c : fetch_word Plain.M.loaded_segments (0x15490 : word) = Some W_1538c.
Proof. vm_refl. Qed.
Lemma D_1538c : decode_any W_1538c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15390 : bv 32 := 0x02813083.
Lemma F_15390 : fetch_word Plain.M.loaded_segments (0x15494 : word) = Some W_15390.
Proof. vm_refl. Qed.
Lemma D_15390 : decode_any W_15390 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15394 : bv 32 := 0x02013403.
Lemma F_15394 : fetch_word Plain.M.loaded_segments (0x15498 : word) = Some W_15394.
Proof. vm_refl. Qed.
Lemma D_15394 : decode_any W_15394 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15398 : bv 32 := 0x01813483.
Lemma F_15398 : fetch_word Plain.M.loaded_segments (0x1549c : word) = Some W_15398.
Proof. vm_refl. Qed.
Lemma D_15398 : decode_any W_15398 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539c : bv 32 := 0x01013903.
Lemma F_1539c : fetch_word Plain.M.loaded_segments (0x154a0 : word) = Some W_1539c.
Proof. vm_refl. Qed.
Lemma D_1539c : decode_any W_1539c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a0 : bv 32 := 0x03010113.
Lemma F_153a0 : fetch_word Plain.M.loaded_segments (0x154a4 : word) = Some W_153a0.
Proof. vm_refl. Qed.
Lemma D_153a0 : decode_any W_153a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a4 : bv 32 := 0x00008067.
Lemma F_153a4 : fetch_word Plain.M.loaded_segments (0x154a8 : word) = Some W_153a4.
Proof. vm_refl. Qed.
Lemma D_153a4 : decode_any W_153a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a8 : bv 32 := 0x04050263.
Lemma F_153a8 : fetch_word Plain.M.loaded_segments (0x154ac : word) = Some W_153a8.
Proof. vm_refl. Qed.
Lemma D_153a8 : decode_any W_153a8 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ac : bv 32 := 0x00c52783.
Lemma F_153ac : fetch_word Plain.M.loaded_segments (0x154b0 : word) = Some W_153ac.
Proof. vm_refl. Qed.
Lemma D_153ac : decode_any W_153ac = Some (Load SZ4 true 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b0 : bv 32 := 0x01052703.
Lemma F_153b0 : fetch_word Plain.M.loaded_segments (0x154b4 : word) = Some W_153b0.
Proof. vm_refl. Qed.
Lemma D_153b0 : decode_any W_153b0 = Some (Load SZ4 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b4 : bv 32 := 0x06f75263.
Lemma F_153b4 : fetch_word Plain.M.loaded_segments (0x154b8 : word) = Some W_153b4.
Proof. vm_refl. Qed.
Lemma D_153b4 : decode_any W_153b4 = Some (Branch BC_GE 14 15 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b8 : bv 32 := 0x00050793.
Lemma F_153b8 : fetch_word Plain.M.loaded_segments (0x154bc : word) = Some W_153b8.
Proof. vm_refl. Qed.
Lemma D_153b8 : decode_any W_153b8 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153bc : bv 32 := 0x00000513.
Lemma F_153bc : fetch_word Plain.M.loaded_segments (0x154c0 : word) = Some W_153bc.
Proof. vm_refl. Qed.
Lemma D_153bc : decode_any W_153bc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c0 : bv 32 := 0x0007b803.
Lemma F_153c0 : fetch_word Plain.M.loaded_segments (0x154c4 : word) = Some W_153c0.
Proof. vm_refl. Qed.
Lemma D_153c0 : decode_any W_153c0 = Some (Load SZ8 true 16 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c4 : bv 32 := 0x00271893.
Lemma F_153c4 : fetch_word Plain.M.loaded_segments (0x154c8 : word) = Some W_153c4.
Proof. vm_refl. Qed.
Lemma D_153c4 : decode_any W_153c4 = Some (ShiftImm ALU_SLL 17 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c8 : bv 32 := 0x01180833.
Lemma F_153c8 : fetch_word Plain.M.loaded_segments (0x154cc : word) = Some W_153c8.
Proof. vm_refl. Qed.
Lemma D_153c8 : decode_any W_153c8 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153cc : bv 32 := 0xfff00893.
Lemma F_153cc : fetch_word Plain.M.loaded_segments (0x154d0 : word) = Some W_153cc.
Proof. vm_refl. Qed.
Lemma D_153cc : decode_any W_153cc = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d0 : bv 32 := 0x00170713.
Lemma F_153d0 : fetch_word Plain.M.loaded_segments (0x154d4 : word) = Some W_153d0.
Proof. vm_refl. Qed.
Lemma D_153d0 : decode_any W_153d0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d4 : bv 32 := 0x00d80023.
Lemma F_153d4 : fetch_word Plain.M.loaded_segments (0x154d8 : word) = Some W_153d4.
Proof. vm_refl. Qed.
Lemma D_153d4 : decode_any W_153d4 = Some (Store SZ1 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d8 : bv 32 := 0x00c800a3.
Lemma F_153d8 : fetch_word Plain.M.loaded_segments (0x154dc : word) = Some W_153d8.
Proof. vm_refl. Qed.
Lemma D_153d8 : decode_any W_153d8 = Some (Store SZ1 16 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153dc : bv 32 := 0x00b80123.
Lemma F_153dc : fetch_word Plain.M.loaded_segments (0x154e0 : word) = Some W_153dc.
Proof. vm_refl. Qed.
Lemma D_153dc : decode_any W_153dc = Some (Store SZ1 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e0 : bv 32 := 0x011801a3.
Lemma F_153e0 : fetch_word Plain.M.loaded_segments (0x154e4 : word) = Some W_153e0.
Proof. vm_refl. Qed.
Lemma D_153e0 : decode_any W_153e0 = Some (Store SZ1 16 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e4 : bv 32 := 0x00e7a823.
Lemma F_153e4 : fetch_word Plain.M.loaded_segments (0x154e8 : word) = Some W_153e4.
Proof. vm_refl. Qed.
Lemma D_153e4 : decode_any W_153e4 = Some (Store SZ4 15 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e8 : bv 32 := 0x00008067.
Lemma F_153e8 : fetch_word Plain.M.loaded_segments (0x154ec : word) = Some W_153e8.
Proof. vm_refl. Qed.
Lemma D_153e8 : decode_any W_153e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15418 : bv 32 := 0x0000b517.
Lemma F_15418 : fetch_word Plain.M.loaded_segments (0x1551c : word) = Some W_15418.
Proof. vm_refl. Qed.
Lemma D_15418 : decode_any W_15418 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1541c : bv 32 := 0x00453503.
Lemma F_1541c : fetch_word Plain.M.loaded_segments (0x15520 : word) = Some W_1541c.
Proof. vm_refl. Qed.
Lemma D_1541c : decode_any W_1541c = Some (Load SZ8 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15420 : bv 32 := 0x00052503.
Lemma F_15420 : fetch_word Plain.M.loaded_segments (0x15524 : word) = Some W_15420.
Proof. vm_refl. Qed.
Lemma D_15420 : decode_any W_15420 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15424 : bv 32 := 0x00500593.
Lemma F_15424 : fetch_word Plain.M.loaded_segments (0x15528 : word) = Some W_15424.
Proof. vm_refl. Qed.
Lemma D_15424 : decode_any W_15424 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15428 : bv 32 := 0x00a5ce63.
Lemma F_15428 : fetch_word Plain.M.loaded_segments (0x1552c : word) = Some W_15428.
Proof. vm_refl. Qed.
Lemma D_15428 : decode_any W_15428 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1542c : bv 32 := 0xffffb517.
Lemma F_1542c : fetch_word Plain.M.loaded_segments (0x15530 : word) = Some W_1542c.
Proof. vm_refl. Qed.
Lemma D_1542c : decode_any W_1542c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15430 : bv 32 := 0xffffb597.
Lemma F_15430 : fetch_word Plain.M.loaded_segments (0x15534 : word) = Some W_15430.
Proof. vm_refl. Qed.
Lemma D_15430 : decode_any W_15430 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15434 : bv 32 := 0x63950513.
Lemma F_15434 : fetch_word Plain.M.loaded_segments (0x15538 : word) = Some W_15434.
Proof. vm_refl. Qed.
Lemma D_15434 : decode_any W_15434 = Some (OpImm ALU_ADD 10 10 1593, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15438 : bv 32 := 0x58758593.
Lemma F_15438 : fetch_word Plain.M.loaded_segments (0x1553c : word) = Some W_15438.
Proof. vm_refl. Qed.
Lemma D_15438 : decode_any W_15438 = Some (OpImm ALU_ADD 11 11 1415, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1543c : bv 32 := 0x00100613.
Lemma F_1543c : fetch_word Plain.M.loaded_segments (0x15540 : word) = Some W_1543c.
Proof. vm_refl. Qed.
Lemma D_1543c : decode_any W_1543c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15440 : bv 32 := 0x871fe06f.
Lemma F_15440 : fetch_word Plain.M.loaded_segments (0x15544 : word) = Some W_15440.
Proof. vm_refl. Qed.
Lemma D_15440 : decode_any W_15440 = Some (Jal 0 2091120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1544c : bv 32 := 0xfe010113.
Lemma F_1544c : fetch_word Plain.M.loaded_segments (0x15550 : word) = Some W_1544c.
Proof. vm_refl. Qed.
Lemma D_1544c : decode_any W_1544c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15450 : bv 32 := 0x00113c23.
Lemma F_15450 : fetch_word Plain.M.loaded_segments (0x15554 : word) = Some W_15450.
Proof. vm_refl. Qed.
Lemma D_15450 : decode_any W_15450 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15454 : bv 32 := 0x00813823.
Lemma F_15454 : fetch_word Plain.M.loaded_segments (0x15558 : word) = Some W_15454.
Proof. vm_refl. Qed.
Lemma D_15454 : decode_any W_15454 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15458 : bv 32 := 0x00913423.
Lemma F_15458 : fetch_word Plain.M.loaded_segments (0x1555c : word) = Some W_15458.
Proof. vm_refl. Qed.
Lemma D_15458 : decode_any W_15458 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1545c : bv 32 := 0x06050463.
Lemma F_1545c : fetch_word Plain.M.loaded_segments (0x15560 : word) = Some W_1545c.
Proof. vm_refl. Qed.
Lemma D_1545c : decode_any W_1545c = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15460 : bv 32 := 0x00050413.
Lemma F_15460 : fetch_word Plain.M.loaded_segments (0x15564 : word) = Some W_15460.
Proof. vm_refl. Qed.
Lemma D_15460 : decode_any W_15460 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15464 : bv 32 := 0x00410613.
Lemma F_15464 : fetch_word Plain.M.loaded_segments (0x15568 : word) = Some W_15464.
Proof. vm_refl. Qed.
Lemma D_15464 : decode_any W_15464 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15468 : bv 32 := 0x00000593.
Lemma F_15468 : fetch_word Plain.M.loaded_segments (0x1556c : word) = Some W_15468.
Proof. vm_refl. Qed.
Lemma D_15468 : decode_any W_15468 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1546c : bv 32 := 0x0dc000ef.
Lemma F_1546c : fetch_word Plain.M.loaded_segments (0x15570 : word) = Some W_1546c.
Proof. vm_refl. Qed.
Lemma D_1546c : decode_any W_1546c = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15470 : bv 32 := 0x00412503.
Lemma F_15470 : fetch_word Plain.M.loaded_segments (0x15574 : word) = Some W_15470.
Proof. vm_refl. Qed.
Lemma D_15470 : decode_any W_15470 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15474 : bv 32 := 0x08050663.
Lemma F_15474 : fetch_word Plain.M.loaded_segments (0x15578 : word) = Some W_15474.
Proof. vm_refl. Qed.
Lemma D_15474 : decode_any W_15474 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15478 : bv 32 := 0x00100513.
Lemma F_15478 : fetch_word Plain.M.loaded_segments (0x1557c : word) = Some W_15478.
Proof. vm_refl. Qed.
Lemma D_15478 : decode_any W_15478 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1547c : bv 32 := 0x01800593.
Lemma F_1547c : fetch_word Plain.M.loaded_segments (0x15580 : word) = Some W_1547c.
Proof. vm_refl. Qed.
Lemma D_1547c : decode_any W_1547c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15480 : bv 32 := 0x314020ef.
Lemma F_15480 : fetch_word Plain.M.loaded_segments (0x15584 : word) = Some W_15480.
Proof. vm_refl. Qed.
Lemma D_15480 : decode_any W_15480 = Some (Jal 1 8980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15484 : bv 32 := 0x00050493.
Lemma F_15484 : fetch_word Plain.M.loaded_segments (0x15588 : word) = Some W_15484.
Proof. vm_refl. Qed.
Lemma D_15484 : decode_any W_15484 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15488 : bv 32 := 0x00c42503.
Lemma F_15488 : fetch_word Plain.M.loaded_segments (0x1558c : word) = Some W_15488.
Proof. vm_refl. Qed.
Lemma D_15488 : decode_any W_15488 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1548c : bv 32 := 0x0025159b.
Lemma F_1548c : fetch_word Plain.M.loaded_segments (0x15590 : word) = Some W_1548c.
Proof. vm_refl. Qed.
Lemma D_1548c : decode_any W_1548c = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15490 : bv 32 := 0x00100513.
Lemma F_15490 : fetch_word Plain.M.loaded_segments (0x15594 : word) = Some W_15490.
Proof. vm_refl. Qed.
Lemma D_15490 : decode_any W_15490 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15494 : bv 32 := 0x300020ef.
Lemma F_15494 : fetch_word Plain.M.loaded_segments (0x15598 : word) = Some W_15494.
Proof. vm_refl. Qed.
Lemma D_15494 : decode_any W_15494 = Some (Jal 1 8960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15498 : bv 32 := 0x00a4b023.
Lemma F_15498 : fetch_word Plain.M.loaded_segments (0x1559c : word) = Some W_15498.
Proof. vm_refl. Qed.
Lemma D_15498 : decode_any W_15498 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1549c : bv 32 := 0x01042603.
Lemma F_1549c : fetch_word Plain.M.loaded_segments (0x155a0 : word) = Some W_1549c.
Proof. vm_refl. Qed.
Lemma D_1549c : decode_any W_1549c = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154a0 : bv 32 := 0x00043583.
Lemma F_154a0 : fetch_word Plain.M.loaded_segments (0x155a4 : word) = Some W_154a0.
Proof. vm_refl. Qed.
Lemma D_154a0 : decode_any W_154a0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154a4 : bv 32 := 0x00261613.
Lemma F_154a4 : fetch_word Plain.M.loaded_segments (0x155a8 : word) = Some W_154a4.
Proof. vm_refl. Qed.
Lemma D_154a4 : decode_any W_154a4 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154a8 : bv 32 := 0x558090ef.
Lemma F_154a8 : fetch_word Plain.M.loaded_segments (0x155ac : word) = Some W_154a8.
Proof. vm_refl. Qed.
Lemma D_154a8 : decode_any W_154a8 = Some (Jal 1 38232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154ac : bv 32 := 0x00048513.
Lemma F_154ac : fetch_word Plain.M.loaded_segments (0x155b0 : word) = Some W_154ac.
Proof. vm_refl. Qed.
Lemma D_154ac : decode_any W_154ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154b0 : bv 32 := 0x01042583.
Lemma F_154b0 : fetch_word Plain.M.loaded_segments (0x155b4 : word) = Some W_154b0.
Proof. vm_refl. Qed.
Lemma D_154b0 : decode_any W_154b0 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154b4 : bv 32 := 0x00b4a823.
Lemma F_154b4 : fetch_word Plain.M.loaded_segments (0x155b8 : word) = Some W_154b4.
Proof. vm_refl. Qed.
Lemma D_154b4 : decode_any W_154b4 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154b8 : bv 32 := 0x00843583.
Lemma F_154b8 : fetch_word Plain.M.loaded_segments (0x155bc : word) = Some W_154b8.
Proof. vm_refl. Qed.
Lemma D_154b8 : decode_any W_154b8 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154bc : bv 32 := 0x00b4b423.
Lemma F_154bc : fetch_word Plain.M.loaded_segments (0x155c0 : word) = Some W_154bc.
Proof. vm_refl. Qed.
Lemma D_154bc : decode_any W_154bc = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c0 : bv 32 := 0x0740006f.
Lemma F_154c0 : fetch_word Plain.M.loaded_segments (0x155c4 : word) = Some W_154c0.
Proof. vm_refl. Qed.
Lemma D_154c0 : decode_any W_154c0 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15534 : bv 32 := 0x01813083.
Lemma F_15534 : fetch_word Plain.M.loaded_segments (0x15638 : word) = Some W_15534.
Proof. vm_refl. Qed.
Lemma D_15534 : decode_any W_15534 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15538 : bv 32 := 0x01013403.
Lemma F_15538 : fetch_word Plain.M.loaded_segments (0x1563c : word) = Some W_15538.
Proof. vm_refl. Qed.
Lemma D_15538 : decode_any W_15538 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1553c : bv 32 := 0x00813483.
Lemma F_1553c : fetch_word Plain.M.loaded_segments (0x15640 : word) = Some W_1553c.
Proof. vm_refl. Qed.
Lemma D_1553c : decode_any W_1553c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15540 : bv 32 := 0x02010113.
Lemma F_15540 : fetch_word Plain.M.loaded_segments (0x15644 : word) = Some W_15540.
Proof. vm_refl. Qed.
Lemma D_15540 : decode_any W_15540 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15544 : bv 32 := 0x00008067.
Lemma F_15544 : fetch_word Plain.M.loaded_segments (0x15648 : word) = Some W_15544.
Proof. vm_refl. Qed.
Lemma D_15544 : decode_any W_15544 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0x06070063.
Lemma F_158c8 : fetch_word Plain.M.loaded_segments (0x159cc : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Branch BC_EQ 14 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0x00072023.
Lemma F_158cc : fetch_word Plain.M.loaded_segments (0x159d0 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0x08050463.
Lemma F_158d0 : fetch_word Plain.M.loaded_segments (0x159d4 : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Branch BC_EQ 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0x00050893.
Lemma F_158d4 : fetch_word Plain.M.loaded_segments (0x159d8 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x01052783.
Lemma F_158d8 : fetch_word Plain.M.loaded_segments (0x159dc : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (Load SZ4 true 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158dc : bv 32 := 0x00100513.
Lemma F_158dc : fetch_word Plain.M.loaded_segments (0x159e0 : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e0 : bv 32 := 0x06f05a63.
Lemma F_158e0 : fetch_word Plain.M.loaded_segments (0x159e4 : word) = Some W_158e0.
Proof. vm_refl. Qed.
Lemma D_158e0 : decode_any W_158e0 = Some (Branch BC_GE 0 15 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e4 : bv 32 := 0x00000813.
Lemma F_158e4 : fetch_word Plain.M.loaded_segments (0x159e8 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e8 : bv 32 := 0x0008b883.
Lemma F_158e8 : fetch_word Plain.M.loaded_segments (0x159ec : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ec : bv 32 := 0x00188893.
Lemma F_158ec : fetch_word Plain.M.loaded_segments (0x159f0 : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f0 : bv 32 := 0x0140006f.
Lemma F_158f0 : fetch_word Plain.M.loaded_segments (0x159f4 : word) = Some W_158f0.
Proof. vm_refl. Qed.
Lemma D_158f0 : decode_any W_158f0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f4 : bv 32 := 0x00180813.
Lemma F_158f4 : fetch_word Plain.M.loaded_segments (0x159f8 : word) = Some W_158f4.
Proof. vm_refl. Qed.
Lemma D_158f4 : decode_any W_158f4 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f8 : bv 32 := 0xfff78793.
Lemma F_158f8 : fetch_word Plain.M.loaded_segments (0x159fc : word) = Some W_158f8.
Proof. vm_refl. Qed.
Lemma D_158f8 : decode_any W_158f8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158fc : bv 32 := 0x00488893.
Lemma F_158fc : fetch_word Plain.M.loaded_segments (0x15a00 : word) = Some W_158fc.
Proof. vm_refl. Qed.
Lemma D_158fc : decode_any W_158fc = Some (OpImm ALU_ADD 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15900 : bv 32 := 0x04078a63.
Lemma F_15900 : fetch_word Plain.M.loaded_segments (0x15a04 : word) = Some W_15900.
Proof. vm_refl. Qed.
Lemma D_15900 : decode_any W_15900 = Some (Branch BC_EQ 15 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15904 : bv 32 := 0x0018c283.
Lemma F_15904 : fetch_word Plain.M.loaded_segments (0x15a08 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (Load SZ1 false 5 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15908 : bv 32 := 0xfe5596e3.
Lemma F_15908 : fetch_word Plain.M.loaded_segments (0x15a0c : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (Branch BC_NE 11 5 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c : bv 32 := 0x0008c283.
Lemma F_1590c : fetch_word Plain.M.loaded_segments (0x15a10 : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Load SZ1 false 5 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0xfe5612e3.
Lemma F_15910 : fetch_word Plain.M.loaded_segments (0x15a14 : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Branch BC_NE 12 5 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0xfff8c283.
Lemma F_15914 : fetch_word Plain.M.loaded_segments (0x15a18 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Load SZ1 false 5 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0xfc569ee3.
Lemma F_15918 : fetch_word Plain.M.loaded_segments (0x15a1c : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Branch BC_NE 13 5 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0x00000513.
Lemma F_1591c : fetch_word Plain.M.loaded_segments (0x15a20 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0x01072023.
Lemma F_15920 : fetch_word Plain.M.loaded_segments (0x15a24 : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Store SZ4 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0x00008067.
Lemma F_15924 : fetch_word Plain.M.loaded_segments (0x15a28 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954 : bv 32 := 0x00008067.
Lemma F_15954 : fetch_word Plain.M.loaded_segments (0x15a58 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0x00050663.
Lemma F_1598c : fetch_word Plain.M.loaded_segments (0x15a90 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x01052503.
Lemma F_15990 : fetch_word Plain.M.loaded_segments (0x15a94 : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x00008067.
Lemma F_15994 : fetch_word Plain.M.loaded_segments (0x15a98 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
