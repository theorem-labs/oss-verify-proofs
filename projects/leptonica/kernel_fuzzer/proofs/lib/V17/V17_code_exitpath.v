(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushU17.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13500 : bv 32 := 0xffffe517.
Lemma F_13500 : fetch_word Ubsan.M.loaded_segments (0x13500 : word) = Some W_13500.
Proof. vm_refl. Qed.
Lemma D_13500 : decode_any W_13500 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13504 : bv 32 := 0x71050513.
Lemma F_13504 : fetch_word Ubsan.M.loaded_segments (0x13504 : word) = Some W_13504.
Proof. vm_refl. Qed.
Lemma D_13504 : decode_any W_13504 = Some (OpImm ALU_ADD 10 10 1808, 4%Z).
Proof. vm_refl. Qed.

Definition W_13508 : bv 32 := 0x0000d597.
Lemma F_13508 : fetch_word Ubsan.M.loaded_segments (0x13508 : word) = Some W_13508.
Proof. vm_refl. Qed.
Lemma D_13508 : decode_any W_13508 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1350c : bv 32 := 0x75058593.
Lemma F_1350c : fetch_word Ubsan.M.loaded_segments (0x1350c : word) = Some W_1350c.
Proof. vm_refl. Qed.
Lemma D_1350c : decode_any W_1350c = Some (OpImm ALU_ADD 11 11 1872, 4%Z).
Proof. vm_refl. Qed.

Definition W_13510 : bv 32 := 0x000000ef.
Lemma F_13510 : fetch_word Ubsan.M.loaded_segments (0x13510 : word) = Some W_13510.
Proof. vm_refl. Qed.
Lemma D_13510 : decode_any W_13510 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13514 : bv 32 := 0x0040006f.
Lemma F_13514 : fetch_word Ubsan.M.loaded_segments (0x13514 : word) = Some W_13514.
Proof. vm_refl. Qed.
Lemma D_13514 : decode_any W_13514 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13518 : bv 32 := 0x00813083.
Lemma F_13518 : fetch_word Ubsan.M.loaded_segments (0x13518 : word) = Some W_13518.
Proof. vm_refl. Qed.
Lemma D_13518 : decode_any W_13518 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351c : bv 32 := 0x00013403.
Lemma F_1351c : fetch_word Ubsan.M.loaded_segments (0x1351c : word) = Some W_1351c.
Proof. vm_refl. Qed.
Lemma D_1351c : decode_any W_1351c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13520 : bv 32 := 0x01010113.
Lemma F_13520 : fetch_word Ubsan.M.loaded_segments (0x13520 : word) = Some W_13520.
Proof. vm_refl. Qed.
Lemma D_13520 : decode_any W_13520 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13524 : bv 32 := 0x00008067.
Lemma F_13524 : fetch_word Ubsan.M.loaded_segments (0x13524 : word) = Some W_13524.
Proof. vm_refl. Qed.
Lemma D_13524 : decode_any W_13524 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13528 : bv 32 := 0xff010113.
Lemma F_13528 : fetch_word Ubsan.M.loaded_segments (0x13528 : word) = Some W_13528.
Proof. vm_refl. Qed.
Lemma D_13528 : decode_any W_13528 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1352c : bv 32 := 0x00113423.
Lemma F_1352c : fetch_word Ubsan.M.loaded_segments (0x1352c : word) = Some W_1352c.
Proof. vm_refl. Qed.
Lemma D_1352c : decode_any W_1352c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13530 : bv 32 := 0x00813023.
Lemma F_13530 : fetch_word Ubsan.M.loaded_segments (0x13530 : word) = Some W_13530.
Proof. vm_refl. Qed.
Lemma D_13530 : decode_any W_13530 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13534 : bv 32 := 0x01010413.
Lemma F_13534 : fetch_word Ubsan.M.loaded_segments (0x13534 : word) = Some W_13534.
Proof. vm_refl. Qed.
Lemma D_13534 : decode_any W_13534 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13538 : bv 32 := 0x0000d517.
Lemma F_13538 : fetch_word Ubsan.M.loaded_segments (0x13538 : word) = Some W_13538.
Proof. vm_refl. Qed.
Lemma D_13538 : decode_any W_13538 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1353c : bv 32 := 0x76050513.
Lemma F_1353c : fetch_word Ubsan.M.loaded_segments (0x1353c : word) = Some W_1353c.
Proof. vm_refl. Qed.
Lemma D_1353c : decode_any W_1353c = Some (OpImm ALU_ADD 10 10 1888, 4%Z).
Proof. vm_refl. Qed.

Definition W_13540 : bv 32 := 0x00054503.
Lemma F_13540 : fetch_word Ubsan.M.loaded_segments (0x13540 : word) = Some W_13540.
Proof. vm_refl. Qed.
Lemma D_13540 : decode_any W_13540 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13544 : bv 32 := 0x00157513.
Lemma F_13544 : fetch_word Ubsan.M.loaded_segments (0x13544 : word) = Some W_13544.
Proof. vm_refl. Qed.
Lemma D_13544 : decode_any W_13544 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13548 : bv 32 := 0x00050663.
Lemma F_13548 : fetch_word Ubsan.M.loaded_segments (0x13548 : word) = Some W_13548.
Proof. vm_refl. Qed.
Lemma D_13548 : decode_any W_13548 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1354c : bv 32 := 0x0040006f.
Lemma F_1354c : fetch_word Ubsan.M.loaded_segments (0x1354c : word) = Some W_1354c.
Proof. vm_refl. Qed.
Lemma D_1354c : decode_any W_1354c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13550 : bv 32 := 0x0580006f.
Lemma F_13550 : fetch_word Ubsan.M.loaded_segments (0x13550 : word) = Some W_13550.
Proof. vm_refl. Qed.
Lemma D_13550 : decode_any W_13550 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_13554 : bv 32 := 0x0000d517.
Lemma F_13554 : fetch_word Ubsan.M.loaded_segments (0x13554 : word) = Some W_13554.
Proof. vm_refl. Qed.
Lemma D_13554 : decode_any W_13554 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13558 : bv 32 := 0x74450593.
Lemma F_13558 : fetch_word Ubsan.M.loaded_segments (0x13558 : word) = Some W_13558.
Proof. vm_refl. Qed.
Lemma D_13558 : decode_any W_13558 = Some (OpImm ALU_ADD 11 10 1860, 4%Z).
Proof. vm_refl. Qed.

Definition W_1355c : bv 32 := 0x00100513.
Lemma F_1355c : fetch_word Ubsan.M.loaded_segments (0x1355c : word) = Some W_1355c.
Proof. vm_refl. Qed.
Lemma D_1355c : decode_any W_1355c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13560 : bv 32 := 0x00a58023.
Lemma F_13560 : fetch_word Ubsan.M.loaded_segments (0x13560 : word) = Some W_13560.
Proof. vm_refl. Qed.
Lemma D_13560 : decode_any W_13560 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13564 : bv 32 := 0x0000c517.
Lemma F_13564 : fetch_word Ubsan.M.loaded_segments (0x13564 : word) = Some W_13564.
Proof. vm_refl. Qed.
Lemma D_13564 : decode_any W_13564 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13568 : bv 32 := 0x44453503.
Lemma F_13568 : fetch_word Ubsan.M.loaded_segments (0x13568 : word) = Some W_13568.
Proof. vm_refl. Qed.
Lemma D_13568 : decode_any W_13568 = Some (Load SZ8 true 10 10 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356c : bv 32 := 0x00050e63.
Lemma F_1356c : fetch_word Ubsan.M.loaded_segments (0x1356c : word) = Some W_1356c.
Proof. vm_refl. Qed.
Lemma D_1356c : decode_any W_1356c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_13570 : bv 32 := 0x0040006f.
Lemma F_13570 : fetch_word Ubsan.M.loaded_segments (0x13570 : word) = Some W_13570.
Proof. vm_refl. Qed.
Lemma D_13570 : decode_any W_13570 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13574 : bv 32 := 0x0000d517.
Lemma F_13574 : fetch_word Ubsan.M.loaded_segments (0x13574 : word) = Some W_13574.
Proof. vm_refl. Qed.
Lemma D_13574 : decode_any W_13574 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13578 : bv 32 := 0x4a450513.
Lemma F_13578 : fetch_word Ubsan.M.loaded_segments (0x13578 : word) = Some W_13578.
Proof. vm_refl. Qed.
Lemma D_13578 : decode_any W_13578 = Some (OpImm ALU_ADD 10 10 1188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1357c : bv 32 := 0x00053503.
Lemma F_1357c : fetch_word Ubsan.M.loaded_segments (0x1357c : word) = Some W_1357c.
Proof. vm_refl. Qed.
Lemma D_1357c : decode_any W_1357c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13580 : bv 32 := 0x4ac030ef.
Lemma F_13580 : fetch_word Ubsan.M.loaded_segments (0x13580 : word) = Some W_13580.
Proof. vm_refl. Qed.
Lemma D_13580 : decode_any W_13580 = Some (Jal 1 13484, 4%Z).
Proof. vm_refl. Qed.

Definition W_13584 : bv 32 := 0x0040006f.
Lemma F_13584 : fetch_word Ubsan.M.loaded_segments (0x13584 : word) = Some W_13584.
Proof. vm_refl. Qed.
Lemma D_13584 : decode_any W_13584 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13588 : bv 32 := 0x0000c517.
Lemma F_13588 : fetch_word Ubsan.M.loaded_segments (0x13588 : word) = Some W_13588.
Proof. vm_refl. Qed.
Lemma D_13588 : decode_any W_13588 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1358c : bv 32 := 0x42853503.
Lemma F_1358c : fetch_word Ubsan.M.loaded_segments (0x1358c : word) = Some W_1358c.
Proof. vm_refl. Qed.
Lemma D_1358c : decode_any W_1358c = Some (Load SZ8 true 10 10 1064, 4%Z).
Proof. vm_refl. Qed.

Definition W_13590 : bv 32 := 0x00050c63.
Lemma F_13590 : fetch_word Ubsan.M.loaded_segments (0x13590 : word) = Some W_13590.
Proof. vm_refl. Qed.
Lemma D_13590 : decode_any W_13590 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13594 : bv 32 := 0x0040006f.
Lemma F_13594 : fetch_word Ubsan.M.loaded_segments (0x13594 : word) = Some W_13594.
Proof. vm_refl. Qed.
Lemma D_13594 : decode_any W_13594 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13598 : bv 32 := 0xffffe517.
Lemma F_13598 : fetch_word Ubsan.M.loaded_segments (0x13598 : word) = Some W_13598.
Proof. vm_refl. Qed.
Lemma D_13598 : decode_any W_13598 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_1359c : bv 32 := 0x67850513.
Lemma F_1359c : fetch_word Ubsan.M.loaded_segments (0x1359c : word) = Some W_1359c.
Proof. vm_refl. Qed.
Lemma D_1359c : decode_any W_1359c = Some (OpImm ALU_ADD 10 10 1656, 4%Z).
Proof. vm_refl. Qed.

Definition W_135a0 : bv 32 := 0x000000ef.
Lemma F_135a0 : fetch_word Ubsan.M.loaded_segments (0x135a0 : word) = Some W_135a0.
Proof. vm_refl. Qed.
Lemma D_135a0 : decode_any W_135a0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135a4 : bv 32 := 0x0040006f.
Lemma F_135a4 : fetch_word Ubsan.M.loaded_segments (0x135a4 : word) = Some W_135a4.
Proof. vm_refl. Qed.
Lemma D_135a4 : decode_any W_135a4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_135a8 : bv 32 := 0x00813083.
Lemma F_135a8 : fetch_word Ubsan.M.loaded_segments (0x135a8 : word) = Some W_135a8.
Proof. vm_refl. Qed.
Lemma D_135a8 : decode_any W_135a8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_135ac : bv 32 := 0x00013403.
Lemma F_135ac : fetch_word Ubsan.M.loaded_segments (0x135ac : word) = Some W_135ac.
Proof. vm_refl. Qed.
Lemma D_135ac : decode_any W_135ac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135b0 : bv 32 := 0x01010113.
Lemma F_135b0 : fetch_word Ubsan.M.loaded_segments (0x135b0 : word) = Some W_135b0.
Proof. vm_refl. Qed.
Lemma D_135b0 : decode_any W_135b0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_135b4 : bv 32 := 0x00008067.
Lemma F_135b4 : fetch_word Ubsan.M.loaded_segments (0x135b4 : word) = Some W_135b4.
Proof. vm_refl. Qed.
Lemma D_135b4 : decode_any W_135b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_139e0 : bv 32 := 0x0001d517.
Lemma F_139e0 : fetch_word Ubsan.M.loaded_segments (0x139e0 : word) = Some W_139e0.
Proof. vm_refl. Qed.
Lemma D_139e0 : decode_any W_139e0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_139e4 : bv 32 := 0x2c454503.
Lemma F_139e4 : fetch_word Ubsan.M.loaded_segments (0x139e4 : word) = Some W_139e4.
Proof. vm_refl. Qed.
Lemma D_139e4 : decode_any W_139e4 = Some (Load SZ1 false 10 10 708, 4%Z).
Proof. vm_refl. Qed.

Definition W_139e8 : bv 32 := 0x00051463.
Lemma F_139e8 : fetch_word Ubsan.M.loaded_segments (0x139e8 : word) = Some W_139e8.
Proof. vm_refl. Qed.
Lemma D_139e8 : decode_any W_139e8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_139ec : bv 32 := 0x00008067.
Lemma F_139ec : fetch_word Ubsan.M.loaded_segments (0x139ec : word) = Some W_139ec.
Proof. vm_refl. Qed.
Lemma D_139ec : decode_any W_139ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_139f0 : bv 32 := 0xff010113.
Lemma F_139f0 : fetch_word Ubsan.M.loaded_segments (0x139f0 : word) = Some W_139f0.
Proof. vm_refl. Qed.
Lemma D_139f0 : decode_any W_139f0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_139f4 : bv 32 := 0x00113423.
Lemma F_139f4 : fetch_word Ubsan.M.loaded_segments (0x139f4 : word) = Some W_139f4.
Proof. vm_refl. Qed.
Lemma D_139f4 : decode_any W_139f4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_139f8 : bv 32 := 0x0000c517.
Lemma F_139f8 : fetch_word Ubsan.M.loaded_segments (0x139f8 : word) = Some W_139f8.
Proof. vm_refl. Qed.
Lemma D_139f8 : decode_any W_139f8 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_139fc : bv 32 := 0xfd053503.
Lemma F_139fc : fetch_word Ubsan.M.loaded_segments (0x139fc : word) = Some W_139fc.
Proof. vm_refl. Qed.
Lemma D_139fc : decode_any W_139fc = Some (Load SZ8 true 10 10 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_13a00 : bv 32 := 0x00053503.
Lemma F_13a00 : fetch_word Ubsan.M.loaded_segments (0x13a00 : word) = Some W_13a00.
Proof. vm_refl. Qed.
Lemma D_13a00 : decode_any W_13a00 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13a04 : bv 32 := 0x19c050ef.
Lemma F_13a04 : fetch_word Ubsan.M.loaded_segments (0x13a04 : word) = Some W_13a04.
Proof. vm_refl. Qed.
Lemma D_13a04 : decode_any W_13a04 = Some (Jal 1 20892, 4%Z).
Proof. vm_refl. Qed.

Definition W_13a08 : bv 32 := 0x04d00513.
Lemma F_13a08 : fetch_word Ubsan.M.loaded_segments (0x13a08 : word) = Some W_13a08.
Proof. vm_refl. Qed.
Lemma D_13a08 : decode_any W_13a08 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13a0c : bv 32 := 0x6a90a0ef.
Lemma F_13a0c : fetch_word Ubsan.M.loaded_segments (0x13a0c : word) = Some W_13a0c.
Proof. vm_refl. Qed.
Lemma D_13a0c : decode_any W_13a0c = Some (Jal 1 44712, 4%Z).
Proof. vm_refl. Qed.

Definition W_16964 : bv 32 := 0xfd010113.
Lemma F_16964 : fetch_word Ubsan.M.loaded_segments (0x16964 : word) = Some W_16964.
Proof. vm_refl. Qed.
Lemma D_16964 : decode_any W_16964 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_16968 : bv 32 := 0x02113423.
Lemma F_16968 : fetch_word Ubsan.M.loaded_segments (0x16968 : word) = Some W_16968.
Proof. vm_refl. Qed.
Lemma D_16968 : decode_any W_16968 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1696c : bv 32 := 0x02813023.
Lemma F_1696c : fetch_word Ubsan.M.loaded_segments (0x1696c : word) = Some W_1696c.
Proof. vm_refl. Qed.
Lemma D_1696c : decode_any W_1696c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16970 : bv 32 := 0x00913c23.
Lemma F_16970 : fetch_word Ubsan.M.loaded_segments (0x16970 : word) = Some W_16970.
Proof. vm_refl. Qed.
Lemma D_16970 : decode_any W_16970 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16974 : bv 32 := 0x01213823.
Lemma F_16974 : fetch_word Ubsan.M.loaded_segments (0x16974 : word) = Some W_16974.
Proof. vm_refl. Qed.
Lemma D_16974 : decode_any W_16974 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16978 : bv 32 := 0x01313423.
Lemma F_16978 : fetch_word Ubsan.M.loaded_segments (0x16978 : word) = Some W_16978.
Proof. vm_refl. Qed.
Lemma D_16978 : decode_any W_16978 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1697c : bv 32 := 0x0003a517.
Lemma F_1697c : fetch_word Ubsan.M.loaded_segments (0x1697c : word) = Some W_1697c.
Proof. vm_refl. Qed.
Lemma D_1697c : decode_any W_1697c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16980 : bv 32 := 0x46450913.
Lemma F_16980 : fetch_word Ubsan.M.loaded_segments (0x16980 : word) = Some W_16980.
Proof. vm_refl. Qed.
Lemma D_16980 : decode_any W_16980 = Some (OpImm ALU_ADD 18 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_16984 : bv 32 := 0x00490413.
Lemma F_16984 : fetch_word Ubsan.M.loaded_segments (0x16984 : word) = Some W_16984.
Proof. vm_refl. Qed.
Lemma D_16984 : decode_any W_16984 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_16988 : bv 32 := 0x00040513.
Lemma F_16988 : fetch_word Ubsan.M.loaded_segments (0x16988 : word) = Some W_16988.
Proof. vm_refl. Qed.
Lemma D_16988 : decode_any W_16988 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1698c : bv 32 := 0x3f9070ef.
Lemma F_1698c : fetch_word Ubsan.M.loaded_segments (0x1698c : word) = Some W_1698c.
Proof. vm_refl. Qed.
Lemma D_1698c : decode_any W_1698c = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_16990 : bv 32 := 0x01093503.
Lemma F_16990 : fetch_word Ubsan.M.loaded_segments (0x16990 : word) = Some W_16990.
Proof. vm_refl. Qed.
Lemma D_16990 : decode_any W_16990 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16994 : bv 32 := 0x06050863.
Lemma F_16994 : fetch_word Ubsan.M.loaded_segments (0x16994 : word) = Some W_16994.
Proof. vm_refl. Qed.
Lemma D_16994 : decode_any W_16994 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_16998 : bv 32 := 0x00892583.
Lemma F_16998 : fetch_word Ubsan.M.loaded_segments (0x16998 : word) = Some W_16998.
Proof. vm_refl. Qed.
Lemma D_16998 : decode_any W_16998 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1699c : bv 32 := 0x0180006f.
Lemma F_1699c : fetch_word Ubsan.M.loaded_segments (0x1699c : word) = Some W_1699c.
Proof. vm_refl. Qed.
Lemma D_1699c : decode_any W_1699c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_169a0 : bv 32 := 0x00053503.
Lemma F_169a0 : fetch_word Ubsan.M.loaded_segments (0x169a0 : word) = Some W_169a0.
Proof. vm_refl. Qed.
Lemma D_169a0 : decode_any W_169a0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_169a4 : bv 32 := 0x02000593.
Lemma F_169a4 : fetch_word Ubsan.M.loaded_segments (0x169a4 : word) = Some W_169a4.
Proof. vm_refl. Qed.
Lemma D_169a4 : decode_any W_169a4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_169a8 : bv 32 := 0x00b92423.
Lemma F_169a8 : fetch_word Ubsan.M.loaded_segments (0x169a8 : word) = Some W_169a8.
Proof. vm_refl. Qed.
Lemma D_169a8 : decode_any W_169a8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_169ac : bv 32 := 0x00a93823.
Lemma F_169ac : fetch_word Ubsan.M.loaded_segments (0x169ac : word) = Some W_169ac.
Proof. vm_refl. Qed.
Lemma D_169ac : decode_any W_169ac = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_169b0 : bv 32 := 0x04050a63.
Lemma F_169b0 : fetch_word Ubsan.M.loaded_segments (0x169b0 : word) = Some W_169b0.
Proof. vm_refl. Qed.
Lemma D_169b0 : decode_any W_169b0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_169b4 : bv 32 := 0xfff5861b.
Lemma F_169b4 : fetch_word Ubsan.M.loaded_segments (0x169b4 : word) = Some W_169b4.
Proof. vm_refl. Qed.
Lemma D_169b4 : decode_any W_169b4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_169b8 : bv 32 := 0x00c92423.
Lemma F_169b8 : fetch_word Ubsan.M.loaded_segments (0x169b8 : word) = Some W_169b8.
Proof. vm_refl. Qed.
Lemma D_169b8 : decode_any W_169b8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_169bc : bv 32 := 0xfeb052e3.
Lemma F_169bc : fetch_word Ubsan.M.loaded_segments (0x169bc : word) = Some W_169bc.
Proof. vm_refl. Qed.
Lemma D_169bc : decode_any W_169bc = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_169c0 : bv 32 := 0x01093503.
Lemma F_169c0 : fetch_word Ubsan.M.loaded_segments (0x169c0 : word) = Some W_169c0.
Proof. vm_refl. Qed.
Lemma D_169c0 : decode_any W_169c0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_169c4 : bv 32 := 0x00361613.
Lemma F_169c4 : fetch_word Ubsan.M.loaded_segments (0x169c4 : word) = Some W_169c4.
Proof. vm_refl. Qed.
Lemma D_169c4 : decode_any W_169c4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_169c8 : bv 32 := 0x00c50533.
Lemma F_169c8 : fetch_word Ubsan.M.loaded_segments (0x169c8 : word) = Some W_169c8.
Proof. vm_refl. Qed.
Lemma D_169c8 : decode_any W_169c8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_169cc : bv 32 := 0x00853983.
Lemma F_169cc : fetch_word Ubsan.M.loaded_segments (0x169cc : word) = Some W_169cc.
Proof. vm_refl. Qed.
Lemma D_169cc : decode_any W_169cc = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_169d0 : bv 32 := 0x10853483.
Lemma F_169d0 : fetch_word Ubsan.M.loaded_segments (0x169d0 : word) = Some W_169d0.
Proof. vm_refl. Qed.
Lemma D_169d0 : decode_any W_169d0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_169d4 : bv 32 := 0x00040513.
Lemma F_169d4 : fetch_word Ubsan.M.loaded_segments (0x169d4 : word) = Some W_169d4.
Proof. vm_refl. Qed.
Lemma D_169d4 : decode_any W_169d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_169d8 : bv 32 := 0x635070ef.
Lemma F_169d8 : fetch_word Ubsan.M.loaded_segments (0x169d8 : word) = Some W_169d8.
Proof. vm_refl. Qed.
Lemma D_169d8 : decode_any W_169d8 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_169dc : bv 32 := 0x00048513.
Lemma F_169dc : fetch_word Ubsan.M.loaded_segments (0x169dc : word) = Some W_169dc.
Proof. vm_refl. Qed.
Lemma D_169dc : decode_any W_169dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_169e0 : bv 32 := 0x000980e7.
Lemma F_169e0 : fetch_word Ubsan.M.loaded_segments (0x169e0 : word) = Some W_169e0.
Proof. vm_refl. Qed.
Lemma D_169e0 : decode_any W_169e0 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_169e4 : bv 32 := 0x00040513.
Lemma F_169e4 : fetch_word Ubsan.M.loaded_segments (0x169e4 : word) = Some W_169e4.
Proof. vm_refl. Qed.
Lemma D_169e4 : decode_any W_169e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_169e8 : bv 32 := 0x39d070ef.
Lemma F_169e8 : fetch_word Ubsan.M.loaded_segments (0x169e8 : word) = Some W_169e8.
Proof. vm_refl. Qed.
Lemma D_169e8 : decode_any W_169e8 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_169ec : bv 32 := 0x00892503.
Lemma F_169ec : fetch_word Ubsan.M.loaded_segments (0x169ec : word) = Some W_169ec.
Proof. vm_refl. Qed.
Lemma D_169ec : decode_any W_169ec = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_169f0 : bv 32 := 0xfff5061b.
Lemma F_169f0 : fetch_word Ubsan.M.loaded_segments (0x169f0 : word) = Some W_169f0.
Proof. vm_refl. Qed.
Lemma D_169f0 : decode_any W_169f0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_169f4 : bv 32 := 0x00c92423.
Lemma F_169f4 : fetch_word Ubsan.M.loaded_segments (0x169f4 : word) = Some W_169f4.
Proof. vm_refl. Qed.
Lemma D_169f4 : decode_any W_169f4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_169f8 : bv 32 := 0xfca044e3.
Lemma F_169f8 : fetch_word Ubsan.M.loaded_segments (0x169f8 : word) = Some W_169f8.
Proof. vm_refl. Qed.
Lemma D_169f8 : decode_any W_169f8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_169fc : bv 32 := 0x01093503.
Lemma F_169fc : fetch_word Ubsan.M.loaded_segments (0x169fc : word) = Some W_169fc.
Proof. vm_refl. Qed.
Lemma D_169fc : decode_any W_169fc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a00 : bv 32 := 0xfa1ff06f.
Lemma F_16a00 : fetch_word Ubsan.M.loaded_segments (0x16a00 : word) = Some W_16a00.
Proof. vm_refl. Qed.
Lemma D_16a00 : decode_any W_16a00 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a04 : bv 32 := 0x00100513.
Lemma F_16a04 : fetch_word Ubsan.M.loaded_segments (0x16a04 : word) = Some W_16a04.
Proof. vm_refl. Qed.
Lemma D_16a04 : decode_any W_16a04 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a08 : bv 32 := 0x00a90023.
Lemma F_16a08 : fetch_word Ubsan.M.loaded_segments (0x16a08 : word) = Some W_16a08.
Proof. vm_refl. Qed.
Lemma D_16a08 : decode_any W_16a08 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a0c : bv 32 := 0x00040513.
Lemma F_16a0c : fetch_word Ubsan.M.loaded_segments (0x16a0c : word) = Some W_16a0c.
Proof. vm_refl. Qed.
Lemma D_16a0c : decode_any W_16a0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a10 : bv 32 := 0x02813083.
Lemma F_16a10 : fetch_word Ubsan.M.loaded_segments (0x16a10 : word) = Some W_16a10.
Proof. vm_refl. Qed.
Lemma D_16a10 : decode_any W_16a10 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a14 : bv 32 := 0x02013403.
Lemma F_16a14 : fetch_word Ubsan.M.loaded_segments (0x16a14 : word) = Some W_16a14.
Proof. vm_refl. Qed.
Lemma D_16a14 : decode_any W_16a14 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a18 : bv 32 := 0x01813483.
Lemma F_16a18 : fetch_word Ubsan.M.loaded_segments (0x16a18 : word) = Some W_16a18.
Proof. vm_refl. Qed.
Lemma D_16a18 : decode_any W_16a18 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a1c : bv 32 := 0x01013903.
Lemma F_16a1c : fetch_word Ubsan.M.loaded_segments (0x16a1c : word) = Some W_16a1c.
Proof. vm_refl. Qed.
Lemma D_16a1c : decode_any W_16a1c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a20 : bv 32 := 0x00813983.
Lemma F_16a20 : fetch_word Ubsan.M.loaded_segments (0x16a20 : word) = Some W_16a20.
Proof. vm_refl. Qed.
Lemma D_16a20 : decode_any W_16a20 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a24 : bv 32 := 0x03010113.
Lemma F_16a24 : fetch_word Ubsan.M.loaded_segments (0x16a24 : word) = Some W_16a24.
Proof. vm_refl. Qed.
Lemma D_16a24 : decode_any W_16a24 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a28 : bv 32 := 0x5e50706f.
Lemma F_16a28 : fetch_word Ubsan.M.loaded_segments (0x16a28 : word) = Some W_16a28.
Proof. vm_refl. Qed.
Lemma D_16a28 : decode_any W_16a28 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a2c : bv 32 := 0x00008067.
Lemma F_16a2c : fetch_word Ubsan.M.loaded_segments (0x16a2c : word) = Some W_16a2c.
Proof. vm_refl. Qed.
Lemma D_16a2c : decode_any W_16a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a30 : bv 32 := 0xfd010113.
Lemma F_16a30 : fetch_word Ubsan.M.loaded_segments (0x16a30 : word) = Some W_16a30.
Proof. vm_refl. Qed.
Lemma D_16a30 : decode_any W_16a30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a34 : bv 32 := 0x02113423.
Lemma F_16a34 : fetch_word Ubsan.M.loaded_segments (0x16a34 : word) = Some W_16a34.
Proof. vm_refl. Qed.
Lemma D_16a34 : decode_any W_16a34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a38 : bv 32 := 0x02813023.
Lemma F_16a38 : fetch_word Ubsan.M.loaded_segments (0x16a38 : word) = Some W_16a38.
Proof. vm_refl. Qed.
Lemma D_16a38 : decode_any W_16a38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a3c : bv 32 := 0x00913c23.
Lemma F_16a3c : fetch_word Ubsan.M.loaded_segments (0x16a3c : word) = Some W_16a3c.
Proof. vm_refl. Qed.
Lemma D_16a3c : decode_any W_16a3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a40 : bv 32 := 0x01213823.
Lemma F_16a40 : fetch_word Ubsan.M.loaded_segments (0x16a40 : word) = Some W_16a40.
Proof. vm_refl. Qed.
Lemma D_16a40 : decode_any W_16a40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a44 : bv 32 := 0x01313423.
Lemma F_16a44 : fetch_word Ubsan.M.loaded_segments (0x16a44 : word) = Some W_16a44.
Proof. vm_refl. Qed.
Lemma D_16a44 : decode_any W_16a44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a48 : bv 32 := 0x00050493.
Lemma F_16a48 : fetch_word Ubsan.M.loaded_segments (0x16a48 : word) = Some W_16a48.
Proof. vm_refl. Qed.
Lemma D_16a48 : decode_any W_16a48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a4c : bv 32 := 0x0003a517.
Lemma F_16a4c : fetch_word Ubsan.M.loaded_segments (0x16a4c : word) = Some W_16a4c.
Proof. vm_refl. Qed.
Lemma D_16a4c : decode_any W_16a4c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a50 : bv 32 := 0x39450993.
Lemma F_16a50 : fetch_word Ubsan.M.loaded_segments (0x16a50 : word) = Some W_16a50.
Proof. vm_refl. Qed.
Lemma D_16a50 : decode_any W_16a50 = Some (OpImm ALU_ADD 19 10 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a54 : bv 32 := 0x00498413.
Lemma F_16a54 : fetch_word Ubsan.M.loaded_segments (0x16a54 : word) = Some W_16a54.
Proof. vm_refl. Qed.
Lemma D_16a54 : decode_any W_16a54 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a58 : bv 32 := 0x00040513.
Lemma F_16a58 : fetch_word Ubsan.M.loaded_segments (0x16a58 : word) = Some W_16a58.
Proof. vm_refl. Qed.
Lemma D_16a58 : decode_any W_16a58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a5c : bv 32 := 0x329070ef.
Lemma F_16a5c : fetch_word Ubsan.M.loaded_segments (0x16a5c : word) = Some W_16a5c.
Proof. vm_refl. Qed.
Lemma D_16a5c : decode_any W_16a5c = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a60 : bv 32 := 0x0009c503.
Lemma F_16a60 : fetch_word Ubsan.M.loaded_segments (0x16a60 : word) = Some W_16a60.
Proof. vm_refl. Qed.
Lemma D_16a60 : decode_any W_16a60 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a64 : bv 32 := 0xfff00913.
Lemma F_16a64 : fetch_word Ubsan.M.loaded_segments (0x16a64 : word) = Some W_16a64.
Proof. vm_refl. Qed.
Lemma D_16a64 : decode_any W_16a64 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a68 : bv 32 := 0x06051263.
Lemma F_16a68 : fetch_word Ubsan.M.loaded_segments (0x16a68 : word) = Some W_16a68.
Proof. vm_refl. Qed.
Lemma D_16a68 : decode_any W_16a68 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a6c : bv 32 := 0x0109b503.
Lemma F_16a6c : fetch_word Ubsan.M.loaded_segments (0x16a6c : word) = Some W_16a6c.
Proof. vm_refl. Qed.
Lemma D_16a6c : decode_any W_16a6c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a70 : bv 32 := 0x00051663.
Lemma F_16a70 : fetch_word Ubsan.M.loaded_segments (0x16a70 : word) = Some W_16a70.
Proof. vm_refl. Qed.
Lemma D_16a70 : decode_any W_16a70 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a74 : bv 32 := 0x01898513.
Lemma F_16a74 : fetch_word Ubsan.M.loaded_segments (0x16a74 : word) = Some W_16a74.
Proof. vm_refl. Qed.
Lemma D_16a74 : decode_any W_16a74 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a78 : bv 32 := 0x00a9b823.
Lemma F_16a78 : fetch_word Ubsan.M.loaded_segments (0x16a78 : word) = Some W_16a78.
Proof. vm_refl. Qed.
Lemma D_16a78 : decode_any W_16a78 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a7c : bv 32 := 0x0089a583.
Lemma F_16a7c : fetch_word Ubsan.M.loaded_segments (0x16a7c : word) = Some W_16a7c.
Proof. vm_refl. Qed.
Lemma D_16a7c : decode_any W_16a7c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a80 : bv 32 := 0x02000613.
Lemma F_16a80 : fetch_word Ubsan.M.loaded_segments (0x16a80 : word) = Some W_16a80.
Proof. vm_refl. Qed.
Lemma D_16a80 : decode_any W_16a80 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a84 : bv 32 := 0x02c59263.
Lemma F_16a84 : fetch_word Ubsan.M.loaded_segments (0x16a84 : word) = Some W_16a84.
Proof. vm_refl. Qed.
Lemma D_16a84 : decode_any W_16a84 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a88 : bv 32 := 0x20800513.
Lemma F_16a88 : fetch_word Ubsan.M.loaded_segments (0x16a88 : word) = Some W_16a88.
Proof. vm_refl. Qed.
Lemma D_16a88 : decode_any W_16a88 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a8c : bv 32 := 0x00100593.
Lemma F_16a8c : fetch_word Ubsan.M.loaded_segments (0x16a8c : word) = Some W_16a8c.
Proof. vm_refl. Qed.
Lemma D_16a8c : decode_any W_16a8c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a90 : bv 32 := 0x3f4000ef.
Lemma F_16a90 : fetch_word Ubsan.M.loaded_segments (0x16a90 : word) = Some W_16a90.
Proof. vm_refl. Qed.
Lemma D_16a90 : decode_any W_16a90 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a94 : bv 32 := 0x02050c63.
Lemma F_16a94 : fetch_word Ubsan.M.loaded_segments (0x16a94 : word) = Some W_16a94.
Proof. vm_refl. Qed.
Lemma D_16a94 : decode_any W_16a94 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a98 : bv 32 := 0x00000593.
Lemma F_16a98 : fetch_word Ubsan.M.loaded_segments (0x16a98 : word) = Some W_16a98.
Proof. vm_refl. Qed.
Lemma D_16a98 : decode_any W_16a98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a9c : bv 32 := 0x0109b603.
Lemma F_16a9c : fetch_word Ubsan.M.loaded_segments (0x16a9c : word) = Some W_16a9c.
Proof. vm_refl. Qed.
Lemma D_16a9c : decode_any W_16a9c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16aa0 : bv 32 := 0x00c53023.
Lemma F_16aa0 : fetch_word Ubsan.M.loaded_segments (0x16aa0 : word) = Some W_16aa0.
Proof. vm_refl. Qed.
Lemma D_16aa0 : decode_any W_16aa0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16aa4 : bv 32 := 0x00a9b823.
Lemma F_16aa4 : fetch_word Ubsan.M.loaded_segments (0x16aa4 : word) = Some W_16aa4.
Proof. vm_refl. Qed.
Lemma D_16aa4 : decode_any W_16aa4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16aa8 : bv 32 := 0x00000913.
Lemma F_16aa8 : fetch_word Ubsan.M.loaded_segments (0x16aa8 : word) = Some W_16aa8.
Proof. vm_refl. Qed.
Lemma D_16aa8 : decode_any W_16aa8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16aac : bv 32 := 0x00359613.
Lemma F_16aac : fetch_word Ubsan.M.loaded_segments (0x16aac : word) = Some W_16aac.
Proof. vm_refl. Qed.
Lemma D_16aac : decode_any W_16aac = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ab0 : bv 32 := 0x00c50533.
Lemma F_16ab0 : fetch_word Ubsan.M.loaded_segments (0x16ab0 : word) = Some W_16ab0.
Proof. vm_refl. Qed.
Lemma D_16ab0 : decode_any W_16ab0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ab4 : bv 32 := 0x00000617.
Lemma F_16ab4 : fetch_word Ubsan.M.loaded_segments (0x16ab4 : word) = Some W_16ab4.
Proof. vm_refl. Qed.
Lemma D_16ab4 : decode_any W_16ab4 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ab8 : bv 32 := 0x00158593.
Lemma F_16ab8 : fetch_word Ubsan.M.loaded_segments (0x16ab8 : word) = Some W_16ab8.
Proof. vm_refl. Qed.
Lemma D_16ab8 : decode_any W_16ab8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16abc : bv 32 := 0x04060613.
Lemma F_16abc : fetch_word Ubsan.M.loaded_segments (0x16abc : word) = Some W_16abc.
Proof. vm_refl. Qed.
Lemma D_16abc : decode_any W_16abc = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ac0 : bv 32 := 0x00c53423.
Lemma F_16ac0 : fetch_word Ubsan.M.loaded_segments (0x16ac0 : word) = Some W_16ac0.
Proof. vm_refl. Qed.
Lemma D_16ac0 : decode_any W_16ac0 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ac4 : bv 32 := 0x10953423.
Lemma F_16ac4 : fetch_word Ubsan.M.loaded_segments (0x16ac4 : word) = Some W_16ac4.
Proof. vm_refl. Qed.
Lemma D_16ac4 : decode_any W_16ac4 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ac8 : bv 32 := 0x00b9a423.
Lemma F_16ac8 : fetch_word Ubsan.M.loaded_segments (0x16ac8 : word) = Some W_16ac8.
Proof. vm_refl. Qed.
Lemma D_16ac8 : decode_any W_16ac8 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16acc : bv 32 := 0x00040513.
Lemma F_16acc : fetch_word Ubsan.M.loaded_segments (0x16acc : word) = Some W_16acc.
Proof. vm_refl. Qed.
Lemma D_16acc : decode_any W_16acc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ad0 : bv 32 := 0x53d070ef.
Lemma F_16ad0 : fetch_word Ubsan.M.loaded_segments (0x16ad0 : word) = Some W_16ad0.
Proof. vm_refl. Qed.
Lemma D_16ad0 : decode_any W_16ad0 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ad4 : bv 32 := 0x00090513.
Lemma F_16ad4 : fetch_word Ubsan.M.loaded_segments (0x16ad4 : word) = Some W_16ad4.
Proof. vm_refl. Qed.
Lemma D_16ad4 : decode_any W_16ad4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ad8 : bv 32 := 0x02813083.
Lemma F_16ad8 : fetch_word Ubsan.M.loaded_segments (0x16ad8 : word) = Some W_16ad8.
Proof. vm_refl. Qed.
Lemma D_16ad8 : decode_any W_16ad8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16adc : bv 32 := 0x02013403.
Lemma F_16adc : fetch_word Ubsan.M.loaded_segments (0x16adc : word) = Some W_16adc.
Proof. vm_refl. Qed.
Lemma D_16adc : decode_any W_16adc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ae0 : bv 32 := 0x01813483.
Lemma F_16ae0 : fetch_word Ubsan.M.loaded_segments (0x16ae0 : word) = Some W_16ae0.
Proof. vm_refl. Qed.
Lemma D_16ae0 : decode_any W_16ae0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ae4 : bv 32 := 0x01013903.
Lemma F_16ae4 : fetch_word Ubsan.M.loaded_segments (0x16ae4 : word) = Some W_16ae4.
Proof. vm_refl. Qed.
Lemma D_16ae4 : decode_any W_16ae4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ae8 : bv 32 := 0x00813983.
Lemma F_16ae8 : fetch_word Ubsan.M.loaded_segments (0x16ae8 : word) = Some W_16ae8.
Proof. vm_refl. Qed.
Lemma D_16ae8 : decode_any W_16ae8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16aec : bv 32 := 0x03010113.
Lemma F_16aec : fetch_word Ubsan.M.loaded_segments (0x16aec : word) = Some W_16aec.
Proof. vm_refl. Qed.
Lemma D_16aec : decode_any W_16aec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16af0 : bv 32 := 0x00008067.
Lemma F_16af0 : fetch_word Ubsan.M.loaded_segments (0x16af0 : word) = Some W_16af0.
Proof. vm_refl. Qed.
Lemma D_16af0 : decode_any W_16af0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16af4 : bv 32 := 0x00050067.
Lemma F_16af4 : fetch_word Ubsan.M.loaded_segments (0x16af4 : word) = Some W_16af4.
Proof. vm_refl. Qed.
Lemma D_16af4 : decode_any W_16af4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16af8 : bv 32 := 0x00008067.
Lemma F_16af8 : fetch_word Ubsan.M.loaded_segments (0x16af8 : word) = Some W_16af8.
Proof. vm_refl. Qed.
Lemma D_16af8 : decode_any W_16af8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16afc : bv 32 := 0xfe010113.
Lemma F_16afc : fetch_word Ubsan.M.loaded_segments (0x16afc : word) = Some W_16afc.
Proof. vm_refl. Qed.
Lemma D_16afc : decode_any W_16afc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b00 : bv 32 := 0x00113c23.
Lemma F_16b00 : fetch_word Ubsan.M.loaded_segments (0x16b00 : word) = Some W_16b00.
Proof. vm_refl. Qed.
Lemma D_16b00 : decode_any W_16b00 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b04 : bv 32 := 0x00813823.
Lemma F_16b04 : fetch_word Ubsan.M.loaded_segments (0x16b04 : word) = Some W_16b04.
Proof. vm_refl. Qed.
Lemma D_16b04 : decode_any W_16b04 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b08 : bv 32 := 0x00913423.
Lemma F_16b08 : fetch_word Ubsan.M.loaded_segments (0x16b08 : word) = Some W_16b08.
Proof. vm_refl. Qed.
Lemma D_16b08 : decode_any W_16b08 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b0c : bv 32 := 0x00009517.
Lemma F_16b0c : fetch_word Ubsan.M.loaded_segments (0x16b0c : word) = Some W_16b0c.
Proof. vm_refl. Qed.
Lemma D_16b0c : decode_any W_16b0c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b10 : bv 32 := 0x00009597.
Lemma F_16b10 : fetch_word Ubsan.M.loaded_segments (0x16b10 : word) = Some W_16b10.
Proof. vm_refl. Qed.
Lemma D_16b10 : decode_any W_16b10 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b14 : bv 32 := 0xefc53503.
Lemma F_16b14 : fetch_word Ubsan.M.loaded_segments (0x16b14 : word) = Some W_16b14.
Proof. vm_refl. Qed.
Lemma D_16b14 : decode_any W_16b14 = Some (Load SZ8 true 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b18 : bv 32 := 0xf005b403.
Lemma F_16b18 : fetch_word Ubsan.M.loaded_segments (0x16b18 : word) = Some W_16b18.
Proof. vm_refl. Qed.
Lemma D_16b18 : decode_any W_16b18 = Some (Load SZ8 true 8 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b1c : bv 32 := 0x00a47c63.
Lemma F_16b1c : fetch_word Ubsan.M.loaded_segments (0x16b1c : word) = Some W_16b1c.
Proof. vm_refl. Qed.
Lemma D_16b1c : decode_any W_16b1c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b20 : bv 32 := 0xff853583.
Lemma F_16b20 : fetch_word Ubsan.M.loaded_segments (0x16b20 : word) = Some W_16b20.
Proof. vm_refl. Qed.
Lemma D_16b20 : decode_any W_16b20 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b24 : bv 32 := 0xff850493.
Lemma F_16b24 : fetch_word Ubsan.M.loaded_segments (0x16b24 : word) = Some W_16b24.
Proof. vm_refl. Qed.
Lemma D_16b24 : decode_any W_16b24 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b28 : bv 32 := 0x000580e7.
Lemma F_16b28 : fetch_word Ubsan.M.loaded_segments (0x16b28 : word) = Some W_16b28.
Proof. vm_refl. Qed.
Lemma D_16b28 : decode_any W_16b28 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b2c : bv 32 := 0x00048513.
Lemma F_16b2c : fetch_word Ubsan.M.loaded_segments (0x16b2c : word) = Some W_16b2c.
Proof. vm_refl. Qed.
Lemma D_16b2c : decode_any W_16b2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b30 : bv 32 := 0xfe9468e3.
Lemma F_16b30 : fetch_word Ubsan.M.loaded_segments (0x16b30 : word) = Some W_16b30.
Proof. vm_refl. Qed.
Lemma D_16b30 : decode_any W_16b30 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b34 : bv 32 := 0x01813083.
Lemma F_16b34 : fetch_word Ubsan.M.loaded_segments (0x16b34 : word) = Some W_16b34.
Proof. vm_refl. Qed.
Lemma D_16b34 : decode_any W_16b34 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b38 : bv 32 := 0x01013403.
Lemma F_16b38 : fetch_word Ubsan.M.loaded_segments (0x16b38 : word) = Some W_16b38.
Proof. vm_refl. Qed.
Lemma D_16b38 : decode_any W_16b38 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b3c : bv 32 := 0x00813483.
Lemma F_16b3c : fetch_word Ubsan.M.loaded_segments (0x16b3c : word) = Some W_16b3c.
Proof. vm_refl. Qed.
Lemma D_16b3c : decode_any W_16b3c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b40 : bv 32 := 0x02010113.
Lemma F_16b40 : fetch_word Ubsan.M.loaded_segments (0x16b40 : word) = Some W_16b40.
Proof. vm_refl. Qed.
Lemma D_16b40 : decode_any W_16b40 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b44 : bv 32 := 0xfb5ff06f.
Lemma F_16b44 : fetch_word Ubsan.M.loaded_segments (0x16b44 : word) = Some W_16b44.
Proof. vm_refl. Qed.
Lemma D_16b44 : decode_any W_16b44 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b48 : bv 32 := 0xff010113.
Lemma F_16b48 : fetch_word Ubsan.M.loaded_segments (0x16b48 : word) = Some W_16b48.
Proof. vm_refl. Qed.
Lemma D_16b48 : decode_any W_16b48 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4c : bv 32 := 0x00113423.
Lemma F_16b4c : fetch_word Ubsan.M.loaded_segments (0x16b4c : word) = Some W_16b4c.
Proof. vm_refl. Qed.
Lemma D_16b4c : decode_any W_16b4c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b50 : bv 32 := 0x00813023.
Lemma F_16b50 : fetch_word Ubsan.M.loaded_segments (0x16b50 : word) = Some W_16b50.
Proof. vm_refl. Qed.
Lemma D_16b50 : decode_any W_16b50 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b54 : bv 32 := 0x00000593.
Lemma F_16b54 : fetch_word Ubsan.M.loaded_segments (0x16b54 : word) = Some W_16b54.
Proof. vm_refl. Qed.
Lemma D_16b54 : decode_any W_16b54 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b58 : bv 32 := 0x00020613.
Lemma F_16b58 : fetch_word Ubsan.M.loaded_segments (0x16b58 : word) = Some W_16b58.
Proof. vm_refl. Qed.
Lemma D_16b58 : decode_any W_16b58 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b5c : bv 32 := 0xf5862603.
Lemma F_16b5c : fetch_word Ubsan.M.loaded_segments (0x16b5c : word) = Some W_16b5c.
Proof. vm_refl. Qed.
Lemma D_16b5c : decode_any W_16b5c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b60 : bv 32 := 0x0003a697.
Lemma F_16b60 : fetch_word Ubsan.M.loaded_segments (0x16b60 : word) = Some W_16b60.
Proof. vm_refl. Qed.
Lemma D_16b60 : decode_any W_16b60 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b64 : bv 32 := 0x4a068693.
Lemma F_16b64 : fetch_word Ubsan.M.loaded_segments (0x16b64 : word) = Some W_16b64.
Proof. vm_refl. Qed.
Lemma D_16b64 : decode_any W_16b64 = Some (OpImm ALU_ADD 13 13 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b68 : bv 32 := 0x1606a72f.
Lemma F_16b68 : fetch_word Ubsan.M.loaded_segments (0x16b68 : word) = Some W_16b68.
Proof. vm_refl. Qed.
Lemma D_16b68 : decode_any W_16b68 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b6c : bv 32 := 0x00b71663.
Lemma F_16b6c : fetch_word Ubsan.M.loaded_segments (0x16b6c : word) = Some W_16b6c.
Proof. vm_refl. Qed.
Lemma D_16b6c : decode_any W_16b6c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b70 : bv 32 := 0x1ec6a7af.
Lemma F_16b70 : fetch_word Ubsan.M.loaded_segments (0x16b70 : word) = Some W_16b70.
Proof. vm_refl. Qed.
Lemma D_16b70 : decode_any W_16b70 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b74 : bv 32 := 0xfe079ae3.
Lemma F_16b74 : fetch_word Ubsan.M.loaded_segments (0x16b74 : word) = Some W_16b74.
Proof. vm_refl. Qed.
Lemma D_16b74 : decode_any W_16b74 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b78 : bv 32 := 0x0007059b.
Lemma F_16b78 : fetch_word Ubsan.M.loaded_segments (0x16b78 : word) = Some W_16b78.
Proof. vm_refl. Qed.
Lemma D_16b78 : decode_any W_16b78 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b7c : bv 32 := 0x02c58263.
Lemma F_16b7c : fetch_word Ubsan.M.loaded_segments (0x16b7c : word) = Some W_16b7c.
Proof. vm_refl. Qed.
Lemma D_16b7c : decode_any W_16b7c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b80 : bv 32 := 0x02058263.
Lemma F_16b80 : fetch_word Ubsan.M.loaded_segments (0x16b80 : word) = Some W_16b80.
Proof. vm_refl. Qed.
Lemma D_16b80 : decode_any W_16b80 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b84 : bv 32 := 0x04900893.
Lemma F_16b84 : fetch_word Ubsan.M.loaded_segments (0x16b84 : word) = Some W_16b84.
Proof. vm_refl. Qed.
Lemma D_16b84 : decode_any W_16b84 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b88 : bv 32 := 0x00000593.
Lemma F_16b88 : fetch_word Ubsan.M.loaded_segments (0x16b88 : word) = Some W_16b88.
Proof. vm_refl. Qed.
Lemma D_16b88 : decode_any W_16b88 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b8c : bv 32 := 0x00000613.
Lemma F_16b8c : fetch_word Ubsan.M.loaded_segments (0x16b8c : word) = Some W_16b8c.
Proof. vm_refl. Qed.
Lemma D_16b8c : decode_any W_16b8c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b90 : bv 32 := 0x00000693.
Lemma F_16b90 : fetch_word Ubsan.M.loaded_segments (0x16b90 : word) = Some W_16b90.
Proof. vm_refl. Qed.
Lemma D_16b90 : decode_any W_16b90 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b94 : bv 32 := 0x00000513.
Lemma F_16b94 : fetch_word Ubsan.M.loaded_segments (0x16b94 : word) = Some W_16b94.
Proof. vm_refl. Qed.
Lemma D_16b94 : decode_any W_16b94 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b98 : bv 32 := 0x00000073.
Lemma F_16b98 : fetch_word Ubsan.M.loaded_segments (0x16b98 : word) = Some W_16b98.
Proof. vm_refl. Qed.
Lemma E_16b98 : is_ecall W_16b98 = true.
Proof. vm_refl. Qed.

Definition W_16b9c : bv 32 := 0xff9ff06f.
Lemma F_16b9c : fetch_word Ubsan.M.loaded_segments (0x16b9c : word) = Some W_16b9c.
Proof. vm_refl. Qed.
Lemma D_16b9c : decode_any W_16b9c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ba0 : bv 32 := 0x00000023.
Lemma F_16ba0 : fetch_word Ubsan.M.loaded_segments (0x16ba0 : word) = Some W_16ba0.
Proof. vm_refl. Qed.
Lemma D_16ba0 : decode_any W_16ba0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ba4 : bv 32 := 0x00050413.
Lemma F_16ba4 : fetch_word Ubsan.M.loaded_segments (0x16ba4 : word) = Some W_16ba4.
Proof. vm_refl. Qed.
Lemma D_16ba4 : decode_any W_16ba4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ba8 : bv 32 := 0xdbdff0ef.
Lemma F_16ba8 : fetch_word Ubsan.M.loaded_segments (0x16ba8 : word) = Some W_16ba8.
Proof. vm_refl. Qed.
Lemma D_16ba8 : decode_any W_16ba8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_16bac : bv 32 := 0xf51ff0ef.
Lemma F_16bac : fetch_word Ubsan.M.loaded_segments (0x16bac : word) = Some W_16bac.
Proof. vm_refl. Qed.
Lemma D_16bac : decode_any W_16bac = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_16bb0 : bv 32 := 0x160020ef.
Lemma F_16bb0 : fetch_word Ubsan.M.loaded_segments (0x16bb0 : word) = Some W_16bb0.
Proof. vm_refl. Qed.
Lemma D_16bb0 : decode_any W_16bb0 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_16bb4 : bv 32 := 0x00040513.
Lemma F_16bb4 : fetch_word Ubsan.M.loaded_segments (0x16bb4 : word) = Some W_16bb4.
Proof. vm_refl. Qed.
Lemma D_16bb4 : decode_any W_16bb4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16bb8 : bv 32 := 0xd91ff0ef.
Lemma F_16bb8 : fetch_word Ubsan.M.loaded_segments (0x16bb8 : word) = Some W_16bb8.
Proof. vm_refl. Qed.
Lemma D_16bb8 : decode_any W_16bb8 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e584 : bv 32 := 0x00033597.
Lemma F_1e584 : fetch_word Ubsan.M.loaded_segments (0x1e584 : word) = Some W_1e584.
Proof. vm_refl. Qed.
Lemma D_1e584 : decode_any W_1e584 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e588 : bv 32 := 0xaa758683.
Lemma F_1e588 : fetch_word Ubsan.M.loaded_segments (0x1e588 : word) = Some W_1e588.
Proof. vm_refl. Qed.
Lemma D_1e588 : decode_any W_1e588 = Some (Load SZ1 true 13 11 2727, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e58c : bv 32 := 0x1e068863.
Lemma F_1e58c : fetch_word Ubsan.M.loaded_segments (0x1e58c : word) = Some W_1e58c.
Proof. vm_refl. Qed.
Lemma D_1e58c : decode_any W_1e58c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e77c : bv 32 := 0x00008067.
Lemma F_1e77c : fetch_word Ubsan.M.loaded_segments (0x1e77c : word) = Some W_1e77c.
Proof. vm_refl. Qed.
Lemma D_1e77c : decode_any W_1e77c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e80c : bv 32 := 0x00052583.
Lemma F_1e80c : fetch_word Ubsan.M.loaded_segments (0x1e80c : word) = Some W_1e80c.
Proof. vm_refl. Qed.
Lemma D_1e80c : decode_any W_1e80c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e810 : bv 32 := 0x0005c463.
Lemma F_1e810 : fetch_word Ubsan.M.loaded_segments (0x1e810 : word) = Some W_1e810.
Proof. vm_refl. Qed.
Lemma D_1e810 : decode_any W_1e810 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e814 : bv 32 := 0x00008067.
Lemma F_1e814 : fetch_word Ubsan.M.loaded_segments (0x1e814 : word) = Some W_1e814.
Proof. vm_refl. Qed.
Lemma D_1e814 : decode_any W_1e814 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
