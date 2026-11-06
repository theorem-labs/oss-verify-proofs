(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_r5bce4_5bd7c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5d55c : bv 32 := 0x000ff517.
Lemma F_5d55c : fetch_word Asan.M.loaded_segments (0x5d5ac : word) = Some W_5d55c.
Proof. vm_refl. Qed.
Lemma D_5d55c : decode_any W_5d55c = Some (Auipc 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d560 : bv 32 := 0xe8c53503.
Lemma F_5d560 : fetch_word Asan.M.loaded_segments (0x5d5b0 : word) = Some W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : decode_any W_5d560 = Some (Load SZ8 true 10 10 3724, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d564 : bv 32 := 0x06a76463.
Lemma F_5d564 : fetch_word Asan.M.loaded_segments (0x5d5b4 : word) = Some W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : decode_any W_5d564 = Some (Branch BC_LTU 14 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d568 : bv 32 := 0x00100593.
Lemma F_5d568 : fetch_word Asan.M.loaded_segments (0x5d5b8 : word) = Some W_5d568.
Proof. vm_refl. Qed.
Lemma D_5d568 : decode_any W_5d568 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d56c : bv 32 := 0x02559593.
Lemma F_5d56c : fetch_word Asan.M.loaded_segments (0x5d5bc : word) = Some W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : decode_any W_5d56c = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d570 : bv 32 := 0x00b50533.
Lemma F_5d570 : fetch_word Asan.M.loaded_segments (0x5d5c0 : word) = Some W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : decode_any W_5d570 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d574 : bv 32 := 0x04a77c63.
Lemma F_5d574 : fetch_word Asan.M.loaded_segments (0x5d5c4 : word) = Some W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : decode_any W_5d574 = Some (Branch BC_GEU 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d578 : bv 32 := 0x000f9517.
Lemma F_5d578 : fetch_word Asan.M.loaded_segments (0x5d5c8 : word) = Some W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : decode_any W_5d578 = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d57c : bv 32 := 0x7c853583.
Lemma F_5d57c : fetch_word Asan.M.loaded_segments (0x5d5cc : word) = Some W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : decode_any W_5d57c = Some (Load SZ8 true 11 10 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d580 : bv 32 := 0x0305a683.
Lemma F_5d580 : fetch_word Asan.M.loaded_segments (0x5d5d0 : word) = Some W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : decode_any W_5d580 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d584 : bv 32 := 0x04d05463.
Lemma F_5d584 : fetch_word Asan.M.loaded_segments (0x5d5d4 : word) = Some W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : decode_any W_5d584 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d588 : bv 32 := 0x00275503.
Lemma F_5d588 : fetch_word Asan.M.loaded_segments (0x5d5d8 : word) = Some W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : decode_any W_5d588 = Some (Load SZ2 false 10 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d58c : bv 32 := 0x00476603.
Lemma F_5d58c : fetch_word Asan.M.loaded_segments (0x5d5dc : word) = Some W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : decode_any W_5d58c = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d590 : bv 32 := 0x02051513.
Lemma F_5d590 : fetch_word Asan.M.loaded_segments (0x5d5e0 : word) = Some W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : decode_any W_5d590 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d594 : bv 32 := 0x00c56633.
Lemma F_5d594 : fetch_word Asan.M.loaded_segments (0x5d5e4 : word) = Some W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : decode_any W_5d594 = Some (Op ALU_OR 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d598 : bv 32 := 0x00800513.
Lemma F_5d598 : fetch_word Asan.M.loaded_segments (0x5d5e8 : word) = Some W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : decode_any W_5d598 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d59c : bv 32 := 0x02a66863.
Lemma F_5d59c : fetch_word Asan.M.loaded_segments (0x5d5ec : word) = Some W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : decode_any W_5d59c = Some (Branch BC_LTU 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a0 : bv 32 := 0xff860613.
Lemma F_5d5a0 : fetch_word Asan.M.loaded_segments (0x5d5f0 : word) = Some W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : decode_any W_5d5a0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a4 : bv 32 := 0x00070913.
Lemma F_5d5a4 : fetch_word Asan.M.loaded_segments (0x5d5f4 : word) = Some W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : decode_any W_5d5a4 = Some (OpImm ALU_ADD 18 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a8 : bv 32 := 0x01870513.
Lemma F_5d5a8 : fetch_word Asan.M.loaded_segments (0x5d5f8 : word) = Some W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : decode_any W_5d5a8 = Some (OpImm ALU_ADD 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5ac : bv 32 := 0x00d66463.
Lemma F_5d5ac : fetch_word Asan.M.loaded_segments (0x5d5fc : word) = Some W_5d5ac.
Proof. vm_refl. Qed.
Lemma D_5d5ac : decode_any W_5d5ac = Some (Branch BC_LTU 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b0 : bv 32 := 0x00068613.
Lemma F_5d5b0 : fetch_word Asan.M.loaded_segments (0x5d600 : word) = Some W_5d5b0.
Proof. vm_refl. Qed.
Lemma D_5d5b0 : decode_any W_5d5b0 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b4 : bv 32 := 0x000f9697.
Lemma F_5d5b4 : fetch_word Asan.M.loaded_segments (0x5d604 : word) = Some W_5d5b4.
Proof. vm_refl. Qed.
Lemma D_5d5b4 : decode_any W_5d5b4 = Some (Auipc 13 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b8 : bv 32 := 0x7b46b683.
Lemma F_5d5b8 : fetch_word Asan.M.loaded_segments (0x5d608 : word) = Some W_5d5b8.
Proof. vm_refl. Qed.
Lemma D_5d5b8 : decode_any W_5d5b8 = Some (Load SZ8 true 13 13 1972, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5bc : bv 32 := 0x0006b683.
Lemma F_5d5bc : fetch_word Asan.M.loaded_segments (0x5d60c : word) = Some W_5d5bc.
Proof. vm_refl. Qed.
Lemma D_5d5bc : decode_any W_5d5bc = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c0 : bv 32 := 0x0385a583.
Lemma F_5d5c0 : fetch_word Asan.M.loaded_segments (0x5d610 : word) = Some W_5d5c0.
Proof. vm_refl. Qed.
Lemma D_5d5c0 : decode_any W_5d5c0 = Some (Load SZ4 true 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c4 : bv 32 := 0x000680e7.
Lemma F_5d5c4 : fetch_word Asan.M.loaded_segments (0x5d614 : word) = Some W_5d5c4.
Proof. vm_refl. Qed.
Lemma D_5d5c4 : decode_any W_5d5c4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c8 : bv 32 := 0x00090713.
Lemma F_5d5c8 : fetch_word Asan.M.loaded_segments (0x5d618 : word) = Some W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : decode_any W_5d5c8 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5cc : bv 32 := 0x00010513.
Lemma F_5d5cc : fetch_word Asan.M.loaded_segments (0x5d61c : word) = Some W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : decode_any W_5d5cc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d0 : bv 32 := 0x00070593.
Lemma F_5d5d0 : fetch_word Asan.M.loaded_segments (0x5d620 : word) = Some W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : decode_any W_5d5d0 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d4 : bv 32 := 0xe91fd0ef.
Lemma F_5d5d4 : fetch_word Asan.M.loaded_segments (0x5d624 : word) = Some W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : decode_any W_5d5d4 = Some (Jal 1 2088592, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d8 : bv 32 := 0x0184b503.
Lemma F_5d5d8 : fetch_word Asan.M.loaded_segments (0x5d628 : word) = Some W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : decode_any W_5d5d8 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5dc : bv 32 := 0x00ab7c63.
Lemma F_5d5dc : fetch_word Asan.M.loaded_segments (0x5d62c : word) = Some W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : decode_any W_5d5dc = Some (Branch BC_GEU 22 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e0 : bv 32 := 0x00013603.
Lemma F_5d5e0 : fetch_word Asan.M.loaded_segments (0x5d630 : word) = Some W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : decode_any W_5d5e0 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e4 : bv 32 := 0x00813683.
Lemma F_5d5e4 : fetch_word Asan.M.loaded_segments (0x5d634 : word) = Some W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : decode_any W_5d5e4 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e8 : bv 32 := 0x00040513.
Lemma F_5d5e8 : fetch_word Asan.M.loaded_segments (0x5d638 : word) = Some W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : decode_any W_5d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5ec : bv 32 := 0x00048593.
Lemma F_5d5ec : fetch_word Asan.M.loaded_segments (0x5d63c : word) = Some W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : decode_any W_5d5ec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f0 : bv 32 := 0x831fd0ef.
Lemma F_5d5f0 : fetch_word Asan.M.loaded_segments (0x5d640 : word) = Some W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : decode_any W_5d5f0 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5bce4_5bd7c.
Module Na0_code_r719f8_71a24.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_92b7c : bv 32 := 0x000c4697.
Lemma F_92b7c : fetch_word Asan.M.loaded_segments (0x92bcc : word) = Some W_92b7c.
Proof. vm_refl. Qed.
Lemma D_92b7c : decode_any W_92b7c = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b80 : bv 32 := 0x20c6b683.
Lemma F_92b80 : fetch_word Asan.M.loaded_segments (0x92bd0 : word) = Some W_92b80.
Proof. vm_refl. Qed.
Lemma D_92b80 : decode_any W_92b80 = Some (Load SZ8 true 13 13 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b84 : bv 32 := 0x00068a63.
Lemma F_92b84 : fetch_word Asan.M.loaded_segments (0x92bd4 : word) = Some W_92b84.
Proof. vm_refl. Qed.
Lemma D_92b84 : decode_any W_92b84 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b88 : bv 32 := 0x00400693.
Lemma F_92b88 : fetch_word Asan.M.loaded_segments (0x92bd8 : word) = Some W_92b88.
Proof. vm_refl. Qed.
Lemma D_92b88 : decode_any W_92b88 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b8c : bv 32 := 0x00d60663.
Lemma F_92b8c : fetch_word Asan.M.loaded_segments (0x92bdc : word) = Some W_92b8c.
Proof. vm_refl. Qed.
Lemma D_92b8c : decode_any W_92b8c = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b98 : bv 32 := 0x0e900893.
Lemma F_92b98 : fetch_word Asan.M.loaded_segments (0x92be8 : word) = Some W_92b98.
Proof. vm_refl. Qed.
Lemma D_92b98 : decode_any W_92b98 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b9c : bv 32 := 0x00000073.
Lemma F_92b9c : fetch_word Asan.M.loaded_segments (0x92bec : word) = Some W_92b9c.
Proof. vm_refl. Qed.
Lemma D_92b9c : decode_any W_92b9c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92b9c : is_ecall W_92b9c = true.
Proof. reflexivity. Qed.

Definition W_92ba0 : bv 32 := 0x0005051b.
Lemma F_92ba0 : fetch_word Asan.M.loaded_segments (0x92bf0 : word) = Some W_92ba0.
Proof. vm_refl. Qed.
Lemma D_92ba0 : decode_any W_92ba0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ba4 : bv 32 := 0x00008067.
Lemma F_92ba4 : fetch_word Asan.M.loaded_segments (0x92bf4 : word) = Some W_92ba4.
Proof. vm_refl. Qed.
Lemma D_92ba4 : decode_any W_92ba4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r719f8_71a24.
Module Na0_code_r5f7d0_5f958.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_803f8 : bv 32 := 0xfe010113.
Lemma F_803f8 : fetch_word Asan.M.loaded_segments (0x80448 : word) = Some W_803f8.
Proof. vm_refl. Qed.
Lemma D_803f8 : decode_any W_803f8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_803fc : bv 32 := 0x00113c23.
Lemma F_803fc : fetch_word Asan.M.loaded_segments (0x8044c : word) = Some W_803fc.
Proof. vm_refl. Qed.
Lemma D_803fc : decode_any W_803fc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80400 : bv 32 := 0x00813823.
Lemma F_80400 : fetch_word Asan.M.loaded_segments (0x80450 : word) = Some W_80400.
Proof. vm_refl. Qed.
Lemma D_80400 : decode_any W_80400 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80404 : bv 32 := 0x00913423.
Lemma F_80404 : fetch_word Asan.M.loaded_segments (0x80454 : word) = Some W_80404.
Proof. vm_refl. Qed.
Lemma D_80404 : decode_any W_80404 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80408 : bv 32 := 0x01213023.
Lemma F_80408 : fetch_word Asan.M.loaded_segments (0x80458 : word) = Some W_80408.
Proof. vm_refl. Qed.
Lemma D_80408 : decode_any W_80408 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8040c : bv 32 := 0x00058413.
Lemma F_8040c : fetch_word Asan.M.loaded_segments (0x8045c : word) = Some W_8040c.
Proof. vm_refl. Qed.
Lemma D_8040c : decode_any W_8040c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80410 : bv 32 := 0x00050493.
Lemma F_80410 : fetch_word Asan.M.loaded_segments (0x80460 : word) = Some W_80410.
Proof. vm_refl. Qed.
Lemma D_80410 : decode_any W_80410 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80414 : bv 32 := 0x030000ef.
Lemma F_80414 : fetch_word Asan.M.loaded_segments (0x80464 : word) = Some W_80414.
Proof. vm_refl. Qed.
Lemma D_80414 : decode_any W_80414 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80418 : bv 32 := 0x00050913.
Lemma F_80418 : fetch_word Asan.M.loaded_segments (0x80468 : word) = Some W_80418.
Proof. vm_refl. Qed.
Lemma D_80418 : decode_any W_80418 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8041c : bv 32 := 0x00940533.
Lemma F_8041c : fetch_word Asan.M.loaded_segments (0x8046c : word) = Some W_8041c.
Proof. vm_refl. Qed.
Lemma D_8041c : decode_any W_8041c = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80420 : bv 32 := 0x024000ef.
Lemma F_80420 : fetch_word Asan.M.loaded_segments (0x80470 : word) = Some W_80420.
Proof. vm_refl. Qed.
Lemma D_80420 : decode_any W_80420 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_80424 : bv 32 := 0x00050593.
Lemma F_80424 : fetch_word Asan.M.loaded_segments (0x80474 : word) = Some W_80424.
Proof. vm_refl. Qed.
Lemma D_80424 : decode_any W_80424 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80428 : bv 32 := 0x00090513.
Lemma F_80428 : fetch_word Asan.M.loaded_segments (0x80478 : word) = Some W_80428.
Proof. vm_refl. Qed.
Lemma D_80428 : decode_any W_80428 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8042c : bv 32 := 0x01813083.
Lemma F_8042c : fetch_word Asan.M.loaded_segments (0x8047c : word) = Some W_8042c.
Proof. vm_refl. Qed.
Lemma D_8042c : decode_any W_8042c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80430 : bv 32 := 0x01013403.
Lemma F_80430 : fetch_word Asan.M.loaded_segments (0x80480 : word) = Some W_80430.
Proof. vm_refl. Qed.
Lemma D_80430 : decode_any W_80430 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80434 : bv 32 := 0x00813483.
Lemma F_80434 : fetch_word Asan.M.loaded_segments (0x80484 : word) = Some W_80434.
Proof. vm_refl. Qed.
Lemma D_80434 : decode_any W_80434 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80438 : bv 32 := 0x00013903.
Lemma F_80438 : fetch_word Asan.M.loaded_segments (0x80488 : word) = Some W_80438.
Proof. vm_refl. Qed.
Lemma D_80438 : decode_any W_80438 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8043c : bv 32 := 0x02010113.
Lemma F_8043c : fetch_word Asan.M.loaded_segments (0x8048c : word) = Some W_8043c.
Proof. vm_refl. Qed.
Lemma D_8043c : decode_any W_8043c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80440 : bv 32 := 0x3151b06f.
Lemma F_80440 : fetch_word Asan.M.loaded_segments (0x80490 : word) = Some W_80440.
Proof. vm_refl. Qed.
Lemma D_80440 : decode_any W_80440 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

Definition W_80444 : bv 32 := 0x000d7597.
Lemma F_80444 : fetch_word Asan.M.loaded_segments (0x80494 : word) = Some W_80444.
Proof. vm_refl. Qed.
Lemma D_80444 : decode_any W_80444 = Some (Auipc 11 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_80448 : bv 32 := 0x9045b583.
Lemma F_80448 : fetch_word Asan.M.loaded_segments (0x80498 : word) = Some W_80448.
Proof. vm_refl. Qed.
Lemma D_80448 : decode_any W_80448 = Some (Load SZ8 true 11 11 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_8044c : bv 32 := 0x0005b583.
Lemma F_8044c : fetch_word Asan.M.loaded_segments (0x8049c : word) = Some W_8044c.
Proof. vm_refl. Qed.
Lemma D_8044c : decode_any W_8044c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80450 : bv 32 := 0xfff58613.
Lemma F_80450 : fetch_word Asan.M.loaded_segments (0x804a0 : word) = Some W_80450.
Proof. vm_refl. Qed.
Lemma D_80450 : decode_any W_80450 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80454 : bv 32 := 0x00c5b6b3.
Lemma F_80454 : fetch_word Asan.M.loaded_segments (0x804a4 : word) = Some W_80454.
Proof. vm_refl. Qed.
Lemma D_80454 : decode_any W_80454 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80458 : bv 32 := 0xfff68693.
Lemma F_80458 : fetch_word Asan.M.loaded_segments (0x804a8 : word) = Some W_80458.
Proof. vm_refl. Qed.
Lemma D_80458 : decode_any W_80458 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8045c : bv 32 := 0x00c6f6b3.
Lemma F_8045c : fetch_word Asan.M.loaded_segments (0x804ac : word) = Some W_8045c.
Proof. vm_refl. Qed.
Lemma D_8045c : decode_any W_8045c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80460 : bv 32 := 0x04a6f263.
Lemma F_80460 : fetch_word Asan.M.loaded_segments (0x804b0 : word) = Some W_80460.
Proof. vm_refl. Qed.
Lemma D_80460 : decode_any W_80460 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_80464 : bv 32 := 0x000d7697.
Lemma F_80464 : fetch_word Asan.M.loaded_segments (0x804b4 : word) = Some W_80464.
Proof. vm_refl. Qed.
Lemma D_80464 : decode_any W_80464 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_80468 : bv 32 := 0x8ec6b683.
Lemma F_80468 : fetch_word Asan.M.loaded_segments (0x804b8 : word) = Some W_80468.
Proof. vm_refl. Qed.
Lemma D_80468 : decode_any W_80468 = Some (Load SZ8 true 13 13 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_8046c : bv 32 := 0x000d7717.
Lemma F_8046c : fetch_word Asan.M.loaded_segments (0x804bc : word) = Some W_8046c.
Proof. vm_refl. Qed.
Lemma D_8046c : decode_any W_8046c = Some (Auipc 14 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_80470 : bv 32 := 0x8ec73703.
Lemma F_80470 : fetch_word Asan.M.loaded_segments (0x804c0 : word) = Some W_80470.
Proof. vm_refl. Qed.
Lemma D_80470 : decode_any W_80470 = Some (Load SZ8 true 14 14 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_80474 : bv 32 := 0x0006b803.
Lemma F_80474 : fetch_word Asan.M.loaded_segments (0x804c4 : word) = Some W_80474.
Proof. vm_refl. Qed.
Lemma D_80474 : decode_any W_80474 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80478 : bv 32 := 0x00073683.
Lemma F_80478 : fetch_word Asan.M.loaded_segments (0x804c8 : word) = Some W_80478.
Proof. vm_refl. Qed.
Lemma D_80478 : decode_any W_80478 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8047c : bv 32 := 0xfff80793.
Lemma F_8047c : fetch_word Asan.M.loaded_segments (0x804cc : word) = Some W_8047c.
Proof. vm_refl. Qed.
Lemma D_8047c : decode_any W_8047c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80480 : bv 32 := 0x00a7f463.
Lemma F_80480 : fetch_word Asan.M.loaded_segments (0x804d0 : word) = Some W_80480.
Proof. vm_refl. Qed.
Lemma D_80480 : decode_any W_80480 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80488 : bv 32 := 0x000d7717.
Lemma F_80488 : fetch_word Asan.M.loaded_segments (0x804d8 : word) = Some W_80488.
Proof. vm_refl. Qed.
Lemma D_80488 : decode_any W_80488 = Some (Auipc 14 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_8048c : bv 32 := 0x8d873703.
Lemma F_8048c : fetch_word Asan.M.loaded_segments (0x804dc : word) = Some W_8048c.
Proof. vm_refl. Qed.
Lemma D_8048c : decode_any W_8048c = Some (Load SZ8 true 14 14 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_80490 : bv 32 := 0x00073283.
Lemma F_80490 : fetch_word Asan.M.loaded_segments (0x804e0 : word) = Some W_80490.
Proof. vm_refl. Qed.
Lemma D_80490 : decode_any W_80490 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80494 : bv 32 := 0x0032d713.
Lemma F_80494 : fetch_word Asan.M.loaded_segments (0x804e4 : word) = Some W_80494.
Proof. vm_refl. Qed.
Lemma D_80494 : decode_any W_80494 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80498 : bv 32 := 0x00b708b3.
Lemma F_80498 : fetch_word Asan.M.loaded_segments (0x804e8 : word) = Some W_80498.
Proof. vm_refl. Qed.
Lemma D_80498 : decode_any W_80498 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8049c : bv 32 := 0x00a2ea63.
Lemma F_8049c : fetch_word Asan.M.loaded_segments (0x804ec : word) = Some W_8049c.
Proof. vm_refl. Qed.
Lemma D_8049c : decode_any W_8049c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a0 : bv 32 := 0x00a8f863.
Lemma F_804a0 : fetch_word Asan.M.loaded_segments (0x804f0 : word) = Some W_804a0.
Proof. vm_refl. Qed.
Lemma D_804a0 : decode_any W_804a0 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a4 : bv 32 := 0x00355513.
Lemma F_804a4 : fetch_word Asan.M.loaded_segments (0x804f4 : word) = Some W_804a4.
Proof. vm_refl. Qed.
Lemma D_804a4 : decode_any W_804a4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a8 : bv 32 := 0x00a58533.
Lemma F_804a8 : fetch_word Asan.M.loaded_segments (0x804f8 : word) = Some W_804a8.
Proof. vm_refl. Qed.
Lemma D_804a8 : decode_any W_804a8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ac : bv 32 := 0x00008067.
Lemma F_804ac : fetch_word Asan.M.loaded_segments (0x804fc : word) = Some W_804ac.
Proof. vm_refl. Qed.
Lemma D_804ac : decode_any W_804ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5f7d0_5f958.
Module Na0_code_r7add0_7ae74.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9bf54 : bv 32 := 0xfe010113.
Lemma F_9bf54 : fetch_word Asan.M.loaded_segments (0x9bfa4 : word) = Some W_9bf54.
Proof. vm_refl. Qed.
Lemma D_9bf54 : decode_any W_9bf54 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf58 : bv 32 := 0x00113c23.
Lemma F_9bf58 : fetch_word Asan.M.loaded_segments (0x9bfa8 : word) = Some W_9bf58.
Proof. vm_refl. Qed.
Lemma D_9bf58 : decode_any W_9bf58 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf5c : bv 32 := 0x00813823.
Lemma F_9bf5c : fetch_word Asan.M.loaded_segments (0x9bfac : word) = Some W_9bf5c.
Proof. vm_refl. Qed.
Lemma D_9bf5c : decode_any W_9bf5c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf60 : bv 32 := 0x00913423.
Lemma F_9bf60 : fetch_word Asan.M.loaded_segments (0x9bfb0 : word) = Some W_9bf60.
Proof. vm_refl. Qed.
Lemma D_9bf60 : decode_any W_9bf60 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf64 : bv 32 := 0x01213023.
Lemma F_9bf64 : fetch_word Asan.M.loaded_segments (0x9bfb4 : word) = Some W_9bf64.
Proof. vm_refl. Qed.
Lemma D_9bf64 : decode_any W_9bf64 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf68 : bv 32 := 0x00058413.
Lemma F_9bf68 : fetch_word Asan.M.loaded_segments (0x9bfb8 : word) = Some W_9bf68.
Proof. vm_refl. Qed.
Lemma D_9bf68 : decode_any W_9bf68 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf6c : bv 32 := 0x000bb597.
Lemma F_9bf6c : fetch_word Asan.M.loaded_segments (0x9bfbc : word) = Some W_9bf6c.
Proof. vm_refl. Qed.
Lemma D_9bf6c : decode_any W_9bf6c = Some (Auipc 11 187, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf70 : bv 32 := 0xdbc5b903.
Lemma F_9bf70 : fetch_word Asan.M.loaded_segments (0x9bfc0 : word) = Some W_9bf70.
Proof. vm_refl. Qed.
Lemma D_9bf70 : decode_any W_9bf70 = Some (Load SZ8 true 18 11 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf74 : bv 32 := 0x00093583.
Lemma F_9bf74 : fetch_word Asan.M.loaded_segments (0x9bfc4 : word) = Some W_9bf74.
Proof. vm_refl. Qed.
Lemma D_9bf74 : decode_any W_9bf74 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf78 : bv 32 := 0x00050493.
Lemma F_9bf78 : fetch_word Asan.M.loaded_segments (0x9bfc8 : word) = Some W_9bf78.
Proof. vm_refl. Qed.
Lemma D_9bf78 : decode_any W_9bf78 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf7c : bv 32 := 0x00059863.
Lemma F_9bf7c : fetch_word Asan.M.loaded_segments (0x9bfcc : word) = Some W_9bf7c.
Proof. vm_refl. Qed.
Lemma D_9bf7c : decode_any W_9bf7c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf8c : bv 32 := 0xfff58513.
Lemma F_9bf8c : fetch_word Asan.M.loaded_segments (0x9bfdc : word) = Some W_9bf8c.
Proof. vm_refl. Qed.
Lemma D_9bf8c : decode_any W_9bf8c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf90 : bv 32 := 0x00a5f533.
Lemma F_9bf90 : fetch_word Asan.M.loaded_segments (0x9bfe0 : word) = Some W_9bf90.
Proof. vm_refl. Qed.
Lemma D_9bf90 : decode_any W_9bf90 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf94 : bv 32 := 0x04051a63.
Lemma F_9bf94 : fetch_word Asan.M.loaded_segments (0x9bfe4 : word) = Some W_9bf94.
Proof. vm_refl. Qed.
Lemma D_9bf94 : decode_any W_9bf94 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf98 : bv 32 := 0x00b484b3.
Lemma F_9bf98 : fetch_word Asan.M.loaded_segments (0x9bfe8 : word) = Some W_9bf98.
Proof. vm_refl. Qed.
Lemma D_9bf98 : decode_any W_9bf98 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bf9c : bv 32 := 0x40b005b3.
Lemma F_9bf9c : fetch_word Asan.M.loaded_segments (0x9bfec : word) = Some W_9bf9c.
Proof. vm_refl. Qed.
Lemma D_9bf9c : decode_any W_9bf9c = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfa0 : bv 32 := 0xfff48513.
Lemma F_9bfa0 : fetch_word Asan.M.loaded_segments (0x9bff0 : word) = Some W_9bfa0.
Proof. vm_refl. Qed.
Lemma D_9bfa0 : decode_any W_9bfa0 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfa4 : bv 32 := 0x00b57533.
Lemma F_9bfa4 : fetch_word Asan.M.loaded_segments (0x9bff4 : word) = Some W_9bfa4.
Proof. vm_refl. Qed.
Lemma D_9bfa4 : decode_any W_9bfa4 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfa8 : bv 32 := 0x00b475b3.
Lemma F_9bfa8 : fetch_word Asan.M.loaded_segments (0x9bff8 : word) = Some W_9bfa8.
Proof. vm_refl. Qed.
Lemma D_9bfa8 : decode_any W_9bfa8 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfac : bv 32 := 0x02b57263.
Lemma F_9bfac : fetch_word Asan.M.loaded_segments (0x9bffc : word) = Some W_9bfac.
Proof. vm_refl. Qed.
Lemma D_9bfac : decode_any W_9bfac = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfb0 : bv 32 := 0x40a585b3.
Lemma F_9bfb0 : fetch_word Asan.M.loaded_segments (0x9c000 : word) = Some W_9bfb0.
Proof. vm_refl. Qed.
Lemma D_9bfb0 : decode_any W_9bfb0 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfb4 : bv 32 := 0x00400613.
Lemma F_9bfb4 : fetch_word Asan.M.loaded_segments (0x9c004 : word) = Some W_9bfb4.
Proof. vm_refl. Qed.
Lemma D_9bfb4 : decode_any W_9bfb4 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfb8 : bv 32 := 0x01813083.
Lemma F_9bfb8 : fetch_word Asan.M.loaded_segments (0x9c008 : word) = Some W_9bfb8.
Proof. vm_refl. Qed.
Lemma D_9bfb8 : decode_any W_9bfb8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfbc : bv 32 := 0x01013403.
Lemma F_9bfbc : fetch_word Asan.M.loaded_segments (0x9c00c : word) = Some W_9bfbc.
Proof. vm_refl. Qed.
Lemma D_9bfbc : decode_any W_9bfbc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfc0 : bv 32 := 0x00813483.
Lemma F_9bfc0 : fetch_word Asan.M.loaded_segments (0x9c010 : word) = Some W_9bfc0.
Proof. vm_refl. Qed.
Lemma D_9bfc0 : decode_any W_9bfc0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfc4 : bv 32 := 0x00013903.
Lemma F_9bfc4 : fetch_word Asan.M.loaded_segments (0x9c014 : word) = Some W_9bfc4.
Proof. vm_refl. Qed.
Lemma D_9bfc4 : decode_any W_9bfc4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfc8 : bv 32 := 0x02010113.
Lemma F_9bfc8 : fetch_word Asan.M.loaded_segments (0x9c018 : word) = Some W_9bfc8.
Proof. vm_refl. Qed.
Lemma D_9bfc8 : decode_any W_9bfc8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfcc : bv 32 := 0xbb1f606f.
Lemma F_9bfcc : fetch_word Asan.M.loaded_segments (0x9c01c : word) = Some W_9bfcc.
Proof. vm_refl. Qed.
Lemma D_9bfcc : decode_any W_9bfcc = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfd0 : bv 32 := 0x01813083.
Lemma F_9bfd0 : fetch_word Asan.M.loaded_segments (0x9c020 : word) = Some W_9bfd0.
Proof. vm_refl. Qed.
Lemma D_9bfd0 : decode_any W_9bfd0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfd4 : bv 32 := 0x01013403.
Lemma F_9bfd4 : fetch_word Asan.M.loaded_segments (0x9c024 : word) = Some W_9bfd4.
Proof. vm_refl. Qed.
Lemma D_9bfd4 : decode_any W_9bfd4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfd8 : bv 32 := 0x00813483.
Lemma F_9bfd8 : fetch_word Asan.M.loaded_segments (0x9c028 : word) = Some W_9bfd8.
Proof. vm_refl. Qed.
Lemma D_9bfd8 : decode_any W_9bfd8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfdc : bv 32 := 0x00013903.
Lemma F_9bfdc : fetch_word Asan.M.loaded_segments (0x9c02c : word) = Some W_9bfdc.
Proof. vm_refl. Qed.
Lemma D_9bfdc : decode_any W_9bfdc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfe0 : bv 32 := 0x02010113.
Lemma F_9bfe0 : fetch_word Asan.M.loaded_segments (0x9c030 : word) = Some W_9bfe0.
Proof. vm_refl. Qed.
Lemma D_9bfe0 : decode_any W_9bfe0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bfe4 : bv 32 := 0x00008067.
Lemma F_9bfe4 : fetch_word Asan.M.loaded_segments (0x9c034 : word) = Some W_9bfe4.
Proof. vm_refl. Qed.
Lemma D_9bfe4 : decode_any W_9bfe4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7add0_7ae74.
Module Na0_code_r5de44_5def8.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_651c0 : bv 32 := 0xff010113.
Lemma F_651c0 : fetch_word Asan.M.loaded_segments (0x65210 : word) = Some W_651c0.
Proof. vm_refl. Qed.
Lemma D_651c0 : decode_any W_651c0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c4 : bv 32 := 0x00113423.
Lemma F_651c4 : fetch_word Asan.M.loaded_segments (0x65214 : word) = Some W_651c4.
Proof. vm_refl. Qed.
Lemma D_651c4 : decode_any W_651c4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_651c8 : bv 32 := 0x00813023.
Lemma F_651c8 : fetch_word Asan.M.loaded_segments (0x65218 : word) = Some W_651c8.
Proof. vm_refl. Qed.
Lemma D_651c8 : decode_any W_651c8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651cc : bv 32 := 0x7f853583.
Lemma F_651cc : fetch_word Asan.M.loaded_segments (0x6521c : word) = Some W_651cc.
Proof. vm_refl. Qed.
Lemma D_651cc : decode_any W_651cc = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d0 : bv 32 := 0x00000413.
Lemma F_651d0 : fetch_word Asan.M.loaded_segments (0x65220 : word) = Some W_651d0.
Proof. vm_refl. Qed.
Lemma D_651d0 : decode_any W_651d0 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d4 : bv 32 := 0x00058023.
Lemma F_651d4 : fetch_word Asan.M.loaded_segments (0x65224 : word) = Some W_651d4.
Proof. vm_refl. Qed.
Lemma D_651d4 : decode_any W_651d4 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651d8 : bv 32 := 0x09c000ef.
Lemma F_651d8 : fetch_word Asan.M.loaded_segments (0x65228 : word) = Some W_651d8.
Proof. vm_refl. Qed.
Lemma D_651d8 : decode_any W_651d8 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_651dc : bv 32 := 0xfffab597.
Lemma F_651dc : fetch_word Asan.M.loaded_segments (0x6522c : word) = Some W_651dc.
Proof. vm_refl. Qed.
Lemma D_651dc : decode_any W_651dc = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e0 : bv 32 := 0x17c5b583.
Lemma F_651e0 : fetch_word Asan.M.loaded_segments (0x65230 : word) = Some W_651e0.
Proof. vm_refl. Qed.
Lemma D_651e0 : decode_any W_651e0 = Some (Load SZ8 true 11 11 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e4 : bv 32 := 0x00b53023.
Lemma F_651e4 : fetch_word Asan.M.loaded_segments (0x65234 : word) = Some W_651e4.
Proof. vm_refl. Qed.
Lemma D_651e4 : decode_any W_651e4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651e8 : bv 32 := 0x00b53423.
Lemma F_651e8 : fetch_word Asan.M.loaded_segments (0x65238 : word) = Some W_651e8.
Proof. vm_refl. Qed.
Lemma D_651e8 : decode_any W_651e8 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_651ec : bv 32 := 0x00b53823.
Lemma F_651ec : fetch_word Asan.M.loaded_segments (0x6523c : word) = Some W_651ec.
Proof. vm_refl. Qed.
Lemma D_651ec : decode_any W_651ec = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f0 : bv 32 := 0x00b53c23.
Lemma F_651f0 : fetch_word Asan.M.loaded_segments (0x65240 : word) = Some W_651f0.
Proof. vm_refl. Qed.
Lemma D_651f0 : decode_any W_651f0 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f4 : bv 32 := 0x02b53023.
Lemma F_651f4 : fetch_word Asan.M.loaded_segments (0x65244 : word) = Some W_651f4.
Proof. vm_refl. Qed.
Lemma D_651f4 : decode_any W_651f4 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_651f8 : bv 32 := 0x02b53423.
Lemma F_651f8 : fetch_word Asan.M.loaded_segments (0x65248 : word) = Some W_651f8.
Proof. vm_refl. Qed.
Lemma D_651f8 : decode_any W_651f8 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_651fc : bv 32 := 0x02b53823.
Lemma F_651fc : fetch_word Asan.M.loaded_segments (0x6524c : word) = Some W_651fc.
Proof. vm_refl. Qed.
Lemma D_651fc : decode_any W_651fc = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65200 : bv 32 := 0x02b53c23.
Lemma F_65200 : fetch_word Asan.M.loaded_segments (0x65250 : word) = Some W_65200.
Proof. vm_refl. Qed.
Lemma D_65200 : decode_any W_65200 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65204 : bv 32 := 0x04b53023.
Lemma F_65204 : fetch_word Asan.M.loaded_segments (0x65254 : word) = Some W_65204.
Proof. vm_refl. Qed.
Lemma D_65204 : decode_any W_65204 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65208 : bv 32 := 0x04b53423.
Lemma F_65208 : fetch_word Asan.M.loaded_segments (0x65258 : word) = Some W_65208.
Proof. vm_refl. Qed.
Lemma D_65208 : decode_any W_65208 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6520c : bv 32 := 0x04b53823.
Lemma F_6520c : fetch_word Asan.M.loaded_segments (0x6525c : word) = Some W_6520c.
Proof. vm_refl. Qed.
Lemma D_6520c : decode_any W_6520c = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65210 : bv 32 := 0x04b53c23.
Lemma F_65210 : fetch_word Asan.M.loaded_segments (0x65260 : word) = Some W_65210.
Proof. vm_refl. Qed.
Lemma D_65210 : decode_any W_65210 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_65214 : bv 32 := 0x06b53023.
Lemma F_65214 : fetch_word Asan.M.loaded_segments (0x65264 : word) = Some W_65214.
Proof. vm_refl. Qed.
Lemma D_65214 : decode_any W_65214 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65218 : bv 32 := 0x06b53423.
Lemma F_65218 : fetch_word Asan.M.loaded_segments (0x65268 : word) = Some W_65218.
Proof. vm_refl. Qed.
Lemma D_65218 : decode_any W_65218 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6521c : bv 32 := 0x06b53823.
Lemma F_6521c : fetch_word Asan.M.loaded_segments (0x6526c : word) = Some W_6521c.
Proof. vm_refl. Qed.
Lemma D_6521c : decode_any W_6521c = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65220 : bv 32 := 0x06b53c23.
Lemma F_65220 : fetch_word Asan.M.loaded_segments (0x65270 : word) = Some W_65220.
Proof. vm_refl. Qed.
Lemma D_65220 : decode_any W_65220 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_65224 : bv 32 := 0x08b53023.
Lemma F_65224 : fetch_word Asan.M.loaded_segments (0x65274 : word) = Some W_65224.
Proof. vm_refl. Qed.
Lemma D_65224 : decode_any W_65224 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_65228 : bv 32 := 0x08b53423.
Lemma F_65228 : fetch_word Asan.M.loaded_segments (0x65278 : word) = Some W_65228.
Proof. vm_refl. Qed.
Lemma D_65228 : decode_any W_65228 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6522c : bv 32 := 0x08b53823.
Lemma F_6522c : fetch_word Asan.M.loaded_segments (0x6527c : word) = Some W_6522c.
Proof. vm_refl. Qed.
Lemma D_6522c : decode_any W_6522c = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65230 : bv 32 := 0x08b53c23.
Lemma F_65230 : fetch_word Asan.M.loaded_segments (0x65280 : word) = Some W_65230.
Proof. vm_refl. Qed.
Lemma D_65230 : decode_any W_65230 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_65234 : bv 32 := 0x0ab53023.
Lemma F_65234 : fetch_word Asan.M.loaded_segments (0x65284 : word) = Some W_65234.
Proof. vm_refl. Qed.
Lemma D_65234 : decode_any W_65234 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_65238 : bv 32 := 0x0ab53423.
Lemma F_65238 : fetch_word Asan.M.loaded_segments (0x65288 : word) = Some W_65238.
Proof. vm_refl. Qed.
Lemma D_65238 : decode_any W_65238 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6523c : bv 32 := 0x0ab53823.
Lemma F_6523c : fetch_word Asan.M.loaded_segments (0x6528c : word) = Some W_6523c.
Proof. vm_refl. Qed.
Lemma D_6523c : decode_any W_6523c = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_65240 : bv 32 := 0x0ab53c23.
Lemma F_65240 : fetch_word Asan.M.loaded_segments (0x65290 : word) = Some W_65240.
Proof. vm_refl. Qed.
Lemma D_65240 : decode_any W_65240 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_65244 : bv 32 := 0x0cb53023.
Lemma F_65244 : fetch_word Asan.M.loaded_segments (0x65294 : word) = Some W_65244.
Proof. vm_refl. Qed.
Lemma D_65244 : decode_any W_65244 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_65248 : bv 32 := 0x0cb53423.
Lemma F_65248 : fetch_word Asan.M.loaded_segments (0x65298 : word) = Some W_65248.
Proof. vm_refl. Qed.
Lemma D_65248 : decode_any W_65248 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6524c : bv 32 := 0x0cb53823.
Lemma F_6524c : fetch_word Asan.M.loaded_segments (0x6529c : word) = Some W_6524c.
Proof. vm_refl. Qed.
Lemma D_6524c : decode_any W_6524c = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_65250 : bv 32 := 0x0cb53c23.
Lemma F_65250 : fetch_word Asan.M.loaded_segments (0x652a0 : word) = Some W_65250.
Proof. vm_refl. Qed.
Lemma D_65250 : decode_any W_65250 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_65254 : bv 32 := 0x0eb53023.
Lemma F_65254 : fetch_word Asan.M.loaded_segments (0x652a4 : word) = Some W_65254.
Proof. vm_refl. Qed.
Lemma D_65254 : decode_any W_65254 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65258 : bv 32 := 0x0eb53423.
Lemma F_65258 : fetch_word Asan.M.loaded_segments (0x652a8 : word) = Some W_65258.
Proof. vm_refl. Qed.
Lemma D_65258 : decode_any W_65258 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6525c : bv 32 := 0x0eb53823.
Lemma F_6525c : fetch_word Asan.M.loaded_segments (0x652ac : word) = Some W_6525c.
Proof. vm_refl. Qed.
Lemma D_6525c : decode_any W_6525c = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65260 : bv 32 := 0x0eb53c23.
Lemma F_65260 : fetch_word Asan.M.loaded_segments (0x652b0 : word) = Some W_65260.
Proof. vm_refl. Qed.
Lemma D_65260 : decode_any W_65260 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_65264 : bv 32 := 0x00813083.
Lemma F_65264 : fetch_word Asan.M.loaded_segments (0x652b4 : word) = Some W_65264.
Proof. vm_refl. Qed.
Lemma D_65264 : decode_any W_65264 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65268 : bv 32 := 0x00013403.
Lemma F_65268 : fetch_word Asan.M.loaded_segments (0x652b8 : word) = Some W_65268.
Proof. vm_refl. Qed.
Lemma D_65268 : decode_any W_65268 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6526c : bv 32 := 0x01010113.
Lemma F_6526c : fetch_word Asan.M.loaded_segments (0x652bc : word) = Some W_6526c.
Proof. vm_refl. Qed.
Lemma D_6526c : decode_any W_6526c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65270 : bv 32 := 0x00008067.
Lemma F_65270 : fetch_word Asan.M.loaded_segments (0x652c0 : word) = Some W_65270.
Proof. vm_refl. Qed.
Lemma D_65270 : decode_any W_65270 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5de44_5def8.
Module Na0_code_r4f7c4_4fa34.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c444 : bv 32 := 0x81010113.
Lemma F_6c444 : fetch_word Asan.M.loaded_segments (0x6c494 : word) = Some W_6c444.
Proof. vm_refl. Qed.
Lemma D_6c444 : decode_any W_6c444 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c448 : bv 32 := 0x7e113423.
Lemma F_6c448 : fetch_word Asan.M.loaded_segments (0x6c498 : word) = Some W_6c448.
Proof. vm_refl. Qed.
Lemma D_6c448 : decode_any W_6c448 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c44c : bv 32 := 0x7e813023.
Lemma F_6c44c : fetch_word Asan.M.loaded_segments (0x6c49c : word) = Some W_6c44c.
Proof. vm_refl. Qed.
Lemma D_6c44c : decode_any W_6c44c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c450 : bv 32 := 0x7c913c23.
Lemma F_6c450 : fetch_word Asan.M.loaded_segments (0x6c4a0 : word) = Some W_6c450.
Proof. vm_refl. Qed.
Lemma D_6c450 : decode_any W_6c450 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c454 : bv 32 := 0x7d213823.
Lemma F_6c454 : fetch_word Asan.M.loaded_segments (0x6c4a4 : word) = Some W_6c454.
Proof. vm_refl. Qed.
Lemma D_6c454 : decode_any W_6c454 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c458 : bv 32 := 0x7d313423.
Lemma F_6c458 : fetch_word Asan.M.loaded_segments (0x6c4a8 : word) = Some W_6c458.
Proof. vm_refl. Qed.
Lemma D_6c458 : decode_any W_6c458 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c45c : bv 32 := 0x7d413023.
Lemma F_6c45c : fetch_word Asan.M.loaded_segments (0x6c4ac : word) = Some W_6c45c.
Proof. vm_refl. Qed.
Lemma D_6c45c : decode_any W_6c45c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c460 : bv 32 := 0x7f010413.
Lemma F_6c460 : fetch_word Asan.M.loaded_segments (0x6c4b0 : word) = Some W_6c460.
Proof. vm_refl. Qed.
Lemma D_6c460 : decode_any W_6c460 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c464 : bv 32 := 0xfa010113.
Lemma F_6c464 : fetch_word Asan.M.loaded_segments (0x6c4b4 : word) = Some W_6c464.
Proof. vm_refl. Qed.
Lemma D_6c464 : decode_any W_6c464 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c468 : bv 32 := 0x00060913.
Lemma F_6c468 : fetch_word Asan.M.loaded_segments (0x6c4b8 : word) = Some W_6c468.
Proof. vm_refl. Qed.
Lemma D_6c468 : decode_any W_6c468 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c46c : bv 32 := 0x00058493.
Lemma F_6c46c : fetch_word Asan.M.loaded_segments (0x6c4bc : word) = Some W_6c46c.
Proof. vm_refl. Qed.
Lemma D_6c46c : decode_any W_6c46c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c470 : bv 32 := 0x00050993.
Lemma F_6c470 : fetch_word Asan.M.loaded_segments (0x6c4c0 : word) = Some W_6c470.
Proof. vm_refl. Qed.
Lemma D_6c470 : decode_any W_6c470 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c474 : bv 32 := 0x3491b0ef.
Lemma F_6c474 : fetch_word Asan.M.loaded_segments (0x6c4c4 : word) = Some W_6c474.
Proof. vm_refl. Qed.
Lemma D_6c474 : decode_any W_6c474 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c478 : bv 32 := 0x000ec597.
Lemma F_6c478 : fetch_word Asan.M.loaded_segments (0x6c4c8 : word) = Some W_6c478.
Proof. vm_refl. Qed.
Lemma D_6c478 : decode_any W_6c478 = Some (Auipc 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c47c : bv 32 := 0x7285b683.
Lemma F_6c47c : fetch_word Asan.M.loaded_segments (0x6c4cc : word) = Some W_6c47c.
Proof. vm_refl. Qed.
Lemma D_6c47c : decode_any W_6c47c = Some (Load SZ8 true 13 11 1832, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c480 : bv 32 := 0x00050a13.
Lemma F_6c480 : fetch_word Asan.M.loaded_segments (0x6c4d0 : word) = Some W_6c480.
Proof. vm_refl. Qed.
Lemma D_6c480 : decode_any W_6c480 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c484 : bv 32 := 0x00098513.
Lemma F_6c484 : fetch_word Asan.M.loaded_segments (0x6c4d4 : word) = Some W_6c484.
Proof. vm_refl. Qed.
Lemma D_6c484 : decode_any W_6c484 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c488 : bv 32 := 0x00048593.
Lemma F_6c488 : fetch_word Asan.M.loaded_segments (0x6c4d8 : word) = Some W_6c488.
Proof. vm_refl. Qed.
Lemma D_6c488 : decode_any W_6c488 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c48c : bv 32 := 0x00090613.
Lemma F_6c48c : fetch_word Asan.M.loaded_segments (0x6c4dc : word) = Some W_6c48c.
Proof. vm_refl. Qed.
Lemma D_6c48c : decode_any W_6c48c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c490 : bv 32 := 0x000680e7.
Lemma F_6c490 : fetch_word Asan.M.loaded_segments (0x6c4e0 : word) = Some W_6c490.
Proof. vm_refl. Qed.
Lemma D_6c490 : decode_any W_6c490 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c494 : bv 32 := 0x060a0063.
Lemma F_6c494 : fetch_word Asan.M.loaded_segments (0x6c4e4 : word) = Some W_6c494.
Proof. vm_refl. Qed.
Lemma D_6c494 : decode_any W_6c494 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c498 : bv 32 := 0x04a05e63.
Lemma F_6c498 : fetch_word Asan.M.loaded_segments (0x6c4e8 : word) = Some W_6c498.
Proof. vm_refl. Qed.
Lemma D_6c498 : decode_any W_6c498 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c49c : bv 32 := 0xfff4c593.
Lemma F_6c49c : fetch_word Asan.M.loaded_segments (0x6c4ec : word) = Some W_6c49c.
Proof. vm_refl. Qed.
Lemma D_6c49c : decode_any W_6c49c = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4a0 : bv 32 := 0x80040a13.
Lemma F_6c4a0 : fetch_word Asan.M.loaded_segments (0x6c4f0 : word) = Some W_6c4a0.
Proof. vm_refl. Qed.
Lemma D_6c4a0 : decode_any W_6c4a0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4a4 : bv 32 := 0xfb8a0a13.
Lemma F_6c4a4 : fetch_word Asan.M.loaded_segments (0x6c4f4 : word) = Some W_6c4a4.
Proof. vm_refl. Qed.
Lemma D_6c4a4 : decode_any W_6c4a4 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4a8 : bv 32 := 0x06a5e863.
Lemma F_6c4a8 : fetch_word Asan.M.loaded_segments (0x6c4f8 : word) = Some W_6c4a8.
Proof. vm_refl. Qed.
Lemma D_6c4a8 : decode_any W_6c4a8 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4ac : bv 32 := 0xfbf50593.
Lemma F_6c4ac : fetch_word Asan.M.loaded_segments (0x6c4fc : word) = Some W_6c4ac.
Proof. vm_refl. Qed.
Lemma D_6c4ac : decode_any W_6c4ac = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4b0 : bv 32 := 0xfc000613.
Lemma F_6c4b0 : fetch_word Asan.M.loaded_segments (0x6c500 : word) = Some W_6c4b0.
Proof. vm_refl. Qed.
Lemma D_6c4b0 : decode_any W_6c4b0 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4b4 : bv 32 := 0x0cc5ee63.
Lemma F_6c4b4 : fetch_word Asan.M.loaded_segments (0x6c504 : word) = Some W_6c4b4.
Proof. vm_refl. Qed.
Lemma D_6c4b4 : decode_any W_6c4b4 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4b8 : bv 32 := 0x000eb597.
Lemma F_6c4b8 : fetch_word Asan.M.loaded_segments (0x6c508 : word) = Some W_6c4b8.
Proof. vm_refl. Qed.
Lemma D_6c4b8 : decode_any W_6c4b8 = Some (Auipc 11 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4bc : bv 32 := 0x8905b583.
Lemma F_6c4bc : fetch_word Asan.M.loaded_segments (0x6c50c : word) = Some W_6c4bc.
Proof. vm_refl. Qed.
Lemma D_6c4bc : decode_any W_6c4bc = Some (Load SZ8 true 11 11 2192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4c0 : bv 32 := 0x00a486b3.
Lemma F_6c4c0 : fetch_word Asan.M.loaded_segments (0x6c510 : word) = Some W_6c4c0.
Proof. vm_refl. Qed.
Lemma D_6c4c0 : decode_any W_6c4c0 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4c4 : bv 32 := 0x0005b603.
Lemma F_6c4c4 : fetch_word Asan.M.loaded_segments (0x6c514 : word) = Some W_6c4c4.
Proof. vm_refl. Qed.
Lemma D_6c4c4 : decode_any W_6c4c4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4c8 : bv 32 := 0x0034d593.
Lemma F_6c4c8 : fetch_word Asan.M.loaded_segments (0x6c518 : word) = Some W_6c4c8.
Proof. vm_refl. Qed.
Lemma D_6c4c8 : decode_any W_6c4c8 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4cc : bv 32 := 0xfff68693.
Lemma F_6c4cc : fetch_word Asan.M.loaded_segments (0x6c51c : word) = Some W_6c4cc.
Proof. vm_refl. Qed.
Lemma D_6c4cc : decode_any W_6c4cc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4d0 : bv 32 := 0x0036d713.
Lemma F_6c4d0 : fetch_word Asan.M.loaded_segments (0x6c520 : word) = Some W_6c4d0.
Proof. vm_refl. Qed.
Lemma D_6c4d0 : decode_any W_6c4d0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4d4 : bv 32 := 0x00b605b3.
Lemma F_6c4d4 : fetch_word Asan.M.loaded_segments (0x6c524 : word) = Some W_6c4d4.
Proof. vm_refl. Qed.
Lemma D_6c4d4 : decode_any W_6c4d4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4d8 : bv 32 := 0x00e60633.
Lemma F_6c4d8 : fetch_word Asan.M.loaded_segments (0x6c528 : word) = Some W_6c4d8.
Proof. vm_refl. Qed.
Lemma D_6c4d8 : decode_any W_6c4d8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4dc : bv 32 := 0xff85f713.
Lemma F_6c4dc : fetch_word Asan.M.loaded_segments (0x6c52c : word) = Some W_6c4dc.
Proof. vm_refl. Qed.
Lemma D_6c4dc : decode_any W_6c4dc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4e0 : bv 32 := 0xff867793.
Lemma F_6c4e0 : fetch_word Asan.M.loaded_segments (0x6c530 : word) = Some W_6c4e0.
Proof. vm_refl. Qed.
Lemma D_6c4e0 : decode_any W_6c4e0 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4e4 : bv 32 := 0x00073703.
Lemma F_6c4e4 : fetch_word Asan.M.loaded_segments (0x6c534 : word) = Some W_6c4e4.
Proof. vm_refl. Qed.
Lemma D_6c4e4 : decode_any W_6c4e4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4e8 : bv 32 := 0x0007b783.
Lemma F_6c4e8 : fetch_word Asan.M.loaded_segments (0x6c538 : word) = Some W_6c4e8.
Proof. vm_refl. Qed.
Lemma D_6c4e8 : decode_any W_6c4e8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4ec : bv 32 := 0x00e7e733.
Lemma F_6c4ec : fetch_word Asan.M.loaded_segments (0x6c53c : word) = Some W_6c4ec.
Proof. vm_refl. Qed.
Lemma D_6c4ec : decode_any W_6c4ec = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4f0 : bv 32 := 0x14071663.
Lemma F_6c4f0 : fetch_word Asan.M.loaded_segments (0x6c540 : word) = Some W_6c4f0.
Proof. vm_refl. Qed.
Lemma D_6c4f0 : decode_any W_6c4f0 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4f4 : bv 32 := 0x06010113.
Lemma F_6c4f4 : fetch_word Asan.M.loaded_segments (0x6c544 : word) = Some W_6c4f4.
Proof. vm_refl. Qed.
Lemma D_6c4f4 : decode_any W_6c4f4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4f8 : bv 32 := 0x7e813083.
Lemma F_6c4f8 : fetch_word Asan.M.loaded_segments (0x6c548 : word) = Some W_6c4f8.
Proof. vm_refl. Qed.
Lemma D_6c4f8 : decode_any W_6c4f8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c4fc : bv 32 := 0x7e013403.
Lemma F_6c4fc : fetch_word Asan.M.loaded_segments (0x6c54c : word) = Some W_6c4fc.
Proof. vm_refl. Qed.
Lemma D_6c4fc : decode_any W_6c4fc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c500 : bv 32 := 0x7d813483.
Lemma F_6c500 : fetch_word Asan.M.loaded_segments (0x6c550 : word) = Some W_6c500.
Proof. vm_refl. Qed.
Lemma D_6c500 : decode_any W_6c500 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c504 : bv 32 := 0x7d013903.
Lemma F_6c504 : fetch_word Asan.M.loaded_segments (0x6c554 : word) = Some W_6c504.
Proof. vm_refl. Qed.
Lemma D_6c504 : decode_any W_6c504 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c508 : bv 32 := 0x7c813983.
Lemma F_6c508 : fetch_word Asan.M.loaded_segments (0x6c558 : word) = Some W_6c508.
Proof. vm_refl. Qed.
Lemma D_6c508 : decode_any W_6c508 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c50c : bv 32 := 0x7c013a03.
Lemma F_6c50c : fetch_word Asan.M.loaded_segments (0x6c55c : word) = Some W_6c50c.
Proof. vm_refl. Qed.
Lemma D_6c50c : decode_any W_6c50c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c510 : bv 32 := 0x7f010113.
Lemma F_6c510 : fetch_word Asan.M.loaded_segments (0x6c560 : word) = Some W_6c510.
Proof. vm_refl. Qed.
Lemma D_6c510 : decode_any W_6c510 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c514 : bv 32 := 0x00008067.
Lemma F_6c514 : fetch_word Asan.M.loaded_segments (0x6c564 : word) = Some W_6c514.
Proof. vm_refl. Qed.
Lemma D_6c514 : decode_any W_6c514 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c590 : bv 32 := 0x00050913.
Lemma F_6c590 : fetch_word Asan.M.loaded_segments (0x6c5e0 : word) = Some W_6c590.
Proof. vm_refl. Qed.
Lemma D_6c590 : decode_any W_6c590 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c594 : bv 32 := 0x00048513.
Lemma F_6c594 : fetch_word Asan.M.loaded_segments (0x6c5e4 : word) = Some W_6c594.
Proof. vm_refl. Qed.
Lemma D_6c594 : decode_any W_6c594 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c598 : bv 32 := 0x00090593.
Lemma F_6c598 : fetch_word Asan.M.loaded_segments (0x6c5e8 : word) = Some W_6c598.
Proof. vm_refl. Qed.
Lemma D_6c598 : decode_any W_6c598 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c59c : bv 32 := 0x5fd150ef.
Lemma F_6c59c : fetch_word Asan.M.loaded_segments (0x6c5ec : word) = Some W_6c59c.
Proof. vm_refl. Qed.
Lemma D_6c59c : decode_any W_6c59c = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5a0 : bv 32 := 0x00050493.
Lemma F_6c5a0 : fetch_word Asan.M.loaded_segments (0x6c5f0 : word) = Some W_6c5a0.
Proof. vm_refl. Qed.
Lemma D_6c5a0 : decode_any W_6c5a0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5a4 : bv 32 := 0x00090513.
Lemma F_6c5a4 : fetch_word Asan.M.loaded_segments (0x6c5f4 : word) = Some W_6c5a4.
Proof. vm_refl. Qed.
Lemma D_6c5a4 : decode_any W_6c5a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5a8 : bv 32 := 0xf40486e3.
Lemma F_6c5a8 : fetch_word Asan.M.loaded_segments (0x6c5f8 : word) = Some W_6c5a8.
Proof. vm_refl. Qed.
Lemma D_6c5a8 : decode_any W_6c5a8 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c63c : bv 32 := 0x00060703.
Lemma F_6c63c : fetch_word Asan.M.loaded_segments (0x6c68c : word) = Some W_6c63c.
Proof. vm_refl. Qed.
Lemma D_6c63c : decode_any W_6c63c = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c640 : bv 32 := 0x0076f693.
Lemma F_6c640 : fetch_word Asan.M.loaded_segments (0x6c690 : word) = Some W_6c640.
Proof. vm_refl. Qed.
Lemma D_6c640 : decode_any W_6c640 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c644 : bv 32 := 0x00e037b3.
Lemma F_6c644 : fetch_word Asan.M.loaded_segments (0x6c694 : word) = Some W_6c644.
Proof. vm_refl. Qed.
Lemma D_6c644 : decode_any W_6c644 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c648 : bv 32 := 0x00e6a6b3.
Lemma F_6c648 : fetch_word Asan.M.loaded_segments (0x6c698 : word) = Some W_6c648.
Proof. vm_refl. Qed.
Lemma D_6c648 : decode_any W_6c648 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c64c : bv 32 := 0x0016c693.
Lemma F_6c64c : fetch_word Asan.M.loaded_segments (0x6c69c : word) = Some W_6c64c.
Proof. vm_refl. Qed.
Lemma D_6c64c : decode_any W_6c64c = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c650 : bv 32 := 0x00d7f6b3.
Lemma F_6c650 : fetch_word Asan.M.loaded_segments (0x6c6a0 : word) = Some W_6c650.
Proof. vm_refl. Qed.
Lemma D_6c650 : decode_any W_6c650 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c654 : bv 32 := 0x00c5fa63.
Lemma F_6c654 : fetch_word Asan.M.loaded_segments (0x6c6a4 : word) = Some W_6c654.
Proof. vm_refl. Qed.
Lemma D_6c654 : decode_any W_6c654 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c658 : bv 32 := 0x0005c703.
Lemma F_6c658 : fetch_word Asan.M.loaded_segments (0x6c6a8 : word) = Some W_6c658.
Proof. vm_refl. Qed.
Lemma D_6c658 : decode_any W_6c658 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c65c : bv 32 := 0x00158593.
Lemma F_6c65c : fetch_word Asan.M.loaded_segments (0x6c6ac : word) = Some W_6c65c.
Proof. vm_refl. Qed.
Lemma D_6c65c : decode_any W_6c65c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c660 : bv 32 := 0x00d766b3.
Lemma F_6c660 : fetch_word Asan.M.loaded_segments (0x6c6b0 : word) = Some W_6c660.
Proof. vm_refl. Qed.
Lemma D_6c660 : decode_any W_6c660 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c664 : bv 32 := 0xfec59ae3.
Lemma F_6c664 : fetch_word Asan.M.loaded_segments (0x6c6b4 : word) = Some W_6c664.
Proof. vm_refl. Qed.
Lemma D_6c664 : decode_any W_6c664 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c668 : bv 32 := 0x0ff6f593.
Lemma F_6c668 : fetch_word Asan.M.loaded_segments (0x6c6b8 : word) = Some W_6c668.
Proof. vm_refl. Qed.
Lemma D_6c668 : decode_any W_6c668 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c66c : bv 32 := 0xe80584e3.
Lemma F_6c66c : fetch_word Asan.M.loaded_segments (0x6c6bc : word) = Some W_6c66c.
Proof. vm_refl. Qed.
Lemma D_6c66c : decode_any W_6c66c = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4f7c4_4fa34.
Module Na0_code_rbd474_bd4ac.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_137fdc : bv 32 := 0xfffff5b7.
Lemma F_137fdc : fetch_word Asan.M.loaded_segments (0x138020 : word) = Some W_137fdc.
Proof. vm_refl. Qed.
Lemma D_137fdc : decode_any W_137fdc = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fe0 : bv 32 := 0x0015859b.
Lemma F_137fe0 : fetch_word Asan.M.loaded_segments (0x138024 : word) = Some W_137fe0.
Proof. vm_refl. Qed.
Lemma D_137fe0 : decode_any W_137fe0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fe4 : bv 32 := 0x02b56663.
Lemma F_137fe4 : fetch_word Asan.M.loaded_segments (0x138028 : word) = Some W_137fe4.
Proof. vm_refl. Qed.
Lemma D_137fe4 : decode_any W_137fe4 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fe8 : bv 32 := 0xff010113.
Lemma F_137fe8 : fetch_word Asan.M.loaded_segments (0x13802c : word) = Some W_137fe8.
Proof. vm_refl. Qed.
Lemma D_137fe8 : decode_any W_137fe8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fec : bv 32 := 0x00113423.
Lemma F_137fec : fetch_word Asan.M.loaded_segments (0x138030 : word) = Some W_137fec.
Proof. vm_refl. Qed.
Lemma D_137fec : decode_any W_137fec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ff0 : bv 32 := 0x00813023.
Lemma F_137ff0 : fetch_word Asan.M.loaded_segments (0x138034 : word) = Some W_137ff0.
Proof. vm_refl. Qed.
Lemma D_137ff0 : decode_any W_137ff0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ff4 : bv 32 := 0x40a0043b.
Lemma F_137ff4 : fetch_word Asan.M.loaded_segments (0x138038 : word) = Some W_137ff4.
Proof. vm_refl. Qed.
Lemma D_137ff4 : decode_any W_137ff4 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ff8 : bv 32 := 0x8b9ff0ef.
Lemma F_137ff8 : fetch_word Asan.M.loaded_segments (0x13803c : word) = Some W_137ff8.
Proof. vm_refl. Qed.
Lemma D_137ff8 : decode_any W_137ff8 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ffc : bv 32 := 0x00852023.
Lemma F_137ffc : fetch_word Asan.M.loaded_segments (0x138040 : word) = Some W_137ffc.
Proof. vm_refl. Qed.
Lemma D_137ffc : decode_any W_137ffc = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138000 : bv 32 := 0xfff00513.
Lemma F_138000 : fetch_word Asan.M.loaded_segments (0x138044 : word) = Some W_138000.
Proof. vm_refl. Qed.
Lemma D_138000 : decode_any W_138000 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_138004 : bv 32 := 0x00813083.
Lemma F_138004 : fetch_word Asan.M.loaded_segments (0x138048 : word) = Some W_138004.
Proof. vm_refl. Qed.
Lemma D_138004 : decode_any W_138004 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_138008 : bv 32 := 0x00013403.
Lemma F_138008 : fetch_word Asan.M.loaded_segments (0x13804c : word) = Some W_138008.
Proof. vm_refl. Qed.
Lemma D_138008 : decode_any W_138008 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13800c : bv 32 := 0x01010113.
Lemma F_13800c : fetch_word Asan.M.loaded_segments (0x138050 : word) = Some W_13800c.
Proof. vm_refl. Qed.
Lemma D_13800c : decode_any W_13800c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_138010 : bv 32 := 0x00008067.
Lemma F_138010 : fetch_word Asan.M.loaded_segments (0x138054 : word) = Some W_138010.
Proof. vm_refl. Qed.
Lemma D_138010 : decode_any W_138010 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbd474_bd4ac.
Module Na0_code_rcc12c_cc154.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_149ce0 : bv 32 := 0x00050893.
Lemma F_149ce0 : fetch_word Asan.M.loaded_segments (0x149d24 : word) = Some W_149ce0.
Proof. vm_refl. Qed.
Lemma D_149ce0 : decode_any W_149ce0 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149ce4 : bv 32 := 0x00058513.
Lemma F_149ce4 : fetch_word Asan.M.loaded_segments (0x149d28 : word) = Some W_149ce4.
Proof. vm_refl. Qed.
Lemma D_149ce4 : decode_any W_149ce4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149ce8 : bv 32 := 0x00060593.
Lemma F_149ce8 : fetch_word Asan.M.loaded_segments (0x149d2c : word) = Some W_149ce8.
Proof. vm_refl. Qed.
Lemma D_149ce8 : decode_any W_149ce8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149cec : bv 32 := 0x00068613.
Lemma F_149cec : fetch_word Asan.M.loaded_segments (0x149d30 : word) = Some W_149cec.
Proof. vm_refl. Qed.
Lemma D_149cec : decode_any W_149cec = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149cf0 : bv 32 := 0x00070693.
Lemma F_149cf0 : fetch_word Asan.M.loaded_segments (0x149d34 : word) = Some W_149cf0.
Proof. vm_refl. Qed.
Lemma D_149cf0 : decode_any W_149cf0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149cf4 : bv 32 := 0x00078713.
Lemma F_149cf4 : fetch_word Asan.M.loaded_segments (0x149d38 : word) = Some W_149cf4.
Proof. vm_refl. Qed.
Lemma D_149cf4 : decode_any W_149cf4 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149cf8 : bv 32 := 0x00080793.
Lemma F_149cf8 : fetch_word Asan.M.loaded_segments (0x149d3c : word) = Some W_149cf8.
Proof. vm_refl. Qed.
Lemma D_149cf8 : decode_any W_149cf8 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149cfc : bv 32 := 0x00000073.
Lemma F_149cfc : fetch_word Asan.M.loaded_segments (0x149d40 : word) = Some W_149cfc.
Proof. vm_refl. Qed.
Lemma D_149cfc : decode_any W_149cfc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_149cfc : is_ecall W_149cfc = true.
Proof. reflexivity. Qed.

Definition W_149d00 : bv 32 := 0x00008067.
Lemma F_149d00 : fetch_word Asan.M.loaded_segments (0x149d44 : word) = Some W_149d00.
Proof. vm_refl. Qed.
Lemma D_149d00 : decode_any W_149d00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d04 : bv 32 := 0xfddff06f.
Lemma F_149d04 : fetch_word Asan.M.loaded_segments (0x149d48 : word) = Some W_149d04.
Proof. vm_refl. Qed.
Lemma D_149d04 : decode_any W_149d04 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc12c_cc154.
Module Na0_code_rd0c58_d0c8c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14f728 : bv 32 := 0xff010113.
Lemma F_14f728 : fetch_word Asan.M.loaded_segments (0x14f76c : word) = Some W_14f728.
Proof. vm_refl. Qed.
Lemma D_14f728 : decode_any W_14f728 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f72c : bv 32 := 0x00113423.
Lemma F_14f72c : fetch_word Asan.M.loaded_segments (0x14f770 : word) = Some W_14f72c.
Proof. vm_refl. Qed.
Lemma D_14f72c : decode_any W_14f72c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f730 : bv 32 := 0x00060693.
Lemma F_14f730 : fetch_word Asan.M.loaded_segments (0x14f774 : word) = Some W_14f730.
Proof. vm_refl. Qed.
Lemma D_14f730 : decode_any W_14f730 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f734 : bv 32 := 0x00058613.
Lemma F_14f734 : fetch_word Asan.M.loaded_segments (0x14f778 : word) = Some W_14f734.
Proof. vm_refl. Qed.
Lemma D_14f734 : decode_any W_14f734 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f738 : bv 32 := 0x00050593.
Lemma F_14f738 : fetch_word Asan.M.loaded_segments (0x14f77c : word) = Some W_14f738.
Proof. vm_refl. Qed.
Lemma D_14f738 : decode_any W_14f738 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f73c : bv 32 := 0x03f00513.
Lemma F_14f73c : fetch_word Asan.M.loaded_segments (0x14f780 : word) = Some W_14f73c.
Proof. vm_refl. Qed.
Lemma D_14f73c : decode_any W_14f73c = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f740 : bv 32 := 0x00000713.
Lemma F_14f740 : fetch_word Asan.M.loaded_segments (0x14f784 : word) = Some W_14f740.
Proof. vm_refl. Qed.
Lemma D_14f740 : decode_any W_14f740 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f744 : bv 32 := 0x00000793.
Lemma F_14f744 : fetch_word Asan.M.loaded_segments (0x14f788 : word) = Some W_14f744.
Proof. vm_refl. Qed.
Lemma D_14f744 : decode_any W_14f744 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f748 : bv 32 := 0x00000813.
Lemma F_14f748 : fetch_word Asan.M.loaded_segments (0x14f78c : word) = Some W_14f748.
Proof. vm_refl. Qed.
Lemma D_14f748 : decode_any W_14f748 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f74c : bv 32 := 0xdb8fa0ef.
Lemma F_14f74c : fetch_word Asan.M.loaded_segments (0x14f790 : word) = Some W_14f74c.
Proof. vm_refl. Qed.
Lemma D_14f74c : decode_any W_14f74c = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f750 : bv 32 := 0x00813083.
Lemma F_14f750 : fetch_word Asan.M.loaded_segments (0x14f794 : word) = Some W_14f750.
Proof. vm_refl. Qed.
Lemma D_14f750 : decode_any W_14f750 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f754 : bv 32 := 0x01010113.
Lemma F_14f754 : fetch_word Asan.M.loaded_segments (0x14f798 : word) = Some W_14f754.
Proof. vm_refl. Qed.
Lemma D_14f754 : decode_any W_14f754 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14f758 : bv 32 := 0x885e806f.
Lemma F_14f758 : fetch_word Asan.M.loaded_segments (0x14f79c : word) = Some W_14f758.
Proof. vm_refl. Qed.
Lemma D_14f758 : decode_any W_14f758 = Some (Jal 0 2001028, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rd0c58_d0c8c.
Module Na0_code_rc2a64_c2bf4.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13f61c : bv 32 := 0x0284b503.
Lemma F_13f61c : fetch_word Asan.M.loaded_segments (0x13f660 : word) = Some W_13f61c.
Proof. vm_refl. Qed.
Lemma D_13f61c : decode_any W_13f61c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f620 : bv 32 := 0x0384b603.
Lemma F_13f620 : fetch_word Asan.M.loaded_segments (0x13f664 : word) = Some W_13f620.
Proof. vm_refl. Qed.
Lemma D_13f620 : decode_any W_13f620 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f624 : bv 32 := 0x40c50b33.
Lemma F_13f624 : fetch_word Asan.M.loaded_segments (0x13f668 : word) = Some W_13f624.
Proof. vm_refl. Qed.
Lemma D_13f624 : decode_any W_13f624 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f628 : bv 32 := 0x00c546b3.
Lemma F_13f628 : fetch_word Asan.M.loaded_segments (0x13f66c : word) = Some W_13f628.
Proof. vm_refl. Qed.
Lemma D_13f628 : decode_any W_13f628 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f62c : bv 32 := 0x00c13423.
Lemma F_13f62c : fetch_word Asan.M.loaded_segments (0x13f670 : word) = Some W_13f62c.
Proof. vm_refl. Qed.
Lemma D_13f62c : decode_any W_13f62c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f630 : bv 32 := 0x01613823.
Lemma F_13f630 : fetch_word Asan.M.loaded_segments (0x13f674 : word) = Some W_13f630.
Proof. vm_refl. Qed.
Lemma D_13f630 : decode_any W_13f630 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f634 : bv 32 := 0x00b13c23.
Lemma F_13f634 : fetch_word Asan.M.loaded_segments (0x13f678 : word) = Some W_13f634.
Proof. vm_refl. Qed.
Lemma D_13f634 : decode_any W_13f634 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f638 : bv 32 := 0x02813023.
Lemma F_13f638 : fetch_word Asan.M.loaded_segments (0x13f67c : word) = Some W_13f638.
Proof. vm_refl. Qed.
Lemma D_13f638 : decode_any W_13f638 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f63c : bv 32 := 0x008b0b33.
Lemma F_13f63c : fetch_word Asan.M.loaded_segments (0x13f680 : word) = Some W_13f63c.
Proof. vm_refl. Qed.
Lemma D_13f63c : decode_any W_13f63c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f640 : bv 32 := 0x00d03933.
Lemma F_13f640 : fetch_word Asan.M.loaded_segments (0x13f684 : word) = Some W_13f640.
Proof. vm_refl. Qed.
Lemma D_13f640 : decode_any W_13f640 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f644 : bv 32 := 0x00c50663.
Lemma F_13f644 : fetch_word Asan.M.loaded_segments (0x13f688 : word) = Some W_13f644.
Proof. vm_refl. Qed.
Lemma D_13f644 : decode_any W_13f644 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f648 : bv 32 := 0x00810993.
Lemma F_13f648 : fetch_word Asan.M.loaded_segments (0x13f68c : word) = Some W_13f648.
Proof. vm_refl. Qed.
Lemma D_13f648 : decode_any W_13f648 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f64c : bv 32 := 0x0080006f.
Lemma F_13f64c : fetch_word Asan.M.loaded_segments (0x13f690 : word) = Some W_13f64c.
Proof. vm_refl. Qed.
Lemma D_13f64c : decode_any W_13f64c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f650 : bv 32 := 0x01810993.
Lemma F_13f650 : fetch_word Asan.M.loaded_segments (0x13f694 : word) = Some W_13f650.
Proof. vm_refl. Qed.
Lemma D_13f650 : decode_any W_13f650 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f654 : bv 32 := 0x0784a503.
Lemma F_13f654 : fetch_word Asan.M.loaded_segments (0x13f698 : word) = Some W_13f654.
Proof. vm_refl. Qed.
Lemma D_13f654 : decode_any W_13f654 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f658 : bv 32 := 0x00190913.
Lemma F_13f658 : fetch_word Asan.M.loaded_segments (0x13f69c : word) = Some W_13f658.
Proof. vm_refl. Qed.
Lemma D_13f658 : decode_any W_13f658 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f65c : bv 32 := 0x04200893.
Lemma F_13f65c : fetch_word Asan.M.loaded_segments (0x13f6a0 : word) = Some W_13f65c.
Proof. vm_refl. Qed.
Lemma D_13f65c : decode_any W_13f65c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f660 : bv 32 := 0x00098593.
Lemma F_13f660 : fetch_word Asan.M.loaded_segments (0x13f6a4 : word) = Some W_13f660.
Proof. vm_refl. Qed.
Lemma D_13f660 : decode_any W_13f660 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f664 : bv 32 := 0x00090613.
Lemma F_13f664 : fetch_word Asan.M.loaded_segments (0x13f6a8 : word) = Some W_13f664.
Proof. vm_refl. Qed.
Lemma D_13f664 : decode_any W_13f664 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f66c : bv 32 := 0x971f80ef.
Lemma F_13f66c : fetch_word Asan.M.loaded_segments (0x13f6b0 : word) = Some W_13f66c.
Proof. vm_refl. Qed.
Lemma D_13f66c : decode_any W_13f66c = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f670 : bv 32 := 0x09651863.
Lemma F_13f670 : fetch_word Asan.M.loaded_segments (0x13f6b4 : word) = Some W_13f670.
Proof. vm_refl. Qed.
Lemma D_13f670 : decode_any W_13f670 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6c4 : bv 32 := 0x00800713.
Lemma F_13f6c4 : fetch_word Asan.M.loaded_segments (0x13f708 : word) = Some W_13f6c4.
Proof. vm_refl. Qed.
Lemma D_13f6c4 : decode_any W_13f6c4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6c8 : bv 32 := 0x000a0593.
Lemma F_13f6c8 : fetch_word Asan.M.loaded_segments (0x13f70c : word) = Some W_13f6c8.
Proof. vm_refl. Qed.
Lemma D_13f6c8 : decode_any W_13f6c8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6cc : bv 32 := 0x00e98733.
Lemma F_13f6cc : fetch_word Asan.M.loaded_segments (0x13f710 : word) = Some W_13f6cc.
Proof. vm_refl. Qed.
Lemma D_13f6cc : decode_any W_13f6cc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6d0 : bv 32 := 0x00073783.
Lemma F_13f6d0 : fetch_word Asan.M.loaded_segments (0x13f714 : word) = Some W_13f6d0.
Proof. vm_refl. Qed.
Lemma D_13f6d0 : decode_any W_13f6d0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6d4 : bv 32 := 0x40ab0b33.
Lemma F_13f6d4 : fetch_word Asan.M.loaded_segments (0x13f718 : word) = Some W_13f6d4.
Proof. vm_refl. Qed.
Lemma D_13f6d4 : decode_any W_13f6d4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6d8 : bv 32 := 0x0784a503.
Lemma F_13f6d8 : fetch_word Asan.M.loaded_segments (0x13f71c : word) = Some W_13f6d8.
Proof. vm_refl. Qed.
Lemma D_13f6d8 : decode_any W_13f6d8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6dc : bv 32 := 0x40c9093b.
Lemma F_13f6dc : fetch_word Asan.M.loaded_segments (0x13f720 : word) = Some W_13f6dc.
Proof. vm_refl. Qed.
Lemma D_13f6dc : decode_any W_13f6dc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6e0 : bv 32 := 0x40d787b3.
Lemma F_13f6e0 : fetch_word Asan.M.loaded_segments (0x13f724 : word) = Some W_13f6e0.
Proof. vm_refl. Qed.
Lemma D_13f6e0 : decode_any W_13f6e0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6e4 : bv 32 := 0x00f73023.
Lemma F_13f6e4 : fetch_word Asan.M.loaded_segments (0x13f728 : word) = Some W_13f6e4.
Proof. vm_refl. Qed.
Lemma D_13f6e4 : decode_any W_13f6e4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6e8 : bv 32 := 0x04200893.
Lemma F_13f6e8 : fetch_word Asan.M.loaded_segments (0x13f72c : word) = Some W_13f6e8.
Proof. vm_refl. Qed.
Lemma D_13f6e8 : decode_any W_13f6e8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6ec : bv 32 := 0x00090613.
Lemma F_13f6ec : fetch_word Asan.M.loaded_segments (0x13f730 : word) = Some W_13f6ec.
Proof. vm_refl. Qed.
Lemma D_13f6ec : decode_any W_13f6ec = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6f4 : bv 32 := 0x8e9f80ef.
Lemma F_13f6f4 : fetch_word Asan.M.loaded_segments (0x13f738 : word) = Some W_13f6f4.
Proof. vm_refl. Qed.
Lemma D_13f6f4 : decode_any W_13f6f4 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6f8 : bv 32 := 0x000a0993.
Lemma F_13f6f8 : fetch_word Asan.M.loaded_segments (0x13f73c : word) = Some W_13f6f8.
Proof. vm_refl. Qed.
Lemma D_13f6f8 : decode_any W_13f6f8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f6fc : bv 32 := 0xf7650ce3.
Lemma F_13f6fc : fetch_word Asan.M.loaded_segments (0x13f740 : word) = Some W_13f6fc.
Proof. vm_refl. Qed.
Lemma D_13f6fc : decode_any W_13f6fc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f700 : bv 32 := 0x02054c63.
Lemma F_13f700 : fetch_word Asan.M.loaded_segments (0x13f744 : word) = Some W_13f700.
Proof. vm_refl. Qed.
Lemma D_13f700 : decode_any W_13f700 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f704 : bv 32 := 0x0089b583.
Lemma F_13f704 : fetch_word Asan.M.loaded_segments (0x13f748 : word) = Some W_13f704.
Proof. vm_refl. Qed.
Lemma D_13f704 : decode_any W_13f704 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f708 : bv 32 := 0x00a5b633.
Lemma F_13f708 : fetch_word Asan.M.loaded_segments (0x13f74c : word) = Some W_13f708.
Proof. vm_refl. Qed.
Lemma D_13f708 : decode_any W_13f708 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f70c : bv 32 := 0x00461a13.
Lemma F_13f70c : fetch_word Asan.M.loaded_segments (0x13f750 : word) = Some W_13f70c.
Proof. vm_refl. Qed.
Lemma D_13f70c : decode_any W_13f70c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f710 : bv 32 := 0x01498a33.
Lemma F_13f710 : fetch_word Asan.M.loaded_segments (0x13f754 : word) = Some W_13f710.
Proof. vm_refl. Qed.
Lemma D_13f710 : decode_any W_13f710 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f714 : bv 32 := 0x000a3703.
Lemma F_13f714 : fetch_word Asan.M.loaded_segments (0x13f758 : word) = Some W_13f714.
Proof. vm_refl. Qed.
Lemma D_13f714 : decode_any W_13f714 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f718 : bv 32 := 0x40c006b3.
Lemma F_13f718 : fetch_word Asan.M.loaded_segments (0x13f75c : word) = Some W_13f718.
Proof. vm_refl. Qed.
Lemma D_13f718 : decode_any W_13f718 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f71c : bv 32 := 0x00b6f6b3.
Lemma F_13f71c : fetch_word Asan.M.loaded_segments (0x13f760 : word) = Some W_13f71c.
Proof. vm_refl. Qed.
Lemma D_13f71c : decode_any W_13f71c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f720 : bv 32 := 0x40d506b3.
Lemma F_13f720 : fetch_word Asan.M.loaded_segments (0x13f764 : word) = Some W_13f720.
Proof. vm_refl. Qed.
Lemma D_13f720 : decode_any W_13f720 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f724 : bv 32 := 0x00d70733.
Lemma F_13f724 : fetch_word Asan.M.loaded_segments (0x13f768 : word) = Some W_13f724.
Proof. vm_refl. Qed.
Lemma D_13f724 : decode_any W_13f724 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f728 : bv 32 := 0x00ea3023.
Lemma F_13f728 : fetch_word Asan.M.loaded_segments (0x13f76c : word) = Some W_13f728.
Proof. vm_refl. Qed.
Lemma D_13f728 : decode_any W_13f728 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f72c : bv 32 := 0xf8a5fce3.
Lemma F_13f72c : fetch_word Asan.M.loaded_segments (0x13f770 : word) = Some W_13f72c.
Proof. vm_refl. Qed.
Lemma D_13f72c : decode_any W_13f72c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f730 : bv 32 := 0x01800713.
Lemma F_13f730 : fetch_word Asan.M.loaded_segments (0x13f774 : word) = Some W_13f730.
Proof. vm_refl. Qed.
Lemma D_13f730 : decode_any W_13f730 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13f734 : bv 32 := 0xf95ff06f.
Lemma F_13f734 : fetch_word Asan.M.loaded_segments (0x13f778 : word) = Some W_13f734.
Proof. vm_refl. Qed.
Lemma D_13f734 : decode_any W_13f734 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc2a64_c2bf4.
Module Na0_code_rbce10_bce1c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1378b0 : bv 32 := 0x00020513.
Lemma F_1378b0 : fetch_word Asan.M.loaded_segments (0x1378f4 : word) = Some W_1378b0.
Proof. vm_refl. Qed.
Lemma D_1378b0 : decode_any W_1378b0 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1378b4 : bv 32 := 0xf5c50513.
Lemma F_1378b4 : fetch_word Asan.M.loaded_segments (0x1378f8 : word) = Some W_1378b4.
Proof. vm_refl. Qed.
Lemma D_1378b4 : decode_any W_1378b4 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_1378b8 : bv 32 := 0x00008067.
Lemma F_1378b8 : fetch_word Asan.M.loaded_segments (0x1378fc : word) = Some W_1378b8.
Proof. vm_refl. Qed.
Lemma D_1378b8 : decode_any W_1378b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbce10_bce1c.
