(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_765d0 : bv 32 := 0x00155593.
Lemma F_765d0 : fetch_word Asan.M.loaded_segments (0x765b8 : word) = Some W_765d0.
Proof. vm_refl. Qed.
Lemma D_765d0 : decode_any W_765d0 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_765d4 : bv 32 := 0x55555637.
Lemma F_765d4 : fetch_word Asan.M.loaded_segments (0x765bc : word) = Some W_765d4.
Proof. vm_refl. Qed.
Lemma D_765d4 : decode_any W_765d4 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_765d8 : bv 32 := 0x333336b7.
Lemma F_765d8 : fetch_word Asan.M.loaded_segments (0x765c0 : word) = Some W_765d8.
Proof. vm_refl. Qed.
Lemma D_765d8 : decode_any W_765d8 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_765dc : bv 32 := 0x0f0f1737.
Lemma F_765dc : fetch_word Asan.M.loaded_segments (0x765c4 : word) = Some W_765dc.
Proof. vm_refl. Qed.
Lemma D_765dc : decode_any W_765dc = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_765e0 : bv 32 := 0x010107b7.
Lemma F_765e0 : fetch_word Asan.M.loaded_segments (0x765c8 : word) = Some W_765e0.
Proof. vm_refl. Qed.
Lemma D_765e0 : decode_any W_765e0 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_765e4 : bv 32 := 0x00b56533.
Lemma F_765e4 : fetch_word Asan.M.loaded_segments (0x765cc : word) = Some W_765e4.
Proof. vm_refl. Qed.
Lemma D_765e4 : decode_any W_765e4 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_765e8 : bv 32 := 0x5556059b.
Lemma F_765e8 : fetch_word Asan.M.loaded_segments (0x765d0 : word) = Some W_765e8.
Proof. vm_refl. Qed.
Lemma D_765e8 : decode_any W_765e8 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_765ec : bv 32 := 0x3336861b.
Lemma F_765ec : fetch_word Asan.M.loaded_segments (0x765d4 : word) = Some W_765ec.
Proof. vm_refl. Qed.
Lemma D_765ec : decode_any W_765ec = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_765f0 : bv 32 := 0xf0f7069b.
Lemma F_765f0 : fetch_word Asan.M.loaded_segments (0x765d8 : word) = Some W_765f0.
Proof. vm_refl. Qed.
Lemma D_765f0 : decode_any W_765f0 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_765f4 : bv 32 := 0x1017871b.
Lemma F_765f4 : fetch_word Asan.M.loaded_segments (0x765dc : word) = Some W_765f4.
Proof. vm_refl. Qed.
Lemma D_765f4 : decode_any W_765f4 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_765f8 : bv 32 := 0x00255793.
Lemma F_765f8 : fetch_word Asan.M.loaded_segments (0x765e0 : word) = Some W_765f8.
Proof. vm_refl. Qed.
Lemma D_765f8 : decode_any W_765f8 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_765fc : bv 32 := 0x00f56533.
Lemma F_765fc : fetch_word Asan.M.loaded_segments (0x765e4 : word) = Some W_765fc.
Proof. vm_refl. Qed.
Lemma D_765fc : decode_any W_765fc = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76600 : bv 32 := 0x02059793.
Lemma F_76600 : fetch_word Asan.M.loaded_segments (0x765e8 : word) = Some W_76600.
Proof. vm_refl. Qed.
Lemma D_76600 : decode_any W_76600 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76604 : bv 32 := 0x00f585b3.
Lemma F_76604 : fetch_word Asan.M.loaded_segments (0x765ec : word) = Some W_76604.
Proof. vm_refl. Qed.
Lemma D_76604 : decode_any W_76604 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76608 : bv 32 := 0x02061793.
Lemma F_76608 : fetch_word Asan.M.loaded_segments (0x765f0 : word) = Some W_76608.
Proof. vm_refl. Qed.
Lemma D_76608 : decode_any W_76608 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7660c : bv 32 := 0x00f60633.
Lemma F_7660c : fetch_word Asan.M.loaded_segments (0x765f4 : word) = Some W_7660c.
Proof. vm_refl. Qed.
Lemma D_7660c : decode_any W_7660c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76610 : bv 32 := 0x02069793.
Lemma F_76610 : fetch_word Asan.M.loaded_segments (0x765f8 : word) = Some W_76610.
Proof. vm_refl. Qed.
Lemma D_76610 : decode_any W_76610 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76614 : bv 32 := 0x00f686b3.
Lemma F_76614 : fetch_word Asan.M.loaded_segments (0x765fc : word) = Some W_76614.
Proof. vm_refl. Qed.
Lemma D_76614 : decode_any W_76614 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76618 : bv 32 := 0x02071793.
Lemma F_76618 : fetch_word Asan.M.loaded_segments (0x76600 : word) = Some W_76618.
Proof. vm_refl. Qed.
Lemma D_76618 : decode_any W_76618 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7661c : bv 32 := 0x00f70733.
Lemma F_7661c : fetch_word Asan.M.loaded_segments (0x76604 : word) = Some W_7661c.
Proof. vm_refl. Qed.
Lemma D_7661c : decode_any W_7661c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76620 : bv 32 := 0x00455793.
Lemma F_76620 : fetch_word Asan.M.loaded_segments (0x76608 : word) = Some W_76620.
Proof. vm_refl. Qed.
Lemma D_76620 : decode_any W_76620 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_76624 : bv 32 := 0x00f56533.
Lemma F_76624 : fetch_word Asan.M.loaded_segments (0x7660c : word) = Some W_76624.
Proof. vm_refl. Qed.
Lemma D_76624 : decode_any W_76624 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76628 : bv 32 := 0x00855793.
Lemma F_76628 : fetch_word Asan.M.loaded_segments (0x76610 : word) = Some W_76628.
Proof. vm_refl. Qed.
Lemma D_76628 : decode_any W_76628 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7662c : bv 32 := 0x00f56533.
Lemma F_7662c : fetch_word Asan.M.loaded_segments (0x76614 : word) = Some W_7662c.
Proof. vm_refl. Qed.
Lemma D_7662c : decode_any W_7662c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76630 : bv 32 := 0x01055793.
Lemma F_76630 : fetch_word Asan.M.loaded_segments (0x76618 : word) = Some W_76630.
Proof. vm_refl. Qed.
Lemma D_76630 : decode_any W_76630 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_76634 : bv 32 := 0x00f56533.
Lemma F_76634 : fetch_word Asan.M.loaded_segments (0x7661c : word) = Some W_76634.
Proof. vm_refl. Qed.
Lemma D_76634 : decode_any W_76634 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76638 : bv 32 := 0x02055793.
Lemma F_76638 : fetch_word Asan.M.loaded_segments (0x76620 : word) = Some W_76638.
Proof. vm_refl. Qed.
Lemma D_76638 : decode_any W_76638 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7663c : bv 32 := 0x00f56533.
Lemma F_7663c : fetch_word Asan.M.loaded_segments (0x76624 : word) = Some W_7663c.
Proof. vm_refl. Qed.
Lemma D_7663c : decode_any W_7663c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76640 : bv 32 := 0xfff54513.

End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_74f0c : bv 32 := 0x02060063.
Lemma D_74f0c : decode_any W_74f0c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f10 : bv 32 := 0x00c50633.
Lemma D_74f10 : decode_any W_74f10 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f14 : bv 32 := 0x00050693.
Lemma D_74f14 : decode_any W_74f14 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f18 : bv 32 := 0x0005c703.
Lemma D_74f18 : decode_any W_74f18 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f1c : bv 32 := 0x00e68023.
Lemma D_74f1c : decode_any W_74f1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f20 : bv 32 := 0x00168693.
Lemma D_74f20 : decode_any W_74f20 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f24 : bv 32 := 0x00158593.
Lemma D_74f24 : decode_any W_74f24 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f28 : bv 32 := 0xfec698e3.
Lemma D_74f28 : decode_any W_74f28 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f2c : bv 32 := 0x00008067.
Lemma D_74f2c : decode_any W_74f2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f88 : bv 32 := 0x00a666b3.
Lemma D_74f88 : decode_any W_74f88 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f8c : bv 32 := 0x00f6f693.
Lemma D_74f8c : decode_any W_74f8c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f90 : bv 32 := 0x02068063.
Lemma D_74f90 : decode_any W_74f90 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f94 : bv 32 := 0x04060863.
Lemma D_74f94 : decode_any W_74f94 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f98 : bv 32 := 0x00c50633.
Lemma D_74f98 : decode_any W_74f98 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_74f9c : bv 32 := 0x00050693.
Lemma D_74f9c : decode_any W_74f9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fa0 : bv 32 := 0x00b68023.
Lemma D_74fa0 : decode_any W_74fa0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fa4 : bv 32 := 0x00168693.
Lemma D_74fa4 : decode_any W_74fa4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fa8 : bv 32 := 0xfec69ce3.
Lemma D_74fa8 : decode_any W_74fa8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fac : bv 32 := 0x0380006f.
Lemma D_74fac : decode_any W_74fac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fb0 : bv 32 := 0x02060a63.
Lemma D_74fb0 : decode_any W_74fb0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fb4 : bv 32 := 0x00c50633.
Lemma D_74fb4 : decode_any W_74fb4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fb8 : bv 32 := 0x00859693.
Lemma D_74fb8 : decode_any W_74fb8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fbc : bv 32 := 0x00b6e5b3.
Lemma D_74fbc : decode_any W_74fbc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fc0 : bv 32 := 0x01059693.
Lemma D_74fc0 : decode_any W_74fc0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fc4 : bv 32 := 0x00b6e5b3.
Lemma D_74fc4 : decode_any W_74fc4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fc8 : bv 32 := 0x02059693.
Lemma D_74fc8 : decode_any W_74fc8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fcc : bv 32 := 0x00b6e5b3.
Lemma D_74fcc : decode_any W_74fcc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fd0 : bv 32 := 0x00050693.
Lemma D_74fd0 : decode_any W_74fd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fd4 : bv 32 := 0x00b6b023.
Lemma D_74fd4 : decode_any W_74fd4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fd8 : bv 32 := 0x00b6b423.
Lemma D_74fd8 : decode_any W_74fd8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fdc : bv 32 := 0x01068693.
Lemma D_74fdc : decode_any W_74fdc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fe0 : bv 32 := 0xfec6eae3.
Lemma D_74fe0 : decode_any W_74fe0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_74fe4 : bv 32 := 0x00008067.
Lemma D_74fe4 : decode_any W_74fe4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_754b8 : bv 32 := 0xff010113.
Lemma D_754b8 : decode_any W_754b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_754bc : bv 32 := 0x00113423.
Lemma D_754bc : decode_any W_754bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_754c0 : bv 32 := 0x00058693.
Lemma D_754c0 : decode_any W_754c0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_754c4 : bv 32 := 0x00100713.
Lemma D_754c4 : decode_any W_754c4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_754c8 : bv 32 := 0x02871713.
Lemma D_754c8 : decode_any W_754c8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_754cc : bv 32 := 0x00170593.
Lemma D_754cc : decode_any W_754cc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_754d0 : bv 32 := 0x08b6f263.
Lemma D_754d0 : decode_any W_754d0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_754d4 : bv 32 := 0x00000593.
Lemma D_754d4 : decode_any W_754d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_754d8 : bv 32 := 0x00d50733.
Lemma D_754d8 : decode_any W_754d8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_754dc : bv 32 := 0x00750793.
Lemma D_754dc : decode_any W_754dc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_754e0 : bv 32 := 0xff87f793.
Lemma D_754e0 : decode_any W_754e0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_754e4 : bv 32 := 0xff877613.
Lemma D_754e4 : decode_any W_754e4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_754e8 : bv 32 := 0x02f57463.
Lemma D_754e8 : decode_any W_754e8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_754ec : bv 32 := 0x02068263.
Lemma D_754ec : decode_any W_754ec = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_754f0 : bv 32 := 0x00000593.
Lemma D_754f0 : decode_any W_754f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_754f4 : bv 32 := 0x00150693.
Lemma D_754f4 : decode_any W_754f4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_754f8 : bv 32 := 0x00068813.
Lemma D_754f8 : decode_any W_754f8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_754fc : bv 32 := 0xfff6c683.
Lemma D_754fc : decode_any W_754fc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_75500 : bv 32 := 0x00d5e5b3.
Lemma D_75500 : decode_any W_75500 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_75504 : bv 32 := 0x00f87663.
Lemma D_75504 : decode_any W_75504 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_75508 : bv 32 := 0x00180693.
Lemma D_75508 : decode_any W_75508 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7550c : bv 32 := 0xfee866e3.
Lemma D_7550c : decode_any W_7550c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_75510 : bv 32 := 0x00c7fa63.
Lemma D_75510 : decode_any W_75510 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_75514 : bv 32 := 0x0007b683.
Lemma D_75514 : decode_any W_75514 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75518 : bv 32 := 0x00878793.
Lemma D_75518 : decode_any W_75518 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7551c : bv 32 := 0x00b6e5b3.
Lemma D_7551c : decode_any W_7551c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_75520 : bv 32 := 0xfec7eae3.
Lemma D_75520 : decode_any W_75520 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_75524 : bv 32 := 0x02a66063.
Lemma D_75524 : decode_any W_75524 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_75528 : bv 32 := 0x00e67e63.
Lemma D_75528 : decode_any W_75528 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7552c : bv 32 := 0x40c70733.
Lemma D_7552c : decode_any W_7552c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_75530 : bv 32 := 0x00064503.
Lemma D_75530 : decode_any W_75530 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75534 : bv 32 := 0xfff70713.
Lemma D_75534 : decode_any W_75534 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_75538 : bv 32 := 0x00a5e5b3.
Lemma D_75538 : decode_any W_75538 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7553c : bv 32 := 0x00160613.
Lemma D_7553c : decode_any W_7553c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75540 : bv 32 := 0xfe0718e3.
Lemma D_75540 : decode_any W_75540 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_75544 : bv 32 := 0x0015b513.
Lemma D_75544 : decode_any W_75544 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75548 : bv 32 := 0x00813083.
Lemma D_75548 : decode_any W_75548 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7554c : bv 32 := 0x01010113.
Lemma D_7554c : decode_any W_7554c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_75550 : bv 32 := 0x00008067.
Lemma D_75550 : decode_any W_75550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End Mq1.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_769d0 : bv 32 := 0x00155593.
Lemma F_769d0 : fetch_word AsanUbsan.M.loaded_segments (0x76990 : word) = Some W_769d0.
Proof. vm_refl. Qed.
Lemma D_769d0 : decode_any W_769d0 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_769d4 : bv 32 := 0x55555637.
Lemma F_769d4 : fetch_word AsanUbsan.M.loaded_segments (0x76994 : word) = Some W_769d4.
Proof. vm_refl. Qed.
Lemma D_769d4 : decode_any W_769d4 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_769d8 : bv 32 := 0x333336b7.
Lemma F_769d8 : fetch_word AsanUbsan.M.loaded_segments (0x76998 : word) = Some W_769d8.
Proof. vm_refl. Qed.
Lemma D_769d8 : decode_any W_769d8 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_769dc : bv 32 := 0x0f0f1737.
Lemma F_769dc : fetch_word AsanUbsan.M.loaded_segments (0x7699c : word) = Some W_769dc.
Proof. vm_refl. Qed.
Lemma D_769dc : decode_any W_769dc = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_769e0 : bv 32 := 0x010107b7.
Lemma F_769e0 : fetch_word AsanUbsan.M.loaded_segments (0x769a0 : word) = Some W_769e0.
Proof. vm_refl. Qed.
Lemma D_769e0 : decode_any W_769e0 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_769e4 : bv 32 := 0x00b56533.
Lemma F_769e4 : fetch_word AsanUbsan.M.loaded_segments (0x769a4 : word) = Some W_769e4.
Proof. vm_refl. Qed.
Lemma D_769e4 : decode_any W_769e4 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_769e8 : bv 32 := 0x5556059b.
Lemma F_769e8 : fetch_word AsanUbsan.M.loaded_segments (0x769a8 : word) = Some W_769e8.
Proof. vm_refl. Qed.
Lemma D_769e8 : decode_any W_769e8 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_769ec : bv 32 := 0x3336861b.
Lemma F_769ec : fetch_word AsanUbsan.M.loaded_segments (0x769ac : word) = Some W_769ec.
Proof. vm_refl. Qed.
Lemma D_769ec : decode_any W_769ec = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_769f0 : bv 32 := 0xf0f7069b.
Lemma F_769f0 : fetch_word AsanUbsan.M.loaded_segments (0x769b0 : word) = Some W_769f0.
Proof. vm_refl. Qed.
Lemma D_769f0 : decode_any W_769f0 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_769f4 : bv 32 := 0x1017871b.
Lemma F_769f4 : fetch_word AsanUbsan.M.loaded_segments (0x769b4 : word) = Some W_769f4.
Proof. vm_refl. Qed.
Lemma D_769f4 : decode_any W_769f4 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_769f8 : bv 32 := 0x00255793.
Lemma F_769f8 : fetch_word AsanUbsan.M.loaded_segments (0x769b8 : word) = Some W_769f8.
Proof. vm_refl. Qed.
Lemma D_769f8 : decode_any W_769f8 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_769fc : bv 32 := 0x00f56533.
Lemma F_769fc : fetch_word AsanUbsan.M.loaded_segments (0x769bc : word) = Some W_769fc.
Proof. vm_refl. Qed.
Lemma D_769fc : decode_any W_769fc = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a00 : bv 32 := 0x02059793.
Lemma F_76a00 : fetch_word AsanUbsan.M.loaded_segments (0x769c0 : word) = Some W_76a00.
Proof. vm_refl. Qed.
Lemma D_76a00 : decode_any W_76a00 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a04 : bv 32 := 0x00f585b3.
Lemma F_76a04 : fetch_word AsanUbsan.M.loaded_segments (0x769c4 : word) = Some W_76a04.
Proof. vm_refl. Qed.
Lemma D_76a04 : decode_any W_76a04 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a08 : bv 32 := 0x02061793.
Lemma F_76a08 : fetch_word AsanUbsan.M.loaded_segments (0x769c8 : word) = Some W_76a08.
Proof. vm_refl. Qed.
Lemma D_76a08 : decode_any W_76a08 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a0c : bv 32 := 0x00f60633.
Lemma F_76a0c : fetch_word AsanUbsan.M.loaded_segments (0x769cc : word) = Some W_76a0c.
Proof. vm_refl. Qed.
Lemma D_76a0c : decode_any W_76a0c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a10 : bv 32 := 0x02069793.
Lemma F_76a10 : fetch_word AsanUbsan.M.loaded_segments (0x769d0 : word) = Some W_76a10.
Proof. vm_refl. Qed.
Lemma D_76a10 : decode_any W_76a10 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a14 : bv 32 := 0x00f686b3.
Lemma F_76a14 : fetch_word AsanUbsan.M.loaded_segments (0x769d4 : word) = Some W_76a14.
Proof. vm_refl. Qed.
Lemma D_76a14 : decode_any W_76a14 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a18 : bv 32 := 0x02071793.
Lemma F_76a18 : fetch_word AsanUbsan.M.loaded_segments (0x769d8 : word) = Some W_76a18.
Proof. vm_refl. Qed.
Lemma D_76a18 : decode_any W_76a18 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a1c : bv 32 := 0x00f70733.
Lemma F_76a1c : fetch_word AsanUbsan.M.loaded_segments (0x769dc : word) = Some W_76a1c.
Proof. vm_refl. Qed.
Lemma D_76a1c : decode_any W_76a1c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a20 : bv 32 := 0x00455793.
Lemma F_76a20 : fetch_word AsanUbsan.M.loaded_segments (0x769e0 : word) = Some W_76a20.
Proof. vm_refl. Qed.
Lemma D_76a20 : decode_any W_76a20 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a24 : bv 32 := 0x00f56533.
Lemma F_76a24 : fetch_word AsanUbsan.M.loaded_segments (0x769e4 : word) = Some W_76a24.
Proof. vm_refl. Qed.
Lemma D_76a24 : decode_any W_76a24 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a28 : bv 32 := 0x00855793.
Lemma F_76a28 : fetch_word AsanUbsan.M.loaded_segments (0x769e8 : word) = Some W_76a28.
Proof. vm_refl. Qed.
Lemma D_76a28 : decode_any W_76a28 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a2c : bv 32 := 0x00f56533.
Lemma F_76a2c : fetch_word AsanUbsan.M.loaded_segments (0x769ec : word) = Some W_76a2c.
Proof. vm_refl. Qed.
Lemma D_76a2c : decode_any W_76a2c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a30 : bv 32 := 0x01055793.
Lemma F_76a30 : fetch_word AsanUbsan.M.loaded_segments (0x769f0 : word) = Some W_76a30.
Proof. vm_refl. Qed.
Lemma D_76a30 : decode_any W_76a30 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a34 : bv 32 := 0x00f56533.
Lemma F_76a34 : fetch_word AsanUbsan.M.loaded_segments (0x769f4 : word) = Some W_76a34.
Proof. vm_refl. Qed.
Lemma D_76a34 : decode_any W_76a34 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a38 : bv 32 := 0x02055793.
Lemma F_76a38 : fetch_word AsanUbsan.M.loaded_segments (0x769f8 : word) = Some W_76a38.
Proof. vm_refl. Qed.
Lemma D_76a38 : decode_any W_76a38 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a3c : bv 32 := 0x00f56533.
Lemma F_76a3c : fetch_word AsanUbsan.M.loaded_segments (0x769fc : word) = Some W_76a3c.
Proof. vm_refl. Qed.
Lemma D_76a3c : decode_any W_76a3c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_76a40 : bv 32 := 0xfff54513.

End Mq2.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_7530c : bv 32 := 0x02060063.
Lemma D_7530c : decode_any W_7530c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_75310 : bv 32 := 0x00c50633.
Lemma D_75310 : decode_any W_75310 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_75314 : bv 32 := 0x00050693.
Lemma D_75314 : decode_any W_75314 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75318 : bv 32 := 0x0005c703.
Lemma D_75318 : decode_any W_75318 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7531c : bv 32 := 0x00e68023.
Lemma D_7531c : decode_any W_7531c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75320 : bv 32 := 0x00168693.
Lemma D_75320 : decode_any W_75320 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75324 : bv 32 := 0x00158593.
Lemma D_75324 : decode_any W_75324 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75328 : bv 32 := 0xfec698e3.
Lemma D_75328 : decode_any W_75328 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7532c : bv 32 := 0x00008067.
Lemma D_7532c : decode_any W_7532c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75388 : bv 32 := 0x00a666b3.
Lemma D_75388 : decode_any W_75388 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7538c : bv 32 := 0x00f6f693.
Lemma D_7538c : decode_any W_7538c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_75390 : bv 32 := 0x02068063.
Lemma D_75390 : decode_any W_75390 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_75394 : bv 32 := 0x04060863.
Lemma D_75394 : decode_any W_75394 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_75398 : bv 32 := 0x00c50633.
Lemma D_75398 : decode_any W_75398 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7539c : bv 32 := 0x00050693.
Lemma D_7539c : decode_any W_7539c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753a0 : bv 32 := 0x00b68023.
Lemma D_753a0 : decode_any W_753a0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753a4 : bv 32 := 0x00168693.
Lemma D_753a4 : decode_any W_753a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_753a8 : bv 32 := 0xfec69ce3.
Lemma D_753a8 : decode_any W_753a8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_753ac : bv 32 := 0x0380006f.
Lemma D_753ac : decode_any W_753ac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_753b0 : bv 32 := 0x02060a63.
Lemma D_753b0 : decode_any W_753b0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_753b4 : bv 32 := 0x00c50633.
Lemma D_753b4 : decode_any W_753b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_753b8 : bv 32 := 0x00859693.
Lemma D_753b8 : decode_any W_753b8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_753bc : bv 32 := 0x00b6e5b3.
Lemma D_753bc : decode_any W_753bc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c0 : bv 32 := 0x01059693.
Lemma D_753c0 : decode_any W_753c0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c4 : bv 32 := 0x00b6e5b3.
Lemma D_753c4 : decode_any W_753c4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c8 : bv 32 := 0x02059693.
Lemma D_753c8 : decode_any W_753c8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_753cc : bv 32 := 0x00b6e5b3.
Lemma D_753cc : decode_any W_753cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d0 : bv 32 := 0x00050693.
Lemma D_753d0 : decode_any W_753d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d4 : bv 32 := 0x00b6b023.
Lemma D_753d4 : decode_any W_753d4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d8 : bv 32 := 0x00b6b423.
Lemma D_753d8 : decode_any W_753d8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_753dc : bv 32 := 0x01068693.
Lemma D_753dc : decode_any W_753dc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_753e0 : bv 32 := 0xfec6eae3.
Lemma D_753e0 : decode_any W_753e0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_753e4 : bv 32 := 0x00008067.
Lemma D_753e4 : decode_any W_753e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_758b8 : bv 32 := 0xff010113.
Lemma D_758b8 : decode_any W_758b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_758bc : bv 32 := 0x00113423.
Lemma D_758bc : decode_any W_758bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_758c0 : bv 32 := 0x00058693.
Lemma D_758c0 : decode_any W_758c0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_758c4 : bv 32 := 0x00100713.
Lemma D_758c4 : decode_any W_758c4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_758c8 : bv 32 := 0x02871713.
Lemma D_758c8 : decode_any W_758c8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_758cc : bv 32 := 0x00170593.
Lemma D_758cc : decode_any W_758cc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_758d0 : bv 32 := 0x08b6f263.
Lemma D_758d0 : decode_any W_758d0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_758d4 : bv 32 := 0x00000593.
Lemma D_758d4 : decode_any W_758d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_758d8 : bv 32 := 0x00d50733.
Lemma D_758d8 : decode_any W_758d8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_758dc : bv 32 := 0x00750793.
Lemma D_758dc : decode_any W_758dc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_758e0 : bv 32 := 0xff87f793.
Lemma D_758e0 : decode_any W_758e0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_758e4 : bv 32 := 0xff877613.
Lemma D_758e4 : decode_any W_758e4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_758e8 : bv 32 := 0x02f57463.
Lemma D_758e8 : decode_any W_758e8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_758ec : bv 32 := 0x02068263.
Lemma D_758ec : decode_any W_758ec = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_758f0 : bv 32 := 0x00000593.
Lemma D_758f0 : decode_any W_758f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_758f4 : bv 32 := 0x00150693.
Lemma D_758f4 : decode_any W_758f4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_758f8 : bv 32 := 0x00068813.
Lemma D_758f8 : decode_any W_758f8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_758fc : bv 32 := 0xfff6c683.
Lemma D_758fc : decode_any W_758fc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_75900 : bv 32 := 0x00d5e5b3.
Lemma D_75900 : decode_any W_75900 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_75904 : bv 32 := 0x00f87663.
Lemma D_75904 : decode_any W_75904 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_75908 : bv 32 := 0x00180693.
Lemma D_75908 : decode_any W_75908 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7590c : bv 32 := 0xfee866e3.
Lemma D_7590c : decode_any W_7590c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_75910 : bv 32 := 0x00c7fa63.
Lemma D_75910 : decode_any W_75910 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_75914 : bv 32 := 0x0007b683.
Lemma D_75914 : decode_any W_75914 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75918 : bv 32 := 0x00878793.
Lemma D_75918 : decode_any W_75918 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7591c : bv 32 := 0x00b6e5b3.
Lemma D_7591c : decode_any W_7591c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_75920 : bv 32 := 0xfec7eae3.
Lemma D_75920 : decode_any W_75920 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_75924 : bv 32 := 0x02a66063.
Lemma D_75924 : decode_any W_75924 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_75928 : bv 32 := 0x00e67e63.
Lemma D_75928 : decode_any W_75928 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7592c : bv 32 := 0x40c70733.
Lemma D_7592c : decode_any W_7592c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_75930 : bv 32 := 0x00064503.
Lemma D_75930 : decode_any W_75930 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_75934 : bv 32 := 0xfff70713.
Lemma D_75934 : decode_any W_75934 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_75938 : bv 32 := 0x00a5e5b3.
Lemma D_75938 : decode_any W_75938 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7593c : bv 32 := 0x00160613.
Lemma D_7593c : decode_any W_7593c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75940 : bv 32 := 0xfe0718e3.
Lemma D_75940 : decode_any W_75940 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_75944 : bv 32 := 0x0015b513.
Lemma D_75944 : decode_any W_75944 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75948 : bv 32 := 0x00813083.
Lemma D_75948 : decode_any W_75948 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7594c : bv 32 := 0x01010113.
Lemma D_7594c : decode_any W_7594c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_75950 : bv 32 := 0x00008067.
Lemma D_75950 : decode_any W_75950 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
