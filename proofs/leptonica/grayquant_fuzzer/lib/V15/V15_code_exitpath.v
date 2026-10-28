(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushU15.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14df0 : bv 32 := 0xffffe517.
Lemma F_14df0 : fetch_word Ubsan.M.loaded_segments (0x14df0 : word) = Some W_14df0.
Proof. vm_refl. Qed.
Lemma D_14df0 : decode_any W_14df0 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14df4 : bv 32 := 0xb5850513.
Lemma F_14df4 : fetch_word Ubsan.M.loaded_segments (0x14df4 : word) = Some W_14df4.
Proof. vm_refl. Qed.
Lemma D_14df4 : decode_any W_14df4 = Some (OpImm ALU_ADD 10 10 2904, 4%Z).
Proof. vm_refl. Qed.

Definition W_14df8 : bv 32 := 0x00020597.
Lemma F_14df8 : fetch_word Ubsan.M.loaded_segments (0x14df8 : word) = Some W_14df8.
Proof. vm_refl. Qed.
Lemma D_14df8 : decode_any W_14df8 = Some (Auipc 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14dfc : bv 32 := 0x68058593.
Lemma F_14dfc : fetch_word Ubsan.M.loaded_segments (0x14dfc : word) = Some W_14dfc.
Proof. vm_refl. Qed.
Lemma D_14dfc : decode_any W_14dfc = Some (OpImm ALU_ADD 11 11 1664, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e00 : bv 32 := 0x000000ef.
Lemma F_14e00 : fetch_word Ubsan.M.loaded_segments (0x14e00 : word) = Some W_14e00.
Proof. vm_refl. Qed.
Lemma D_14e00 : decode_any W_14e00 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e04 : bv 32 := 0x0040006f.
Lemma F_14e04 : fetch_word Ubsan.M.loaded_segments (0x14e04 : word) = Some W_14e04.
Proof. vm_refl. Qed.
Lemma D_14e04 : decode_any W_14e04 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e08 : bv 32 := 0x00813083.
Lemma F_14e08 : fetch_word Ubsan.M.loaded_segments (0x14e08 : word) = Some W_14e08.
Proof. vm_refl. Qed.
Lemma D_14e08 : decode_any W_14e08 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e0c : bv 32 := 0x00013403.
Lemma F_14e0c : fetch_word Ubsan.M.loaded_segments (0x14e0c : word) = Some W_14e0c.
Proof. vm_refl. Qed.
Lemma D_14e0c : decode_any W_14e0c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e10 : bv 32 := 0x01010113.
Lemma F_14e10 : fetch_word Ubsan.M.loaded_segments (0x14e10 : word) = Some W_14e10.
Proof. vm_refl. Qed.
Lemma D_14e10 : decode_any W_14e10 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e14 : bv 32 := 0x00008067.
Lemma F_14e14 : fetch_word Ubsan.M.loaded_segments (0x14e14 : word) = Some W_14e14.
Proof. vm_refl. Qed.
Lemma D_14e14 : decode_any W_14e14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e18 : bv 32 := 0xff010113.
Lemma F_14e18 : fetch_word Ubsan.M.loaded_segments (0x14e18 : word) = Some W_14e18.
Proof. vm_refl. Qed.
Lemma D_14e18 : decode_any W_14e18 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e1c : bv 32 := 0x00113423.
Lemma F_14e1c : fetch_word Ubsan.M.loaded_segments (0x14e1c : word) = Some W_14e1c.
Proof. vm_refl. Qed.
Lemma D_14e1c : decode_any W_14e1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e20 : bv 32 := 0x00813023.
Lemma F_14e20 : fetch_word Ubsan.M.loaded_segments (0x14e20 : word) = Some W_14e20.
Proof. vm_refl. Qed.
Lemma D_14e20 : decode_any W_14e20 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e24 : bv 32 := 0x01010413.
Lemma F_14e24 : fetch_word Ubsan.M.loaded_segments (0x14e24 : word) = Some W_14e24.
Proof. vm_refl. Qed.
Lemma D_14e24 : decode_any W_14e24 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e28 : bv 32 := 0x00020517.
Lemma F_14e28 : fetch_word Ubsan.M.loaded_segments (0x14e28 : word) = Some W_14e28.
Proof. vm_refl. Qed.
Lemma D_14e28 : decode_any W_14e28 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e2c : bv 32 := 0x69050513.
Lemma F_14e2c : fetch_word Ubsan.M.loaded_segments (0x14e2c : word) = Some W_14e2c.
Proof. vm_refl. Qed.
Lemma D_14e2c : decode_any W_14e2c = Some (OpImm ALU_ADD 10 10 1680, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e30 : bv 32 := 0x00054503.
Lemma F_14e30 : fetch_word Ubsan.M.loaded_segments (0x14e30 : word) = Some W_14e30.
Proof. vm_refl. Qed.
Lemma D_14e30 : decode_any W_14e30 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e34 : bv 32 := 0x00157513.
Lemma F_14e34 : fetch_word Ubsan.M.loaded_segments (0x14e34 : word) = Some W_14e34.
Proof. vm_refl. Qed.
Lemma D_14e34 : decode_any W_14e34 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e38 : bv 32 := 0x00050663.
Lemma F_14e38 : fetch_word Ubsan.M.loaded_segments (0x14e38 : word) = Some W_14e38.
Proof. vm_refl. Qed.
Lemma D_14e38 : decode_any W_14e38 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e3c : bv 32 := 0x0040006f.
Lemma F_14e3c : fetch_word Ubsan.M.loaded_segments (0x14e3c : word) = Some W_14e3c.
Proof. vm_refl. Qed.
Lemma D_14e3c : decode_any W_14e3c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e40 : bv 32 := 0x0580006f.
Lemma F_14e40 : fetch_word Ubsan.M.loaded_segments (0x14e40 : word) = Some W_14e40.
Proof. vm_refl. Qed.
Lemma D_14e40 : decode_any W_14e40 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e44 : bv 32 := 0x00020517.
Lemma F_14e44 : fetch_word Ubsan.M.loaded_segments (0x14e44 : word) = Some W_14e44.
Proof. vm_refl. Qed.
Lemma D_14e44 : decode_any W_14e44 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e48 : bv 32 := 0x67450593.
Lemma F_14e48 : fetch_word Ubsan.M.loaded_segments (0x14e48 : word) = Some W_14e48.
Proof. vm_refl. Qed.
Lemma D_14e48 : decode_any W_14e48 = Some (OpImm ALU_ADD 11 10 1652, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e4c : bv 32 := 0x00100513.
Lemma F_14e4c : fetch_word Ubsan.M.loaded_segments (0x14e4c : word) = Some W_14e4c.
Proof. vm_refl. Qed.
Lemma D_14e4c : decode_any W_14e4c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e50 : bv 32 := 0x00a58023.
Lemma F_14e50 : fetch_word Ubsan.M.loaded_segments (0x14e50 : word) = Some W_14e50.
Proof. vm_refl. Qed.
Lemma D_14e50 : decode_any W_14e50 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e54 : bv 32 := 0x0001f517.
Lemma F_14e54 : fetch_word Ubsan.M.loaded_segments (0x14e54 : word) = Some W_14e54.
Proof. vm_refl. Qed.
Lemma D_14e54 : decode_any W_14e54 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e58 : bv 32 := 0x37c53503.
Lemma F_14e58 : fetch_word Ubsan.M.loaded_segments (0x14e58 : word) = Some W_14e58.
Proof. vm_refl. Qed.
Lemma D_14e58 : decode_any W_14e58 = Some (Load SZ8 true 10 10 892, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e5c : bv 32 := 0x00050e63.
Lemma F_14e5c : fetch_word Ubsan.M.loaded_segments (0x14e5c : word) = Some W_14e5c.
Proof. vm_refl. Qed.
Lemma D_14e5c : decode_any W_14e5c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e60 : bv 32 := 0x0040006f.
Lemma F_14e60 : fetch_word Ubsan.M.loaded_segments (0x14e60 : word) = Some W_14e60.
Proof. vm_refl. Qed.
Lemma D_14e60 : decode_any W_14e60 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e64 : bv 32 := 0x00020517.
Lemma F_14e64 : fetch_word Ubsan.M.loaded_segments (0x14e64 : word) = Some W_14e64.
Proof. vm_refl. Qed.
Lemma D_14e64 : decode_any W_14e64 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e68 : bv 32 := 0x3dc50513.
Lemma F_14e68 : fetch_word Ubsan.M.loaded_segments (0x14e68 : word) = Some W_14e68.
Proof. vm_refl. Qed.
Lemma D_14e68 : decode_any W_14e68 = Some (OpImm ALU_ADD 10 10 988, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e6c : bv 32 := 0x00053503.
Lemma F_14e6c : fetch_word Ubsan.M.loaded_segments (0x14e6c : word) = Some W_14e6c.
Proof. vm_refl. Qed.
Lemma D_14e6c : decode_any W_14e6c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e70 : bv 32 := 0x790130ef.
Lemma F_14e70 : fetch_word Ubsan.M.loaded_segments (0x14e70 : word) = Some W_14e70.
Proof. vm_refl. Qed.
Lemma D_14e70 : decode_any W_14e70 = Some (Jal 1 79760, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e74 : bv 32 := 0x0040006f.
Lemma F_14e74 : fetch_word Ubsan.M.loaded_segments (0x14e74 : word) = Some W_14e74.
Proof. vm_refl. Qed.
Lemma D_14e74 : decode_any W_14e74 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e78 : bv 32 := 0x0001f517.
Lemma F_14e78 : fetch_word Ubsan.M.loaded_segments (0x14e78 : word) = Some W_14e78.
Proof. vm_refl. Qed.
Lemma D_14e78 : decode_any W_14e78 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e7c : bv 32 := 0x36053503.
Lemma F_14e7c : fetch_word Ubsan.M.loaded_segments (0x14e7c : word) = Some W_14e7c.
Proof. vm_refl. Qed.
Lemma D_14e7c : decode_any W_14e7c = Some (Load SZ8 true 10 10 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e80 : bv 32 := 0x00050c63.
Lemma F_14e80 : fetch_word Ubsan.M.loaded_segments (0x14e80 : word) = Some W_14e80.
Proof. vm_refl. Qed.
Lemma D_14e80 : decode_any W_14e80 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e84 : bv 32 := 0x0040006f.
Lemma F_14e84 : fetch_word Ubsan.M.loaded_segments (0x14e84 : word) = Some W_14e84.
Proof. vm_refl. Qed.
Lemma D_14e84 : decode_any W_14e84 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e88 : bv 32 := 0xffffe517.
Lemma F_14e88 : fetch_word Ubsan.M.loaded_segments (0x14e88 : word) = Some W_14e88.
Proof. vm_refl. Qed.
Lemma D_14e88 : decode_any W_14e88 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e8c : bv 32 := 0xac050513.
Lemma F_14e8c : fetch_word Ubsan.M.loaded_segments (0x14e8c : word) = Some W_14e8c.
Proof. vm_refl. Qed.
Lemma D_14e8c : decode_any W_14e8c = Some (OpImm ALU_ADD 10 10 2752, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e90 : bv 32 := 0x000000ef.
Lemma F_14e90 : fetch_word Ubsan.M.loaded_segments (0x14e90 : word) = Some W_14e90.
Proof. vm_refl. Qed.
Lemma D_14e90 : decode_any W_14e90 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e94 : bv 32 := 0x0040006f.
Lemma F_14e94 : fetch_word Ubsan.M.loaded_segments (0x14e94 : word) = Some W_14e94.
Proof. vm_refl. Qed.
Lemma D_14e94 : decode_any W_14e94 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e98 : bv 32 := 0x00813083.
Lemma F_14e98 : fetch_word Ubsan.M.loaded_segments (0x14e98 : word) = Some W_14e98.
Proof. vm_refl. Qed.
Lemma D_14e98 : decode_any W_14e98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e9c : bv 32 := 0x00013403.
Lemma F_14e9c : fetch_word Ubsan.M.loaded_segments (0x14e9c : word) = Some W_14e9c.
Proof. vm_refl. Qed.
Lemma D_14e9c : decode_any W_14e9c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ea0 : bv 32 := 0x01010113.
Lemma F_14ea0 : fetch_word Ubsan.M.loaded_segments (0x14ea0 : word) = Some W_14ea0.
Proof. vm_refl. Qed.
Lemma D_14ea0 : decode_any W_14ea0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ea4 : bv 32 := 0x00008067.
Lemma F_14ea4 : fetch_word Ubsan.M.loaded_segments (0x14ea4 : word) = Some W_14ea4.
Proof. vm_refl. Qed.
Lemma D_14ea4 : decode_any W_14ea4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d0 : bv 32 := 0x00030517.
Lemma F_152d0 : fetch_word Ubsan.M.loaded_segments (0x152d0 : word) = Some W_152d0.
Proof. vm_refl. Qed.
Lemma D_152d0 : decode_any W_152d0 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d4 : bv 32 := 0x1f454503.
Lemma F_152d4 : fetch_word Ubsan.M.loaded_segments (0x152d4 : word) = Some W_152d4.
Proof. vm_refl. Qed.
Lemma D_152d4 : decode_any W_152d4 = Some (Load SZ1 false 10 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d8 : bv 32 := 0x00051463.
Lemma F_152d8 : fetch_word Ubsan.M.loaded_segments (0x152d8 : word) = Some W_152d8.
Proof. vm_refl. Qed.
Lemma D_152d8 : decode_any W_152d8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_152dc : bv 32 := 0x00008067.
Lemma F_152dc : fetch_word Ubsan.M.loaded_segments (0x152dc : word) = Some W_152dc.
Proof. vm_refl. Qed.
Lemma D_152dc : decode_any W_152dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e0 : bv 32 := 0xff010113.
Lemma F_152e0 : fetch_word Ubsan.M.loaded_segments (0x152e0 : word) = Some W_152e0.
Proof. vm_refl. Qed.
Lemma D_152e0 : decode_any W_152e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e4 : bv 32 := 0x00113423.
Lemma F_152e4 : fetch_word Ubsan.M.loaded_segments (0x152e4 : word) = Some W_152e4.
Proof. vm_refl. Qed.
Lemma D_152e4 : decode_any W_152e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e8 : bv 32 := 0x0001f517.
Lemma F_152e8 : fetch_word Ubsan.M.loaded_segments (0x152e8 : word) = Some W_152e8.
Proof. vm_refl. Qed.
Lemma D_152e8 : decode_any W_152e8 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_152ec : bv 32 := 0xf0853503.
Lemma F_152ec : fetch_word Ubsan.M.loaded_segments (0x152ec : word) = Some W_152ec.
Proof. vm_refl. Qed.
Lemma D_152ec : decode_any W_152ec = Some (Load SZ8 true 10 10 3848, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f0 : bv 32 := 0x00053503.
Lemma F_152f0 : fetch_word Ubsan.M.loaded_segments (0x152f0 : word) = Some W_152f0.
Proof. vm_refl. Qed.
Lemma D_152f0 : decode_any W_152f0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f4 : bv 32 := 0x480150ef.
Lemma F_152f4 : fetch_word Ubsan.M.loaded_segments (0x152f4 : word) = Some W_152f4.
Proof. vm_refl. Qed.
Lemma D_152f4 : decode_any W_152f4 = Some (Jal 1 87168, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f8 : bv 32 := 0x04d00513.
Lemma F_152f8 : fetch_word Ubsan.M.loaded_segments (0x152f8 : word) = Some W_152f8.
Proof. vm_refl. Qed.
Lemma D_152f8 : decode_any W_152f8 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_152fc : bv 32 := 0x5e51d0ef.
Lemma F_152fc : fetch_word Ubsan.M.loaded_segments (0x152fc : word) = Some W_152fc.
Proof. vm_refl. Qed.
Lemma D_152fc : decode_any W_152fc = Some (Jal 1 122340, 4%Z).
Proof. vm_refl. Qed.

Definition W_28538 : bv 32 := 0xfd010113.
Lemma F_28538 : fetch_word Ubsan.M.loaded_segments (0x28538 : word) = Some W_28538.
Proof. vm_refl. Qed.
Lemma D_28538 : decode_any W_28538 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_2853c : bv 32 := 0x02113423.
Lemma F_2853c : fetch_word Ubsan.M.loaded_segments (0x2853c : word) = Some W_2853c.
Proof. vm_refl. Qed.
Lemma D_2853c : decode_any W_2853c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_28540 : bv 32 := 0x02813023.
Lemma F_28540 : fetch_word Ubsan.M.loaded_segments (0x28540 : word) = Some W_28540.
Proof. vm_refl. Qed.
Lemma D_28540 : decode_any W_28540 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28544 : bv 32 := 0x00913c23.
Lemma F_28544 : fetch_word Ubsan.M.loaded_segments (0x28544 : word) = Some W_28544.
Proof. vm_refl. Qed.
Lemma D_28544 : decode_any W_28544 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_28548 : bv 32 := 0x01213823.
Lemma F_28548 : fetch_word Ubsan.M.loaded_segments (0x28548 : word) = Some W_28548.
Proof. vm_refl. Qed.
Lemma D_28548 : decode_any W_28548 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2854c : bv 32 := 0x01313423.
Lemma F_2854c : fetch_word Ubsan.M.loaded_segments (0x2854c : word) = Some W_2854c.
Proof. vm_refl. Qed.
Lemma D_2854c : decode_any W_2854c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28550 : bv 32 := 0x0003d517.
Lemma F_28550 : fetch_word Ubsan.M.loaded_segments (0x28550 : word) = Some W_28550.
Proof. vm_refl. Qed.
Lemma D_28550 : decode_any W_28550 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_28554 : bv 32 := 0x0b050913.
Lemma F_28554 : fetch_word Ubsan.M.loaded_segments (0x28554 : word) = Some W_28554.
Proof. vm_refl. Qed.
Lemma D_28554 : decode_any W_28554 = Some (OpImm ALU_ADD 18 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_28558 : bv 32 := 0x00490413.
Lemma F_28558 : fetch_word Ubsan.M.loaded_segments (0x28558 : word) = Some W_28558.
Proof. vm_refl. Qed.
Lemma D_28558 : decode_any W_28558 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2855c : bv 32 := 0x00040513.
Lemma F_2855c : fetch_word Ubsan.M.loaded_segments (0x2855c : word) = Some W_2855c.
Proof. vm_refl. Qed.
Lemma D_2855c : decode_any W_2855c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28560 : bv 32 := 0x0510a0ef.
Lemma F_28560 : fetch_word Ubsan.M.loaded_segments (0x28560 : word) = Some W_28560.
Proof. vm_refl. Qed.
Lemma D_28560 : decode_any W_28560 = Some (Jal 1 43088, 4%Z).
Proof. vm_refl. Qed.

Definition W_28564 : bv 32 := 0x01093503.
Lemma F_28564 : fetch_word Ubsan.M.loaded_segments (0x28564 : word) = Some W_28564.
Proof. vm_refl. Qed.
Lemma D_28564 : decode_any W_28564 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28568 : bv 32 := 0x06050863.
Lemma F_28568 : fetch_word Ubsan.M.loaded_segments (0x28568 : word) = Some W_28568.
Proof. vm_refl. Qed.
Lemma D_28568 : decode_any W_28568 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_2856c : bv 32 := 0x00892583.
Lemma F_2856c : fetch_word Ubsan.M.loaded_segments (0x2856c : word) = Some W_2856c.
Proof. vm_refl. Qed.
Lemma D_2856c : decode_any W_2856c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28570 : bv 32 := 0x0180006f.
Lemma F_28570 : fetch_word Ubsan.M.loaded_segments (0x28570 : word) = Some W_28570.
Proof. vm_refl. Qed.
Lemma D_28570 : decode_any W_28570 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_28574 : bv 32 := 0x00053503.
Lemma F_28574 : fetch_word Ubsan.M.loaded_segments (0x28574 : word) = Some W_28574.
Proof. vm_refl. Qed.
Lemma D_28574 : decode_any W_28574 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28578 : bv 32 := 0x02000593.
Lemma F_28578 : fetch_word Ubsan.M.loaded_segments (0x28578 : word) = Some W_28578.
Proof. vm_refl. Qed.
Lemma D_28578 : decode_any W_28578 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_2857c : bv 32 := 0x00b92423.
Lemma F_2857c : fetch_word Ubsan.M.loaded_segments (0x2857c : word) = Some W_2857c.
Proof. vm_refl. Qed.
Lemma D_2857c : decode_any W_2857c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28580 : bv 32 := 0x00a93823.
Lemma F_28580 : fetch_word Ubsan.M.loaded_segments (0x28580 : word) = Some W_28580.
Proof. vm_refl. Qed.
Lemma D_28580 : decode_any W_28580 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28584 : bv 32 := 0x04050a63.
Lemma F_28584 : fetch_word Ubsan.M.loaded_segments (0x28584 : word) = Some W_28584.
Proof. vm_refl. Qed.
Lemma D_28584 : decode_any W_28584 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_28588 : bv 32 := 0xfff5861b.
Lemma F_28588 : fetch_word Ubsan.M.loaded_segments (0x28588 : word) = Some W_28588.
Proof. vm_refl. Qed.
Lemma D_28588 : decode_any W_28588 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2858c : bv 32 := 0x00c92423.
Lemma F_2858c : fetch_word Ubsan.M.loaded_segments (0x2858c : word) = Some W_2858c.
Proof. vm_refl. Qed.
Lemma D_2858c : decode_any W_2858c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28590 : bv 32 := 0xfeb052e3.
Lemma F_28590 : fetch_word Ubsan.M.loaded_segments (0x28590 : word) = Some W_28590.
Proof. vm_refl. Qed.
Lemma D_28590 : decode_any W_28590 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_28594 : bv 32 := 0x01093503.
Lemma F_28594 : fetch_word Ubsan.M.loaded_segments (0x28594 : word) = Some W_28594.
Proof. vm_refl. Qed.
Lemma D_28594 : decode_any W_28594 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28598 : bv 32 := 0x00361613.
Lemma F_28598 : fetch_word Ubsan.M.loaded_segments (0x28598 : word) = Some W_28598.
Proof. vm_refl. Qed.
Lemma D_28598 : decode_any W_28598 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_2859c : bv 32 := 0x00c50533.
Lemma F_2859c : fetch_word Ubsan.M.loaded_segments (0x2859c : word) = Some W_2859c.
Proof. vm_refl. Qed.
Lemma D_2859c : decode_any W_2859c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a0 : bv 32 := 0x00853983.
Lemma F_285a0 : fetch_word Ubsan.M.loaded_segments (0x285a0 : word) = Some W_285a0.
Proof. vm_refl. Qed.
Lemma D_285a0 : decode_any W_285a0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a4 : bv 32 := 0x10853483.
Lemma F_285a4 : fetch_word Ubsan.M.loaded_segments (0x285a4 : word) = Some W_285a4.
Proof. vm_refl. Qed.
Lemma D_285a4 : decode_any W_285a4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_285a8 : bv 32 := 0x00040513.
Lemma F_285a8 : fetch_word Ubsan.M.loaded_segments (0x285a8 : word) = Some W_285a8.
Proof. vm_refl. Qed.
Lemma D_285a8 : decode_any W_285a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285ac : bv 32 := 0x28d0a0ef.
Lemma F_285ac : fetch_word Ubsan.M.loaded_segments (0x285ac : word) = Some W_285ac.
Proof. vm_refl. Qed.
Lemma D_285ac : decode_any W_285ac = Some (Jal 1 43660, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b0 : bv 32 := 0x00048513.
Lemma F_285b0 : fetch_word Ubsan.M.loaded_segments (0x285b0 : word) = Some W_285b0.
Proof. vm_refl. Qed.
Lemma D_285b0 : decode_any W_285b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b4 : bv 32 := 0x000980e7.
Lemma F_285b4 : fetch_word Ubsan.M.loaded_segments (0x285b4 : word) = Some W_285b4.
Proof. vm_refl. Qed.
Lemma D_285b4 : decode_any W_285b4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285b8 : bv 32 := 0x00040513.
Lemma F_285b8 : fetch_word Ubsan.M.loaded_segments (0x285b8 : word) = Some W_285b8.
Proof. vm_refl. Qed.
Lemma D_285b8 : decode_any W_285b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285bc : bv 32 := 0x7f40a0ef.
Lemma F_285bc : fetch_word Ubsan.M.loaded_segments (0x285bc : word) = Some W_285bc.
Proof. vm_refl. Qed.
Lemma D_285bc : decode_any W_285bc = Some (Jal 1 42996, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c0 : bv 32 := 0x00892503.
Lemma F_285c0 : fetch_word Ubsan.M.loaded_segments (0x285c0 : word) = Some W_285c0.
Proof. vm_refl. Qed.
Lemma D_285c0 : decode_any W_285c0 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c4 : bv 32 := 0xfff5061b.
Lemma F_285c4 : fetch_word Ubsan.M.loaded_segments (0x285c4 : word) = Some W_285c4.
Proof. vm_refl. Qed.
Lemma D_285c4 : decode_any W_285c4 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_285c8 : bv 32 := 0x00c92423.
Lemma F_285c8 : fetch_word Ubsan.M.loaded_segments (0x285c8 : word) = Some W_285c8.
Proof. vm_refl. Qed.
Lemma D_285c8 : decode_any W_285c8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285cc : bv 32 := 0xfca044e3.
Lemma F_285cc : fetch_word Ubsan.M.loaded_segments (0x285cc : word) = Some W_285cc.
Proof. vm_refl. Qed.
Lemma D_285cc : decode_any W_285cc = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d0 : bv 32 := 0x01093503.
Lemma F_285d0 : fetch_word Ubsan.M.loaded_segments (0x285d0 : word) = Some W_285d0.
Proof. vm_refl. Qed.
Lemma D_285d0 : decode_any W_285d0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d4 : bv 32 := 0xfa1ff06f.
Lemma F_285d4 : fetch_word Ubsan.M.loaded_segments (0x285d4 : word) = Some W_285d4.
Proof. vm_refl. Qed.
Lemma D_285d4 : decode_any W_285d4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_285d8 : bv 32 := 0x00100513.
Lemma F_285d8 : fetch_word Ubsan.M.loaded_segments (0x285d8 : word) = Some W_285d8.
Proof. vm_refl. Qed.
Lemma D_285d8 : decode_any W_285d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_285dc : bv 32 := 0x00a90023.
Lemma F_285dc : fetch_word Ubsan.M.loaded_segments (0x285dc : word) = Some W_285dc.
Proof. vm_refl. Qed.
Lemma D_285dc : decode_any W_285dc = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e0 : bv 32 := 0x00040513.
Lemma F_285e0 : fetch_word Ubsan.M.loaded_segments (0x285e0 : word) = Some W_285e0.
Proof. vm_refl. Qed.
Lemma D_285e0 : decode_any W_285e0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e4 : bv 32 := 0x02813083.
Lemma F_285e4 : fetch_word Ubsan.M.loaded_segments (0x285e4 : word) = Some W_285e4.
Proof. vm_refl. Qed.
Lemma D_285e4 : decode_any W_285e4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_285e8 : bv 32 := 0x02013403.
Lemma F_285e8 : fetch_word Ubsan.M.loaded_segments (0x285e8 : word) = Some W_285e8.
Proof. vm_refl. Qed.
Lemma D_285e8 : decode_any W_285e8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_285ec : bv 32 := 0x01813483.
Lemma F_285ec : fetch_word Ubsan.M.loaded_segments (0x285ec : word) = Some W_285ec.
Proof. vm_refl. Qed.
Lemma D_285ec : decode_any W_285ec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f0 : bv 32 := 0x01013903.
Lemma F_285f0 : fetch_word Ubsan.M.loaded_segments (0x285f0 : word) = Some W_285f0.
Proof. vm_refl. Qed.
Lemma D_285f0 : decode_any W_285f0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f4 : bv 32 := 0x00813983.
Lemma F_285f4 : fetch_word Ubsan.M.loaded_segments (0x285f4 : word) = Some W_285f4.
Proof. vm_refl. Qed.
Lemma D_285f4 : decode_any W_285f4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_285f8 : bv 32 := 0x03010113.
Lemma F_285f8 : fetch_word Ubsan.M.loaded_segments (0x285f8 : word) = Some W_285f8.
Proof. vm_refl. Qed.
Lemma D_285f8 : decode_any W_285f8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_285fc : bv 32 := 0x23d0a06f.
Lemma F_285fc : fetch_word Ubsan.M.loaded_segments (0x285fc : word) = Some W_285fc.
Proof. vm_refl. Qed.
Lemma D_285fc : decode_any W_285fc = Some (Jal 0 43580, 4%Z).
Proof. vm_refl. Qed.

Definition W_28600 : bv 32 := 0x00008067.
Lemma F_28600 : fetch_word Ubsan.M.loaded_segments (0x28600 : word) = Some W_28600.
Proof. vm_refl. Qed.
Lemma D_28600 : decode_any W_28600 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28604 : bv 32 := 0xfd010113.
Lemma F_28604 : fetch_word Ubsan.M.loaded_segments (0x28604 : word) = Some W_28604.
Proof. vm_refl. Qed.
Lemma D_28604 : decode_any W_28604 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_28608 : bv 32 := 0x02113423.
Lemma F_28608 : fetch_word Ubsan.M.loaded_segments (0x28608 : word) = Some W_28608.
Proof. vm_refl. Qed.
Lemma D_28608 : decode_any W_28608 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_2860c : bv 32 := 0x02813023.
Lemma F_2860c : fetch_word Ubsan.M.loaded_segments (0x2860c : word) = Some W_2860c.
Proof. vm_refl. Qed.
Lemma D_2860c : decode_any W_2860c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28610 : bv 32 := 0x00913c23.
Lemma F_28610 : fetch_word Ubsan.M.loaded_segments (0x28610 : word) = Some W_28610.
Proof. vm_refl. Qed.
Lemma D_28610 : decode_any W_28610 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_28614 : bv 32 := 0x01213823.
Lemma F_28614 : fetch_word Ubsan.M.loaded_segments (0x28614 : word) = Some W_28614.
Proof. vm_refl. Qed.
Lemma D_28614 : decode_any W_28614 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28618 : bv 32 := 0x01313423.
Lemma F_28618 : fetch_word Ubsan.M.loaded_segments (0x28618 : word) = Some W_28618.
Proof. vm_refl. Qed.
Lemma D_28618 : decode_any W_28618 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2861c : bv 32 := 0x00050493.
Lemma F_2861c : fetch_word Ubsan.M.loaded_segments (0x2861c : word) = Some W_2861c.
Proof. vm_refl. Qed.
Lemma D_2861c : decode_any W_2861c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28620 : bv 32 := 0x0003d517.
Lemma F_28620 : fetch_word Ubsan.M.loaded_segments (0x28620 : word) = Some W_28620.
Proof. vm_refl. Qed.
Lemma D_28620 : decode_any W_28620 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_28624 : bv 32 := 0xfe050993.
Lemma F_28624 : fetch_word Ubsan.M.loaded_segments (0x28624 : word) = Some W_28624.
Proof. vm_refl. Qed.
Lemma D_28624 : decode_any W_28624 = Some (OpImm ALU_ADD 19 10 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_28628 : bv 32 := 0x00498413.
Lemma F_28628 : fetch_word Ubsan.M.loaded_segments (0x28628 : word) = Some W_28628.
Proof. vm_refl. Qed.
Lemma D_28628 : decode_any W_28628 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2862c : bv 32 := 0x00040513.
Lemma F_2862c : fetch_word Ubsan.M.loaded_segments (0x2862c : word) = Some W_2862c.
Proof. vm_refl. Qed.
Lemma D_2862c : decode_any W_2862c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28630 : bv 32 := 0x7800a0ef.
Lemma F_28630 : fetch_word Ubsan.M.loaded_segments (0x28630 : word) = Some W_28630.
Proof. vm_refl. Qed.
Lemma D_28630 : decode_any W_28630 = Some (Jal 1 42880, 4%Z).
Proof. vm_refl. Qed.

Definition W_28634 : bv 32 := 0x0009c503.
Lemma F_28634 : fetch_word Ubsan.M.loaded_segments (0x28634 : word) = Some W_28634.
Proof. vm_refl. Qed.
Lemma D_28634 : decode_any W_28634 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28638 : bv 32 := 0xfff00913.
Lemma F_28638 : fetch_word Ubsan.M.loaded_segments (0x28638 : word) = Some W_28638.
Proof. vm_refl. Qed.
Lemma D_28638 : decode_any W_28638 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2863c : bv 32 := 0x06051263.
Lemma F_2863c : fetch_word Ubsan.M.loaded_segments (0x2863c : word) = Some W_2863c.
Proof. vm_refl. Qed.
Lemma D_2863c : decode_any W_2863c = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_28640 : bv 32 := 0x0109b503.
Lemma F_28640 : fetch_word Ubsan.M.loaded_segments (0x28640 : word) = Some W_28640.
Proof. vm_refl. Qed.
Lemma D_28640 : decode_any W_28640 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28644 : bv 32 := 0x00051663.
Lemma F_28644 : fetch_word Ubsan.M.loaded_segments (0x28644 : word) = Some W_28644.
Proof. vm_refl. Qed.
Lemma D_28644 : decode_any W_28644 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28648 : bv 32 := 0x01898513.
Lemma F_28648 : fetch_word Ubsan.M.loaded_segments (0x28648 : word) = Some W_28648.
Proof. vm_refl. Qed.
Lemma D_28648 : decode_any W_28648 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2864c : bv 32 := 0x00a9b823.
Lemma F_2864c : fetch_word Ubsan.M.loaded_segments (0x2864c : word) = Some W_2864c.
Proof. vm_refl. Qed.
Lemma D_2864c : decode_any W_2864c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28650 : bv 32 := 0x0089a583.
Lemma F_28650 : fetch_word Ubsan.M.loaded_segments (0x28650 : word) = Some W_28650.
Proof. vm_refl. Qed.
Lemma D_28650 : decode_any W_28650 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28654 : bv 32 := 0x02000613.
Lemma F_28654 : fetch_word Ubsan.M.loaded_segments (0x28654 : word) = Some W_28654.
Proof. vm_refl. Qed.
Lemma D_28654 : decode_any W_28654 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28658 : bv 32 := 0x02c59263.
Lemma F_28658 : fetch_word Ubsan.M.loaded_segments (0x28658 : word) = Some W_28658.
Proof. vm_refl. Qed.
Lemma D_28658 : decode_any W_28658 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_2865c : bv 32 := 0x20800513.
Lemma F_2865c : fetch_word Ubsan.M.loaded_segments (0x2865c : word) = Some W_2865c.
Proof. vm_refl. Qed.
Lemma D_2865c : decode_any W_2865c = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_28660 : bv 32 := 0x00100593.
Lemma F_28660 : fetch_word Ubsan.M.loaded_segments (0x28660 : word) = Some W_28660.
Proof. vm_refl. Qed.
Lemma D_28660 : decode_any W_28660 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28664 : bv 32 := 0x3f4000ef.
Lemma F_28664 : fetch_word Ubsan.M.loaded_segments (0x28664 : word) = Some W_28664.
Proof. vm_refl. Qed.
Lemma D_28664 : decode_any W_28664 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_28668 : bv 32 := 0x02050c63.
Lemma F_28668 : fetch_word Ubsan.M.loaded_segments (0x28668 : word) = Some W_28668.
Proof. vm_refl. Qed.
Lemma D_28668 : decode_any W_28668 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_2866c : bv 32 := 0x00000593.
Lemma F_2866c : fetch_word Ubsan.M.loaded_segments (0x2866c : word) = Some W_2866c.
Proof. vm_refl. Qed.
Lemma D_2866c : decode_any W_2866c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28670 : bv 32 := 0x0109b603.
Lemma F_28670 : fetch_word Ubsan.M.loaded_segments (0x28670 : word) = Some W_28670.
Proof. vm_refl. Qed.
Lemma D_28670 : decode_any W_28670 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28674 : bv 32 := 0x00c53023.
Lemma F_28674 : fetch_word Ubsan.M.loaded_segments (0x28674 : word) = Some W_28674.
Proof. vm_refl. Qed.
Lemma D_28674 : decode_any W_28674 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28678 : bv 32 := 0x00a9b823.
Lemma F_28678 : fetch_word Ubsan.M.loaded_segments (0x28678 : word) = Some W_28678.
Proof. vm_refl. Qed.
Lemma D_28678 : decode_any W_28678 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2867c : bv 32 := 0x00000913.
Lemma F_2867c : fetch_word Ubsan.M.loaded_segments (0x2867c : word) = Some W_2867c.
Proof. vm_refl. Qed.
Lemma D_2867c : decode_any W_2867c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28680 : bv 32 := 0x00359613.
Lemma F_28680 : fetch_word Ubsan.M.loaded_segments (0x28680 : word) = Some W_28680.
Proof. vm_refl. Qed.
Lemma D_28680 : decode_any W_28680 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_28684 : bv 32 := 0x00c50533.
Lemma F_28684 : fetch_word Ubsan.M.loaded_segments (0x28684 : word) = Some W_28684.
Proof. vm_refl. Qed.
Lemma D_28684 : decode_any W_28684 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28688 : bv 32 := 0x00000617.
Lemma F_28688 : fetch_word Ubsan.M.loaded_segments (0x28688 : word) = Some W_28688.
Proof. vm_refl. Qed.
Lemma D_28688 : decode_any W_28688 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2868c : bv 32 := 0x00158593.
Lemma F_2868c : fetch_word Ubsan.M.loaded_segments (0x2868c : word) = Some W_2868c.
Proof. vm_refl. Qed.
Lemma D_2868c : decode_any W_2868c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_28690 : bv 32 := 0x04060613.
Lemma F_28690 : fetch_word Ubsan.M.loaded_segments (0x28690 : word) = Some W_28690.
Proof. vm_refl. Qed.
Lemma D_28690 : decode_any W_28690 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_28694 : bv 32 := 0x00c53423.
Lemma F_28694 : fetch_word Ubsan.M.loaded_segments (0x28694 : word) = Some W_28694.
Proof. vm_refl. Qed.
Lemma D_28694 : decode_any W_28694 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28698 : bv 32 := 0x10953423.
Lemma F_28698 : fetch_word Ubsan.M.loaded_segments (0x28698 : word) = Some W_28698.
Proof. vm_refl. Qed.
Lemma D_28698 : decode_any W_28698 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_2869c : bv 32 := 0x00b9a423.
Lemma F_2869c : fetch_word Ubsan.M.loaded_segments (0x2869c : word) = Some W_2869c.
Proof. vm_refl. Qed.
Lemma D_2869c : decode_any W_2869c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a0 : bv 32 := 0x00040513.
Lemma F_286a0 : fetch_word Ubsan.M.loaded_segments (0x286a0 : word) = Some W_286a0.
Proof. vm_refl. Qed.
Lemma D_286a0 : decode_any W_286a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a4 : bv 32 := 0x1950a0ef.
Lemma F_286a4 : fetch_word Ubsan.M.loaded_segments (0x286a4 : word) = Some W_286a4.
Proof. vm_refl. Qed.
Lemma D_286a4 : decode_any W_286a4 = Some (Jal 1 43412, 4%Z).
Proof. vm_refl. Qed.

Definition W_286a8 : bv 32 := 0x00090513.
Lemma F_286a8 : fetch_word Ubsan.M.loaded_segments (0x286a8 : word) = Some W_286a8.
Proof. vm_refl. Qed.
Lemma D_286a8 : decode_any W_286a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286ac : bv 32 := 0x02813083.
Lemma F_286ac : fetch_word Ubsan.M.loaded_segments (0x286ac : word) = Some W_286ac.
Proof. vm_refl. Qed.
Lemma D_286ac : decode_any W_286ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b0 : bv 32 := 0x02013403.
Lemma F_286b0 : fetch_word Ubsan.M.loaded_segments (0x286b0 : word) = Some W_286b0.
Proof. vm_refl. Qed.
Lemma D_286b0 : decode_any W_286b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b4 : bv 32 := 0x01813483.
Lemma F_286b4 : fetch_word Ubsan.M.loaded_segments (0x286b4 : word) = Some W_286b4.
Proof. vm_refl. Qed.
Lemma D_286b4 : decode_any W_286b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_286b8 : bv 32 := 0x01013903.
Lemma F_286b8 : fetch_word Ubsan.M.loaded_segments (0x286b8 : word) = Some W_286b8.
Proof. vm_refl. Qed.
Lemma D_286b8 : decode_any W_286b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_286bc : bv 32 := 0x00813983.
Lemma F_286bc : fetch_word Ubsan.M.loaded_segments (0x286bc : word) = Some W_286bc.
Proof. vm_refl. Qed.
Lemma D_286bc : decode_any W_286bc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c0 : bv 32 := 0x03010113.
Lemma F_286c0 : fetch_word Ubsan.M.loaded_segments (0x286c0 : word) = Some W_286c0.
Proof. vm_refl. Qed.
Lemma D_286c0 : decode_any W_286c0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c4 : bv 32 := 0x00008067.
Lemma F_286c4 : fetch_word Ubsan.M.loaded_segments (0x286c4 : word) = Some W_286c4.
Proof. vm_refl. Qed.
Lemma D_286c4 : decode_any W_286c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286c8 : bv 32 := 0x00050067.
Lemma F_286c8 : fetch_word Ubsan.M.loaded_segments (0x286c8 : word) = Some W_286c8.
Proof. vm_refl. Qed.
Lemma D_286c8 : decode_any W_286c8 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286cc : bv 32 := 0x00008067.
Lemma F_286cc : fetch_word Ubsan.M.loaded_segments (0x286cc : word) = Some W_286cc.
Proof. vm_refl. Qed.
Lemma D_286cc : decode_any W_286cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d0 : bv 32 := 0xfe010113.
Lemma F_286d0 : fetch_word Ubsan.M.loaded_segments (0x286d0 : word) = Some W_286d0.
Proof. vm_refl. Qed.
Lemma D_286d0 : decode_any W_286d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d4 : bv 32 := 0x00113c23.
Lemma F_286d4 : fetch_word Ubsan.M.loaded_segments (0x286d4 : word) = Some W_286d4.
Proof. vm_refl. Qed.
Lemma D_286d4 : decode_any W_286d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_286d8 : bv 32 := 0x00813823.
Lemma F_286d8 : fetch_word Ubsan.M.loaded_segments (0x286d8 : word) = Some W_286d8.
Proof. vm_refl. Qed.
Lemma D_286d8 : decode_any W_286d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_286dc : bv 32 := 0x00913423.
Lemma F_286dc : fetch_word Ubsan.M.loaded_segments (0x286dc : word) = Some W_286dc.
Proof. vm_refl. Qed.
Lemma D_286dc : decode_any W_286dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e0 : bv 32 := 0x0000c517.
Lemma F_286e0 : fetch_word Ubsan.M.loaded_segments (0x286e0 : word) = Some W_286e0.
Proof. vm_refl. Qed.
Lemma D_286e0 : decode_any W_286e0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e4 : bv 32 := 0x0000c597.
Lemma F_286e4 : fetch_word Ubsan.M.loaded_segments (0x286e4 : word) = Some W_286e4.
Proof. vm_refl. Qed.
Lemma D_286e4 : decode_any W_286e4 = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_286e8 : bv 32 := 0xb5053503.
Lemma F_286e8 : fetch_word Ubsan.M.loaded_segments (0x286e8 : word) = Some W_286e8.
Proof. vm_refl. Qed.
Lemma D_286e8 : decode_any W_286e8 = Some (Load SZ8 true 10 10 2896, 4%Z).
Proof. vm_refl. Qed.

Definition W_286ec : bv 32 := 0xb545b403.
Lemma F_286ec : fetch_word Ubsan.M.loaded_segments (0x286ec : word) = Some W_286ec.
Proof. vm_refl. Qed.
Lemma D_286ec : decode_any W_286ec = Some (Load SZ8 true 8 11 2900, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f0 : bv 32 := 0x00a47c63.
Lemma F_286f0 : fetch_word Ubsan.M.loaded_segments (0x286f0 : word) = Some W_286f0.
Proof. vm_refl. Qed.
Lemma D_286f0 : decode_any W_286f0 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f4 : bv 32 := 0xff853583.
Lemma F_286f4 : fetch_word Ubsan.M.loaded_segments (0x286f4 : word) = Some W_286f4.
Proof. vm_refl. Qed.
Lemma D_286f4 : decode_any W_286f4 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_286f8 : bv 32 := 0xff850493.
Lemma F_286f8 : fetch_word Ubsan.M.loaded_segments (0x286f8 : word) = Some W_286f8.
Proof. vm_refl. Qed.
Lemma D_286f8 : decode_any W_286f8 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_286fc : bv 32 := 0x000580e7.
Lemma F_286fc : fetch_word Ubsan.M.loaded_segments (0x286fc : word) = Some W_286fc.
Proof. vm_refl. Qed.
Lemma D_286fc : decode_any W_286fc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28700 : bv 32 := 0x00048513.
Lemma F_28700 : fetch_word Ubsan.M.loaded_segments (0x28700 : word) = Some W_28700.
Proof. vm_refl. Qed.
Lemma D_28700 : decode_any W_28700 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28704 : bv 32 := 0xfe9468e3.
Lemma F_28704 : fetch_word Ubsan.M.loaded_segments (0x28704 : word) = Some W_28704.
Proof. vm_refl. Qed.
Lemma D_28704 : decode_any W_28704 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_28708 : bv 32 := 0x01813083.
Lemma F_28708 : fetch_word Ubsan.M.loaded_segments (0x28708 : word) = Some W_28708.
Proof. vm_refl. Qed.
Lemma D_28708 : decode_any W_28708 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2870c : bv 32 := 0x01013403.
Lemma F_2870c : fetch_word Ubsan.M.loaded_segments (0x2870c : word) = Some W_2870c.
Proof. vm_refl. Qed.
Lemma D_2870c : decode_any W_2870c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_28710 : bv 32 := 0x00813483.
Lemma F_28710 : fetch_word Ubsan.M.loaded_segments (0x28710 : word) = Some W_28710.
Proof. vm_refl. Qed.
Lemma D_28710 : decode_any W_28710 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28714 : bv 32 := 0x02010113.
Lemma F_28714 : fetch_word Ubsan.M.loaded_segments (0x28714 : word) = Some W_28714.
Proof. vm_refl. Qed.
Lemma D_28714 : decode_any W_28714 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_28718 : bv 32 := 0xfb5ff06f.
Lemma F_28718 : fetch_word Ubsan.M.loaded_segments (0x28718 : word) = Some W_28718.
Proof. vm_refl. Qed.
Lemma D_28718 : decode_any W_28718 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_2871c : bv 32 := 0xff010113.
Lemma F_2871c : fetch_word Ubsan.M.loaded_segments (0x2871c : word) = Some W_2871c.
Proof. vm_refl. Qed.
Lemma D_2871c : decode_any W_2871c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_28720 : bv 32 := 0x00113423.
Lemma F_28720 : fetch_word Ubsan.M.loaded_segments (0x28720 : word) = Some W_28720.
Proof. vm_refl. Qed.
Lemma D_28720 : decode_any W_28720 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_28724 : bv 32 := 0x00813023.
Lemma F_28724 : fetch_word Ubsan.M.loaded_segments (0x28724 : word) = Some W_28724.
Proof. vm_refl. Qed.
Lemma D_28724 : decode_any W_28724 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28728 : bv 32 := 0x00000593.
Lemma F_28728 : fetch_word Ubsan.M.loaded_segments (0x28728 : word) = Some W_28728.
Proof. vm_refl. Qed.
Lemma D_28728 : decode_any W_28728 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2872c : bv 32 := 0x00020613.
Lemma F_2872c : fetch_word Ubsan.M.loaded_segments (0x2872c : word) = Some W_2872c.
Proof. vm_refl. Qed.
Lemma D_2872c : decode_any W_2872c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28730 : bv 32 := 0xf5862603.
Lemma F_28730 : fetch_word Ubsan.M.loaded_segments (0x28730 : word) = Some W_28730.
Proof. vm_refl. Qed.
Lemma D_28730 : decode_any W_28730 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_28734 : bv 32 := 0x0003d697.
Lemma F_28734 : fetch_word Ubsan.M.loaded_segments (0x28734 : word) = Some W_28734.
Proof. vm_refl. Qed.
Lemma D_28734 : decode_any W_28734 = Some (Auipc 13 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_28738 : bv 32 := 0x0ec68693.
Lemma F_28738 : fetch_word Ubsan.M.loaded_segments (0x28738 : word) = Some W_28738.
Proof. vm_refl. Qed.
Lemma D_28738 : decode_any W_28738 = Some (OpImm ALU_ADD 13 13 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_2873c : bv 32 := 0x1606a72f.
Lemma F_2873c : fetch_word Ubsan.M.loaded_segments (0x2873c : word) = Some W_2873c.
Proof. vm_refl. Qed.
Lemma D_2873c : decode_any W_2873c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_28740 : bv 32 := 0x00b71663.
Lemma F_28740 : fetch_word Ubsan.M.loaded_segments (0x28740 : word) = Some W_28740.
Proof. vm_refl. Qed.
Lemma D_28740 : decode_any W_28740 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28744 : bv 32 := 0x1ec6a7af.
Lemma F_28744 : fetch_word Ubsan.M.loaded_segments (0x28744 : word) = Some W_28744.
Proof. vm_refl. Qed.
Lemma D_28744 : decode_any W_28744 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_28748 : bv 32 := 0xfe079ae3.
Lemma F_28748 : fetch_word Ubsan.M.loaded_segments (0x28748 : word) = Some W_28748.
Proof. vm_refl. Qed.
Lemma D_28748 : decode_any W_28748 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_2874c : bv 32 := 0x0007059b.
Lemma F_2874c : fetch_word Ubsan.M.loaded_segments (0x2874c : word) = Some W_2874c.
Proof. vm_refl. Qed.
Lemma D_2874c : decode_any W_2874c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28750 : bv 32 := 0x02c58263.
Lemma F_28750 : fetch_word Ubsan.M.loaded_segments (0x28750 : word) = Some W_28750.
Proof. vm_refl. Qed.
Lemma D_28750 : decode_any W_28750 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_28754 : bv 32 := 0x02058263.
Lemma F_28754 : fetch_word Ubsan.M.loaded_segments (0x28754 : word) = Some W_28754.
Proof. vm_refl. Qed.
Lemma D_28754 : decode_any W_28754 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_28758 : bv 32 := 0x04900893.
Lemma F_28758 : fetch_word Ubsan.M.loaded_segments (0x28758 : word) = Some W_28758.
Proof. vm_refl. Qed.
Lemma D_28758 : decode_any W_28758 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_2875c : bv 32 := 0x00000593.
Lemma F_2875c : fetch_word Ubsan.M.loaded_segments (0x2875c : word) = Some W_2875c.
Proof. vm_refl. Qed.
Lemma D_2875c : decode_any W_2875c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28760 : bv 32 := 0x00000613.
Lemma F_28760 : fetch_word Ubsan.M.loaded_segments (0x28760 : word) = Some W_28760.
Proof. vm_refl. Qed.
Lemma D_28760 : decode_any W_28760 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28764 : bv 32 := 0x00000693.
Lemma F_28764 : fetch_word Ubsan.M.loaded_segments (0x28764 : word) = Some W_28764.
Proof. vm_refl. Qed.
Lemma D_28764 : decode_any W_28764 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28768 : bv 32 := 0x00000513.
Lemma F_28768 : fetch_word Ubsan.M.loaded_segments (0x28768 : word) = Some W_28768.
Proof. vm_refl. Qed.
Lemma D_28768 : decode_any W_28768 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2876c : bv 32 := 0x00000073.
Lemma F_2876c : fetch_word Ubsan.M.loaded_segments (0x2876c : word) = Some W_2876c.
Proof. vm_refl. Qed.
Lemma E_2876c : is_ecall W_2876c = true.
Proof. vm_refl. Qed.

Definition W_28770 : bv 32 := 0xff9ff06f.
Lemma F_28770 : fetch_word Ubsan.M.loaded_segments (0x28770 : word) = Some W_28770.
Proof. vm_refl. Qed.
Lemma D_28770 : decode_any W_28770 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_28774 : bv 32 := 0x00000023.
Lemma F_28774 : fetch_word Ubsan.M.loaded_segments (0x28774 : word) = Some W_28774.
Proof. vm_refl. Qed.
Lemma D_28774 : decode_any W_28774 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_28778 : bv 32 := 0x00050413.
Lemma F_28778 : fetch_word Ubsan.M.loaded_segments (0x28778 : word) = Some W_28778.
Proof. vm_refl. Qed.
Lemma D_28778 : decode_any W_28778 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2877c : bv 32 := 0xdbdff0ef.
Lemma F_2877c : fetch_word Ubsan.M.loaded_segments (0x2877c : word) = Some W_2877c.
Proof. vm_refl. Qed.
Lemma D_2877c : decode_any W_2877c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_28780 : bv 32 := 0xf51ff0ef.
Lemma F_28780 : fetch_word Ubsan.M.loaded_segments (0x28780 : word) = Some W_28780.
Proof. vm_refl. Qed.
Lemma D_28780 : decode_any W_28780 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_28784 : bv 32 := 0x280020ef.
Lemma F_28784 : fetch_word Ubsan.M.loaded_segments (0x28784 : word) = Some W_28784.
Proof. vm_refl. Qed.
Lemma D_28784 : decode_any W_28784 = Some (Jal 1 8832, 4%Z).
Proof. vm_refl. Qed.

Definition W_28788 : bv 32 := 0x00040513.
Lemma F_28788 : fetch_word Ubsan.M.loaded_segments (0x28788 : word) = Some W_28788.
Proof. vm_refl. Qed.
Lemma D_28788 : decode_any W_28788 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2878c : bv 32 := 0xd91ff0ef.
Lemma F_2878c : fetch_word Ubsan.M.loaded_segments (0x2878c : word) = Some W_2878c.
Proof. vm_refl. Qed.
Lemma D_2878c : decode_any W_2878c = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_32db0 : bv 32 := 0x00033597.
Lemma F_32db0 : fetch_word Ubsan.M.loaded_segments (0x32db0 : word) = Some W_32db0.
Proof. vm_refl. Qed.
Lemma D_32db0 : decode_any W_32db0 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_32db4 : bv 32 := 0xa9b58683.
Lemma F_32db4 : fetch_word Ubsan.M.loaded_segments (0x32db4 : word) = Some W_32db4.
Proof. vm_refl. Qed.
Lemma D_32db4 : decode_any W_32db4 = Some (Load SZ1 true 13 11 2715, 4%Z).
Proof. vm_refl. Qed.

Definition W_32db8 : bv 32 := 0x1e068863.
Lemma F_32db8 : fetch_word Ubsan.M.loaded_segments (0x32db8 : word) = Some W_32db8.
Proof. vm_refl. Qed.
Lemma D_32db8 : decode_any W_32db8 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_32fa8 : bv 32 := 0x00008067.
Lemma F_32fa8 : fetch_word Ubsan.M.loaded_segments (0x32fa8 : word) = Some W_32fa8.
Proof. vm_refl. Qed.
Lemma D_32fa8 : decode_any W_32fa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_33038 : bv 32 := 0x00052583.
Lemma F_33038 : fetch_word Ubsan.M.loaded_segments (0x33038 : word) = Some W_33038.
Proof. vm_refl. Qed.
Lemma D_33038 : decode_any W_33038 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3303c : bv 32 := 0x0005c463.
Lemma F_3303c : fetch_word Ubsan.M.loaded_segments (0x3303c : word) = Some W_3303c.
Proof. vm_refl. Qed.
Lemma D_3303c : decode_any W_3303c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_33040 : bv 32 := 0x00008067.
Lemma F_33040 : fetch_word Ubsan.M.loaded_segments (0x33040 : word) = Some W_33040.
Proof. vm_refl. Qed.
Lemma D_33040 : decode_any W_33040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
