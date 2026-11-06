(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushS14.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14cec : bv 32 := 0xffffe517.
Lemma F_14cec : fetch_word Plain.M.loaded_segments (0x14cec : word) = Some W_14cec.
Proof. vm_refl. Qed.
Lemma D_14cec : decode_any W_14cec = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cf0 : bv 32 := 0xad450513.
Lemma F_14cf0 : fetch_word Plain.M.loaded_segments (0x14cf0 : word) = Some W_14cf0.
Proof. vm_refl. Qed.
Lemma D_14cf0 : decode_any W_14cf0 = Some (OpImm ALU_ADD 10 10 2772, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cf4 : bv 32 := 0x00017597.
Lemma F_14cf4 : fetch_word Plain.M.loaded_segments (0x14cf4 : word) = Some W_14cf4.
Proof. vm_refl. Qed.
Lemma D_14cf4 : decode_any W_14cf4 = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cf8 : bv 32 := 0xfd458593.
Lemma F_14cf8 : fetch_word Plain.M.loaded_segments (0x14cf8 : word) = Some W_14cf8.
Proof. vm_refl. Qed.
Lemma D_14cf8 : decode_any W_14cf8 = Some (OpImm ALU_ADD 11 11 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cfc : bv 32 := 0x000000ef.
Lemma F_14cfc : fetch_word Plain.M.loaded_segments (0x14cfc : word) = Some W_14cfc.
Proof. vm_refl. Qed.
Lemma D_14cfc : decode_any W_14cfc = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d00 : bv 32 := 0x0040006f.
Lemma F_14d00 : fetch_word Plain.M.loaded_segments (0x14d00 : word) = Some W_14d00.
Proof. vm_refl. Qed.
Lemma D_14d00 : decode_any W_14d00 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d04 : bv 32 := 0x00813083.
Lemma F_14d04 : fetch_word Plain.M.loaded_segments (0x14d04 : word) = Some W_14d04.
Proof. vm_refl. Qed.
Lemma D_14d04 : decode_any W_14d04 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d08 : bv 32 := 0x00013403.
Lemma F_14d08 : fetch_word Plain.M.loaded_segments (0x14d08 : word) = Some W_14d08.
Proof. vm_refl. Qed.
Lemma D_14d08 : decode_any W_14d08 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d0c : bv 32 := 0x01010113.
Lemma F_14d0c : fetch_word Plain.M.loaded_segments (0x14d0c : word) = Some W_14d0c.
Proof. vm_refl. Qed.
Lemma D_14d0c : decode_any W_14d0c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d10 : bv 32 := 0x00008067.
Lemma F_14d10 : fetch_word Plain.M.loaded_segments (0x14d10 : word) = Some W_14d10.
Proof. vm_refl. Qed.
Lemma D_14d10 : decode_any W_14d10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d14 : bv 32 := 0xff010113.
Lemma F_14d14 : fetch_word Plain.M.loaded_segments (0x14d14 : word) = Some W_14d14.
Proof. vm_refl. Qed.
Lemma D_14d14 : decode_any W_14d14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d18 : bv 32 := 0x00113423.
Lemma F_14d18 : fetch_word Plain.M.loaded_segments (0x14d18 : word) = Some W_14d18.
Proof. vm_refl. Qed.
Lemma D_14d18 : decode_any W_14d18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d1c : bv 32 := 0x00813023.
Lemma F_14d1c : fetch_word Plain.M.loaded_segments (0x14d1c : word) = Some W_14d1c.
Proof. vm_refl. Qed.
Lemma D_14d1c : decode_any W_14d1c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d20 : bv 32 := 0x01010413.
Lemma F_14d20 : fetch_word Plain.M.loaded_segments (0x14d20 : word) = Some W_14d20.
Proof. vm_refl. Qed.
Lemma D_14d20 : decode_any W_14d20 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d24 : bv 32 := 0x00017517.
Lemma F_14d24 : fetch_word Plain.M.loaded_segments (0x14d24 : word) = Some W_14d24.
Proof. vm_refl. Qed.
Lemma D_14d24 : decode_any W_14d24 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d28 : bv 32 := 0xfe450513.
Lemma F_14d28 : fetch_word Plain.M.loaded_segments (0x14d28 : word) = Some W_14d28.
Proof. vm_refl. Qed.
Lemma D_14d28 : decode_any W_14d28 = Some (OpImm ALU_ADD 10 10 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d2c : bv 32 := 0x00054503.
Lemma F_14d2c : fetch_word Plain.M.loaded_segments (0x14d2c : word) = Some W_14d2c.
Proof. vm_refl. Qed.
Lemma D_14d2c : decode_any W_14d2c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d30 : bv 32 := 0x00157513.
Lemma F_14d30 : fetch_word Plain.M.loaded_segments (0x14d30 : word) = Some W_14d30.
Proof. vm_refl. Qed.
Lemma D_14d30 : decode_any W_14d30 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d34 : bv 32 := 0x00050663.
Lemma F_14d34 : fetch_word Plain.M.loaded_segments (0x14d34 : word) = Some W_14d34.
Proof. vm_refl. Qed.
Lemma D_14d34 : decode_any W_14d34 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d38 : bv 32 := 0x0040006f.
Lemma F_14d38 : fetch_word Plain.M.loaded_segments (0x14d38 : word) = Some W_14d38.
Proof. vm_refl. Qed.
Lemma D_14d38 : decode_any W_14d38 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d3c : bv 32 := 0x0580006f.
Lemma F_14d3c : fetch_word Plain.M.loaded_segments (0x14d3c : word) = Some W_14d3c.
Proof. vm_refl. Qed.
Lemma D_14d3c : decode_any W_14d3c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d40 : bv 32 := 0x00017517.
Lemma F_14d40 : fetch_word Plain.M.loaded_segments (0x14d40 : word) = Some W_14d40.
Proof. vm_refl. Qed.
Lemma D_14d40 : decode_any W_14d40 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d44 : bv 32 := 0xfc850593.
Lemma F_14d44 : fetch_word Plain.M.loaded_segments (0x14d44 : word) = Some W_14d44.
Proof. vm_refl. Qed.
Lemma D_14d44 : decode_any W_14d44 = Some (OpImm ALU_ADD 11 10 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d48 : bv 32 := 0x00100513.
Lemma F_14d48 : fetch_word Plain.M.loaded_segments (0x14d48 : word) = Some W_14d48.
Proof. vm_refl. Qed.
Lemma D_14d48 : decode_any W_14d48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d4c : bv 32 := 0x00a58023.
Lemma F_14d4c : fetch_word Plain.M.loaded_segments (0x14d4c : word) = Some W_14d4c.
Proof. vm_refl. Qed.
Lemma D_14d4c : decode_any W_14d4c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d50 : bv 32 := 0x00016517.
Lemma F_14d50 : fetch_word Plain.M.loaded_segments (0x14d50 : word) = Some W_14d50.
Proof. vm_refl. Qed.
Lemma D_14d50 : decode_any W_14d50 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d54 : bv 32 := 0xcc853503.
Lemma F_14d54 : fetch_word Plain.M.loaded_segments (0x14d54 : word) = Some W_14d54.
Proof. vm_refl. Qed.
Lemma D_14d54 : decode_any W_14d54 = Some (Load SZ8 true 10 10 3272, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d58 : bv 32 := 0x00050e63.
Lemma F_14d58 : fetch_word Plain.M.loaded_segments (0x14d58 : word) = Some W_14d58.
Proof. vm_refl. Qed.
Lemma D_14d58 : decode_any W_14d58 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d5c : bv 32 := 0x0040006f.
Lemma F_14d5c : fetch_word Plain.M.loaded_segments (0x14d5c : word) = Some W_14d5c.
Proof. vm_refl. Qed.
Lemma D_14d5c : decode_any W_14d5c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d60 : bv 32 := 0x00017517.
Lemma F_14d60 : fetch_word Plain.M.loaded_segments (0x14d60 : word) = Some W_14d60.
Proof. vm_refl. Qed.
Lemma D_14d60 : decode_any W_14d60 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d64 : bv 32 := 0xd2850513.
Lemma F_14d64 : fetch_word Plain.M.loaded_segments (0x14d64 : word) = Some W_14d64.
Proof. vm_refl. Qed.
Lemma D_14d64 : decode_any W_14d64 = Some (OpImm ALU_ADD 10 10 3368, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d68 : bv 32 := 0x00053503.
Lemma F_14d68 : fetch_word Plain.M.loaded_segments (0x14d68 : word) = Some W_14d68.
Proof. vm_refl. Qed.
Lemma D_14d68 : decode_any W_14d68 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d6c : bv 32 := 0x5350c0ef.
Lemma F_14d6c : fetch_word Plain.M.loaded_segments (0x14d6c : word) = Some W_14d6c.
Proof. vm_refl. Qed.
Lemma D_14d6c : decode_any W_14d6c = Some (Jal 1 52532, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d70 : bv 32 := 0x0040006f.
Lemma F_14d70 : fetch_word Plain.M.loaded_segments (0x14d70 : word) = Some W_14d70.
Proof. vm_refl. Qed.
Lemma D_14d70 : decode_any W_14d70 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d74 : bv 32 := 0x00016517.
Lemma F_14d74 : fetch_word Plain.M.loaded_segments (0x14d74 : word) = Some W_14d74.
Proof. vm_refl. Qed.
Lemma D_14d74 : decode_any W_14d74 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d78 : bv 32 := 0xcac53503.
Lemma F_14d78 : fetch_word Plain.M.loaded_segments (0x14d78 : word) = Some W_14d78.
Proof. vm_refl. Qed.
Lemma D_14d78 : decode_any W_14d78 = Some (Load SZ8 true 10 10 3244, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d7c : bv 32 := 0x00050c63.
Lemma F_14d7c : fetch_word Plain.M.loaded_segments (0x14d7c : word) = Some W_14d7c.
Proof. vm_refl. Qed.
Lemma D_14d7c : decode_any W_14d7c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d80 : bv 32 := 0x0040006f.
Lemma F_14d80 : fetch_word Plain.M.loaded_segments (0x14d80 : word) = Some W_14d80.
Proof. vm_refl. Qed.
Lemma D_14d80 : decode_any W_14d80 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d84 : bv 32 := 0xffffe517.
Lemma F_14d84 : fetch_word Plain.M.loaded_segments (0x14d84 : word) = Some W_14d84.
Proof. vm_refl. Qed.
Lemma D_14d84 : decode_any W_14d84 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d88 : bv 32 := 0xa3c50513.
Lemma F_14d88 : fetch_word Plain.M.loaded_segments (0x14d88 : word) = Some W_14d88.
Proof. vm_refl. Qed.
Lemma D_14d88 : decode_any W_14d88 = Some (OpImm ALU_ADD 10 10 2620, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d8c : bv 32 := 0x000000ef.
Lemma F_14d8c : fetch_word Plain.M.loaded_segments (0x14d8c : word) = Some W_14d8c.
Proof. vm_refl. Qed.
Lemma D_14d8c : decode_any W_14d8c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d90 : bv 32 := 0x0040006f.
Lemma F_14d90 : fetch_word Plain.M.loaded_segments (0x14d90 : word) = Some W_14d90.
Proof. vm_refl. Qed.
Lemma D_14d90 : decode_any W_14d90 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d94 : bv 32 := 0x00813083.
Lemma F_14d94 : fetch_word Plain.M.loaded_segments (0x14d94 : word) = Some W_14d94.
Proof. vm_refl. Qed.
Lemma D_14d94 : decode_any W_14d94 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d98 : bv 32 := 0x00013403.
Lemma F_14d98 : fetch_word Plain.M.loaded_segments (0x14d98 : word) = Some W_14d98.
Proof. vm_refl. Qed.
Lemma D_14d98 : decode_any W_14d98 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d9c : bv 32 := 0x01010113.
Lemma F_14d9c : fetch_word Plain.M.loaded_segments (0x14d9c : word) = Some W_14d9c.
Proof. vm_refl. Qed.
Lemma D_14d9c : decode_any W_14d9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14da0 : bv 32 := 0x00008067.
Lemma F_14da0 : fetch_word Plain.M.loaded_segments (0x14da0 : word) = Some W_14da0.
Proof. vm_refl. Qed.
Lemma D_14da0 : decode_any W_14da0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_151cc : bv 32 := 0x00027517.
Lemma F_151cc : fetch_word Plain.M.loaded_segments (0x151cc : word) = Some W_151cc.
Proof. vm_refl. Qed.
Lemma D_151cc : decode_any W_151cc = Some (Auipc 10 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_151d0 : bv 32 := 0xb4854503.
Lemma F_151d0 : fetch_word Plain.M.loaded_segments (0x151d0 : word) = Some W_151d0.
Proof. vm_refl. Qed.
Lemma D_151d0 : decode_any W_151d0 = Some (Load SZ1 false 10 10 2888, 4%Z).
Proof. vm_refl. Qed.

Definition W_151d4 : bv 32 := 0x00051463.
Lemma F_151d4 : fetch_word Plain.M.loaded_segments (0x151d4 : word) = Some W_151d4.
Proof. vm_refl. Qed.
Lemma D_151d4 : decode_any W_151d4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_151d8 : bv 32 := 0x00008067.
Lemma F_151d8 : fetch_word Plain.M.loaded_segments (0x151d8 : word) = Some W_151d8.
Proof. vm_refl. Qed.
Lemma D_151d8 : decode_any W_151d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_151dc : bv 32 := 0xff010113.
Lemma F_151dc : fetch_word Plain.M.loaded_segments (0x151dc : word) = Some W_151dc.
Proof. vm_refl. Qed.
Lemma D_151dc : decode_any W_151dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_151e0 : bv 32 := 0x00113423.
Lemma F_151e0 : fetch_word Plain.M.loaded_segments (0x151e0 : word) = Some W_151e0.
Proof. vm_refl. Qed.
Lemma D_151e0 : decode_any W_151e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_151e4 : bv 32 := 0x00016517.
Lemma F_151e4 : fetch_word Plain.M.loaded_segments (0x151e4 : word) = Some W_151e4.
Proof. vm_refl. Qed.
Lemma D_151e4 : decode_any W_151e4 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_151e8 : bv 32 := 0x85453503.
Lemma F_151e8 : fetch_word Plain.M.loaded_segments (0x151e8 : word) = Some W_151e8.
Proof. vm_refl. Qed.
Lemma D_151e8 : decode_any W_151e8 = Some (Load SZ8 true 10 10 2132, 4%Z).
Proof. vm_refl. Qed.

Definition W_151ec : bv 32 := 0x00053503.
Lemma F_151ec : fetch_word Plain.M.loaded_segments (0x151ec : word) = Some W_151ec.
Proof. vm_refl. Qed.
Lemma D_151ec : decode_any W_151ec = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_151f0 : bv 32 := 0x2250e0ef.
Lemma F_151f0 : fetch_word Plain.M.loaded_segments (0x151f0 : word) = Some W_151f0.
Proof. vm_refl. Qed.
Lemma D_151f0 : decode_any W_151f0 = Some (Jal 1 59940, 4%Z).
Proof. vm_refl. Qed.

Definition W_151f4 : bv 32 := 0x04d00513.
Lemma F_151f4 : fetch_word Plain.M.loaded_segments (0x151f4 : word) = Some W_151f4.
Proof. vm_refl. Qed.
Lemma D_151f4 : decode_any W_151f4 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_151f8 : bv 32 := 0x730140ef.
Lemma F_151f8 : fetch_word Plain.M.loaded_segments (0x151f8 : word) = Some W_151f8.
Proof. vm_refl. Qed.
Lemma D_151f8 : decode_any W_151f8 = Some (Jal 1 83760, 4%Z).
Proof. vm_refl. Qed.

Definition W_219d8 : bv 32 := 0xfd010113.
Lemma F_219d8 : fetch_word Plain.M.loaded_segments (0x219d8 : word) = Some W_219d8.
Proof. vm_refl. Qed.
Lemma D_219d8 : decode_any W_219d8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_219dc : bv 32 := 0x02113423.
Lemma F_219dc : fetch_word Plain.M.loaded_segments (0x219dc : word) = Some W_219dc.
Proof. vm_refl. Qed.
Lemma D_219dc : decode_any W_219dc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_219e0 : bv 32 := 0x02813023.
Lemma F_219e0 : fetch_word Plain.M.loaded_segments (0x219e0 : word) = Some W_219e0.
Proof. vm_refl. Qed.
Lemma D_219e0 : decode_any W_219e0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_219e4 : bv 32 := 0x00913c23.
Lemma F_219e4 : fetch_word Plain.M.loaded_segments (0x219e4 : word) = Some W_219e4.
Proof. vm_refl. Qed.
Lemma D_219e4 : decode_any W_219e4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_219e8 : bv 32 := 0x01213823.
Lemma F_219e8 : fetch_word Plain.M.loaded_segments (0x219e8 : word) = Some W_219e8.
Proof. vm_refl. Qed.
Lemma D_219e8 : decode_any W_219e8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_219ec : bv 32 := 0x01313423.
Lemma F_219ec : fetch_word Plain.M.loaded_segments (0x219ec : word) = Some W_219ec.
Proof. vm_refl. Qed.
Lemma D_219ec : decode_any W_219ec = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_219f0 : bv 32 := 0x0003a517.
Lemma F_219f0 : fetch_word Plain.M.loaded_segments (0x219f0 : word) = Some W_219f0.
Proof. vm_refl. Qed.
Lemma D_219f0 : decode_any W_219f0 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_219f4 : bv 32 := 0x46050913.
Lemma F_219f4 : fetch_word Plain.M.loaded_segments (0x219f4 : word) = Some W_219f4.
Proof. vm_refl. Qed.
Lemma D_219f4 : decode_any W_219f4 = Some (OpImm ALU_ADD 18 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_219f8 : bv 32 := 0x00490413.
Lemma F_219f8 : fetch_word Plain.M.loaded_segments (0x219f8 : word) = Some W_219f8.
Proof. vm_refl. Qed.
Lemma D_219f8 : decode_any W_219f8 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_219fc : bv 32 := 0x00040513.
Lemma F_219fc : fetch_word Plain.M.loaded_segments (0x219fc : word) = Some W_219fc.
Proof. vm_refl. Qed.
Lemma D_219fc : decode_any W_219fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a00 : bv 32 := 0x3f9070ef.
Lemma F_21a00 : fetch_word Plain.M.loaded_segments (0x21a00 : word) = Some W_21a00.
Proof. vm_refl. Qed.
Lemma D_21a00 : decode_any W_21a00 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a04 : bv 32 := 0x01093503.
Lemma F_21a04 : fetch_word Plain.M.loaded_segments (0x21a04 : word) = Some W_21a04.
Proof. vm_refl. Qed.
Lemma D_21a04 : decode_any W_21a04 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a08 : bv 32 := 0x06050863.
Lemma F_21a08 : fetch_word Plain.M.loaded_segments (0x21a08 : word) = Some W_21a08.
Proof. vm_refl. Qed.
Lemma D_21a08 : decode_any W_21a08 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a0c : bv 32 := 0x00892583.
Lemma F_21a0c : fetch_word Plain.M.loaded_segments (0x21a0c : word) = Some W_21a0c.
Proof. vm_refl. Qed.
Lemma D_21a0c : decode_any W_21a0c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a10 : bv 32 := 0x0180006f.
Lemma F_21a10 : fetch_word Plain.M.loaded_segments (0x21a10 : word) = Some W_21a10.
Proof. vm_refl. Qed.
Lemma D_21a10 : decode_any W_21a10 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a14 : bv 32 := 0x00053503.
Lemma F_21a14 : fetch_word Plain.M.loaded_segments (0x21a14 : word) = Some W_21a14.
Proof. vm_refl. Qed.
Lemma D_21a14 : decode_any W_21a14 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a18 : bv 32 := 0x02000593.
Lemma F_21a18 : fetch_word Plain.M.loaded_segments (0x21a18 : word) = Some W_21a18.
Proof. vm_refl. Qed.
Lemma D_21a18 : decode_any W_21a18 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a1c : bv 32 := 0x00b92423.
Lemma F_21a1c : fetch_word Plain.M.loaded_segments (0x21a1c : word) = Some W_21a1c.
Proof. vm_refl. Qed.
Lemma D_21a1c : decode_any W_21a1c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a20 : bv 32 := 0x00a93823.
Lemma F_21a20 : fetch_word Plain.M.loaded_segments (0x21a20 : word) = Some W_21a20.
Proof. vm_refl. Qed.
Lemma D_21a20 : decode_any W_21a20 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a24 : bv 32 := 0x04050a63.
Lemma F_21a24 : fetch_word Plain.M.loaded_segments (0x21a24 : word) = Some W_21a24.
Proof. vm_refl. Qed.
Lemma D_21a24 : decode_any W_21a24 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a28 : bv 32 := 0xfff5861b.
Lemma F_21a28 : fetch_word Plain.M.loaded_segments (0x21a28 : word) = Some W_21a28.
Proof. vm_refl. Qed.
Lemma D_21a28 : decode_any W_21a28 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a2c : bv 32 := 0x00c92423.
Lemma F_21a2c : fetch_word Plain.M.loaded_segments (0x21a2c : word) = Some W_21a2c.
Proof. vm_refl. Qed.
Lemma D_21a2c : decode_any W_21a2c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a30 : bv 32 := 0xfeb052e3.
Lemma F_21a30 : fetch_word Plain.M.loaded_segments (0x21a30 : word) = Some W_21a30.
Proof. vm_refl. Qed.
Lemma D_21a30 : decode_any W_21a30 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a34 : bv 32 := 0x01093503.
Lemma F_21a34 : fetch_word Plain.M.loaded_segments (0x21a34 : word) = Some W_21a34.
Proof. vm_refl. Qed.
Lemma D_21a34 : decode_any W_21a34 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a38 : bv 32 := 0x00361613.
Lemma F_21a38 : fetch_word Plain.M.loaded_segments (0x21a38 : word) = Some W_21a38.
Proof. vm_refl. Qed.
Lemma D_21a38 : decode_any W_21a38 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a3c : bv 32 := 0x00c50533.
Lemma F_21a3c : fetch_word Plain.M.loaded_segments (0x21a3c : word) = Some W_21a3c.
Proof. vm_refl. Qed.
Lemma D_21a3c : decode_any W_21a3c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a40 : bv 32 := 0x00853983.
Lemma F_21a40 : fetch_word Plain.M.loaded_segments (0x21a40 : word) = Some W_21a40.
Proof. vm_refl. Qed.
Lemma D_21a40 : decode_any W_21a40 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a44 : bv 32 := 0x10853483.
Lemma F_21a44 : fetch_word Plain.M.loaded_segments (0x21a44 : word) = Some W_21a44.
Proof. vm_refl. Qed.
Lemma D_21a44 : decode_any W_21a44 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a48 : bv 32 := 0x00040513.
Lemma F_21a48 : fetch_word Plain.M.loaded_segments (0x21a48 : word) = Some W_21a48.
Proof. vm_refl. Qed.
Lemma D_21a48 : decode_any W_21a48 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a4c : bv 32 := 0x635070ef.
Lemma F_21a4c : fetch_word Plain.M.loaded_segments (0x21a4c : word) = Some W_21a4c.
Proof. vm_refl. Qed.
Lemma D_21a4c : decode_any W_21a4c = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a50 : bv 32 := 0x00048513.
Lemma F_21a50 : fetch_word Plain.M.loaded_segments (0x21a50 : word) = Some W_21a50.
Proof. vm_refl. Qed.
Lemma D_21a50 : decode_any W_21a50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a54 : bv 32 := 0x000980e7.
Lemma F_21a54 : fetch_word Plain.M.loaded_segments (0x21a54 : word) = Some W_21a54.
Proof. vm_refl. Qed.
Lemma D_21a54 : decode_any W_21a54 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a58 : bv 32 := 0x00040513.
Lemma F_21a58 : fetch_word Plain.M.loaded_segments (0x21a58 : word) = Some W_21a58.
Proof. vm_refl. Qed.
Lemma D_21a58 : decode_any W_21a58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a5c : bv 32 := 0x39d070ef.
Lemma F_21a5c : fetch_word Plain.M.loaded_segments (0x21a5c : word) = Some W_21a5c.
Proof. vm_refl. Qed.
Lemma D_21a5c : decode_any W_21a5c = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a60 : bv 32 := 0x00892503.
Lemma F_21a60 : fetch_word Plain.M.loaded_segments (0x21a60 : word) = Some W_21a60.
Proof. vm_refl. Qed.
Lemma D_21a60 : decode_any W_21a60 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a64 : bv 32 := 0xfff5061b.
Lemma F_21a64 : fetch_word Plain.M.loaded_segments (0x21a64 : word) = Some W_21a64.
Proof. vm_refl. Qed.
Lemma D_21a64 : decode_any W_21a64 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a68 : bv 32 := 0x00c92423.
Lemma F_21a68 : fetch_word Plain.M.loaded_segments (0x21a68 : word) = Some W_21a68.
Proof. vm_refl. Qed.
Lemma D_21a68 : decode_any W_21a68 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a6c : bv 32 := 0xfca044e3.
Lemma F_21a6c : fetch_word Plain.M.loaded_segments (0x21a6c : word) = Some W_21a6c.
Proof. vm_refl. Qed.
Lemma D_21a6c : decode_any W_21a6c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a70 : bv 32 := 0x01093503.
Lemma F_21a70 : fetch_word Plain.M.loaded_segments (0x21a70 : word) = Some W_21a70.
Proof. vm_refl. Qed.
Lemma D_21a70 : decode_any W_21a70 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a74 : bv 32 := 0xfa1ff06f.
Lemma F_21a74 : fetch_word Plain.M.loaded_segments (0x21a74 : word) = Some W_21a74.
Proof. vm_refl. Qed.
Lemma D_21a74 : decode_any W_21a74 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a78 : bv 32 := 0x00100513.
Lemma F_21a78 : fetch_word Plain.M.loaded_segments (0x21a78 : word) = Some W_21a78.
Proof. vm_refl. Qed.
Lemma D_21a78 : decode_any W_21a78 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a7c : bv 32 := 0x00a90023.
Lemma F_21a7c : fetch_word Plain.M.loaded_segments (0x21a7c : word) = Some W_21a7c.
Proof. vm_refl. Qed.
Lemma D_21a7c : decode_any W_21a7c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a80 : bv 32 := 0x00040513.
Lemma F_21a80 : fetch_word Plain.M.loaded_segments (0x21a80 : word) = Some W_21a80.
Proof. vm_refl. Qed.
Lemma D_21a80 : decode_any W_21a80 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a84 : bv 32 := 0x02813083.
Lemma F_21a84 : fetch_word Plain.M.loaded_segments (0x21a84 : word) = Some W_21a84.
Proof. vm_refl. Qed.
Lemma D_21a84 : decode_any W_21a84 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a88 : bv 32 := 0x02013403.
Lemma F_21a88 : fetch_word Plain.M.loaded_segments (0x21a88 : word) = Some W_21a88.
Proof. vm_refl. Qed.
Lemma D_21a88 : decode_any W_21a88 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a8c : bv 32 := 0x01813483.
Lemma F_21a8c : fetch_word Plain.M.loaded_segments (0x21a8c : word) = Some W_21a8c.
Proof. vm_refl. Qed.
Lemma D_21a8c : decode_any W_21a8c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a90 : bv 32 := 0x01013903.
Lemma F_21a90 : fetch_word Plain.M.loaded_segments (0x21a90 : word) = Some W_21a90.
Proof. vm_refl. Qed.
Lemma D_21a90 : decode_any W_21a90 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a94 : bv 32 := 0x00813983.
Lemma F_21a94 : fetch_word Plain.M.loaded_segments (0x21a94 : word) = Some W_21a94.
Proof. vm_refl. Qed.
Lemma D_21a94 : decode_any W_21a94 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a98 : bv 32 := 0x03010113.
Lemma F_21a98 : fetch_word Plain.M.loaded_segments (0x21a98 : word) = Some W_21a98.
Proof. vm_refl. Qed.
Lemma D_21a98 : decode_any W_21a98 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_21a9c : bv 32 := 0x5e50706f.
Lemma F_21a9c : fetch_word Plain.M.loaded_segments (0x21a9c : word) = Some W_21a9c.
Proof. vm_refl. Qed.
Lemma D_21a9c : decode_any W_21a9c = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_21aa0 : bv 32 := 0x00008067.
Lemma F_21aa0 : fetch_word Plain.M.loaded_segments (0x21aa0 : word) = Some W_21aa0.
Proof. vm_refl. Qed.
Lemma D_21aa0 : decode_any W_21aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21aa4 : bv 32 := 0xfd010113.
Lemma F_21aa4 : fetch_word Plain.M.loaded_segments (0x21aa4 : word) = Some W_21aa4.
Proof. vm_refl. Qed.
Lemma D_21aa4 : decode_any W_21aa4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_21aa8 : bv 32 := 0x02113423.
Lemma F_21aa8 : fetch_word Plain.M.loaded_segments (0x21aa8 : word) = Some W_21aa8.
Proof. vm_refl. Qed.
Lemma D_21aa8 : decode_any W_21aa8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_21aac : bv 32 := 0x02813023.
Lemma F_21aac : fetch_word Plain.M.loaded_segments (0x21aac : word) = Some W_21aac.
Proof. vm_refl. Qed.
Lemma D_21aac : decode_any W_21aac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ab0 : bv 32 := 0x00913c23.
Lemma F_21ab0 : fetch_word Plain.M.loaded_segments (0x21ab0 : word) = Some W_21ab0.
Proof. vm_refl. Qed.
Lemma D_21ab0 : decode_any W_21ab0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ab4 : bv 32 := 0x01213823.
Lemma F_21ab4 : fetch_word Plain.M.loaded_segments (0x21ab4 : word) = Some W_21ab4.
Proof. vm_refl. Qed.
Lemma D_21ab4 : decode_any W_21ab4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ab8 : bv 32 := 0x01313423.
Lemma F_21ab8 : fetch_word Plain.M.loaded_segments (0x21ab8 : word) = Some W_21ab8.
Proof. vm_refl. Qed.
Lemma D_21ab8 : decode_any W_21ab8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21abc : bv 32 := 0x00050493.
Lemma F_21abc : fetch_word Plain.M.loaded_segments (0x21abc : word) = Some W_21abc.
Proof. vm_refl. Qed.
Lemma D_21abc : decode_any W_21abc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ac0 : bv 32 := 0x0003a517.
Lemma F_21ac0 : fetch_word Plain.M.loaded_segments (0x21ac0 : word) = Some W_21ac0.
Proof. vm_refl. Qed.
Lemma D_21ac0 : decode_any W_21ac0 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ac4 : bv 32 := 0x39050993.
Lemma F_21ac4 : fetch_word Plain.M.loaded_segments (0x21ac4 : word) = Some W_21ac4.
Proof. vm_refl. Qed.
Lemma D_21ac4 : decode_any W_21ac4 = Some (OpImm ALU_ADD 19 10 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ac8 : bv 32 := 0x00498413.
Lemma F_21ac8 : fetch_word Plain.M.loaded_segments (0x21ac8 : word) = Some W_21ac8.
Proof. vm_refl. Qed.
Lemma D_21ac8 : decode_any W_21ac8 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21acc : bv 32 := 0x00040513.
Lemma F_21acc : fetch_word Plain.M.loaded_segments (0x21acc : word) = Some W_21acc.
Proof. vm_refl. Qed.
Lemma D_21acc : decode_any W_21acc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ad0 : bv 32 := 0x329070ef.
Lemma F_21ad0 : fetch_word Plain.M.loaded_segments (0x21ad0 : word) = Some W_21ad0.
Proof. vm_refl. Qed.
Lemma D_21ad0 : decode_any W_21ad0 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ad4 : bv 32 := 0x0009c503.
Lemma F_21ad4 : fetch_word Plain.M.loaded_segments (0x21ad4 : word) = Some W_21ad4.
Proof. vm_refl. Qed.
Lemma D_21ad4 : decode_any W_21ad4 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ad8 : bv 32 := 0xfff00913.
Lemma F_21ad8 : fetch_word Plain.M.loaded_segments (0x21ad8 : word) = Some W_21ad8.
Proof. vm_refl. Qed.
Lemma D_21ad8 : decode_any W_21ad8 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21adc : bv 32 := 0x06051263.
Lemma F_21adc : fetch_word Plain.M.loaded_segments (0x21adc : word) = Some W_21adc.
Proof. vm_refl. Qed.
Lemma D_21adc : decode_any W_21adc = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ae0 : bv 32 := 0x0109b503.
Lemma F_21ae0 : fetch_word Plain.M.loaded_segments (0x21ae0 : word) = Some W_21ae0.
Proof. vm_refl. Qed.
Lemma D_21ae0 : decode_any W_21ae0 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ae4 : bv 32 := 0x00051663.
Lemma F_21ae4 : fetch_word Plain.M.loaded_segments (0x21ae4 : word) = Some W_21ae4.
Proof. vm_refl. Qed.
Lemma D_21ae4 : decode_any W_21ae4 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ae8 : bv 32 := 0x01898513.
Lemma F_21ae8 : fetch_word Plain.M.loaded_segments (0x21ae8 : word) = Some W_21ae8.
Proof. vm_refl. Qed.
Lemma D_21ae8 : decode_any W_21ae8 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21aec : bv 32 := 0x00a9b823.
Lemma F_21aec : fetch_word Plain.M.loaded_segments (0x21aec : word) = Some W_21aec.
Proof. vm_refl. Qed.
Lemma D_21aec : decode_any W_21aec = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21af0 : bv 32 := 0x0089a583.
Lemma F_21af0 : fetch_word Plain.M.loaded_segments (0x21af0 : word) = Some W_21af0.
Proof. vm_refl. Qed.
Lemma D_21af0 : decode_any W_21af0 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21af4 : bv 32 := 0x02000613.
Lemma F_21af4 : fetch_word Plain.M.loaded_segments (0x21af4 : word) = Some W_21af4.
Proof. vm_refl. Qed.
Lemma D_21af4 : decode_any W_21af4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21af8 : bv 32 := 0x02c59263.
Lemma F_21af8 : fetch_word Plain.M.loaded_segments (0x21af8 : word) = Some W_21af8.
Proof. vm_refl. Qed.
Lemma D_21af8 : decode_any W_21af8 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_21afc : bv 32 := 0x20800513.
Lemma F_21afc : fetch_word Plain.M.loaded_segments (0x21afc : word) = Some W_21afc.
Proof. vm_refl. Qed.
Lemma D_21afc : decode_any W_21afc = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b00 : bv 32 := 0x00100593.
Lemma F_21b00 : fetch_word Plain.M.loaded_segments (0x21b00 : word) = Some W_21b00.
Proof. vm_refl. Qed.
Lemma D_21b00 : decode_any W_21b00 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b04 : bv 32 := 0x3f4000ef.
Lemma F_21b04 : fetch_word Plain.M.loaded_segments (0x21b04 : word) = Some W_21b04.
Proof. vm_refl. Qed.
Lemma D_21b04 : decode_any W_21b04 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b08 : bv 32 := 0x02050c63.
Lemma F_21b08 : fetch_word Plain.M.loaded_segments (0x21b08 : word) = Some W_21b08.
Proof. vm_refl. Qed.
Lemma D_21b08 : decode_any W_21b08 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b0c : bv 32 := 0x00000593.
Lemma F_21b0c : fetch_word Plain.M.loaded_segments (0x21b0c : word) = Some W_21b0c.
Proof. vm_refl. Qed.
Lemma D_21b0c : decode_any W_21b0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b10 : bv 32 := 0x0109b603.
Lemma F_21b10 : fetch_word Plain.M.loaded_segments (0x21b10 : word) = Some W_21b10.
Proof. vm_refl. Qed.
Lemma D_21b10 : decode_any W_21b10 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b14 : bv 32 := 0x00c53023.
Lemma F_21b14 : fetch_word Plain.M.loaded_segments (0x21b14 : word) = Some W_21b14.
Proof. vm_refl. Qed.
Lemma D_21b14 : decode_any W_21b14 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b18 : bv 32 := 0x00a9b823.
Lemma F_21b18 : fetch_word Plain.M.loaded_segments (0x21b18 : word) = Some W_21b18.
Proof. vm_refl. Qed.
Lemma D_21b18 : decode_any W_21b18 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b1c : bv 32 := 0x00000913.
Lemma F_21b1c : fetch_word Plain.M.loaded_segments (0x21b1c : word) = Some W_21b1c.
Proof. vm_refl. Qed.
Lemma D_21b1c : decode_any W_21b1c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b20 : bv 32 := 0x00359613.
Lemma F_21b20 : fetch_word Plain.M.loaded_segments (0x21b20 : word) = Some W_21b20.
Proof. vm_refl. Qed.
Lemma D_21b20 : decode_any W_21b20 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b24 : bv 32 := 0x00c50533.
Lemma F_21b24 : fetch_word Plain.M.loaded_segments (0x21b24 : word) = Some W_21b24.
Proof. vm_refl. Qed.
Lemma D_21b24 : decode_any W_21b24 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b28 : bv 32 := 0x00000617.
Lemma F_21b28 : fetch_word Plain.M.loaded_segments (0x21b28 : word) = Some W_21b28.
Proof. vm_refl. Qed.
Lemma D_21b28 : decode_any W_21b28 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b2c : bv 32 := 0x00158593.
Lemma F_21b2c : fetch_word Plain.M.loaded_segments (0x21b2c : word) = Some W_21b2c.
Proof. vm_refl. Qed.
Lemma D_21b2c : decode_any W_21b2c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b30 : bv 32 := 0x04060613.
Lemma F_21b30 : fetch_word Plain.M.loaded_segments (0x21b30 : word) = Some W_21b30.
Proof. vm_refl. Qed.
Lemma D_21b30 : decode_any W_21b30 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b34 : bv 32 := 0x00c53423.
Lemma F_21b34 : fetch_word Plain.M.loaded_segments (0x21b34 : word) = Some W_21b34.
Proof. vm_refl. Qed.
Lemma D_21b34 : decode_any W_21b34 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b38 : bv 32 := 0x10953423.
Lemma F_21b38 : fetch_word Plain.M.loaded_segments (0x21b38 : word) = Some W_21b38.
Proof. vm_refl. Qed.
Lemma D_21b38 : decode_any W_21b38 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b3c : bv 32 := 0x00b9a423.
Lemma F_21b3c : fetch_word Plain.M.loaded_segments (0x21b3c : word) = Some W_21b3c.
Proof. vm_refl. Qed.
Lemma D_21b3c : decode_any W_21b3c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b40 : bv 32 := 0x00040513.
Lemma F_21b40 : fetch_word Plain.M.loaded_segments (0x21b40 : word) = Some W_21b40.
Proof. vm_refl. Qed.
Lemma D_21b40 : decode_any W_21b40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b44 : bv 32 := 0x53d070ef.
Lemma F_21b44 : fetch_word Plain.M.loaded_segments (0x21b44 : word) = Some W_21b44.
Proof. vm_refl. Qed.
Lemma D_21b44 : decode_any W_21b44 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b48 : bv 32 := 0x00090513.
Lemma F_21b48 : fetch_word Plain.M.loaded_segments (0x21b48 : word) = Some W_21b48.
Proof. vm_refl. Qed.
Lemma D_21b48 : decode_any W_21b48 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b4c : bv 32 := 0x02813083.
Lemma F_21b4c : fetch_word Plain.M.loaded_segments (0x21b4c : word) = Some W_21b4c.
Proof. vm_refl. Qed.
Lemma D_21b4c : decode_any W_21b4c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b50 : bv 32 := 0x02013403.
Lemma F_21b50 : fetch_word Plain.M.loaded_segments (0x21b50 : word) = Some W_21b50.
Proof. vm_refl. Qed.
Lemma D_21b50 : decode_any W_21b50 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b54 : bv 32 := 0x01813483.
Lemma F_21b54 : fetch_word Plain.M.loaded_segments (0x21b54 : word) = Some W_21b54.
Proof. vm_refl. Qed.
Lemma D_21b54 : decode_any W_21b54 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b58 : bv 32 := 0x01013903.
Lemma F_21b58 : fetch_word Plain.M.loaded_segments (0x21b58 : word) = Some W_21b58.
Proof. vm_refl. Qed.
Lemma D_21b58 : decode_any W_21b58 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b5c : bv 32 := 0x00813983.
Lemma F_21b5c : fetch_word Plain.M.loaded_segments (0x21b5c : word) = Some W_21b5c.
Proof. vm_refl. Qed.
Lemma D_21b5c : decode_any W_21b5c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b60 : bv 32 := 0x03010113.
Lemma F_21b60 : fetch_word Plain.M.loaded_segments (0x21b60 : word) = Some W_21b60.
Proof. vm_refl. Qed.
Lemma D_21b60 : decode_any W_21b60 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b64 : bv 32 := 0x00008067.
Lemma F_21b64 : fetch_word Plain.M.loaded_segments (0x21b64 : word) = Some W_21b64.
Proof. vm_refl. Qed.
Lemma D_21b64 : decode_any W_21b64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b68 : bv 32 := 0x00050067.
Lemma F_21b68 : fetch_word Plain.M.loaded_segments (0x21b68 : word) = Some W_21b68.
Proof. vm_refl. Qed.
Lemma D_21b68 : decode_any W_21b68 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b6c : bv 32 := 0x00008067.
Lemma F_21b6c : fetch_word Plain.M.loaded_segments (0x21b6c : word) = Some W_21b6c.
Proof. vm_refl. Qed.
Lemma D_21b6c : decode_any W_21b6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b70 : bv 32 := 0xfe010113.
Lemma F_21b70 : fetch_word Plain.M.loaded_segments (0x21b70 : word) = Some W_21b70.
Proof. vm_refl. Qed.
Lemma D_21b70 : decode_any W_21b70 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b74 : bv 32 := 0x00113c23.
Lemma F_21b74 : fetch_word Plain.M.loaded_segments (0x21b74 : word) = Some W_21b74.
Proof. vm_refl. Qed.
Lemma D_21b74 : decode_any W_21b74 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b78 : bv 32 := 0x00813823.
Lemma F_21b78 : fetch_word Plain.M.loaded_segments (0x21b78 : word) = Some W_21b78.
Proof. vm_refl. Qed.
Lemma D_21b78 : decode_any W_21b78 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b7c : bv 32 := 0x00913423.
Lemma F_21b7c : fetch_word Plain.M.loaded_segments (0x21b7c : word) = Some W_21b7c.
Proof. vm_refl. Qed.
Lemma D_21b7c : decode_any W_21b7c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b80 : bv 32 := 0x00009517.
Lemma F_21b80 : fetch_word Plain.M.loaded_segments (0x21b80 : word) = Some W_21b80.
Proof. vm_refl. Qed.
Lemma D_21b80 : decode_any W_21b80 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b84 : bv 32 := 0x00009597.
Lemma F_21b84 : fetch_word Plain.M.loaded_segments (0x21b84 : word) = Some W_21b84.
Proof. vm_refl. Qed.
Lemma D_21b84 : decode_any W_21b84 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b88 : bv 32 := 0xef853503.
Lemma F_21b88 : fetch_word Plain.M.loaded_segments (0x21b88 : word) = Some W_21b88.
Proof. vm_refl. Qed.
Lemma D_21b88 : decode_any W_21b88 = Some (Load SZ8 true 10 10 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b8c : bv 32 := 0xefc5b403.
Lemma F_21b8c : fetch_word Plain.M.loaded_segments (0x21b8c : word) = Some W_21b8c.
Proof. vm_refl. Qed.
Lemma D_21b8c : decode_any W_21b8c = Some (Load SZ8 true 8 11 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b90 : bv 32 := 0x00a47c63.
Lemma F_21b90 : fetch_word Plain.M.loaded_segments (0x21b90 : word) = Some W_21b90.
Proof. vm_refl. Qed.
Lemma D_21b90 : decode_any W_21b90 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b94 : bv 32 := 0xff853583.
Lemma F_21b94 : fetch_word Plain.M.loaded_segments (0x21b94 : word) = Some W_21b94.
Proof. vm_refl. Qed.
Lemma D_21b94 : decode_any W_21b94 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b98 : bv 32 := 0xff850493.
Lemma F_21b98 : fetch_word Plain.M.loaded_segments (0x21b98 : word) = Some W_21b98.
Proof. vm_refl. Qed.
Lemma D_21b98 : decode_any W_21b98 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b9c : bv 32 := 0x000580e7.
Lemma F_21b9c : fetch_word Plain.M.loaded_segments (0x21b9c : word) = Some W_21b9c.
Proof. vm_refl. Qed.
Lemma D_21b9c : decode_any W_21b9c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ba0 : bv 32 := 0x00048513.
Lemma F_21ba0 : fetch_word Plain.M.loaded_segments (0x21ba0 : word) = Some W_21ba0.
Proof. vm_refl. Qed.
Lemma D_21ba0 : decode_any W_21ba0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ba4 : bv 32 := 0xfe9468e3.
Lemma F_21ba4 : fetch_word Plain.M.loaded_segments (0x21ba4 : word) = Some W_21ba4.
Proof. vm_refl. Qed.
Lemma D_21ba4 : decode_any W_21ba4 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ba8 : bv 32 := 0x01813083.
Lemma F_21ba8 : fetch_word Plain.M.loaded_segments (0x21ba8 : word) = Some W_21ba8.
Proof. vm_refl. Qed.
Lemma D_21ba8 : decode_any W_21ba8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bac : bv 32 := 0x01013403.
Lemma F_21bac : fetch_word Plain.M.loaded_segments (0x21bac : word) = Some W_21bac.
Proof. vm_refl. Qed.
Lemma D_21bac : decode_any W_21bac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bb0 : bv 32 := 0x00813483.
Lemma F_21bb0 : fetch_word Plain.M.loaded_segments (0x21bb0 : word) = Some W_21bb0.
Proof. vm_refl. Qed.
Lemma D_21bb0 : decode_any W_21bb0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bb4 : bv 32 := 0x02010113.
Lemma F_21bb4 : fetch_word Plain.M.loaded_segments (0x21bb4 : word) = Some W_21bb4.
Proof. vm_refl. Qed.
Lemma D_21bb4 : decode_any W_21bb4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bb8 : bv 32 := 0xfb5ff06f.
Lemma F_21bb8 : fetch_word Plain.M.loaded_segments (0x21bb8 : word) = Some W_21bb8.
Proof. vm_refl. Qed.
Lemma D_21bb8 : decode_any W_21bb8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bbc : bv 32 := 0xff010113.
Lemma F_21bbc : fetch_word Plain.M.loaded_segments (0x21bbc : word) = Some W_21bbc.
Proof. vm_refl. Qed.
Lemma D_21bbc : decode_any W_21bbc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bc0 : bv 32 := 0x00113423.
Lemma F_21bc0 : fetch_word Plain.M.loaded_segments (0x21bc0 : word) = Some W_21bc0.
Proof. vm_refl. Qed.
Lemma D_21bc0 : decode_any W_21bc0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bc4 : bv 32 := 0x00813023.
Lemma F_21bc4 : fetch_word Plain.M.loaded_segments (0x21bc4 : word) = Some W_21bc4.
Proof. vm_refl. Qed.
Lemma D_21bc4 : decode_any W_21bc4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bc8 : bv 32 := 0x00000593.
Lemma F_21bc8 : fetch_word Plain.M.loaded_segments (0x21bc8 : word) = Some W_21bc8.
Proof. vm_refl. Qed.
Lemma D_21bc8 : decode_any W_21bc8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bcc : bv 32 := 0x00020613.
Lemma F_21bcc : fetch_word Plain.M.loaded_segments (0x21bcc : word) = Some W_21bcc.
Proof. vm_refl. Qed.
Lemma D_21bcc : decode_any W_21bcc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bd0 : bv 32 := 0xf5862603.
Lemma F_21bd0 : fetch_word Plain.M.loaded_segments (0x21bd0 : word) = Some W_21bd0.
Proof. vm_refl. Qed.
Lemma D_21bd0 : decode_any W_21bd0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bd4 : bv 32 := 0x0003a697.
Lemma F_21bd4 : fetch_word Plain.M.loaded_segments (0x21bd4 : word) = Some W_21bd4.
Proof. vm_refl. Qed.
Lemma D_21bd4 : decode_any W_21bd4 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bd8 : bv 32 := 0x49c68693.
Lemma F_21bd8 : fetch_word Plain.M.loaded_segments (0x21bd8 : word) = Some W_21bd8.
Proof. vm_refl. Qed.
Lemma D_21bd8 : decode_any W_21bd8 = Some (OpImm ALU_ADD 13 13 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bdc : bv 32 := 0x1606a72f.
Lemma F_21bdc : fetch_word Plain.M.loaded_segments (0x21bdc : word) = Some W_21bdc.
Proof. vm_refl. Qed.
Lemma D_21bdc : decode_any W_21bdc = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21be0 : bv 32 := 0x00b71663.
Lemma F_21be0 : fetch_word Plain.M.loaded_segments (0x21be0 : word) = Some W_21be0.
Proof. vm_refl. Qed.
Lemma D_21be0 : decode_any W_21be0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21be4 : bv 32 := 0x1ec6a7af.
Lemma F_21be4 : fetch_word Plain.M.loaded_segments (0x21be4 : word) = Some W_21be4.
Proof. vm_refl. Qed.
Lemma D_21be4 : decode_any W_21be4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21be8 : bv 32 := 0xfe079ae3.
Lemma F_21be8 : fetch_word Plain.M.loaded_segments (0x21be8 : word) = Some W_21be8.
Proof. vm_refl. Qed.
Lemma D_21be8 : decode_any W_21be8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bec : bv 32 := 0x0007059b.
Lemma F_21bec : fetch_word Plain.M.loaded_segments (0x21bec : word) = Some W_21bec.
Proof. vm_refl. Qed.
Lemma D_21bec : decode_any W_21bec = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bf0 : bv 32 := 0x02c58263.
Lemma F_21bf0 : fetch_word Plain.M.loaded_segments (0x21bf0 : word) = Some W_21bf0.
Proof. vm_refl. Qed.
Lemma D_21bf0 : decode_any W_21bf0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bf4 : bv 32 := 0x02058263.
Lemma F_21bf4 : fetch_word Plain.M.loaded_segments (0x21bf4 : word) = Some W_21bf4.
Proof. vm_refl. Qed.
Lemma D_21bf4 : decode_any W_21bf4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bf8 : bv 32 := 0x04900893.
Lemma F_21bf8 : fetch_word Plain.M.loaded_segments (0x21bf8 : word) = Some W_21bf8.
Proof. vm_refl. Qed.
Lemma D_21bf8 : decode_any W_21bf8 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bfc : bv 32 := 0x00000593.
Lemma F_21bfc : fetch_word Plain.M.loaded_segments (0x21bfc : word) = Some W_21bfc.
Proof. vm_refl. Qed.
Lemma D_21bfc : decode_any W_21bfc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c00 : bv 32 := 0x00000613.
Lemma F_21c00 : fetch_word Plain.M.loaded_segments (0x21c00 : word) = Some W_21c00.
Proof. vm_refl. Qed.
Lemma D_21c00 : decode_any W_21c00 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c04 : bv 32 := 0x00000693.
Lemma F_21c04 : fetch_word Plain.M.loaded_segments (0x21c04 : word) = Some W_21c04.
Proof. vm_refl. Qed.
Lemma D_21c04 : decode_any W_21c04 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c08 : bv 32 := 0x00000513.
Lemma F_21c08 : fetch_word Plain.M.loaded_segments (0x21c08 : word) = Some W_21c08.
Proof. vm_refl. Qed.
Lemma D_21c08 : decode_any W_21c08 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c0c : bv 32 := 0x00000073.
Lemma F_21c0c : fetch_word Plain.M.loaded_segments (0x21c0c : word) = Some W_21c0c.
Proof. vm_refl. Qed.
Lemma E_21c0c : is_ecall W_21c0c = true.
Proof. vm_refl. Qed.

Definition W_21c10 : bv 32 := 0xff9ff06f.
Lemma F_21c10 : fetch_word Plain.M.loaded_segments (0x21c10 : word) = Some W_21c10.
Proof. vm_refl. Qed.
Lemma D_21c10 : decode_any W_21c10 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c14 : bv 32 := 0x00000023.
Lemma F_21c14 : fetch_word Plain.M.loaded_segments (0x21c14 : word) = Some W_21c14.
Proof. vm_refl. Qed.
Lemma D_21c14 : decode_any W_21c14 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c18 : bv 32 := 0x00050413.
Lemma F_21c18 : fetch_word Plain.M.loaded_segments (0x21c18 : word) = Some W_21c18.
Proof. vm_refl. Qed.
Lemma D_21c18 : decode_any W_21c18 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c1c : bv 32 := 0xdbdff0ef.
Lemma F_21c1c : fetch_word Plain.M.loaded_segments (0x21c1c : word) = Some W_21c1c.
Proof. vm_refl. Qed.
Lemma D_21c1c : decode_any W_21c1c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c20 : bv 32 := 0xf51ff0ef.
Lemma F_21c20 : fetch_word Plain.M.loaded_segments (0x21c20 : word) = Some W_21c20.
Proof. vm_refl. Qed.
Lemma D_21c20 : decode_any W_21c20 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c24 : bv 32 := 0x160020ef.
Lemma F_21c24 : fetch_word Plain.M.loaded_segments (0x21c24 : word) = Some W_21c24.
Proof. vm_refl. Qed.
Lemma D_21c24 : decode_any W_21c24 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c28 : bv 32 := 0x00040513.
Lemma F_21c28 : fetch_word Plain.M.loaded_segments (0x21c28 : word) = Some W_21c28.
Proof. vm_refl. Qed.
Lemma D_21c28 : decode_any W_21c28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c2c : bv 32 := 0xd91ff0ef.
Lemma F_21c2c : fetch_word Plain.M.loaded_segments (0x21c2c : word) = Some W_21c2c.
Proof. vm_refl. Qed.
Lemma D_21c2c : decode_any W_21c2c = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_295f8 : bv 32 := 0x00033597.
Lemma F_295f8 : fetch_word Plain.M.loaded_segments (0x295f8 : word) = Some W_295f8.
Proof. vm_refl. Qed.
Lemma D_295f8 : decode_any W_295f8 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_295fc : bv 32 := 0xaa358683.
Lemma F_295fc : fetch_word Plain.M.loaded_segments (0x295fc : word) = Some W_295fc.
Proof. vm_refl. Qed.
Lemma D_295fc : decode_any W_295fc = Some (Load SZ1 true 13 11 2723, 4%Z).
Proof. vm_refl. Qed.

Definition W_29600 : bv 32 := 0x1e068863.
Lemma F_29600 : fetch_word Plain.M.loaded_segments (0x29600 : word) = Some W_29600.
Proof. vm_refl. Qed.
Lemma D_29600 : decode_any W_29600 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_297f0 : bv 32 := 0x00008067.
Lemma F_297f0 : fetch_word Plain.M.loaded_segments (0x297f0 : word) = Some W_297f0.
Proof. vm_refl. Qed.
Lemma D_297f0 : decode_any W_297f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29880 : bv 32 := 0x00052583.
Lemma F_29880 : fetch_word Plain.M.loaded_segments (0x29880 : word) = Some W_29880.
Proof. vm_refl. Qed.
Lemma D_29880 : decode_any W_29880 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29884 : bv 32 := 0x0005c463.
Lemma F_29884 : fetch_word Plain.M.loaded_segments (0x29884 : word) = Some W_29884.
Proof. vm_refl. Qed.
Lemma D_29884 : decode_any W_29884 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29888 : bv 32 := 0x00008067.
Lemma F_29888 : fetch_word Plain.M.loaded_segments (0x29888 : word) = Some W_29888.
Proof. vm_refl. Qed.
Lemma D_29888 : decode_any W_29888 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
