(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ac844 : bv 32 := 0x08b50663.
Lemma F_ac844 : fetch_word Plain.M.loaded_segments (0xac890 : word) = Some W_ac844.
Proof. vm_refl. Qed.
Lemma D_ac844 : decode_any W_ac844 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac848 : bv 32 := 0x00a606b3.
Lemma F_ac848 : fetch_word Plain.M.loaded_segments (0xac894 : word) = Some W_ac848.
Proof. vm_refl. Qed.
Lemma D_ac848 : decode_any W_ac848 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac84c : bv 32 := 0x00161713.
Lemma F_ac84c : fetch_word Plain.M.loaded_segments (0xac898 : word) = Some W_ac84c.
Proof. vm_refl. Qed.
Lemma D_ac84c : decode_any W_ac84c = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac850 : bv 32 := 0x40d586b3.
Lemma F_ac850 : fetch_word Plain.M.loaded_segments (0xac89c : word) = Some W_ac850.
Proof. vm_refl. Qed.
Lemma D_ac850 : decode_any W_ac850 = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac854 : bv 32 := 0x40e00733.
Lemma F_ac854 : fetch_word Plain.M.loaded_segments (0xac8a0 : word) = Some W_ac854.
Proof. vm_refl. Qed.
Lemma D_ac854 : decode_any W_ac854 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac858 : bv 32 := 0x04d77063.
Lemma F_ac858 : fetch_word Plain.M.loaded_segments (0xac8a4 : word) = Some W_ac858.
Proof. vm_refl. Qed.
Lemma D_ac858 : decode_any W_ac858 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac85c : bv 32 := 0x00a5c6b3.
Lemma F_ac85c : fetch_word Plain.M.loaded_segments (0xac8a8 : word) = Some W_ac85c.
Proof. vm_refl. Qed.
Lemma D_ac85c : decode_any W_ac85c = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac860 : bv 32 := 0x0076f693.
Lemma F_ac860 : fetch_word Plain.M.loaded_segments (0xac8ac : word) = Some W_ac860.
Proof. vm_refl. Qed.
Lemma D_ac860 : decode_any W_ac860 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac864 : bv 32 := 0x02b57c63.
Lemma F_ac864 : fetch_word Plain.M.loaded_segments (0xac8b0 : word) = Some W_ac864.
Proof. vm_refl. Qed.
Lemma D_ac864 : decode_any W_ac864 = Some (Branch BC_GEU 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac868 : bv 32 := 0x06068663.
Lemma F_ac868 : fetch_word Plain.M.loaded_segments (0xac8b4 : word) = Some W_ac868.
Proof. vm_refl. Qed.
Lemma D_ac868 : decode_any W_ac868 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac86c : bv 32 := 0x00050693.
Lemma F_ac86c : fetch_word Plain.M.loaded_segments (0xac8b8 : word) = Some W_ac86c.
Proof. vm_refl. Qed.
Lemma D_ac86c : decode_any W_ac86c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac870 : bv 32 := 0x00058713.
Lemma F_ac870 : fetch_word Plain.M.loaded_segments (0xac8bc : word) = Some W_ac870.
Proof. vm_refl. Qed.
Lemma D_ac870 : decode_any W_ac870 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac874 : bv 32 := 0x04060e63.
Lemma F_ac874 : fetch_word Plain.M.loaded_segments (0xac8c0 : word) = Some W_ac874.
Proof. vm_refl. Qed.
Lemma D_ac874 : decode_any W_ac874 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac878 : bv 32 := 0x00c68633.
Lemma F_ac878 : fetch_word Plain.M.loaded_segments (0xac8c4 : word) = Some W_ac878.
Proof. vm_refl. Qed.
Lemma D_ac878 : decode_any W_ac878 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac87c : bv 32 := 0x00074583.
Lemma F_ac87c : fetch_word Plain.M.loaded_segments (0xac8c8 : word) = Some W_ac87c.
Proof. vm_refl. Qed.
Lemma D_ac87c : decode_any W_ac87c = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac880 : bv 32 := 0x00170713.
Lemma F_ac880 : fetch_word Plain.M.loaded_segments (0xac8cc : word) = Some W_ac880.
Proof. vm_refl. Qed.
Lemma D_ac880 : decode_any W_ac880 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac884 : bv 32 := 0x00168793.
Lemma F_ac884 : fetch_word Plain.M.loaded_segments (0xac8d0 : word) = Some W_ac884.
Proof. vm_refl. Qed.
Lemma D_ac884 : decode_any W_ac884 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac888 : bv 32 := 0x00b68023.
Lemma F_ac888 : fetch_word Plain.M.loaded_segments (0xac8d4 : word) = Some W_ac888.
Proof. vm_refl. Qed.
Lemma D_ac888 : decode_any W_ac888 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac88c : bv 32 := 0x00078693.
Lemma F_ac88c : fetch_word Plain.M.loaded_segments (0xac8d8 : word) = Some W_ac88c.
Proof. vm_refl. Qed.
Lemma D_ac88c : decode_any W_ac88c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac890 : bv 32 := 0xfec796e3.
Lemma F_ac890 : fetch_word Plain.M.loaded_segments (0xac8dc : word) = Some W_ac890.
Proof. vm_refl. Qed.
Lemma D_ac890 : decode_any W_ac890 = Some (Branch BC_NE 15 12 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac894 : bv 32 := 0x03c0006f.
Lemma F_ac894 : fetch_word Plain.M.loaded_segments (0xac8e0 : word) = Some W_ac894.
Proof. vm_refl. Qed.
Lemma D_ac894 : decode_any W_ac894 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac898 : bv 32 := 0xba9ff06f.
Lemma F_ac898 : fetch_word Plain.M.loaded_segments (0xac8e4 : word) = Some W_ac898.
Proof. vm_refl. Qed.
Lemma D_ac898 : decode_any W_ac898 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.
