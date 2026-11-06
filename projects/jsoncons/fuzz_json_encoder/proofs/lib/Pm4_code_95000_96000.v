(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_95020 : bv 32 := 0x00155593.
Lemma F_95020 : fetch_word Asan.M.loaded_segments (0x95070 : word) = Some W_95020.
Proof. vm_refl. Qed.
Lemma D_95020 : decode_any W_95020 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95024 : bv 32 := 0x55555637.
Lemma F_95024 : fetch_word Asan.M.loaded_segments (0x95074 : word) = Some W_95024.
Proof. vm_refl. Qed.
Lemma D_95024 : decode_any W_95024 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95028 : bv 32 := 0x333336b7.
Lemma F_95028 : fetch_word Asan.M.loaded_segments (0x95078 : word) = Some W_95028.
Proof. vm_refl. Qed.
Lemma D_95028 : decode_any W_95028 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9502c : bv 32 := 0x0f0f1737.
Lemma F_9502c : fetch_word Asan.M.loaded_segments (0x9507c : word) = Some W_9502c.
Proof. vm_refl. Qed.
Lemma D_9502c : decode_any W_9502c = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95030 : bv 32 := 0x010107b7.
Lemma F_95030 : fetch_word Asan.M.loaded_segments (0x95080 : word) = Some W_95030.
Proof. vm_refl. Qed.
Lemma D_95030 : decode_any W_95030 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95034 : bv 32 := 0x00b56533.
Lemma F_95034 : fetch_word Asan.M.loaded_segments (0x95084 : word) = Some W_95034.
Proof. vm_refl. Qed.
Lemma D_95034 : decode_any W_95034 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95038 : bv 32 := 0x5556059b.
Lemma F_95038 : fetch_word Asan.M.loaded_segments (0x95088 : word) = Some W_95038.
Proof. vm_refl. Qed.
Lemma D_95038 : decode_any W_95038 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9503c : bv 32 := 0x3336861b.
Lemma F_9503c : fetch_word Asan.M.loaded_segments (0x9508c : word) = Some W_9503c.
Proof. vm_refl. Qed.
Lemma D_9503c : decode_any W_9503c = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95040 : bv 32 := 0xf0f7069b.
Lemma F_95040 : fetch_word Asan.M.loaded_segments (0x95090 : word) = Some W_95040.
Proof. vm_refl. Qed.
Lemma D_95040 : decode_any W_95040 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95044 : bv 32 := 0x1017871b.
Lemma F_95044 : fetch_word Asan.M.loaded_segments (0x95094 : word) = Some W_95044.
Proof. vm_refl. Qed.
Lemma D_95044 : decode_any W_95044 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95048 : bv 32 := 0x00255793.
Lemma F_95048 : fetch_word Asan.M.loaded_segments (0x95098 : word) = Some W_95048.
Proof. vm_refl. Qed.
Lemma D_95048 : decode_any W_95048 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9504c : bv 32 := 0x00f56533.
Lemma F_9504c : fetch_word Asan.M.loaded_segments (0x9509c : word) = Some W_9504c.
Proof. vm_refl. Qed.
Lemma D_9504c : decode_any W_9504c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95050 : bv 32 := 0x02059793.
Lemma F_95050 : fetch_word Asan.M.loaded_segments (0x950a0 : word) = Some W_95050.
Proof. vm_refl. Qed.
Lemma D_95050 : decode_any W_95050 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95054 : bv 32 := 0x00f585b3.
Lemma F_95054 : fetch_word Asan.M.loaded_segments (0x950a4 : word) = Some W_95054.
Proof. vm_refl. Qed.
Lemma D_95054 : decode_any W_95054 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95058 : bv 32 := 0x02061793.
Lemma F_95058 : fetch_word Asan.M.loaded_segments (0x950a8 : word) = Some W_95058.
Proof. vm_refl. Qed.
Lemma D_95058 : decode_any W_95058 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9505c : bv 32 := 0x00f60633.
Lemma F_9505c : fetch_word Asan.M.loaded_segments (0x950ac : word) = Some W_9505c.
Proof. vm_refl. Qed.
Lemma D_9505c : decode_any W_9505c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95060 : bv 32 := 0x02069793.
Lemma F_95060 : fetch_word Asan.M.loaded_segments (0x950b0 : word) = Some W_95060.
Proof. vm_refl. Qed.
Lemma D_95060 : decode_any W_95060 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95064 : bv 32 := 0x00f686b3.
Lemma F_95064 : fetch_word Asan.M.loaded_segments (0x950b4 : word) = Some W_95064.
Proof. vm_refl. Qed.
Lemma D_95064 : decode_any W_95064 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95068 : bv 32 := 0x02071793.
Lemma F_95068 : fetch_word Asan.M.loaded_segments (0x950b8 : word) = Some W_95068.
Proof. vm_refl. Qed.
Lemma D_95068 : decode_any W_95068 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9506c : bv 32 := 0x00f70733.
Lemma F_9506c : fetch_word Asan.M.loaded_segments (0x950bc : word) = Some W_9506c.
Proof. vm_refl. Qed.
Lemma D_9506c : decode_any W_9506c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95070 : bv 32 := 0x00455793.
Lemma F_95070 : fetch_word Asan.M.loaded_segments (0x950c0 : word) = Some W_95070.
Proof. vm_refl. Qed.
Lemma D_95070 : decode_any W_95070 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95074 : bv 32 := 0x00f56533.
Lemma F_95074 : fetch_word Asan.M.loaded_segments (0x950c4 : word) = Some W_95074.
Proof. vm_refl. Qed.
Lemma D_95074 : decode_any W_95074 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95078 : bv 32 := 0x00855793.
Lemma F_95078 : fetch_word Asan.M.loaded_segments (0x950c8 : word) = Some W_95078.
Proof. vm_refl. Qed.
Lemma D_95078 : decode_any W_95078 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9507c : bv 32 := 0x00f56533.
Lemma F_9507c : fetch_word Asan.M.loaded_segments (0x950cc : word) = Some W_9507c.
Proof. vm_refl. Qed.
Lemma D_9507c : decode_any W_9507c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95080 : bv 32 := 0x01055793.
Lemma F_95080 : fetch_word Asan.M.loaded_segments (0x950d0 : word) = Some W_95080.
Proof. vm_refl. Qed.
Lemma D_95080 : decode_any W_95080 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95084 : bv 32 := 0x00f56533.
Lemma F_95084 : fetch_word Asan.M.loaded_segments (0x950d4 : word) = Some W_95084.
Proof. vm_refl. Qed.
Lemma D_95084 : decode_any W_95084 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95088 : bv 32 := 0x02055793.
Lemma F_95088 : fetch_word Asan.M.loaded_segments (0x950d8 : word) = Some W_95088.
Proof. vm_refl. Qed.
Lemma D_95088 : decode_any W_95088 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9508c : bv 32 := 0x00f56533.
Lemma F_9508c : fetch_word Asan.M.loaded_segments (0x950dc : word) = Some W_9508c.
Proof. vm_refl. Qed.
Lemma D_9508c : decode_any W_9508c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95090 : bv 32 := 0xfff54513.
Lemma F_95090 : fetch_word Asan.M.loaded_segments (0x950e0 : word) = Some W_95090.
Proof. vm_refl. Qed.
Lemma D_95090 : decode_any W_95090 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95094 : bv 32 := 0x00155793.
Lemma F_95094 : fetch_word Asan.M.loaded_segments (0x950e4 : word) = Some W_95094.
Proof. vm_refl. Qed.
Lemma D_95094 : decode_any W_95094 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95098 : bv 32 := 0x00b7f5b3.
Lemma F_95098 : fetch_word Asan.M.loaded_segments (0x950e8 : word) = Some W_95098.
Proof. vm_refl. Qed.
Lemma D_95098 : decode_any W_95098 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9509c : bv 32 := 0x40b50533.
Lemma F_9509c : fetch_word Asan.M.loaded_segments (0x950ec : word) = Some W_9509c.
Proof. vm_refl. Qed.
Lemma D_9509c : decode_any W_9509c = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950a0 : bv 32 := 0x00c575b3.
Lemma F_950a0 : fetch_word Asan.M.loaded_segments (0x950f0 : word) = Some W_950a0.
Proof. vm_refl. Qed.
Lemma D_950a0 : decode_any W_950a0 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950a4 : bv 32 := 0x00255513.
Lemma F_950a4 : fetch_word Asan.M.loaded_segments (0x950f4 : word) = Some W_950a4.
Proof. vm_refl. Qed.
Lemma D_950a4 : decode_any W_950a4 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950a8 : bv 32 := 0x00c57533.
Lemma F_950a8 : fetch_word Asan.M.loaded_segments (0x950f8 : word) = Some W_950a8.
Proof. vm_refl. Qed.
Lemma D_950a8 : decode_any W_950a8 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950ac : bv 32 := 0x00a58533.
Lemma F_950ac : fetch_word Asan.M.loaded_segments (0x950fc : word) = Some W_950ac.
Proof. vm_refl. Qed.
Lemma D_950ac : decode_any W_950ac = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950b0 : bv 32 := 0x00455593.
Lemma F_950b0 : fetch_word Asan.M.loaded_segments (0x95100 : word) = Some W_950b0.
Proof. vm_refl. Qed.
Lemma D_950b0 : decode_any W_950b0 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950b4 : bv 32 := 0x00b50533.
Lemma F_950b4 : fetch_word Asan.M.loaded_segments (0x95104 : word) = Some W_950b4.
Proof. vm_refl. Qed.
Lemma D_950b4 : decode_any W_950b4 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950b8 : bv 32 := 0x00d57533.
Lemma F_950b8 : fetch_word Asan.M.loaded_segments (0x95108 : word) = Some W_950b8.
Proof. vm_refl. Qed.
Lemma D_950b8 : decode_any W_950b8 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950bc : bv 32 := 0x02e50533.
Lemma F_950bc : fetch_word Asan.M.loaded_segments (0x9510c : word) = Some W_950bc.
Proof. vm_refl. Qed.
Lemma D_950bc : decode_any W_950bc = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950c0 : bv 32 := 0x03855513.
Lemma F_950c0 : fetch_word Asan.M.loaded_segments (0x95110 : word) = Some W_950c0.
Proof. vm_refl. Qed.
Lemma D_950c0 : decode_any W_950c0 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950c4 : bv 32 := 0x40a0053b.
Lemma F_950c4 : fetch_word Asan.M.loaded_segments (0x95114 : word) = Some W_950c4.
Proof. vm_refl. Qed.
Lemma D_950c4 : decode_any W_950c4 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950c8 : bv 32 := 0xfff00593.
Lemma F_950c8 : fetch_word Asan.M.loaded_segments (0x95118 : word) = Some W_950c8.
Proof. vm_refl. Qed.
Lemma D_950c8 : decode_any W_950c8 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950cc : bv 32 := 0x00a59533.
Lemma F_950cc : fetch_word Asan.M.loaded_segments (0x9511c : word) = Some W_950cc.
Proof. vm_refl. Qed.
Lemma D_950cc : decode_any W_950cc = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_950d0 : bv 32 := 0xfff54513.
Lemma F_950d0 : fetch_word Asan.M.loaded_segments (0x95120 : word) = Some W_950d0.
Proof. vm_refl. Qed.
Lemma D_950d0 : decode_any W_950d0 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a28 : bv 32 := 0xfd010113.
Lemma F_95a28 : fetch_word Asan.M.loaded_segments (0x95a78 : word) = Some W_95a28.
Proof. vm_refl. Qed.
Lemma D_95a28 : decode_any W_95a28 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a2c : bv 32 := 0x02113423.
Lemma F_95a2c : fetch_word Asan.M.loaded_segments (0x95a7c : word) = Some W_95a2c.
Proof. vm_refl. Qed.
Lemma D_95a2c : decode_any W_95a2c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a30 : bv 32 := 0x02813023.
Lemma F_95a30 : fetch_word Asan.M.loaded_segments (0x95a80 : word) = Some W_95a30.
Proof. vm_refl. Qed.
Lemma D_95a30 : decode_any W_95a30 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a34 : bv 32 := 0x00913c23.
Lemma F_95a34 : fetch_word Asan.M.loaded_segments (0x95a84 : word) = Some W_95a34.
Proof. vm_refl. Qed.
Lemma D_95a34 : decode_any W_95a34 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a38 : bv 32 := 0x01213823.
Lemma F_95a38 : fetch_word Asan.M.loaded_segments (0x95a88 : word) = Some W_95a38.
Proof. vm_refl. Qed.
Lemma D_95a38 : decode_any W_95a38 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a3c : bv 32 := 0x02050e63.
Lemma F_95a3c : fetch_word Asan.M.loaded_segments (0x95a8c : word) = Some W_95a3c.
Proof. vm_refl. Qed.
Lemma D_95a3c : decode_any W_95a3c = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a40 : bv 32 := 0x00058413.
Lemma F_95a40 : fetch_word Asan.M.loaded_segments (0x95a90 : word) = Some W_95a40.
Proof. vm_refl. Qed.
Lemma D_95a40 : decode_any W_95a40 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a44 : bv 32 := 0x02058a63.
Lemma F_95a44 : fetch_word Asan.M.loaded_segments (0x95a94 : word) = Some W_95a44.
Proof. vm_refl. Qed.
Lemma D_95a44 : decode_any W_95a44 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a48 : bv 32 := 0x00060493.
Lemma F_95a48 : fetch_word Asan.M.loaded_segments (0x95a98 : word) = Some W_95a48.
Proof. vm_refl. Qed.
Lemma D_95a48 : decode_any W_95a48 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a4c : bv 32 := 0x00050913.
Lemma F_95a4c : fetch_word Asan.M.loaded_segments (0x95a9c : word) = Some W_95a4c.
Proof. vm_refl. Qed.
Lemma D_95a4c : decode_any W_95a4c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a50 : bv 32 := 0x00040593.
Lemma F_95a50 : fetch_word Asan.M.loaded_segments (0x95aa0 : word) = Some W_95a50.
Proof. vm_refl. Qed.
Lemma D_95a50 : decode_any W_95a50 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a54 : bv 32 := 0xf90fe0ef.
Lemma F_95a54 : fetch_word Asan.M.loaded_segments (0x95aa4 : word) = Some W_95a54.
Proof. vm_refl. Qed.
Lemma D_95a54 : decode_any W_95a54 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a58 : bv 32 := 0xaaaab5b7.
Lemma F_95a58 : fetch_word Asan.M.loaded_segments (0x95aa8 : word) = Some W_95a58.
Proof. vm_refl. Qed.
Lemma D_95a58 : decode_any W_95a58 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a5c : bv 32 := 0xaaa58593.
Lemma F_95a5c : fetch_word Asan.M.loaded_segments (0x95aac : word) = Some W_95a5c.
Proof. vm_refl. Qed.
Lemma D_95a5c : decode_any W_95a5c = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a60 : bv 32 := 0x00b12623.
Lemma F_95a60 : fetch_word Asan.M.loaded_segments (0x95ab0 : word) = Some W_95a60.
Proof. vm_refl. Qed.
Lemma D_95a60 : decode_any W_95a60 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a64 : bv 32 := 0x00c10593.
Lemma F_95a64 : fetch_word Asan.M.loaded_segments (0x95ab4 : word) = Some W_95a64.
Proof. vm_refl. Qed.
Lemma D_95a64 : decode_any W_95a64 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a68 : bv 32 := 0xf50fe0ef.
Lemma F_95a68 : fetch_word Asan.M.loaded_segments (0x95ab8 : word) = Some W_95a68.
Proof. vm_refl. Qed.
Lemma D_95a68 : decode_any W_95a68 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a6c : bv 32 := 0x02051263.
Lemma F_95a6c : fetch_word Asan.M.loaded_segments (0x95abc : word) = Some W_95a6c.
Proof. vm_refl. Qed.
Lemma D_95a6c : decode_any W_95a6c = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a70 : bv 32 := 0x00040513.
Lemma F_95a70 : fetch_word Asan.M.loaded_segments (0x95ac0 : word) = Some W_95a70.
Proof. vm_refl. Qed.
Lemma D_95a70 : decode_any W_95a70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a74 : bv 32 := 0xe70fa0ef.
Lemma F_95a74 : fetch_word Asan.M.loaded_segments (0x95ac4 : word) = Some W_95a74.
Proof. vm_refl. Qed.
Lemma D_95a74 : decode_any W_95a74 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a78 : bv 32 := 0x02813083.
Lemma F_95a78 : fetch_word Asan.M.loaded_segments (0x95ac8 : word) = Some W_95a78.
Proof. vm_refl. Qed.
Lemma D_95a78 : decode_any W_95a78 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a7c : bv 32 := 0x02013403.
Lemma F_95a7c : fetch_word Asan.M.loaded_segments (0x95acc : word) = Some W_95a7c.
Proof. vm_refl. Qed.
Lemma D_95a7c : decode_any W_95a7c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a80 : bv 32 := 0x01813483.
Lemma F_95a80 : fetch_word Asan.M.loaded_segments (0x95ad0 : word) = Some W_95a80.
Proof. vm_refl. Qed.
Lemma D_95a80 : decode_any W_95a80 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a84 : bv 32 := 0x01013903.
Lemma F_95a84 : fetch_word Asan.M.loaded_segments (0x95ad4 : word) = Some W_95a84.
Proof. vm_refl. Qed.
Lemma D_95a84 : decode_any W_95a84 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a88 : bv 32 := 0x03010113.
Lemma F_95a88 : fetch_word Asan.M.loaded_segments (0x95ad8 : word) = Some W_95a88.
Proof. vm_refl. Qed.
Lemma D_95a88 : decode_any W_95a88 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a8c : bv 32 := 0x00008067.
Lemma F_95a8c : fetch_word Asan.M.loaded_segments (0x95adc : word) = Some W_95a8c.
Proof. vm_refl. Qed.
Lemma D_95a8c : decode_any W_95a8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aa4 : bv 32 := 0xfd010113.
Lemma F_95aa4 : fetch_word Asan.M.loaded_segments (0x95af4 : word) = Some W_95aa4.
Proof. vm_refl. Qed.
Lemma D_95aa4 : decode_any W_95aa4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aa8 : bv 32 := 0x02113423.
Lemma F_95aa8 : fetch_word Asan.M.loaded_segments (0x95af8 : word) = Some W_95aa8.
Proof. vm_refl. Qed.
Lemma D_95aa8 : decode_any W_95aa8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aac : bv 32 := 0x02813023.
Lemma F_95aac : fetch_word Asan.M.loaded_segments (0x95afc : word) = Some W_95aac.
Proof. vm_refl. Qed.
Lemma D_95aac : decode_any W_95aac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab0 : bv 32 := 0x00913c23.
Lemma F_95ab0 : fetch_word Asan.M.loaded_segments (0x95b00 : word) = Some W_95ab0.
Proof. vm_refl. Qed.
Lemma D_95ab0 : decode_any W_95ab0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab4 : bv 32 := 0x01213823.
Lemma F_95ab4 : fetch_word Asan.M.loaded_segments (0x95b04 : word) = Some W_95ab4.
Proof. vm_refl. Qed.
Lemma D_95ab4 : decode_any W_95ab4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab8 : bv 32 := 0x00058413.
Lemma F_95ab8 : fetch_word Asan.M.loaded_segments (0x95b08 : word) = Some W_95ab8.
Proof. vm_refl. Qed.
Lemma D_95ab8 : decode_any W_95ab8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95abc : bv 32 := 0x000cb597.
Lemma F_95abc : fetch_word Asan.M.loaded_segments (0x95b0c : word) = Some W_95abc.
Proof. vm_refl. Qed.
Lemma D_95abc : decode_any W_95abc = Some (Auipc 11 203, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ac0 : bv 32 := 0x0ec5b903.
Lemma F_95ac0 : fetch_word Asan.M.loaded_segments (0x95b10 : word) = Some W_95ac0.
Proof. vm_refl. Qed.
Lemma D_95ac0 : decode_any W_95ac0 = Some (Load SZ8 true 18 11 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ac4 : bv 32 := 0x00093583.
Lemma F_95ac4 : fetch_word Asan.M.loaded_segments (0x95b14 : word) = Some W_95ac4.
Proof. vm_refl. Qed.
Lemma D_95ac4 : decode_any W_95ac4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ac8 : bv 32 := 0x00050493.
Lemma F_95ac8 : fetch_word Asan.M.loaded_segments (0x95b18 : word) = Some W_95ac8.
Proof. vm_refl. Qed.
Lemma D_95ac8 : decode_any W_95ac8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95acc : bv 32 := 0x00059863.
Lemma F_95acc : fetch_word Asan.M.loaded_segments (0x95b1c : word) = Some W_95acc.
Proof. vm_refl. Qed.
Lemma D_95acc : decode_any W_95acc = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95adc : bv 32 := 0xfff58513.
Lemma F_95adc : fetch_word Asan.M.loaded_segments (0x95b2c : word) = Some W_95adc.
Proof. vm_refl. Qed.
Lemma D_95adc : decode_any W_95adc = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ae0 : bv 32 := 0x00a5f533.
Lemma F_95ae0 : fetch_word Asan.M.loaded_segments (0x95b30 : word) = Some W_95ae0.
Proof. vm_refl. Qed.
Lemma D_95ae0 : decode_any W_95ae0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ae4 : bv 32 := 0x08051a63.
Lemma F_95ae4 : fetch_word Asan.M.loaded_segments (0x95b34 : word) = Some W_95ae4.
Proof. vm_refl. Qed.
Lemma D_95ae4 : decode_any W_95ae4 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ae8 : bv 32 := 0x00b484b3.
Lemma F_95ae8 : fetch_word Asan.M.loaded_segments (0x95b38 : word) = Some W_95ae8.
Proof. vm_refl. Qed.
Lemma D_95ae8 : decode_any W_95ae8 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aec : bv 32 := 0x40b00533.
Lemma F_95aec : fetch_word Asan.M.loaded_segments (0x95b3c : word) = Some W_95aec.
Proof. vm_refl. Qed.
Lemma D_95aec : decode_any W_95aec = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af0 : bv 32 := 0xfff48493.
Lemma F_95af0 : fetch_word Asan.M.loaded_segments (0x95b40 : word) = Some W_95af0.
Proof. vm_refl. Qed.
Lemma D_95af0 : decode_any W_95af0 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af4 : bv 32 := 0x00a4f4b3.
Lemma F_95af4 : fetch_word Asan.M.loaded_segments (0x95b44 : word) = Some W_95af4.
Proof. vm_refl. Qed.
Lemma D_95af4 : decode_any W_95af4 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af8 : bv 32 := 0x02200513.
Lemma F_95af8 : fetch_word Asan.M.loaded_segments (0x95b48 : word) = Some W_95af8.
Proof. vm_refl. Qed.
Lemma D_95af8 : decode_any W_95af8 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95afc : bv 32 := 0x00a12623.
Lemma F_95afc : fetch_word Asan.M.loaded_segments (0x95b4c : word) = Some W_95afc.
Proof. vm_refl. Qed.
Lemma D_95afc : decode_any W_95afc = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b00 : bv 32 := 0x00c10613.
Lemma F_95b00 : fetch_word Asan.M.loaded_segments (0x95b50 : word) = Some W_95b00.
Proof. vm_refl. Qed.
Lemma D_95b00 : decode_any W_95b00 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b04 : bv 32 := 0x00040513.
Lemma F_95b04 : fetch_word Asan.M.loaded_segments (0x95b54 : word) = Some W_95b04.
Proof. vm_refl. Qed.
Lemma D_95b04 : decode_any W_95b04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b08 : bv 32 := 0x00048593.
Lemma F_95b08 : fetch_word Asan.M.loaded_segments (0x95b58 : word) = Some W_95b08.
Proof. vm_refl. Qed.
Lemma D_95b08 : decode_any W_95b08 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b0c : bv 32 := 0x279000ef.
Lemma F_95b0c : fetch_word Asan.M.loaded_segments (0x95b5c : word) = Some W_95b0c.
Proof. vm_refl. Qed.
Lemma D_95b0c : decode_any W_95b0c = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b10 : bv 32 := 0x00c12683.
Lemma F_95b10 : fetch_word Asan.M.loaded_segments (0x95b60 : word) = Some W_95b10.
Proof. vm_refl. Qed.
Lemma D_95b10 : decode_any W_95b10 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b14 : bv 32 := 0x00050713.
Lemma F_95b14 : fetch_word Asan.M.loaded_segments (0x95b64 : word) = Some W_95b14.
Proof. vm_refl. Qed.
Lemma D_95b14 : decode_any W_95b14 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b18 : bv 32 := 0x00300613.
Lemma F_95b18 : fetch_word Asan.M.loaded_segments (0x95b68 : word) = Some W_95b18.
Proof. vm_refl. Qed.
Lemma D_95b18 : decode_any W_95b18 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b1c : bv 32 := 0x00000513.
Lemma F_95b1c : fetch_word Asan.M.loaded_segments (0x95b6c : word) = Some W_95b1c.
Proof. vm_refl. Qed.
Lemma D_95b1c : decode_any W_95b1c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b20 : bv 32 := 0x00048593.
Lemma F_95b20 : fetch_word Asan.M.loaded_segments (0x95b70 : word) = Some W_95b20.
Proof. vm_refl. Qed.
Lemma D_95b20 : decode_any W_95b20 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b24 : bv 32 := 0x00000793.
Lemma F_95b24 : fetch_word Asan.M.loaded_segments (0x95b74 : word) = Some W_95b24.
Proof. vm_refl. Qed.
Lemma D_95b24 : decode_any W_95b24 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b28 : bv 32 := 0xeb0fe0ef.
Lemma F_95b28 : fetch_word Asan.M.loaded_segments (0x95b78 : word) = Some W_95b28.
Proof. vm_refl. Qed.
Lemma D_95b28 : decode_any W_95b28 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b2c : bv 32 := 0x00050913.
Lemma F_95b2c : fetch_word Asan.M.loaded_segments (0x95b7c : word) = Some W_95b2c.
Proof. vm_refl. Qed.
Lemma D_95b2c : decode_any W_95b2c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b30 : bv 32 := 0x00000593.
Lemma F_95b30 : fetch_word Asan.M.loaded_segments (0x95b80 : word) = Some W_95b30.
Proof. vm_refl. Qed.
Lemma D_95b30 : decode_any W_95b30 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b34 : bv 32 := 0xe84fe0ef.
Lemma F_95b34 : fetch_word Asan.M.loaded_segments (0x95b84 : word) = Some W_95b34.
Proof. vm_refl. Qed.
Lemma D_95b34 : decode_any W_95b34 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b38 : bv 32 := 0xaaaab537.
Lemma F_95b38 : fetch_word Asan.M.loaded_segments (0x95b88 : word) = Some W_95b38.
Proof. vm_refl. Qed.
Lemma D_95b38 : decode_any W_95b38 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b3c : bv 32 := 0xaaa50513.
Lemma F_95b3c : fetch_word Asan.M.loaded_segments (0x95b8c : word) = Some W_95b3c.
Proof. vm_refl. Qed.
Lemma D_95b3c : decode_any W_95b3c = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b40 : bv 32 := 0x00a12423.
Lemma F_95b40 : fetch_word Asan.M.loaded_segments (0x95b90 : word) = Some W_95b40.
Proof. vm_refl. Qed.
Lemma D_95b40 : decode_any W_95b40 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b44 : bv 32 := 0x00810593.
Lemma F_95b44 : fetch_word Asan.M.loaded_segments (0x95b94 : word) = Some W_95b44.
Proof. vm_refl. Qed.
Lemma D_95b44 : decode_any W_95b44 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b48 : bv 32 := 0x00090513.
Lemma F_95b48 : fetch_word Asan.M.loaded_segments (0x95b98 : word) = Some W_95b48.
Proof. vm_refl. Qed.
Lemma D_95b48 : decode_any W_95b48 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b4c : bv 32 := 0xe6cfe0ef.
Lemma F_95b4c : fetch_word Asan.M.loaded_segments (0x95b9c : word) = Some W_95b4c.
Proof. vm_refl. Qed.
Lemma D_95b4c : decode_any W_95b4c = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b50 : bv 32 := 0x02051c63.
Lemma F_95b50 : fetch_word Asan.M.loaded_segments (0x95ba0 : word) = Some W_95b50.
Proof. vm_refl. Qed.
Lemma D_95b50 : decode_any W_95b50 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b54 : bv 32 := 0x00048513.
Lemma F_95b54 : fetch_word Asan.M.loaded_segments (0x95ba4 : word) = Some W_95b54.
Proof. vm_refl. Qed.
Lemma D_95b54 : decode_any W_95b54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b58 : bv 32 := 0xd48fa0ef.
Lemma F_95b58 : fetch_word Asan.M.loaded_segments (0x95ba8 : word) = Some W_95b58.
Proof. vm_refl. Qed.
Lemma D_95b58 : decode_any W_95b58 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b5c : bv 32 := 0x00090513.
Lemma F_95b5c : fetch_word Asan.M.loaded_segments (0x95bac : word) = Some W_95b5c.
Proof. vm_refl. Qed.
Lemma D_95b5c : decode_any W_95b5c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b60 : bv 32 := 0x02813083.
Lemma F_95b60 : fetch_word Asan.M.loaded_segments (0x95bb0 : word) = Some W_95b60.
Proof. vm_refl. Qed.
Lemma D_95b60 : decode_any W_95b60 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b64 : bv 32 := 0x02013403.
Lemma F_95b64 : fetch_word Asan.M.loaded_segments (0x95bb4 : word) = Some W_95b64.
Proof. vm_refl. Qed.
Lemma D_95b64 : decode_any W_95b64 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b68 : bv 32 := 0x01813483.
Lemma F_95b68 : fetch_word Asan.M.loaded_segments (0x95bb8 : word) = Some W_95b68.
Proof. vm_refl. Qed.
Lemma D_95b68 : decode_any W_95b68 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b6c : bv 32 := 0x01013903.
Lemma F_95b6c : fetch_word Asan.M.loaded_segments (0x95bbc : word) = Some W_95b6c.
Proof. vm_refl. Qed.
Lemma D_95b6c : decode_any W_95b6c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b70 : bv 32 := 0x03010113.
Lemma F_95b70 : fetch_word Asan.M.loaded_segments (0x95bc0 : word) = Some W_95b70.
Proof. vm_refl. Qed.
Lemma D_95b70 : decode_any W_95b70 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b74 : bv 32 := 0x00008067.
Lemma F_95b74 : fetch_word Asan.M.loaded_segments (0x95bc4 : word) = Some W_95b74.
Proof. vm_refl. Qed.
Lemma D_95b74 : decode_any W_95b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ee4 : bv 32 := 0x00060693.
Lemma F_95ee4 : fetch_word Asan.M.loaded_segments (0x95f34 : word) = Some W_95ee4.
Proof. vm_refl. Qed.
Lemma D_95ee4 : decode_any W_95ee4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ee8 : bv 32 := 0x00000613.
Lemma F_95ee8 : fetch_word Asan.M.loaded_segments (0x95f38 : word) = Some W_95ee8.
Proof. vm_refl. Qed.
Lemma D_95ee8 : decode_any W_95ee8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eec : bv 32 := 0x0040006f.
Lemma F_95eec : fetch_word Asan.M.loaded_segments (0x95f3c : word) = Some W_95eec.
Proof. vm_refl. Qed.
Lemma D_95eec : decode_any W_95eec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef0 : bv 32 := 0xfa010113.
Lemma F_95ef0 : fetch_word Asan.M.loaded_segments (0x95f40 : word) = Some W_95ef0.
Proof. vm_refl. Qed.
Lemma D_95ef0 : decode_any W_95ef0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef4 : bv 32 := 0x04113c23.
Lemma F_95ef4 : fetch_word Asan.M.loaded_segments (0x95f44 : word) = Some W_95ef4.
Proof. vm_refl. Qed.
Lemma D_95ef4 : decode_any W_95ef4 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef8 : bv 32 := 0x04813823.
Lemma F_95ef8 : fetch_word Asan.M.loaded_segments (0x95f48 : word) = Some W_95ef8.
Proof. vm_refl. Qed.
Lemma D_95ef8 : decode_any W_95ef8 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95efc : bv 32 := 0x04913423.
Lemma F_95efc : fetch_word Asan.M.loaded_segments (0x95f4c : word) = Some W_95efc.
Proof. vm_refl. Qed.
Lemma D_95efc : decode_any W_95efc = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f00 : bv 32 := 0x05213023.
Lemma F_95f00 : fetch_word Asan.M.loaded_segments (0x95f50 : word) = Some W_95f00.
Proof. vm_refl. Qed.
Lemma D_95f00 : decode_any W_95f00 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f04 : bv 32 := 0x03313c23.
Lemma F_95f04 : fetch_word Asan.M.loaded_segments (0x95f54 : word) = Some W_95f04.
Proof. vm_refl. Qed.
Lemma D_95f04 : decode_any W_95f04 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f08 : bv 32 := 0x03413823.
Lemma F_95f08 : fetch_word Asan.M.loaded_segments (0x95f58 : word) = Some W_95f08.
Proof. vm_refl. Qed.
Lemma D_95f08 : decode_any W_95f08 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f0c : bv 32 := 0x00068993.
Lemma F_95f0c : fetch_word Asan.M.loaded_segments (0x95f5c : word) = Some W_95f0c.
Proof. vm_refl. Qed.
Lemma D_95f0c : decode_any W_95f0c = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f10 : bv 32 := 0x00060493.
Lemma F_95f10 : fetch_word Asan.M.loaded_segments (0x95f60 : word) = Some W_95f10.
Proof. vm_refl. Qed.
Lemma D_95f10 : decode_any W_95f10 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f14 : bv 32 := 0x00058413.
Lemma F_95f14 : fetch_word Asan.M.loaded_segments (0x95f64 : word) = Some W_95f14.
Proof. vm_refl. Qed.
Lemma D_95f14 : decode_any W_95f14 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f18 : bv 32 := 0x000cb597.
Lemma F_95f18 : fetch_word Asan.M.loaded_segments (0x95f68 : word) = Some W_95f18.
Proof. vm_refl. Qed.
Lemma D_95f18 : decode_any W_95f18 = Some (Auipc 11 203, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f1c : bv 32 := 0xc905ba03.
Lemma F_95f1c : fetch_word Asan.M.loaded_segments (0x95f6c : word) = Some W_95f1c.
Proof. vm_refl. Qed.
Lemma D_95f1c : decode_any W_95f1c = Some (Load SZ8 true 20 11 3216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f20 : bv 32 := 0x000a3583.
Lemma F_95f20 : fetch_word Asan.M.loaded_segments (0x95f70 : word) = Some W_95f20.
Proof. vm_refl. Qed.
Lemma D_95f20 : decode_any W_95f20 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f24 : bv 32 := 0x00050913.
Lemma F_95f24 : fetch_word Asan.M.loaded_segments (0x95f74 : word) = Some W_95f24.
Proof. vm_refl. Qed.
Lemma D_95f24 : decode_any W_95f24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f28 : bv 32 := 0x00059863.
Lemma F_95f28 : fetch_word Asan.M.loaded_segments (0x95f78 : word) = Some W_95f28.
Proof. vm_refl. Qed.
Lemma D_95f28 : decode_any W_95f28 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f38 : bv 32 := 0xfff58513.
Lemma F_95f38 : fetch_word Asan.M.loaded_segments (0x95f88 : word) = Some W_95f38.
Proof. vm_refl. Qed.
Lemma D_95f38 : decode_any W_95f38 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f3c : bv 32 := 0x00a5f533.
Lemma F_95f3c : fetch_word Asan.M.loaded_segments (0x95f8c : word) = Some W_95f3c.
Proof. vm_refl. Qed.
Lemma D_95f3c : decode_any W_95f3c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f40 : bv 32 := 0x0a051863.
Lemma F_95f40 : fetch_word Asan.M.loaded_segments (0x95f90 : word) = Some W_95f40.
Proof. vm_refl. Qed.
Lemma D_95f40 : decode_any W_95f40 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f44 : bv 32 := 0x00b40433.
Lemma F_95f44 : fetch_word Asan.M.loaded_segments (0x95f94 : word) = Some W_95f44.
Proof. vm_refl. Qed.
Lemma D_95f44 : decode_any W_95f44 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f48 : bv 32 := 0xfff40413.
Lemma F_95f48 : fetch_word Asan.M.loaded_segments (0x95f98 : word) = Some W_95f48.
Proof. vm_refl. Qed.
Lemma D_95f48 : decode_any W_95f48 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f4c : bv 32 := 0x40b00533.
Lemma F_95f4c : fetch_word Asan.M.loaded_segments (0x95f9c : word) = Some W_95f4c.
Proof. vm_refl. Qed.
Lemma D_95f4c : decode_any W_95f4c = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f50 : bv 32 := 0x00a47433.
Lemma F_95f50 : fetch_word Asan.M.loaded_segments (0x95fa0 : word) = Some W_95f50.
Proof. vm_refl. Qed.
Lemma D_95f50 : decode_any W_95f50 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f54 : bv 32 := 0x00059863.
Lemma F_95f54 : fetch_word Asan.M.loaded_segments (0x95fa4 : word) = Some W_95f54.
Proof. vm_refl. Qed.
Lemma D_95f54 : decode_any W_95f54 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f64 : bv 32 := 0x00a97933.
Lemma F_95f64 : fetch_word Asan.M.loaded_segments (0x95fb4 : word) = Some W_95f64.
Proof. vm_refl. Qed.
Lemma D_95f64 : decode_any W_95f64 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f68 : bv 32 := 0x03200513.
Lemma F_95f68 : fetch_word Asan.M.loaded_segments (0x95fb8 : word) = Some W_95f68.
Proof. vm_refl. Qed.
Lemma D_95f68 : decode_any W_95f68 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f6c : bv 32 := 0x00a12023.
Lemma F_95f6c : fetch_word Asan.M.loaded_segments (0x95fbc : word) = Some W_95f6c.
Proof. vm_refl. Qed.
Lemma D_95f6c : decode_any W_95f6c = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f70 : bv 32 := 0x00010613.
Lemma F_95f70 : fetch_word Asan.M.loaded_segments (0x95fc0 : word) = Some W_95f70.
Proof. vm_refl. Qed.
Lemma D_95f70 : decode_any W_95f70 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f74 : bv 32 := 0x00098513.
Lemma F_95f74 : fetch_word Asan.M.loaded_segments (0x95fc4 : word) = Some W_95f74.
Proof. vm_refl. Qed.
Lemma D_95f74 : decode_any W_95f74 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f78 : bv 32 := 0x00040593.
Lemma F_95f78 : fetch_word Asan.M.loaded_segments (0x95fc8 : word) = Some W_95f78.
Proof. vm_refl. Qed.
Lemma D_95f78 : decode_any W_95f78 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f7c : bv 32 := 0x608000ef.
Lemma F_95f7c : fetch_word Asan.M.loaded_segments (0x95fcc : word) = Some W_95f7c.
Proof. vm_refl. Qed.
Lemma D_95f7c : decode_any W_95f7c = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f80 : bv 32 := 0x00012683.
Lemma F_95f80 : fetch_word Asan.M.loaded_segments (0x95fd0 : word) = Some W_95f80.
Proof. vm_refl. Qed.
Lemma D_95f80 : decode_any W_95f80 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f84 : bv 32 := 0x00050713.
Lemma F_95f84 : fetch_word Asan.M.loaded_segments (0x95fd4 : word) = Some W_95f84.
Proof. vm_refl. Qed.
Lemma D_95f84 : decode_any W_95f84 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f88 : bv 32 := 0x00300613.
Lemma F_95f88 : fetch_word Asan.M.loaded_segments (0x95fd8 : word) = Some W_95f88.
Proof. vm_refl. Qed.
Lemma D_95f88 : decode_any W_95f88 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f8c : bv 32 := 0x00090513.
Lemma F_95f8c : fetch_word Asan.M.loaded_segments (0x95fdc : word) = Some W_95f8c.
Proof. vm_refl. Qed.
Lemma D_95f8c : decode_any W_95f8c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f90 : bv 32 := 0x00040593.
Lemma F_95f90 : fetch_word Asan.M.loaded_segments (0x95fe0 : word) = Some W_95f90.
Proof. vm_refl. Qed.
Lemma D_95f90 : decode_any W_95f90 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f94 : bv 32 := 0x00000793.
Lemma F_95f94 : fetch_word Asan.M.loaded_segments (0x95fe4 : word) = Some W_95f94.
Proof. vm_refl. Qed.
Lemma D_95f94 : decode_any W_95f94 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f98 : bv 32 := 0xa40fe0ef.
Lemma F_95f98 : fetch_word Asan.M.loaded_segments (0x95fe8 : word) = Some W_95f98.
Proof. vm_refl. Qed.
Lemma D_95f98 : decode_any W_95f98 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f9c : bv 32 := 0x00050993.
Lemma F_95f9c : fetch_word Asan.M.loaded_segments (0x95fec : word) = Some W_95f9c.
Proof. vm_refl. Qed.
Lemma D_95f9c : decode_any W_95f9c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa0 : bv 32 := 0x00000593.
Lemma F_95fa0 : fetch_word Asan.M.loaded_segments (0x95ff0 : word) = Some W_95fa0.
Proof. vm_refl. Qed.
Lemma D_95fa0 : decode_any W_95fa0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa4 : bv 32 := 0xa14fe0ef.
Lemma F_95fa4 : fetch_word Asan.M.loaded_segments (0x95ff4 : word) = Some W_95fa4.
Proof. vm_refl. Qed.
Lemma D_95fa4 : decode_any W_95fa4 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fa8 : bv 32 := 0xaaaab537.
Lemma F_95fa8 : fetch_word Asan.M.loaded_segments (0x95ff8 : word) = Some W_95fa8.
Proof. vm_refl. Qed.
Lemma D_95fa8 : decode_any W_95fa8 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fac : bv 32 := 0xaaa50513.
Lemma F_95fac : fetch_word Asan.M.loaded_segments (0x95ffc : word) = Some W_95fac.
Proof. vm_refl. Qed.
Lemma D_95fac : decode_any W_95fac = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb0 : bv 32 := 0x02a12623.
Lemma F_95fb0 : fetch_word Asan.M.loaded_segments (0x96000 : word) = Some W_95fb0.
Proof. vm_refl. Qed.
Lemma D_95fb0 : decode_any W_95fb0 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb4 : bv 32 := 0x02c10593.
Lemma F_95fb4 : fetch_word Asan.M.loaded_segments (0x96004 : word) = Some W_95fb4.
Proof. vm_refl. Qed.
Lemma D_95fb4 : decode_any W_95fb4 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fb8 : bv 32 := 0x00098513.
Lemma F_95fb8 : fetch_word Asan.M.loaded_segments (0x96008 : word) = Some W_95fb8.
Proof. vm_refl. Qed.
Lemma D_95fb8 : decode_any W_95fb8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fbc : bv 32 := 0x9fcfe0ef.
Lemma F_95fbc : fetch_word Asan.M.loaded_segments (0x9600c : word) = Some W_95fbc.
Proof. vm_refl. Qed.
Lemma D_95fbc : decode_any W_95fbc = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fc0 : bv 32 := 0x04051063.
Lemma F_95fc0 : fetch_word Asan.M.loaded_segments (0x96010 : word) = Some W_95fc0.
Proof. vm_refl. Qed.
Lemma D_95fc0 : decode_any W_95fc0 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fc4 : bv 32 := 0x00040513.
Lemma F_95fc4 : fetch_word Asan.M.loaded_segments (0x96014 : word) = Some W_95fc4.
Proof. vm_refl. Qed.
Lemma D_95fc4 : decode_any W_95fc4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fc8 : bv 32 := 0x8d8fa0ef.
Lemma F_95fc8 : fetch_word Asan.M.loaded_segments (0x96018 : word) = Some W_95fc8.
Proof. vm_refl. Qed.
Lemma D_95fc8 : decode_any W_95fc8 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fcc : bv 32 := 0x00098513.
Lemma F_95fcc : fetch_word Asan.M.loaded_segments (0x9601c : word) = Some W_95fcc.
Proof. vm_refl. Qed.
Lemma D_95fcc : decode_any W_95fcc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd0 : bv 32 := 0x05813083.
Lemma F_95fd0 : fetch_word Asan.M.loaded_segments (0x96020 : word) = Some W_95fd0.
Proof. vm_refl. Qed.
Lemma D_95fd0 : decode_any W_95fd0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd4 : bv 32 := 0x05013403.
Lemma F_95fd4 : fetch_word Asan.M.loaded_segments (0x96024 : word) = Some W_95fd4.
Proof. vm_refl. Qed.
Lemma D_95fd4 : decode_any W_95fd4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fd8 : bv 32 := 0x04813483.
Lemma F_95fd8 : fetch_word Asan.M.loaded_segments (0x96028 : word) = Some W_95fd8.
Proof. vm_refl. Qed.
Lemma D_95fd8 : decode_any W_95fd8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fdc : bv 32 := 0x04013903.
Lemma F_95fdc : fetch_word Asan.M.loaded_segments (0x9602c : word) = Some W_95fdc.
Proof. vm_refl. Qed.
Lemma D_95fdc : decode_any W_95fdc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe0 : bv 32 := 0x03813983.
Lemma F_95fe0 : fetch_word Asan.M.loaded_segments (0x96030 : word) = Some W_95fe0.
Proof. vm_refl. Qed.
Lemma D_95fe0 : decode_any W_95fe0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe4 : bv 32 := 0x03013a03.
Lemma F_95fe4 : fetch_word Asan.M.loaded_segments (0x96034 : word) = Some W_95fe4.
Proof. vm_refl. Qed.
Lemma D_95fe4 : decode_any W_95fe4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fe8 : bv 32 := 0x06010113.
Lemma F_95fe8 : fetch_word Asan.M.loaded_segments (0x96038 : word) = Some W_95fe8.
Proof. vm_refl. Qed.
Lemma D_95fe8 : decode_any W_95fe8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95fec : bv 32 := 0x00008067.
Lemma F_95fec : fetch_word Asan.M.loaded_segments (0x9603c : word) = Some W_95fec.
Proof. vm_refl. Qed.
Lemma D_95fec : decode_any W_95fec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

