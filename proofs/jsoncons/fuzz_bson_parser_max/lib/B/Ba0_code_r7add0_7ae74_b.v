(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_94c64 : bv 32 := 0xfe010113.
Lemma F_94c64 : fetch_word AsanUbsan.M.loaded_segments (0x9507c : word) = Some W_94c64.
Proof. vm_refl. Qed.
Lemma D_94c64 : decode_any W_94c64 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c68 : bv 32 := 0x00113c23.
Lemma F_94c68 : fetch_word AsanUbsan.M.loaded_segments (0x95080 : word) = Some W_94c68.
Proof. vm_refl. Qed.
Lemma D_94c68 : decode_any W_94c68 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c6c : bv 32 := 0x00813823.
Lemma F_94c6c : fetch_word AsanUbsan.M.loaded_segments (0x95084 : word) = Some W_94c6c.
Proof. vm_refl. Qed.
Lemma D_94c6c : decode_any W_94c6c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c70 : bv 32 := 0x00913423.
Lemma F_94c70 : fetch_word AsanUbsan.M.loaded_segments (0x95088 : word) = Some W_94c70.
Proof. vm_refl. Qed.
Lemma D_94c70 : decode_any W_94c70 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c74 : bv 32 := 0x01213023.
Lemma F_94c74 : fetch_word AsanUbsan.M.loaded_segments (0x9508c : word) = Some W_94c74.
Proof. vm_refl. Qed.
Lemma D_94c74 : decode_any W_94c74 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c78 : bv 32 := 0x00058413.
Lemma F_94c78 : fetch_word AsanUbsan.M.loaded_segments (0x95090 : word) = Some W_94c78.
Proof. vm_refl. Qed.
Lemma D_94c78 : decode_any W_94c78 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c7c : bv 32 := 0x000a2597.
Lemma F_94c7c : fetch_word AsanUbsan.M.loaded_segments (0x95094 : word) = Some W_94c7c.
Proof. vm_refl. Qed.
Lemma D_94c7c : decode_any W_94c7c = Some (Auipc 11 162, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c80 : bv 32 := 0x40c5b903.
Lemma F_94c80 : fetch_word AsanUbsan.M.loaded_segments (0x95098 : word) = Some W_94c80.
Proof. vm_refl. Qed.
Lemma D_94c80 : decode_any W_94c80 = Some (Load SZ8 true 18 11 1036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c84 : bv 32 := 0x00093583.
Lemma F_94c84 : fetch_word AsanUbsan.M.loaded_segments (0x9509c : word) = Some W_94c84.
Proof. vm_refl. Qed.
Lemma D_94c84 : decode_any W_94c84 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c88 : bv 32 := 0x00050493.
Lemma F_94c88 : fetch_word AsanUbsan.M.loaded_segments (0x950a0 : word) = Some W_94c88.
Proof. vm_refl. Qed.
Lemma D_94c88 : decode_any W_94c88 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c8c : bv 32 := 0x00059863.
Lemma F_94c8c : fetch_word AsanUbsan.M.loaded_segments (0x950a4 : word) = Some W_94c8c.
Proof. vm_refl. Qed.
Lemma D_94c8c : decode_any W_94c8c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c9c : bv 32 := 0xfff58513.
Lemma F_94c9c : fetch_word AsanUbsan.M.loaded_segments (0x950b4 : word) = Some W_94c9c.
Proof. vm_refl. Qed.
Lemma D_94c9c : decode_any W_94c9c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ca0 : bv 32 := 0x00a5f533.
Lemma F_94ca0 : fetch_word AsanUbsan.M.loaded_segments (0x950b8 : word) = Some W_94ca0.
Proof. vm_refl. Qed.
Lemma D_94ca0 : decode_any W_94ca0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ca4 : bv 32 := 0x04051a63.
Lemma F_94ca4 : fetch_word AsanUbsan.M.loaded_segments (0x950bc : word) = Some W_94ca4.
Proof. vm_refl. Qed.
Lemma D_94ca4 : decode_any W_94ca4 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ca8 : bv 32 := 0x00b484b3.
Lemma F_94ca8 : fetch_word AsanUbsan.M.loaded_segments (0x950c0 : word) = Some W_94ca8.
Proof. vm_refl. Qed.
Lemma D_94ca8 : decode_any W_94ca8 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cac : bv 32 := 0x40b005b3.
Lemma F_94cac : fetch_word AsanUbsan.M.loaded_segments (0x950c4 : word) = Some W_94cac.
Proof. vm_refl. Qed.
Lemma D_94cac : decode_any W_94cac = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cb0 : bv 32 := 0xfff48513.
Lemma F_94cb0 : fetch_word AsanUbsan.M.loaded_segments (0x950c8 : word) = Some W_94cb0.
Proof. vm_refl. Qed.
Lemma D_94cb0 : decode_any W_94cb0 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cb4 : bv 32 := 0x00b57533.
Lemma F_94cb4 : fetch_word AsanUbsan.M.loaded_segments (0x950cc : word) = Some W_94cb4.
Proof. vm_refl. Qed.
Lemma D_94cb4 : decode_any W_94cb4 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cb8 : bv 32 := 0x00b475b3.
Lemma F_94cb8 : fetch_word AsanUbsan.M.loaded_segments (0x950d0 : word) = Some W_94cb8.
Proof. vm_refl. Qed.
Lemma D_94cb8 : decode_any W_94cb8 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cbc : bv 32 := 0x02b57263.
Lemma F_94cbc : fetch_word AsanUbsan.M.loaded_segments (0x950d4 : word) = Some W_94cbc.
Proof. vm_refl. Qed.
Lemma D_94cbc : decode_any W_94cbc = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cc0 : bv 32 := 0x40a585b3.
Lemma F_94cc0 : fetch_word AsanUbsan.M.loaded_segments (0x950d8 : word) = Some W_94cc0.
Proof. vm_refl. Qed.
Lemma D_94cc0 : decode_any W_94cc0 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cc4 : bv 32 := 0x00400613.
Lemma F_94cc4 : fetch_word AsanUbsan.M.loaded_segments (0x950dc : word) = Some W_94cc4.
Proof. vm_refl. Qed.
Lemma D_94cc4 : decode_any W_94cc4 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cc8 : bv 32 := 0x01813083.
Lemma F_94cc8 : fetch_word AsanUbsan.M.loaded_segments (0x950e0 : word) = Some W_94cc8.
Proof. vm_refl. Qed.
Lemma D_94cc8 : decode_any W_94cc8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ccc : bv 32 := 0x01013403.
Lemma F_94ccc : fetch_word AsanUbsan.M.loaded_segments (0x950e4 : word) = Some W_94ccc.
Proof. vm_refl. Qed.
Lemma D_94ccc : decode_any W_94ccc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cd0 : bv 32 := 0x00813483.
Lemma F_94cd0 : fetch_word AsanUbsan.M.loaded_segments (0x950e8 : word) = Some W_94cd0.
Proof. vm_refl. Qed.
Lemma D_94cd0 : decode_any W_94cd0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cd4 : bv 32 := 0x00013903.
Lemma F_94cd4 : fetch_word AsanUbsan.M.loaded_segments (0x950ec : word) = Some W_94cd4.
Proof. vm_refl. Qed.
Lemma D_94cd4 : decode_any W_94cd4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cd8 : bv 32 := 0x02010113.
Lemma F_94cd8 : fetch_word AsanUbsan.M.loaded_segments (0x950f0 : word) = Some W_94cd8.
Proof. vm_refl. Qed.
Lemma D_94cd8 : decode_any W_94cd8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cdc : bv 32 := 0xbb1f606f.
Lemma F_94cdc : fetch_word AsanUbsan.M.loaded_segments (0x950f4 : word) = Some W_94cdc.
Proof. vm_refl. Qed.
Lemma D_94cdc : decode_any W_94cdc = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ce0 : bv 32 := 0x01813083.
Lemma F_94ce0 : fetch_word AsanUbsan.M.loaded_segments (0x950f8 : word) = Some W_94ce0.
Proof. vm_refl. Qed.
Lemma D_94ce0 : decode_any W_94ce0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ce4 : bv 32 := 0x01013403.
Lemma F_94ce4 : fetch_word AsanUbsan.M.loaded_segments (0x950fc : word) = Some W_94ce4.
Proof. vm_refl. Qed.
Lemma D_94ce4 : decode_any W_94ce4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ce8 : bv 32 := 0x00813483.
Lemma F_94ce8 : fetch_word AsanUbsan.M.loaded_segments (0x95100 : word) = Some W_94ce8.
Proof. vm_refl. Qed.
Lemma D_94ce8 : decode_any W_94ce8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cec : bv 32 := 0x00013903.
Lemma F_94cec : fetch_word AsanUbsan.M.loaded_segments (0x95104 : word) = Some W_94cec.
Proof. vm_refl. Qed.
Lemma D_94cec : decode_any W_94cec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cf0 : bv 32 := 0x02010113.
Lemma F_94cf0 : fetch_word AsanUbsan.M.loaded_segments (0x95108 : word) = Some W_94cf0.
Proof. vm_refl. Qed.
Lemma D_94cf0 : decode_any W_94cf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94cf4 : bv 32 := 0x00008067.
Lemma F_94cf4 : fetch_word AsanUbsan.M.loaded_segments (0x9510c : word) = Some W_94cf4.
Proof. vm_refl. Qed.
Lemma D_94cf4 : decode_any W_94cf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
