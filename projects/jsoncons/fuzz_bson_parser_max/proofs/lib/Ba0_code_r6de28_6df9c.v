(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_87ca0 : bv 32 := 0xfe010113.
Lemma F_87ca0 : fetch_word Asan.M.loaded_segments (0x87cf0 : word) = Some W_87ca0.
Proof. vm_refl. Qed.
Lemma D_87ca0 : decode_any W_87ca0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ca4 : bv 32 := 0x00113c23.
Lemma F_87ca4 : fetch_word Asan.M.loaded_segments (0x87cf4 : word) = Some W_87ca4.
Proof. vm_refl. Qed.
Lemma D_87ca4 : decode_any W_87ca4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ca8 : bv 32 := 0x00813823.
Lemma F_87ca8 : fetch_word Asan.M.loaded_segments (0x87cf8 : word) = Some W_87ca8.
Proof. vm_refl. Qed.
Lemma D_87ca8 : decode_any W_87ca8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cac : bv 32 := 0x00913423.
Lemma F_87cac : fetch_word Asan.M.loaded_segments (0x87cfc : word) = Some W_87cac.
Proof. vm_refl. Qed.
Lemma D_87cac : decode_any W_87cac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cb0 : bv 32 := 0x01213023.
Lemma F_87cb0 : fetch_word Asan.M.loaded_segments (0x87d00 : word) = Some W_87cb0.
Proof. vm_refl. Qed.
Lemma D_87cb0 : decode_any W_87cb0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cb4 : bv 32 := 0x00058413.
Lemma F_87cb4 : fetch_word Asan.M.loaded_segments (0x87d04 : word) = Some W_87cb4.
Proof. vm_refl. Qed.
Lemma D_87cb4 : decode_any W_87cb4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cb8 : bv 32 := 0x00050493.
Lemma F_87cb8 : fetch_word Asan.M.loaded_segments (0x87d08 : word) = Some W_87cb8.
Proof. vm_refl. Qed.
Lemma D_87cb8 : decode_any W_87cb8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cbc : bv 32 := 0x09c000ef.
Lemma F_87cbc : fetch_word Asan.M.loaded_segments (0x87d0c : word) = Some W_87cbc.
Proof. vm_refl. Qed.
Lemma D_87cbc : decode_any W_87cbc = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cc0 : bv 32 := 0x00147517.
Lemma F_87cc0 : fetch_word Asan.M.loaded_segments (0x87d10 : word) = Some W_87cc0.
Proof. vm_refl. Qed.
Lemma D_87cc0 : decode_any W_87cc0 = Some (Auipc 10 327, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cc4 : bv 32 := 0x57050913.
Lemma F_87cc4 : fetch_word Asan.M.loaded_segments (0x87d14 : word) = Some W_87cc4.
Proof. vm_refl. Qed.
Lemma D_87cc4 : decode_any W_87cc4 = Some (OpImm ALU_ADD 18 10 1392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cc8 : bv 32 := 0x00093603.
Lemma F_87cc8 : fetch_word Asan.M.loaded_segments (0x87d18 : word) = Some W_87cc8.
Proof. vm_refl. Qed.
Lemma D_87cc8 : decode_any W_87cc8 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ccc : bv 32 := 0x06060a63.
Lemma F_87ccc : fetch_word Asan.M.loaded_segments (0x87d1c : word) = Some W_87ccc.
Proof. vm_refl. Qed.
Lemma D_87ccc : decode_any W_87ccc = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d40 : bv 32 := 0x01813083.
Lemma F_87d40 : fetch_word Asan.M.loaded_segments (0x87d90 : word) = Some W_87d40.
Proof. vm_refl. Qed.
Lemma D_87d40 : decode_any W_87d40 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d44 : bv 32 := 0x01013403.
Lemma F_87d44 : fetch_word Asan.M.loaded_segments (0x87d94 : word) = Some W_87d44.
Proof. vm_refl. Qed.
Lemma D_87d44 : decode_any W_87d44 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d48 : bv 32 := 0x00813483.
Lemma F_87d48 : fetch_word Asan.M.loaded_segments (0x87d98 : word) = Some W_87d48.
Proof. vm_refl. Qed.
Lemma D_87d48 : decode_any W_87d48 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d4c : bv 32 := 0x00013903.
Lemma F_87d4c : fetch_word Asan.M.loaded_segments (0x87d9c : word) = Some W_87d4c.
Proof. vm_refl. Qed.
Lemma D_87d4c : decode_any W_87d4c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d50 : bv 32 := 0x02010113.
Lemma F_87d50 : fetch_word Asan.M.loaded_segments (0x87da0 : word) = Some W_87d50.
Proof. vm_refl. Qed.
Lemma D_87d50 : decode_any W_87d50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d54 : bv 32 := 0x00008067.
Lemma F_87d54 : fetch_word Asan.M.loaded_segments (0x87da4 : word) = Some W_87d54.
Proof. vm_refl. Qed.
Lemma D_87d54 : decode_any W_87d54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d58 : bv 32 := 0x00008067.
Lemma F_87d58 : fetch_word Asan.M.loaded_segments (0x87da8 : word) = Some W_87d58.
Proof. vm_refl. Qed.
Lemma D_87d58 : decode_any W_87d58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d5c : bv 32 := 0xfe010113.
Lemma F_87d5c : fetch_word Asan.M.loaded_segments (0x87dac : word) = Some W_87d5c.
Proof. vm_refl. Qed.
Lemma D_87d5c : decode_any W_87d5c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d60 : bv 32 := 0x00113c23.
Lemma F_87d60 : fetch_word Asan.M.loaded_segments (0x87db0 : word) = Some W_87d60.
Proof. vm_refl. Qed.
Lemma D_87d60 : decode_any W_87d60 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d64 : bv 32 := 0x00813823.
Lemma F_87d64 : fetch_word Asan.M.loaded_segments (0x87db4 : word) = Some W_87d64.
Proof. vm_refl. Qed.
Lemma D_87d64 : decode_any W_87d64 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d68 : bv 32 := 0x00913423.
Lemma F_87d68 : fetch_word Asan.M.loaded_segments (0x87db8 : word) = Some W_87d68.
Proof. vm_refl. Qed.
Lemma D_87d68 : decode_any W_87d68 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d6c : bv 32 := 0x00050413.
Lemma F_87d6c : fetch_word Asan.M.loaded_segments (0x87dbc : word) = Some W_87d6c.
Proof. vm_refl. Qed.
Lemma D_87d6c : decode_any W_87d6c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d70 : bv 32 := 0x098000ef.
Lemma F_87d70 : fetch_word Asan.M.loaded_segments (0x87dc0 : word) = Some W_87d70.
Proof. vm_refl. Qed.
Lemma D_87d70 : decode_any W_87d70 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d74 : bv 32 := 0x00050e63.
Lemma F_87d74 : fetch_word Asan.M.loaded_segments (0x87dc4 : word) = Some W_87d74.
Proof. vm_refl. Qed.
Lemma D_87d74 : decode_any W_87d74 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d90 : bv 32 := 0x00040513.
Lemma F_87d90 : fetch_word Asan.M.loaded_segments (0x87de0 : word) = Some W_87d90.
Proof. vm_refl. Qed.
Lemma D_87d90 : decode_any W_87d90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d94 : bv 32 := 0x07c000ef.
Lemma F_87d94 : fetch_word Asan.M.loaded_segments (0x87de4 : word) = Some W_87d94.
Proof. vm_refl. Qed.
Lemma D_87d94 : decode_any W_87d94 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d98 : bv 32 := 0x00147517.
Lemma F_87d98 : fetch_word Asan.M.loaded_segments (0x87de8 : word) = Some W_87d98.
Proof. vm_refl. Qed.
Lemma D_87d98 : decode_any W_87d98 = Some (Auipc 10 327, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87d9c : bv 32 := 0x49850493.
Lemma F_87d9c : fetch_word Asan.M.loaded_segments (0x87dec : word) = Some W_87d9c.
Proof. vm_refl. Qed.
Lemma D_87d9c : decode_any W_87d9c = Some (OpImm ALU_ADD 9 10 1176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87da0 : bv 32 := 0x0084b583.
Lemma F_87da0 : fetch_word Asan.M.loaded_segments (0x87df0 : word) = Some W_87da0.
Proof. vm_refl. Qed.
Lemma D_87da0 : decode_any W_87da0 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87da4 : bv 32 := 0x04058663.
Lemma F_87da4 : fetch_word Asan.M.loaded_segments (0x87df4 : word) = Some W_87da4.
Proof. vm_refl. Qed.
Lemma D_87da4 : decode_any W_87da4 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87df0 : bv 32 := 0x00000513.
Lemma F_87df0 : fetch_word Asan.M.loaded_segments (0x87e40 : word) = Some W_87df0.
Proof. vm_refl. Qed.
Lemma D_87df0 : decode_any W_87df0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87df4 : bv 32 := 0x01813083.
Lemma F_87df4 : fetch_word Asan.M.loaded_segments (0x87e44 : word) = Some W_87df4.
Proof. vm_refl. Qed.
Lemma D_87df4 : decode_any W_87df4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87df8 : bv 32 := 0x01013403.
Lemma F_87df8 : fetch_word Asan.M.loaded_segments (0x87e48 : word) = Some W_87df8.
Proof. vm_refl. Qed.
Lemma D_87df8 : decode_any W_87df8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87dfc : bv 32 := 0x00813483.
Lemma F_87dfc : fetch_word Asan.M.loaded_segments (0x87e4c : word) = Some W_87dfc.
Proof. vm_refl. Qed.
Lemma D_87dfc : decode_any W_87dfc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e00 : bv 32 := 0x02010113.
Lemma F_87e00 : fetch_word Asan.M.loaded_segments (0x87e50 : word) = Some W_87e00.
Proof. vm_refl. Qed.
Lemma D_87e00 : decode_any W_87e00 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e04 : bv 32 := 0x00008067.
Lemma F_87e04 : fetch_word Asan.M.loaded_segments (0x87e54 : word) = Some W_87e04.
Proof. vm_refl. Qed.
Lemma D_87e04 : decode_any W_87e04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e08 : bv 32 := 0x00000513.
Lemma F_87e08 : fetch_word Asan.M.loaded_segments (0x87e58 : word) = Some W_87e08.
Proof. vm_refl. Qed.
Lemma D_87e08 : decode_any W_87e08 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e0c : bv 32 := 0x00008067.
Lemma F_87e0c : fetch_word Asan.M.loaded_segments (0x87e5c : word) = Some W_87e0c.
Proof. vm_refl. Qed.
Lemma D_87e0c : decode_any W_87e0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e10 : bv 32 := 0x00008067.
Lemma F_87e10 : fetch_word Asan.M.loaded_segments (0x87e60 : word) = Some W_87e10.
Proof. vm_refl. Qed.
Lemma D_87e10 : decode_any W_87e10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
