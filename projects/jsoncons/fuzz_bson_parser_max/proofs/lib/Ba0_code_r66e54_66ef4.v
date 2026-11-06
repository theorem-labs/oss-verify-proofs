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
Definition W_80ccc : bv 32 := 0xff010113.
Lemma F_80ccc : fetch_word Asan.M.loaded_segments (0x80d1c : word) = Some W_80ccc.
Proof. vm_refl. Qed.
Lemma D_80ccc : decode_any W_80ccc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd0 : bv 32 := 0x00113423.
Lemma F_80cd0 : fetch_word Asan.M.loaded_segments (0x80d20 : word) = Some W_80cd0.
Proof. vm_refl. Qed.
Lemma D_80cd0 : decode_any W_80cd0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd4 : bv 32 := 0x00813023.
Lemma F_80cd4 : fetch_word Asan.M.loaded_segments (0x80d24 : word) = Some W_80cd4.
Proof. vm_refl. Qed.
Lemma D_80cd4 : decode_any W_80cd4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd8 : bv 32 := 0x000bd517.
Lemma F_80cd8 : fetch_word Asan.M.loaded_segments (0x80d28 : word) = Some W_80cd8.
Proof. vm_refl. Qed.
Lemma D_80cd8 : decode_any W_80cd8 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cdc : bv 32 := 0x77050413.
Lemma F_80cdc : fetch_word Asan.M.loaded_segments (0x80d2c : word) = Some W_80cdc.
Proof. vm_refl. Qed.
Lemma D_80cdc : decode_any W_80cdc = Some (OpImm ALU_ADD 8 10 1904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce0 : bv 32 := 0x00040583.
Lemma F_80ce0 : fetch_word Asan.M.loaded_segments (0x80d30 : word) = Some W_80ce0.
Proof. vm_refl. Qed.
Lemma D_80ce0 : decode_any W_80ce0 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce4 : bv 32 := 0x00100513.
Lemma F_80ce4 : fetch_word Asan.M.loaded_segments (0x80d34 : word) = Some W_80ce4.
Proof. vm_refl. Qed.
Lemma D_80ce4 : decode_any W_80ce4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce8 : bv 32 := 0x0230000f.
Lemma F_80ce8 : fetch_word Asan.M.loaded_segments (0x80d38 : word) = Some W_80ce8.
Proof. vm_refl. Qed.
Lemma D_80ce8 : decode_any W_80ce8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cec : bv 32 := 0x00a59a63.
Lemma F_80cec : fetch_word Asan.M.loaded_segments (0x80d3c : word) = Some W_80cec.
Proof. vm_refl. Qed.
Lemma D_80cec : decode_any W_80cec = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf0 : bv 32 := 0x00813083.
Lemma F_80cf0 : fetch_word Asan.M.loaded_segments (0x80d40 : word) = Some W_80cf0.
Proof. vm_refl. Qed.
Lemma D_80cf0 : decode_any W_80cf0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf4 : bv 32 := 0x00013403.
Lemma F_80cf4 : fetch_word Asan.M.loaded_segments (0x80d44 : word) = Some W_80cf4.
Proof. vm_refl. Qed.
Lemma D_80cf4 : decode_any W_80cf4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf8 : bv 32 := 0x01010113.
Lemma F_80cf8 : fetch_word Asan.M.loaded_segments (0x80d48 : word) = Some W_80cf8.
Proof. vm_refl. Qed.
Lemma D_80cf8 : decode_any W_80cf8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cfc : bv 32 := 0x00008067.
Lemma F_80cfc : fetch_word Asan.M.loaded_segments (0x80d4c : word) = Some W_80cfc.
Proof. vm_refl. Qed.
Lemma D_80cfc : decode_any W_80cfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
