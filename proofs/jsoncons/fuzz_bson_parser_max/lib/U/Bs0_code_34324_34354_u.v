(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_34324 : bv 32 := 0x00094517.
Lemma F_34324 : fetch_word Ubsan.M.loaded_segments (0x346a4 : word) = Some W_34324.
Proof. vm_refl. Qed.
Lemma D_34324 : decode_any W_34324 = Some (Auipc 10 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34328 : bv 32 := 0xeb054503.
Lemma F_34328 : fetch_word Ubsan.M.loaded_segments (0x346a8 : word) = Some W_34328.
Proof. vm_refl. Qed.
Lemma D_34328 : decode_any W_34328 = Some (Load SZ1 false 10 10 3760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3432c : bv 32 := 0x00051463.
Lemma F_3432c : fetch_word Ubsan.M.loaded_segments (0x346ac : word) = Some W_3432c.
Proof. vm_refl. Qed.
Lemma D_3432c : decode_any W_3432c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34330 : bv 32 := 0x00008067.
Lemma F_34330 : fetch_word Ubsan.M.loaded_segments (0x346b0 : word) = Some W_34330.
Proof. vm_refl. Qed.
Lemma D_34330 : decode_any W_34330 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34334 : bv 32 := 0xff010113.
Lemma F_34334 : fetch_word Ubsan.M.loaded_segments (0x346b4 : word) = Some W_34334.
Proof. vm_refl. Qed.
Lemma D_34334 : decode_any W_34334 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34338 : bv 32 := 0x00113423.
Lemma F_34338 : fetch_word Ubsan.M.loaded_segments (0x346b8 : word) = Some W_34338.
Proof. vm_refl. Qed.
Lemma D_34338 : decode_any W_34338 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3433c : bv 32 := 0x00083517.
Lemma F_3433c : fetch_word Ubsan.M.loaded_segments (0x346bc : word) = Some W_3433c.
Proof. vm_refl. Qed.
Lemma D_3433c : decode_any W_3433c = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34340 : bv 32 := 0x9ec53503.
Lemma F_34340 : fetch_word Ubsan.M.loaded_segments (0x346c0 : word) = Some W_34340.
Proof. vm_refl. Qed.
Lemma D_34340 : decode_any W_34340 = Some (Load SZ8 true 10 10 2540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34344 : bv 32 := 0x00053503.
Lemma F_34344 : fetch_word Ubsan.M.loaded_segments (0x346c4 : word) = Some W_34344.
Proof. vm_refl. Qed.
Lemma D_34344 : decode_any W_34344 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34348 : bv 32 := 0x5c46b0ef.
Lemma F_34348 : fetch_word Ubsan.M.loaded_segments (0x346c8 : word) = Some W_34348.
Proof. vm_refl. Qed.
Lemma D_34348 : decode_any W_34348 = Some (Jal 1 439748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3434c : bv 32 := 0x04d00513.
Lemma F_3434c : fetch_word Ubsan.M.loaded_segments (0x346cc : word) = Some W_3434c.
Proof. vm_refl. Qed.
Lemma D_3434c : decode_any W_3434c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34350 : bv 32 := 0x4497b0ef.
Lemma F_34350 : fetch_word Ubsan.M.loaded_segments (0x346d0 : word) = Some W_34350.
Proof. vm_refl. Qed.
Lemma D_34350 : decode_any W_34350 = Some (Jal 1 506952, 4%Z).
Proof. vm_refl. Qed.
