(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_64e1c : bv 32 := 0xfe010113.
Lemma F_64e1c : fetch_word Plain.M.loaded_segments (0x64e74 : word) = Some W_64e1c.
Proof. vm_refl. Qed.
Lemma D_64e1c : decode_any W_64e1c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e20 : bv 32 := 0x00113c23.
Lemma F_64e20 : fetch_word Plain.M.loaded_segments (0x64e78 : word) = Some W_64e20.
Proof. vm_refl. Qed.
Lemma D_64e20 : decode_any W_64e20 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e24 : bv 32 := 0x00813823.
Lemma F_64e24 : fetch_word Plain.M.loaded_segments (0x64e7c : word) = Some W_64e24.
Proof. vm_refl. Qed.
Lemma D_64e24 : decode_any W_64e24 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e28 : bv 32 := 0x00913423.
Lemma F_64e28 : fetch_word Plain.M.loaded_segments (0x64e80 : word) = Some W_64e28.
Proof. vm_refl. Qed.
Lemma D_64e28 : decode_any W_64e28 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e2c : bv 32 := 0x06050463.
Lemma F_64e2c : fetch_word Plain.M.loaded_segments (0x64e84 : word) = Some W_64e2c.
Proof. vm_refl. Qed.
Lemma D_64e2c : decode_any W_64e2c = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e30 : bv 32 := 0x00050413.
Lemma F_64e30 : fetch_word Plain.M.loaded_segments (0x64e88 : word) = Some W_64e30.
Proof. vm_refl. Qed.
Lemma D_64e30 : decode_any W_64e30 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e34 : bv 32 := 0x00410613.
Lemma F_64e34 : fetch_word Plain.M.loaded_segments (0x64e8c : word) = Some W_64e34.
Proof. vm_refl. Qed.
Lemma D_64e34 : decode_any W_64e34 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e38 : bv 32 := 0x00000593.
Lemma F_64e38 : fetch_word Plain.M.loaded_segments (0x64e90 : word) = Some W_64e38.
Proof. vm_refl. Qed.
Lemma D_64e38 : decode_any W_64e38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e3c : bv 32 := 0x0dc000ef.
Lemma F_64e3c : fetch_word Plain.M.loaded_segments (0x64e94 : word) = Some W_64e3c.
Proof. vm_refl. Qed.
Lemma D_64e3c : decode_any W_64e3c = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e40 : bv 32 := 0x00412503.
Lemma F_64e40 : fetch_word Plain.M.loaded_segments (0x64e98 : word) = Some W_64e40.
Proof. vm_refl. Qed.
Lemma D_64e40 : decode_any W_64e40 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e44 : bv 32 := 0x08050663.
Lemma F_64e44 : fetch_word Plain.M.loaded_segments (0x64e9c : word) = Some W_64e44.
Proof. vm_refl. Qed.
Lemma D_64e44 : decode_any W_64e44 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e48 : bv 32 := 0x00100513.
Lemma F_64e48 : fetch_word Plain.M.loaded_segments (0x64ea0 : word) = Some W_64e48.
Proof. vm_refl. Qed.
Lemma D_64e48 : decode_any W_64e48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e4c : bv 32 := 0x01800593.
Lemma F_64e4c : fetch_word Plain.M.loaded_segments (0x64ea4 : word) = Some W_64e4c.
Proof. vm_refl. Qed.
Lemma D_64e4c : decode_any W_64e4c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e50 : bv 32 := 0x225720ef.
Lemma F_64e50 : fetch_word Plain.M.loaded_segments (0x64ea8 : word) = Some W_64e50.
Proof. vm_refl. Qed.
Lemma D_64e50 : decode_any W_64e50 = Some (Jal 1 469540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e54 : bv 32 := 0x00050493.
Lemma F_64e54 : fetch_word Plain.M.loaded_segments (0x64eac : word) = Some W_64e54.
Proof. vm_refl. Qed.
Lemma D_64e54 : decode_any W_64e54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e58 : bv 32 := 0x00c42503.
Lemma F_64e58 : fetch_word Plain.M.loaded_segments (0x64eb0 : word) = Some W_64e58.
Proof. vm_refl. Qed.
Lemma D_64e58 : decode_any W_64e58 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e5c : bv 32 := 0x0025159b.
Lemma F_64e5c : fetch_word Plain.M.loaded_segments (0x64eb4 : word) = Some W_64e5c.
Proof. vm_refl. Qed.
Lemma D_64e5c : decode_any W_64e5c = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e60 : bv 32 := 0x00100513.
Lemma F_64e60 : fetch_word Plain.M.loaded_segments (0x64eb8 : word) = Some W_64e60.
Proof. vm_refl. Qed.
Lemma D_64e60 : decode_any W_64e60 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e64 : bv 32 := 0x211720ef.
Lemma F_64e64 : fetch_word Plain.M.loaded_segments (0x64ebc : word) = Some W_64e64.
Proof. vm_refl. Qed.
Lemma D_64e64 : decode_any W_64e64 = Some (Jal 1 469520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e68 : bv 32 := 0x00a4b023.
Lemma F_64e68 : fetch_word Plain.M.loaded_segments (0x64ec0 : word) = Some W_64e68.
Proof. vm_refl. Qed.
Lemma D_64e68 : decode_any W_64e68 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e6c : bv 32 := 0x01042603.
Lemma F_64e6c : fetch_word Plain.M.loaded_segments (0x64ec4 : word) = Some W_64e6c.
Proof. vm_refl. Qed.
Lemma D_64e6c : decode_any W_64e6c = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e70 : bv 32 := 0x00043583.
Lemma F_64e70 : fetch_word Plain.M.loaded_segments (0x64ec8 : word) = Some W_64e70.
Proof. vm_refl. Qed.
Lemma D_64e70 : decode_any W_64e70 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e74 : bv 32 := 0x00261613.
Lemma F_64e74 : fetch_word Plain.M.loaded_segments (0x64ecc : word) = Some W_64e74.
Proof. vm_refl. Qed.
Lemma D_64e74 : decode_any W_64e74 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e78 : bv 32 := 0x004810ef.
Lemma F_64e78 : fetch_word Plain.M.loaded_segments (0x64ed0 : word) = Some W_64e78.
Proof. vm_refl. Qed.
Lemma D_64e78 : decode_any W_64e78 = Some (Jal 1 528388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e7c : bv 32 := 0x00048513.
Lemma F_64e7c : fetch_word Plain.M.loaded_segments (0x64ed4 : word) = Some W_64e7c.
Proof. vm_refl. Qed.
Lemma D_64e7c : decode_any W_64e7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e80 : bv 32 := 0x01042583.
Lemma F_64e80 : fetch_word Plain.M.loaded_segments (0x64ed8 : word) = Some W_64e80.
Proof. vm_refl. Qed.
Lemma D_64e80 : decode_any W_64e80 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e84 : bv 32 := 0x00b4a823.
Lemma F_64e84 : fetch_word Plain.M.loaded_segments (0x64edc : word) = Some W_64e84.
Proof. vm_refl. Qed.
Lemma D_64e84 : decode_any W_64e84 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e88 : bv 32 := 0x00843583.
Lemma F_64e88 : fetch_word Plain.M.loaded_segments (0x64ee0 : word) = Some W_64e88.
Proof. vm_refl. Qed.
Lemma D_64e88 : decode_any W_64e88 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e8c : bv 32 := 0x00b4b423.
Lemma F_64e8c : fetch_word Plain.M.loaded_segments (0x64ee4 : word) = Some W_64e8c.
Proof. vm_refl. Qed.
Lemma D_64e8c : decode_any W_64e8c = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e90 : bv 32 := 0x0740006f.
Lemma F_64e90 : fetch_word Plain.M.loaded_segments (0x64ee8 : word) = Some W_64e90.
Proof. vm_refl. Qed.
Lemma D_64e90 : decode_any W_64e90 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64f04 : bv 32 := 0x01813083.
Lemma F_64f04 : fetch_word Plain.M.loaded_segments (0x64f5c : word) = Some W_64f04.
Proof. vm_refl. Qed.
Lemma D_64f04 : decode_any W_64f04 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64f08 : bv 32 := 0x01013403.
Lemma F_64f08 : fetch_word Plain.M.loaded_segments (0x64f60 : word) = Some W_64f08.
Proof. vm_refl. Qed.
Lemma D_64f08 : decode_any W_64f08 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64f0c : bv 32 := 0x00813483.
Lemma F_64f0c : fetch_word Plain.M.loaded_segments (0x64f64 : word) = Some W_64f0c.
Proof. vm_refl. Qed.
Lemma D_64f0c : decode_any W_64f0c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64f10 : bv 32 := 0x02010113.
Lemma F_64f10 : fetch_word Plain.M.loaded_segments (0x64f68 : word) = Some W_64f10.
Proof. vm_refl. Qed.
Lemma D_64f10 : decode_any W_64f10 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64f14 : bv 32 := 0x00008067.
Lemma F_64f14 : fetch_word Plain.M.loaded_segments (0x64f6c : word) = Some W_64f14.
Proof. vm_refl. Qed.
Lemma D_64f14 : decode_any W_64f14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

