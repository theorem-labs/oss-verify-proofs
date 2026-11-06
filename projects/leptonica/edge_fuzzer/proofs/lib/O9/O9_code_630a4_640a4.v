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
Definition W_63e30 : bv 32 := 0xfd010113.
Lemma F_63e30 : fetch_word Plain.M.loaded_segments (0x63e88 : word) = Some W_63e30.
Proof. vm_refl. Qed.
Lemma D_63e30 : decode_any W_63e30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e34 : bv 32 := 0x02113423.
Lemma F_63e34 : fetch_word Plain.M.loaded_segments (0x63e8c : word) = Some W_63e34.
Proof. vm_refl. Qed.
Lemma D_63e34 : decode_any W_63e34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e38 : bv 32 := 0x02813023.
Lemma F_63e38 : fetch_word Plain.M.loaded_segments (0x63e90 : word) = Some W_63e38.
Proof. vm_refl. Qed.
Lemma D_63e38 : decode_any W_63e38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e3c : bv 32 := 0x00913c23.
Lemma F_63e3c : fetch_word Plain.M.loaded_segments (0x63e94 : word) = Some W_63e3c.
Proof. vm_refl. Qed.
Lemma D_63e3c : decode_any W_63e3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e40 : bv 32 := 0x01213823.
Lemma F_63e40 : fetch_word Plain.M.loaded_segments (0x63e98 : word) = Some W_63e40.
Proof. vm_refl. Qed.
Lemma D_63e40 : decode_any W_63e40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e44 : bv 32 := 0x06050063.
Lemma F_63e44 : fetch_word Plain.M.loaded_segments (0x63e9c : word) = Some W_63e44.
Proof. vm_refl. Qed.
Lemma D_63e44 : decode_any W_63e44 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e48 : bv 32 := 0x00050493.
Lemma F_63e48 : fetch_word Plain.M.loaded_segments (0x63ea0 : word) = Some W_63e48.
Proof. vm_refl. Qed.
Lemma D_63e48 : decode_any W_63e48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e4c : bv 32 := 0x00058913.
Lemma F_63e4c : fetch_word Plain.M.loaded_segments (0x63ea4 : word) = Some W_63e4c.
Proof. vm_refl. Qed.
Lemma D_63e4c : decode_any W_63e4c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e50 : bv 32 := 0x00c10593.
Lemma F_63e50 : fetch_word Plain.M.loaded_segments (0x63ea8 : word) = Some W_63e50.
Proof. vm_refl. Qed.
Lemma D_63e50 : decode_any W_63e50 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e54 : bv 32 := 0x00810613.
Lemma F_63e54 : fetch_word Plain.M.loaded_segments (0x63eac : word) = Some W_63e54.
Proof. vm_refl. Qed.
Lemma D_63e54 : decode_any W_63e54 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e58 : bv 32 := 0x00410693.
Lemma F_63e58 : fetch_word Plain.M.loaded_segments (0x63eb0 : word) = Some W_63e58.
Proof. vm_refl. Qed.
Lemma D_63e58 : decode_any W_63e58 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e5c : bv 32 := 0xa5dfe0ef.
Lemma F_63e5c : fetch_word Plain.M.loaded_segments (0x63eb4 : word) = Some W_63e5c.
Proof. vm_refl. Qed.
Lemma D_63e5c : decode_any W_63e5c = Some (Jal 1 2091612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e60 : bv 32 := 0x00412503.
Lemma F_63e60 : fetch_word Plain.M.loaded_segments (0x63eb8 : word) = Some W_63e60.
Proof. vm_refl. Qed.
Lemma D_63e60 : decode_any W_63e60 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e64 : bv 32 := 0x02000593.
Lemma F_63e64 : fetch_word Plain.M.loaded_segments (0x63ebc : word) = Some W_63e64.
Proof. vm_refl. Qed.
Lemma D_63e64 : decode_any W_63e64 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63e68 : bv 32 := 0x12b50463.
Lemma F_63e68 : fetch_word Plain.M.loaded_segments (0x63ec0 : word) = Some W_63e68.
Proof. vm_refl. Qed.
Lemma D_63e68 : decode_any W_63e68 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63f90 : bv 32 := 0x00000513.
Lemma F_63f90 : fetch_word Plain.M.loaded_segments (0x63fe8 : word) = Some W_63f90.
Proof. vm_refl. Qed.
Lemma D_63f90 : decode_any W_63f90 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63f94 : bv 32 := 0x02813083.
Lemma F_63f94 : fetch_word Plain.M.loaded_segments (0x63fec : word) = Some W_63f94.
Proof. vm_refl. Qed.
Lemma D_63f94 : decode_any W_63f94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63f98 : bv 32 := 0x02013403.
Lemma F_63f98 : fetch_word Plain.M.loaded_segments (0x63ff0 : word) = Some W_63f98.
Proof. vm_refl. Qed.
Lemma D_63f98 : decode_any W_63f98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63f9c : bv 32 := 0x01813483.
Lemma F_63f9c : fetch_word Plain.M.loaded_segments (0x63ff4 : word) = Some W_63f9c.
Proof. vm_refl. Qed.
Lemma D_63f9c : decode_any W_63f9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63fa0 : bv 32 := 0x01013903.
Lemma F_63fa0 : fetch_word Plain.M.loaded_segments (0x63ff8 : word) = Some W_63fa0.
Proof. vm_refl. Qed.
Lemma D_63fa0 : decode_any W_63fa0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63fa4 : bv 32 := 0x03010113.
Lemma F_63fa4 : fetch_word Plain.M.loaded_segments (0x63ffc : word) = Some W_63fa4.
Proof. vm_refl. Qed.
Lemma D_63fa4 : decode_any W_63fa4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63fa8 : bv 32 := 0x00008067.
Lemma F_63fa8 : fetch_word Plain.M.loaded_segments (0x64000 : word) = Some W_63fa8.
Proof. vm_refl. Qed.
Lemma D_63fa8 : decode_any W_63fa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

