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
Definition W_5d384 : bv 32 := 0x02050e63.
Lemma F_5d384 : fetch_word Plain.M.loaded_segments (0x5d3dc : word) = Some W_5d384.
Proof. vm_refl. Qed.
Lemma D_5d384 : decode_any W_5d384 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d388 : bv 32 := 0xfe010113.
Lemma F_5d388 : fetch_word Plain.M.loaded_segments (0x5d3e0 : word) = Some W_5d388.
Proof. vm_refl. Qed.
Lemma D_5d388 : decode_any W_5d388 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d38c : bv 32 := 0x00113c23.
Lemma F_5d38c : fetch_word Plain.M.loaded_segments (0x5d3e4 : word) = Some W_5d38c.
Proof. vm_refl. Qed.
Lemma D_5d38c : decode_any W_5d38c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d390 : bv 32 := 0x00813823.
Lemma F_5d390 : fetch_word Plain.M.loaded_segments (0x5d3e8 : word) = Some W_5d390.
Proof. vm_refl. Qed.
Lemma D_5d390 : decode_any W_5d390 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d394 : bv 32 := 0x00913423.
Lemma F_5d394 : fetch_word Plain.M.loaded_segments (0x5d3ec : word) = Some W_5d394.
Proof. vm_refl. Qed.
Lemma D_5d394 : decode_any W_5d394 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d398 : bv 32 := 0x00058493.
Lemma F_5d398 : fetch_word Plain.M.loaded_segments (0x5d3f0 : word) = Some W_5d398.
Proof. vm_refl. Qed.
Lemma D_5d398 : decode_any W_5d398 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d39c : bv 32 := 0x00050413.
Lemma F_5d39c : fetch_word Plain.M.loaded_segments (0x5d3f4 : word) = Some W_5d39c.
Proof. vm_refl. Qed.
Lemma D_5d39c : decode_any W_5d39c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3a0 : bv 32 := 0x00053503.
Lemma F_5d3a0 : fetch_word Plain.M.loaded_segments (0x5d3f8 : word) = Some W_5d3a0.
Proof. vm_refl. Qed.
Lemma D_5d3a0 : decode_any W_5d3a0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3a4 : bv 32 := 0x00050463.
Lemma F_5d3a4 : fetch_word Plain.M.loaded_segments (0x5d3fc : word) = Some W_5d3a4.
Proof. vm_refl. Qed.
Lemma D_5d3a4 : decode_any W_5d3a4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3ac : bv 32 := 0x04048063.
Lemma F_5d3ac : fetch_word Plain.M.loaded_segments (0x5d404 : word) = Some W_5d3ac.
Proof. vm_refl. Qed.
Lemma D_5d3ac : decode_any W_5d3ac = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3ec : bv 32 := 0x00000593.
Lemma F_5d3ec : fetch_word Plain.M.loaded_segments (0x5d444 : word) = Some W_5d3ec.
Proof. vm_refl. Qed.
Lemma D_5d3ec : decode_any W_5d3ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f0 : bv 32 := 0x00000513.
Lemma F_5d3f0 : fetch_word Plain.M.loaded_segments (0x5d448 : word) = Some W_5d3f0.
Proof. vm_refl. Qed.
Lemma D_5d3f0 : decode_any W_5d3f0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f4 : bv 32 := 0x00b43023.
Lemma F_5d3f4 : fetch_word Plain.M.loaded_segments (0x5d44c : word) = Some W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : decode_any W_5d3f4 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f8 : bv 32 := 0x01813083.
Lemma F_5d3f8 : fetch_word Plain.M.loaded_segments (0x5d450 : word) = Some W_5d3f8.
Proof. vm_refl. Qed.
Lemma D_5d3f8 : decode_any W_5d3f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3fc : bv 32 := 0x01013403.
Lemma F_5d3fc : fetch_word Plain.M.loaded_segments (0x5d454 : word) = Some W_5d3fc.
Proof. vm_refl. Qed.
Lemma D_5d3fc : decode_any W_5d3fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d400 : bv 32 := 0x00813483.
Lemma F_5d400 : fetch_word Plain.M.loaded_segments (0x5d458 : word) = Some W_5d400.
Proof. vm_refl. Qed.
Lemma D_5d400 : decode_any W_5d400 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d404 : bv 32 := 0x02010113.
Lemma F_5d404 : fetch_word Plain.M.loaded_segments (0x5d45c : word) = Some W_5d404.
Proof. vm_refl. Qed.
Lemma D_5d404 : decode_any W_5d404 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d408 : bv 32 := 0x00008067.
Lemma F_5d408 : fetch_word Plain.M.loaded_segments (0x5d460 : word) = Some W_5d408.
Proof. vm_refl. Qed.
Lemma D_5d408 : decode_any W_5d408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

