(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17b4c : bv 32 := 0xff010113.
Lemma F_17b4c : fetch_word Plain.M.loaded_segments (0x17ba4 : word) = Some W_17b4c.
Proof. vm_refl. Qed.
Lemma D_17b4c : decode_any W_17b4c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b50 : bv 32 := 0x00113423.
Lemma F_17b50 : fetch_word Plain.M.loaded_segments (0x17ba8 : word) = Some W_17b50.
Proof. vm_refl. Qed.
Lemma D_17b50 : decode_any W_17b50 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b54 : bv 32 := 0x00813023.
Lemma F_17b54 : fetch_word Plain.M.loaded_segments (0x17bac : word) = Some W_17b54.
Proof. vm_refl. Qed.
Lemma D_17b54 : decode_any W_17b54 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b58 : bv 32 := 0x00060413.
Lemma F_17b58 : fetch_word Plain.M.loaded_segments (0x17bb0 : word) = Some W_17b58.
Proof. vm_refl. Qed.
Lemma D_17b58 : decode_any W_17b58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b5c : bv 32 := 0x00050613.
Lemma F_17b5c : fetch_word Plain.M.loaded_segments (0x17bb4 : word) = Some W_17b5c.
Proof. vm_refl. Qed.
Lemma D_17b5c : decode_any W_17b5c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b60 : bv 32 := 0xffffb517.
Lemma F_17b60 : fetch_word Plain.M.loaded_segments (0x17bb8 : word) = Some W_17b60.
Proof. vm_refl. Qed.
Lemma D_17b60 : decode_any W_17b60 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b64 : bv 32 := 0x83850513.
Lemma F_17b64 : fetch_word Plain.M.loaded_segments (0x17bbc : word) = Some W_17b64.
Proof. vm_refl. Qed.
Lemma D_17b64 : decode_any W_17b64 = Some (OpImm ALU_ADD 10 10 2104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b68 : bv 32 := 0x018000ef.
Lemma F_17b68 : fetch_word Plain.M.loaded_segments (0x17bc0 : word) = Some W_17b68.
Proof. vm_refl. Qed.
Lemma D_17b68 : decode_any W_17b68 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b6c : bv 32 := 0x00040513.
Lemma F_17b6c : fetch_word Plain.M.loaded_segments (0x17bc4 : word) = Some W_17b6c.
Proof. vm_refl. Qed.
Lemma D_17b6c : decode_any W_17b6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b70 : bv 32 := 0x00813083.
Lemma F_17b70 : fetch_word Plain.M.loaded_segments (0x17bc8 : word) = Some W_17b70.
Proof. vm_refl. Qed.
Lemma D_17b70 : decode_any W_17b70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b74 : bv 32 := 0x00013403.
Lemma F_17b74 : fetch_word Plain.M.loaded_segments (0x17bcc : word) = Some W_17b74.
Proof. vm_refl. Qed.
Lemma D_17b74 : decode_any W_17b74 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b78 : bv 32 := 0x01010113.
Lemma F_17b78 : fetch_word Plain.M.loaded_segments (0x17bd0 : word) = Some W_17b78.
Proof. vm_refl. Qed.
Lemma D_17b78 : decode_any W_17b78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b7c : bv 32 := 0x00008067.
Lemma F_17b7c : fetch_word Plain.M.loaded_segments (0x17bd4 : word) = Some W_17b7c.
Proof. vm_refl. Qed.
Lemma D_17b7c : decode_any W_17b7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c1c : bv 32 := 0xff010113.
Lemma F_17c1c : fetch_word Plain.M.loaded_segments (0x17c74 : word) = Some W_17c1c.
Proof. vm_refl. Qed.
Lemma D_17c1c : decode_any W_17c1c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c20 : bv 32 := 0x00113423.
Lemma F_17c20 : fetch_word Plain.M.loaded_segments (0x17c78 : word) = Some W_17c20.
Proof. vm_refl. Qed.
Lemma D_17c20 : decode_any W_17c20 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c24 : bv 32 := 0x00813023.
Lemma F_17c24 : fetch_word Plain.M.loaded_segments (0x17c7c : word) = Some W_17c24.
Proof. vm_refl. Qed.
Lemma D_17c24 : decode_any W_17c24 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c28 : bv 32 := 0x00060413.
Lemma F_17c28 : fetch_word Plain.M.loaded_segments (0x17c80 : word) = Some W_17c28.
Proof. vm_refl. Qed.
Lemma D_17c28 : decode_any W_17c28 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c2c : bv 32 := 0x00050613.
Lemma F_17c2c : fetch_word Plain.M.loaded_segments (0x17c84 : word) = Some W_17c2c.
Proof. vm_refl. Qed.
Lemma D_17c2c : decode_any W_17c2c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c30 : bv 32 := 0xffffa517.
Lemma F_17c30 : fetch_word Plain.M.loaded_segments (0x17c88 : word) = Some W_17c30.
Proof. vm_refl. Qed.
Lemma D_17c30 : decode_any W_17c30 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c34 : bv 32 := 0x76850513.
Lemma F_17c34 : fetch_word Plain.M.loaded_segments (0x17c8c : word) = Some W_17c34.
Proof. vm_refl. Qed.
Lemma D_17c34 : decode_any W_17c34 = Some (OpImm ALU_ADD 10 10 1896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c38 : bv 32 := 0xf49ff0ef.
Lemma F_17c38 : fetch_word Plain.M.loaded_segments (0x17c90 : word) = Some W_17c38.
Proof. vm_refl. Qed.
Lemma D_17c38 : decode_any W_17c38 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c3c : bv 32 := 0x00040513.
Lemma F_17c3c : fetch_word Plain.M.loaded_segments (0x17c94 : word) = Some W_17c3c.
Proof. vm_refl. Qed.
Lemma D_17c3c : decode_any W_17c3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c40 : bv 32 := 0x00813083.
Lemma F_17c40 : fetch_word Plain.M.loaded_segments (0x17c98 : word) = Some W_17c40.
Proof. vm_refl. Qed.
Lemma D_17c40 : decode_any W_17c40 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c44 : bv 32 := 0x00013403.
Lemma F_17c44 : fetch_word Plain.M.loaded_segments (0x17c9c : word) = Some W_17c44.
Proof. vm_refl. Qed.
Lemma D_17c44 : decode_any W_17c44 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c48 : bv 32 := 0x01010113.
Lemma F_17c48 : fetch_word Plain.M.loaded_segments (0x17ca0 : word) = Some W_17c48.
Proof. vm_refl. Qed.
Lemma D_17c48 : decode_any W_17c48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c4c : bv 32 := 0x00008067.
Lemma F_17c4c : fetch_word Plain.M.loaded_segments (0x17ca4 : word) = Some W_17c4c.
Proof. vm_refl. Qed.
Lemma D_17c4c : decode_any W_17c4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dc4 : bv 32 := 0x02050e63.
Lemma F_17dc4 : fetch_word Plain.M.loaded_segments (0x17e1c : word) = Some W_17dc4.
Proof. vm_refl. Qed.
Lemma D_17dc4 : decode_any W_17dc4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dc8 : bv 32 := 0xfe010113.
Lemma F_17dc8 : fetch_word Plain.M.loaded_segments (0x17e20 : word) = Some W_17dc8.
Proof. vm_refl. Qed.
Lemma D_17dc8 : decode_any W_17dc8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dcc : bv 32 := 0x00113c23.
Lemma F_17dcc : fetch_word Plain.M.loaded_segments (0x17e24 : word) = Some W_17dcc.
Proof. vm_refl. Qed.
Lemma D_17dcc : decode_any W_17dcc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dd0 : bv 32 := 0x00813823.
Lemma F_17dd0 : fetch_word Plain.M.loaded_segments (0x17e28 : word) = Some W_17dd0.
Proof. vm_refl. Qed.
Lemma D_17dd0 : decode_any W_17dd0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dd4 : bv 32 := 0x00913423.
Lemma F_17dd4 : fetch_word Plain.M.loaded_segments (0x17e2c : word) = Some W_17dd4.
Proof. vm_refl. Qed.
Lemma D_17dd4 : decode_any W_17dd4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dd8 : bv 32 := 0x00058493.
Lemma F_17dd8 : fetch_word Plain.M.loaded_segments (0x17e30 : word) = Some W_17dd8.
Proof. vm_refl. Qed.
Lemma D_17dd8 : decode_any W_17dd8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ddc : bv 32 := 0x00050413.
Lemma F_17ddc : fetch_word Plain.M.loaded_segments (0x17e34 : word) = Some W_17ddc.
Proof. vm_refl. Qed.
Lemma D_17ddc : decode_any W_17ddc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17de0 : bv 32 := 0x00053503.
Lemma F_17de0 : fetch_word Plain.M.loaded_segments (0x17e38 : word) = Some W_17de0.
Proof. vm_refl. Qed.
Lemma D_17de0 : decode_any W_17de0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17de4 : bv 32 := 0x00050463.
Lemma F_17de4 : fetch_word Plain.M.loaded_segments (0x17e3c : word) = Some W_17de4.
Proof. vm_refl. Qed.
Lemma D_17de4 : decode_any W_17de4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17dec : bv 32 := 0x04048063.
Lemma F_17dec : fetch_word Plain.M.loaded_segments (0x17e44 : word) = Some W_17dec.
Proof. vm_refl. Qed.
Lemma D_17dec : decode_any W_17dec = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e2c : bv 32 := 0x00000593.
Lemma F_17e2c : fetch_word Plain.M.loaded_segments (0x17e84 : word) = Some W_17e2c.
Proof. vm_refl. Qed.
Lemma D_17e2c : decode_any W_17e2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e30 : bv 32 := 0x00000513.
Lemma F_17e30 : fetch_word Plain.M.loaded_segments (0x17e88 : word) = Some W_17e30.
Proof. vm_refl. Qed.
Lemma D_17e30 : decode_any W_17e30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e34 : bv 32 := 0x00b43023.
Lemma F_17e34 : fetch_word Plain.M.loaded_segments (0x17e8c : word) = Some W_17e34.
Proof. vm_refl. Qed.
Lemma D_17e34 : decode_any W_17e34 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e38 : bv 32 := 0x01813083.
Lemma F_17e38 : fetch_word Plain.M.loaded_segments (0x17e90 : word) = Some W_17e38.
Proof. vm_refl. Qed.
Lemma D_17e38 : decode_any W_17e38 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e3c : bv 32 := 0x01013403.
Lemma F_17e3c : fetch_word Plain.M.loaded_segments (0x17e94 : word) = Some W_17e3c.
Proof. vm_refl. Qed.
Lemma D_17e3c : decode_any W_17e3c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e40 : bv 32 := 0x00813483.
Lemma F_17e40 : fetch_word Plain.M.loaded_segments (0x17e98 : word) = Some W_17e40.
Proof. vm_refl. Qed.
Lemma D_17e40 : decode_any W_17e40 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e44 : bv 32 := 0x02010113.
Lemma F_17e44 : fetch_word Plain.M.loaded_segments (0x17e9c : word) = Some W_17e44.
Proof. vm_refl. Qed.
Lemma D_17e44 : decode_any W_17e44 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e48 : bv 32 := 0x00008067.
Lemma F_17e48 : fetch_word Plain.M.loaded_segments (0x17ea0 : word) = Some W_17e48.
Proof. vm_refl. Qed.
Lemma D_17e48 : decode_any W_17e48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
