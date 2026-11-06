(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.H Require GcFlushU22.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_14294 : bv 32 := 0xfe010113.
Lemma F_14294 : fetch_word Ubsan.M.loaded_segments (0x14390 : word) = Some W_14294.
Proof. vm_refl. Qed.
Lemma D_14294 : decode_any W_14294 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14298 : bv 32 := 0x00113c23.
Lemma F_14298 : fetch_word Ubsan.M.loaded_segments (0x14394 : word) = Some W_14298.
Proof. vm_refl. Qed.
Lemma D_14298 : decode_any W_14298 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1429c : bv 32 := 0x00813823.
Lemma F_1429c : fetch_word Ubsan.M.loaded_segments (0x14398 : word) = Some W_1429c.
Proof. vm_refl. Qed.
Lemma D_1429c : decode_any W_1429c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142a0 : bv 32 := 0x00913423.
Lemma F_142a0 : fetch_word Ubsan.M.loaded_segments (0x1439c : word) = Some W_142a0.
Proof. vm_refl. Qed.
Lemma D_142a0 : decode_any W_142a0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142a4 : bv 32 := 0x02050663.
Lemma F_142a4 : fetch_word Ubsan.M.loaded_segments (0x143a0 : word) = Some W_142a4.
Proof. vm_refl. Qed.
Lemma D_142a4 : decode_any W_142a4 = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142a8 : bv 32 := 0x00757593.
Lemma F_142a8 : fetch_word Ubsan.M.loaded_segments (0x143a4 : word) = Some W_142a8.
Proof. vm_refl. Qed.
Lemma D_142a8 : decode_any W_142a8 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142ac : bv 32 := 0x10059863.
Lemma F_142ac : fetch_word Ubsan.M.loaded_segments (0x143a8 : word) = Some W_142ac.
Proof. vm_refl. Qed.
Lemma D_142ac : decode_any W_142ac = Some (Branch BC_NE 11 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142b0 : bv 32 := 0x0330000f.
Lemma F_142b0 : fetch_word Ubsan.M.loaded_segments (0x143ac : word) = Some W_142b0.
Proof. vm_refl. Qed.
Lemma D_142b0 : decode_any W_142b0 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142b4 : bv 32 := 0x01452583.
Lemma F_142b4 : fetch_word Ubsan.M.loaded_segments (0x143b0 : word) = Some W_142b4.
Proof. vm_refl. Qed.
Lemma D_142b4 : decode_any W_142b4 = Some (Load SZ4 true 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142b8 : bv 32 := 0x00100613.
Lemma F_142b8 : fetch_word Ubsan.M.loaded_segments (0x143b4 : word) = Some W_142b8.
Proof. vm_refl. Qed.
Lemma D_142b8 : decode_any W_142b8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142bc : bv 32 := 0x0230000f.
Lemma F_142bc : fetch_word Ubsan.M.loaded_segments (0x143b8 : word) = Some W_142bc.
Proof. vm_refl. Qed.
Lemma D_142bc : decode_any W_142bc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142c0 : bv 32 := 0x02c59c63.
Lemma F_142c0 : fetch_word Ubsan.M.loaded_segments (0x143bc : word) = Some W_142c0.
Proof. vm_refl. Qed.
Lemma D_142c0 : decode_any W_142c0 = Some (Branch BC_NE 11 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142c4 : bv 32 := 0x03853583.
Lemma F_142c4 : fetch_word Ubsan.M.loaded_segments (0x143c0 : word) = Some W_142c4.
Proof. vm_refl. Qed.
Lemma D_142c4 : decode_any W_142c4 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142c8 : bv 32 := 0x02053c23.
Lemma F_142c8 : fetch_word Ubsan.M.loaded_segments (0x143c4 : word) = Some W_142c8.
Proof. vm_refl. Qed.
Lemma D_142c8 : decode_any W_142c8 = Some (Store SZ8 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_142cc : bv 32 := 0x0d80006f.
Lemma F_142cc : fetch_word Ubsan.M.loaded_segments (0x143c8 : word) = Some W_142cc.
Proof. vm_refl. Qed.
Lemma D_142cc : decode_any W_142cc = Some (Jal 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143a4 : bv 32 := 0x00058513.
Lemma F_143a4 : fetch_word Ubsan.M.loaded_segments (0x144a0 : word) = Some W_143a4.
Proof. vm_refl. Qed.
Lemma D_143a4 : decode_any W_143a4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143a8 : bv 32 := 0x01813083.
Lemma F_143a8 : fetch_word Ubsan.M.loaded_segments (0x144a4 : word) = Some W_143a8.
Proof. vm_refl. Qed.
Lemma D_143a8 : decode_any W_143a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143ac : bv 32 := 0x01013403.
Lemma F_143ac : fetch_word Ubsan.M.loaded_segments (0x144a8 : word) = Some W_143ac.
Proof. vm_refl. Qed.
Lemma D_143ac : decode_any W_143ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143b0 : bv 32 := 0x00813483.
Lemma F_143b0 : fetch_word Ubsan.M.loaded_segments (0x144ac : word) = Some W_143b0.
Proof. vm_refl. Qed.
Lemma D_143b0 : decode_any W_143b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143b4 : bv 32 := 0x02010113.
Lemma F_143b4 : fetch_word Ubsan.M.loaded_segments (0x144b0 : word) = Some W_143b4.
Proof. vm_refl. Qed.
Lemma D_143b4 : decode_any W_143b4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_143b8 : bv 32 := 0x00008067.
Lemma F_143b8 : fetch_word Ubsan.M.loaded_segments (0x144b4 : word) = Some W_143b8.
Proof. vm_refl. Qed.
Lemma D_143b8 : decode_any W_143b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
