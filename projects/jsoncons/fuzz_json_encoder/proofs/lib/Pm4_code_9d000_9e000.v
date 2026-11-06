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
Definition W_9d5d8 : bv 32 := 0xfe010113.
Lemma F_9d5d8 : fetch_word Asan.M.loaded_segments (0x9d628 : word) = Some W_9d5d8.
Proof. vm_refl. Qed.
Lemma D_9d5d8 : decode_any W_9d5d8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5dc : bv 32 := 0x00113c23.
Lemma F_9d5dc : fetch_word Asan.M.loaded_segments (0x9d62c : word) = Some W_9d5dc.
Proof. vm_refl. Qed.
Lemma D_9d5dc : decode_any W_9d5dc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5e0 : bv 32 := 0x00813823.
Lemma F_9d5e0 : fetch_word Asan.M.loaded_segments (0x9d630 : word) = Some W_9d5e0.
Proof. vm_refl. Qed.
Lemma D_9d5e0 : decode_any W_9d5e0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5e4 : bv 32 := 0x00913423.
Lemma F_9d5e4 : fetch_word Asan.M.loaded_segments (0x9d634 : word) = Some W_9d5e4.
Proof. vm_refl. Qed.
Lemma D_9d5e4 : decode_any W_9d5e4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5e8 : bv 32 := 0x01213023.
Lemma F_9d5e8 : fetch_word Asan.M.loaded_segments (0x9d638 : word) = Some W_9d5e8.
Proof. vm_refl. Qed.
Lemma D_9d5e8 : decode_any W_9d5e8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5ec : bv 32 := 0x00058413.
Lemma F_9d5ec : fetch_word Asan.M.loaded_segments (0x9d63c : word) = Some W_9d5ec.
Proof. vm_refl. Qed.
Lemma D_9d5ec : decode_any W_9d5ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5f0 : bv 32 := 0x000c3597.
Lemma F_9d5f0 : fetch_word Asan.M.loaded_segments (0x9d640 : word) = Some W_9d5f0.
Proof. vm_refl. Qed.
Lemma D_9d5f0 : decode_any W_9d5f0 = Some (Auipc 11 195, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5f4 : bv 32 := 0x5b85b903.
Lemma F_9d5f4 : fetch_word Asan.M.loaded_segments (0x9d644 : word) = Some W_9d5f4.
Proof. vm_refl. Qed.
Lemma D_9d5f4 : decode_any W_9d5f4 = Some (Load SZ8 true 18 11 1464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5f8 : bv 32 := 0x00093583.
Lemma F_9d5f8 : fetch_word Asan.M.loaded_segments (0x9d648 : word) = Some W_9d5f8.
Proof. vm_refl. Qed.
Lemma D_9d5f8 : decode_any W_9d5f8 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d5fc : bv 32 := 0x00050493.
Lemma F_9d5fc : fetch_word Asan.M.loaded_segments (0x9d64c : word) = Some W_9d5fc.
Proof. vm_refl. Qed.
Lemma D_9d5fc : decode_any W_9d5fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d600 : bv 32 := 0x00059863.
Lemma F_9d600 : fetch_word Asan.M.loaded_segments (0x9d650 : word) = Some W_9d600.
Proof. vm_refl. Qed.
Lemma D_9d600 : decode_any W_9d600 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d610 : bv 32 := 0xfff58513.
Lemma F_9d610 : fetch_word Asan.M.loaded_segments (0x9d660 : word) = Some W_9d610.
Proof. vm_refl. Qed.
Lemma D_9d610 : decode_any W_9d610 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d614 : bv 32 := 0x00a5f533.
Lemma F_9d614 : fetch_word Asan.M.loaded_segments (0x9d664 : word) = Some W_9d614.
Proof. vm_refl. Qed.
Lemma D_9d614 : decode_any W_9d614 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d618 : bv 32 := 0x04051a63.
Lemma F_9d618 : fetch_word Asan.M.loaded_segments (0x9d668 : word) = Some W_9d618.
Proof. vm_refl. Qed.
Lemma D_9d618 : decode_any W_9d618 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d61c : bv 32 := 0x00b484b3.
Lemma F_9d61c : fetch_word Asan.M.loaded_segments (0x9d66c : word) = Some W_9d61c.
Proof. vm_refl. Qed.
Lemma D_9d61c : decode_any W_9d61c = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d620 : bv 32 := 0x40b005b3.
Lemma F_9d620 : fetch_word Asan.M.loaded_segments (0x9d670 : word) = Some W_9d620.
Proof. vm_refl. Qed.
Lemma D_9d620 : decode_any W_9d620 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d624 : bv 32 := 0xfff48513.
Lemma F_9d624 : fetch_word Asan.M.loaded_segments (0x9d674 : word) = Some W_9d624.
Proof. vm_refl. Qed.
Lemma D_9d624 : decode_any W_9d624 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d628 : bv 32 := 0x00b57533.
Lemma F_9d628 : fetch_word Asan.M.loaded_segments (0x9d678 : word) = Some W_9d628.
Proof. vm_refl. Qed.
Lemma D_9d628 : decode_any W_9d628 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d62c : bv 32 := 0x00b475b3.
Lemma F_9d62c : fetch_word Asan.M.loaded_segments (0x9d67c : word) = Some W_9d62c.
Proof. vm_refl. Qed.
Lemma D_9d62c : decode_any W_9d62c = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d630 : bv 32 := 0x02b57263.
Lemma F_9d630 : fetch_word Asan.M.loaded_segments (0x9d680 : word) = Some W_9d630.
Proof. vm_refl. Qed.
Lemma D_9d630 : decode_any W_9d630 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d634 : bv 32 := 0x40a585b3.
Lemma F_9d634 : fetch_word Asan.M.loaded_segments (0x9d684 : word) = Some W_9d634.
Proof. vm_refl. Qed.
Lemma D_9d634 : decode_any W_9d634 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d638 : bv 32 := 0x00400613.
Lemma F_9d638 : fetch_word Asan.M.loaded_segments (0x9d688 : word) = Some W_9d638.
Proof. vm_refl. Qed.
Lemma D_9d638 : decode_any W_9d638 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d63c : bv 32 := 0x01813083.
Lemma F_9d63c : fetch_word Asan.M.loaded_segments (0x9d68c : word) = Some W_9d63c.
Proof. vm_refl. Qed.
Lemma D_9d63c : decode_any W_9d63c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d640 : bv 32 := 0x01013403.
Lemma F_9d640 : fetch_word Asan.M.loaded_segments (0x9d690 : word) = Some W_9d640.
Proof. vm_refl. Qed.
Lemma D_9d640 : decode_any W_9d640 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d644 : bv 32 := 0x00813483.
Lemma F_9d644 : fetch_word Asan.M.loaded_segments (0x9d694 : word) = Some W_9d644.
Proof. vm_refl. Qed.
Lemma D_9d644 : decode_any W_9d644 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d648 : bv 32 := 0x00013903.
Lemma F_9d648 : fetch_word Asan.M.loaded_segments (0x9d698 : word) = Some W_9d648.
Proof. vm_refl. Qed.
Lemma D_9d648 : decode_any W_9d648 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d64c : bv 32 := 0x02010113.
Lemma F_9d64c : fetch_word Asan.M.loaded_segments (0x9d69c : word) = Some W_9d64c.
Proof. vm_refl. Qed.
Lemma D_9d64c : decode_any W_9d64c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d650 : bv 32 := 0xbb1f606f.
Lemma F_9d650 : fetch_word Asan.M.loaded_segments (0x9d6a0 : word) = Some W_9d650.
Proof. vm_refl. Qed.
Lemma D_9d650 : decode_any W_9d650 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d654 : bv 32 := 0x01813083.
Lemma F_9d654 : fetch_word Asan.M.loaded_segments (0x9d6a4 : word) = Some W_9d654.
Proof. vm_refl. Qed.
Lemma D_9d654 : decode_any W_9d654 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d658 : bv 32 := 0x01013403.
Lemma F_9d658 : fetch_word Asan.M.loaded_segments (0x9d6a8 : word) = Some W_9d658.
Proof. vm_refl. Qed.
Lemma D_9d658 : decode_any W_9d658 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d65c : bv 32 := 0x00813483.
Lemma F_9d65c : fetch_word Asan.M.loaded_segments (0x9d6ac : word) = Some W_9d65c.
Proof. vm_refl. Qed.
Lemma D_9d65c : decode_any W_9d65c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d660 : bv 32 := 0x00013903.
Lemma F_9d660 : fetch_word Asan.M.loaded_segments (0x9d6b0 : word) = Some W_9d660.
Proof. vm_refl. Qed.
Lemma D_9d660 : decode_any W_9d660 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d664 : bv 32 := 0x02010113.
Lemma F_9d664 : fetch_word Asan.M.loaded_segments (0x9d6b4 : word) = Some W_9d664.
Proof. vm_refl. Qed.
Lemma D_9d664 : decode_any W_9d664 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d668 : bv 32 := 0x00008067.
Lemma F_9d668 : fetch_word Asan.M.loaded_segments (0x9d6b8 : word) = Some W_9d668.
Proof. vm_refl. Qed.
Lemma D_9d668 : decode_any W_9d668 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

