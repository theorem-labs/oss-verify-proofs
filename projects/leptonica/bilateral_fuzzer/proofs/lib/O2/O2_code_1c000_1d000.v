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
Definition W_1c580 : bv 32 := 0xfe010113.
Lemma F_1c580 : fetch_word Plain.M.loaded_segments (0x1c5d8 : word) = Some W_1c580.
Proof. vm_refl. Qed.
Lemma D_1c580 : decode_any W_1c580 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c584 : bv 32 := 0x00113c23.
Lemma F_1c584 : fetch_word Plain.M.loaded_segments (0x1c5dc : word) = Some W_1c584.
Proof. vm_refl. Qed.
Lemma D_1c584 : decode_any W_1c584 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c588 : bv 32 := 0x00813823.
Lemma F_1c588 : fetch_word Plain.M.loaded_segments (0x1c5e0 : word) = Some W_1c588.
Proof. vm_refl. Qed.
Lemma D_1c588 : decode_any W_1c588 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c58c : bv 32 := 0x00913423.
Lemma F_1c58c : fetch_word Plain.M.loaded_segments (0x1c5e4 : word) = Some W_1c58c.
Proof. vm_refl. Qed.
Lemma D_1c58c : decode_any W_1c58c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c590 : bv 32 := 0x06050463.
Lemma F_1c590 : fetch_word Plain.M.loaded_segments (0x1c5e8 : word) = Some W_1c590.
Proof. vm_refl. Qed.
Lemma D_1c590 : decode_any W_1c590 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c594 : bv 32 := 0x00050413.
Lemma F_1c594 : fetch_word Plain.M.loaded_segments (0x1c5ec : word) = Some W_1c594.
Proof. vm_refl. Qed.
Lemma D_1c594 : decode_any W_1c594 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c598 : bv 32 := 0x00410613.
Lemma F_1c598 : fetch_word Plain.M.loaded_segments (0x1c5f0 : word) = Some W_1c598.
Proof. vm_refl. Qed.
Lemma D_1c598 : decode_any W_1c598 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c59c : bv 32 := 0x00000593.
Lemma F_1c59c : fetch_word Plain.M.loaded_segments (0x1c5f4 : word) = Some W_1c59c.
Proof. vm_refl. Qed.
Lemma D_1c59c : decode_any W_1c59c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5a0 : bv 32 := 0x0dc000ef.
Lemma F_1c5a0 : fetch_word Plain.M.loaded_segments (0x1c5f8 : word) = Some W_1c5a0.
Proof. vm_refl. Qed.
Lemma D_1c5a0 : decode_any W_1c5a0 = Some (Jal 1 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5a4 : bv 32 := 0x00412503.
Lemma F_1c5a4 : fetch_word Plain.M.loaded_segments (0x1c5fc : word) = Some W_1c5a4.
Proof. vm_refl. Qed.
Lemma D_1c5a4 : decode_any W_1c5a4 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5a8 : bv 32 := 0x08050663.
Lemma F_1c5a8 : fetch_word Plain.M.loaded_segments (0x1c600 : word) = Some W_1c5a8.
Proof. vm_refl. Qed.
Lemma D_1c5a8 : decode_any W_1c5a8 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5ac : bv 32 := 0x00100513.
Lemma F_1c5ac : fetch_word Plain.M.loaded_segments (0x1c604 : word) = Some W_1c5ac.
Proof. vm_refl. Qed.
Lemma D_1c5ac : decode_any W_1c5ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5b0 : bv 32 := 0x01800593.
Lemma F_1c5b0 : fetch_word Plain.M.loaded_segments (0x1c608 : word) = Some W_1c5b0.
Proof. vm_refl. Qed.
Lemma D_1c5b0 : decode_any W_1c5b0 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5b4 : bv 32 := 0x0c8130ef.
Lemma F_1c5b4 : fetch_word Plain.M.loaded_segments (0x1c60c : word) = Some W_1c5b4.
Proof. vm_refl. Qed.
Lemma D_1c5b4 : decode_any W_1c5b4 = Some (Jal 1 78024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5b8 : bv 32 := 0x00050493.
Lemma F_1c5b8 : fetch_word Plain.M.loaded_segments (0x1c610 : word) = Some W_1c5b8.
Proof. vm_refl. Qed.
Lemma D_1c5b8 : decode_any W_1c5b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5bc : bv 32 := 0x00c42503.
Lemma F_1c5bc : fetch_word Plain.M.loaded_segments (0x1c614 : word) = Some W_1c5bc.
Proof. vm_refl. Qed.
Lemma D_1c5bc : decode_any W_1c5bc = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5c0 : bv 32 := 0x0025159b.
Lemma F_1c5c0 : fetch_word Plain.M.loaded_segments (0x1c618 : word) = Some W_1c5c0.
Proof. vm_refl. Qed.
Lemma D_1c5c0 : decode_any W_1c5c0 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5c4 : bv 32 := 0x00100513.
Lemma F_1c5c4 : fetch_word Plain.M.loaded_segments (0x1c61c : word) = Some W_1c5c4.
Proof. vm_refl. Qed.
Lemma D_1c5c4 : decode_any W_1c5c4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5c8 : bv 32 := 0x0b4130ef.
Lemma F_1c5c8 : fetch_word Plain.M.loaded_segments (0x1c620 : word) = Some W_1c5c8.
Proof. vm_refl. Qed.
Lemma D_1c5c8 : decode_any W_1c5c8 = Some (Jal 1 78004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5cc : bv 32 := 0x00a4b023.
Lemma F_1c5cc : fetch_word Plain.M.loaded_segments (0x1c624 : word) = Some W_1c5cc.
Proof. vm_refl. Qed.
Lemma D_1c5cc : decode_any W_1c5cc = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5d0 : bv 32 := 0x01042603.
Lemma F_1c5d0 : fetch_word Plain.M.loaded_segments (0x1c628 : word) = Some W_1c5d0.
Proof. vm_refl. Qed.
Lemma D_1c5d0 : decode_any W_1c5d0 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5d4 : bv 32 := 0x00043583.
Lemma F_1c5d4 : fetch_word Plain.M.loaded_segments (0x1c62c : word) = Some W_1c5d4.
Proof. vm_refl. Qed.
Lemma D_1c5d4 : decode_any W_1c5d4 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5d8 : bv 32 := 0x00261613.
Lemma F_1c5d8 : fetch_word Plain.M.loaded_segments (0x1c630 : word) = Some W_1c5d8.
Proof. vm_refl. Qed.
Lemma D_1c5d8 : decode_any W_1c5d8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5dc : bv 32 := 0x4241a0ef.
Lemma F_1c5dc : fetch_word Plain.M.loaded_segments (0x1c634 : word) = Some W_1c5dc.
Proof. vm_refl. Qed.
Lemma D_1c5dc : decode_any W_1c5dc = Some (Jal 1 107556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5e0 : bv 32 := 0x00048513.
Lemma F_1c5e0 : fetch_word Plain.M.loaded_segments (0x1c638 : word) = Some W_1c5e0.
Proof. vm_refl. Qed.
Lemma D_1c5e0 : decode_any W_1c5e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5e4 : bv 32 := 0x01042583.
Lemma F_1c5e4 : fetch_word Plain.M.loaded_segments (0x1c63c : word) = Some W_1c5e4.
Proof. vm_refl. Qed.
Lemma D_1c5e4 : decode_any W_1c5e4 = Some (Load SZ4 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5e8 : bv 32 := 0x00b4a823.
Lemma F_1c5e8 : fetch_word Plain.M.loaded_segments (0x1c640 : word) = Some W_1c5e8.
Proof. vm_refl. Qed.
Lemma D_1c5e8 : decode_any W_1c5e8 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5ec : bv 32 := 0x00843583.
Lemma F_1c5ec : fetch_word Plain.M.loaded_segments (0x1c644 : word) = Some W_1c5ec.
Proof. vm_refl. Qed.
Lemma D_1c5ec : decode_any W_1c5ec = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5f0 : bv 32 := 0x00b4b423.
Lemma F_1c5f0 : fetch_word Plain.M.loaded_segments (0x1c648 : word) = Some W_1c5f0.
Proof. vm_refl. Qed.
Lemma D_1c5f0 : decode_any W_1c5f0 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5f4 : bv 32 := 0x0740006f.
Lemma F_1c5f4 : fetch_word Plain.M.loaded_segments (0x1c64c : word) = Some W_1c5f4.
Proof. vm_refl. Qed.
Lemma D_1c5f4 : decode_any W_1c5f4 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c668 : bv 32 := 0x01813083.
Lemma F_1c668 : fetch_word Plain.M.loaded_segments (0x1c6c0 : word) = Some W_1c668.
Proof. vm_refl. Qed.
Lemma D_1c668 : decode_any W_1c668 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c66c : bv 32 := 0x01013403.
Lemma F_1c66c : fetch_word Plain.M.loaded_segments (0x1c6c4 : word) = Some W_1c66c.
Proof. vm_refl. Qed.
Lemma D_1c66c : decode_any W_1c66c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c670 : bv 32 := 0x00813483.
Lemma F_1c670 : fetch_word Plain.M.loaded_segments (0x1c6c8 : word) = Some W_1c670.
Proof. vm_refl. Qed.
Lemma D_1c670 : decode_any W_1c670 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c674 : bv 32 := 0x02010113.
Lemma F_1c674 : fetch_word Plain.M.loaded_segments (0x1c6cc : word) = Some W_1c674.
Proof. vm_refl. Qed.
Lemma D_1c674 : decode_any W_1c674 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c678 : bv 32 := 0x00008067.
Lemma F_1c678 : fetch_word Plain.M.loaded_segments (0x1c6d0 : word) = Some W_1c678.
Proof. vm_refl. Qed.
Lemma D_1c678 : decode_any W_1c678 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
