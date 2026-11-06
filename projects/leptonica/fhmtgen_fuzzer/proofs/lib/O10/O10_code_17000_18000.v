(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushS10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17508 : bv 32 := 0xfd010113.
Lemma F_17508 : fetch_word Plain.M.loaded_segments (0x17604 : word) = Some W_17508.
Proof. vm_refl. Qed.
Lemma D_17508 : decode_any W_17508 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1750c : bv 32 := 0x02113423.
Lemma F_1750c : fetch_word Plain.M.loaded_segments (0x17608 : word) = Some W_1750c.
Proof. vm_refl. Qed.
Lemma D_1750c : decode_any W_1750c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17510 : bv 32 := 0x02813023.
Lemma F_17510 : fetch_word Plain.M.loaded_segments (0x1760c : word) = Some W_17510.
Proof. vm_refl. Qed.
Lemma D_17510 : decode_any W_17510 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17514 : bv 32 := 0x00913c23.
Lemma F_17514 : fetch_word Plain.M.loaded_segments (0x17610 : word) = Some W_17514.
Proof. vm_refl. Qed.
Lemma D_17514 : decode_any W_17514 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17518 : bv 32 := 0x01213823.
Lemma F_17518 : fetch_word Plain.M.loaded_segments (0x17614 : word) = Some W_17518.
Proof. vm_refl. Qed.
Lemma D_17518 : decode_any W_17518 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1751c : bv 32 := 0x06050063.
Lemma F_1751c : fetch_word Plain.M.loaded_segments (0x17618 : word) = Some W_1751c.
Proof. vm_refl. Qed.
Lemma D_1751c : decode_any W_1751c = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17520 : bv 32 := 0x00050493.
Lemma F_17520 : fetch_word Plain.M.loaded_segments (0x1761c : word) = Some W_17520.
Proof. vm_refl. Qed.
Lemma D_17520 : decode_any W_17520 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17524 : bv 32 := 0x00058913.
Lemma F_17524 : fetch_word Plain.M.loaded_segments (0x17620 : word) = Some W_17524.
Proof. vm_refl. Qed.
Lemma D_17524 : decode_any W_17524 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17528 : bv 32 := 0x00c10593.
Lemma F_17528 : fetch_word Plain.M.loaded_segments (0x17624 : word) = Some W_17528.
Proof. vm_refl. Qed.
Lemma D_17528 : decode_any W_17528 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1752c : bv 32 := 0x00810613.
Lemma F_1752c : fetch_word Plain.M.loaded_segments (0x17628 : word) = Some W_1752c.
Proof. vm_refl. Qed.
Lemma D_1752c : decode_any W_1752c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17530 : bv 32 := 0x00410693.
Lemma F_17530 : fetch_word Plain.M.loaded_segments (0x1762c : word) = Some W_17530.
Proof. vm_refl. Qed.
Lemma D_17530 : decode_any W_17530 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17534 : bv 32 := 0xc41fe0ef.
Lemma F_17534 : fetch_word Plain.M.loaded_segments (0x17630 : word) = Some W_17534.
Proof. vm_refl. Qed.
Lemma D_17534 : decode_any W_17534 = Some (Jal 1 2092096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17538 : bv 32 := 0x00412503.
Lemma F_17538 : fetch_word Plain.M.loaded_segments (0x17634 : word) = Some W_17538.
Proof. vm_refl. Qed.
Lemma D_17538 : decode_any W_17538 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1753c : bv 32 := 0x02000593.
Lemma F_1753c : fetch_word Plain.M.loaded_segments (0x17638 : word) = Some W_1753c.
Proof. vm_refl. Qed.
Lemma D_1753c : decode_any W_1753c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17540 : bv 32 := 0x12b50463.
Lemma F_17540 : fetch_word Plain.M.loaded_segments (0x1763c : word) = Some W_17540.
Proof. vm_refl. Qed.
Lemma D_17540 : decode_any W_17540 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17668 : bv 32 := 0x00000513.
Lemma F_17668 : fetch_word Plain.M.loaded_segments (0x17764 : word) = Some W_17668.
Proof. vm_refl. Qed.
Lemma D_17668 : decode_any W_17668 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1766c : bv 32 := 0x02813083.
Lemma F_1766c : fetch_word Plain.M.loaded_segments (0x17768 : word) = Some W_1766c.
Proof. vm_refl. Qed.
Lemma D_1766c : decode_any W_1766c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17670 : bv 32 := 0x02013403.
Lemma F_17670 : fetch_word Plain.M.loaded_segments (0x1776c : word) = Some W_17670.
Proof. vm_refl. Qed.
Lemma D_17670 : decode_any W_17670 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17674 : bv 32 := 0x01813483.
Lemma F_17674 : fetch_word Plain.M.loaded_segments (0x17770 : word) = Some W_17674.
Proof. vm_refl. Qed.
Lemma D_17674 : decode_any W_17674 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17678 : bv 32 := 0x01013903.
Lemma F_17678 : fetch_word Plain.M.loaded_segments (0x17774 : word) = Some W_17678.
Proof. vm_refl. Qed.
Lemma D_17678 : decode_any W_17678 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1767c : bv 32 := 0x03010113.
Lemma F_1767c : fetch_word Plain.M.loaded_segments (0x17778 : word) = Some W_1767c.
Proof. vm_refl. Qed.
Lemma D_1767c : decode_any W_1767c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17680 : bv 32 := 0x00008067.
Lemma F_17680 : fetch_word Plain.M.loaded_segments (0x1777c : word) = Some W_17680.
Proof. vm_refl. Qed.
Lemma D_17680 : decode_any W_17680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
