(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_867a8 : bv 32 := 0x0013d517.
Lemma F_867a8 : fetch_word Asan.M.loaded_segments (0x867f8 : word) = Some W_867a8.
Proof. vm_refl. Qed.
Lemma D_867a8 : decode_any W_867a8 = Some (Auipc 10 317, 4%Z).
Proof. vm_refl. Qed.

Definition W_867ac : bv 32 := 0x46950503.
Lemma F_867ac : fetch_word Asan.M.loaded_segments (0x867fc : word) = Some W_867ac.
Proof. vm_refl. Qed.
Lemma D_867ac : decode_any W_867ac = Some (Load SZ1 true 10 10 1129, 4%Z).
Proof. vm_refl. Qed.

Definition W_867b0 : bv 32 := 0x00a03533.
Lemma F_867b0 : fetch_word Asan.M.loaded_segments (0x86800 : word) = Some W_867b0.
Proof. vm_refl. Qed.
Lemma D_867b0 : decode_any W_867b0 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_867b4 : bv 32 := 0x00008067.
Lemma F_867b4 : fetch_word Asan.M.loaded_segments (0x86804 : word) = Some W_867b4.
Proof. vm_refl. Qed.
Lemma D_867b4 : decode_any W_867b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d0 : bv 32 := 0x0013d517.
Lemma F_867d0 : fetch_word Asan.M.loaded_segments (0x86820 : word) = Some W_867d0.
Proof. vm_refl. Qed.
Lemma D_867d0 : decode_any W_867d0 = Some (Auipc 10 317, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d4 : bv 32 := 0x44250503.
Lemma F_867d4 : fetch_word Asan.M.loaded_segments (0x86824 : word) = Some W_867d4.
Proof. vm_refl. Qed.
Lemma D_867d4 : decode_any W_867d4 = Some (Load SZ1 true 10 10 1090, 4%Z).
Proof. vm_refl. Qed.

Definition W_867d8 : bv 32 := 0x00a03533.
Lemma F_867d8 : fetch_word Asan.M.loaded_segments (0x86828 : word) = Some W_867d8.
Proof. vm_refl. Qed.
Lemma D_867d8 : decode_any W_867d8 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_867dc : bv 32 := 0x00008067.
Lemma F_867dc : fetch_word Asan.M.loaded_segments (0x8682c : word) = Some W_867dc.
Proof. vm_refl. Qed.
Lemma D_867dc : decode_any W_867dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
