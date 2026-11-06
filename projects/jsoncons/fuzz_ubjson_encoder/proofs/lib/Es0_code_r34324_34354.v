(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_34914 : bv 32 := 0x00095517.
Lemma F_34914 : fetch_word Plain.M.loaded_segments (0x3496c : word) = Some W_34914.
Proof. vm_refl. Qed.
Lemma D_34914 : decode_any W_34914 = Some (Auipc 10 149, 4%Z).
Proof. vm_refl. Qed.

Definition W_34918 : bv 32 := 0xca854503.
Lemma F_34918 : fetch_word Plain.M.loaded_segments (0x34970 : word) = Some W_34918.
Proof. vm_refl. Qed.
Lemma D_34918 : decode_any W_34918 = Some (Load SZ1 false 10 10 3240, 4%Z).
Proof. vm_refl. Qed.

Definition W_3491c : bv 32 := 0x00051463.
Lemma F_3491c : fetch_word Plain.M.loaded_segments (0x34974 : word) = Some W_3491c.
Proof. vm_refl. Qed.
Lemma D_3491c : decode_any W_3491c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34920 : bv 32 := 0x00008067.
Lemma F_34920 : fetch_word Plain.M.loaded_segments (0x34978 : word) = Some W_34920.
Proof. vm_refl. Qed.
Lemma D_34920 : decode_any W_34920 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34924 : bv 32 := 0xff010113.
Lemma F_34924 : fetch_word Plain.M.loaded_segments (0x3497c : word) = Some W_34924.
Proof. vm_refl. Qed.
Lemma D_34924 : decode_any W_34924 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34928 : bv 32 := 0x00113423.
Lemma F_34928 : fetch_word Plain.M.loaded_segments (0x34980 : word) = Some W_34928.
Proof. vm_refl. Qed.
Lemma D_34928 : decode_any W_34928 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3492c : bv 32 := 0x00083517.
Lemma F_3492c : fetch_word Plain.M.loaded_segments (0x34984 : word) = Some W_3492c.
Proof. vm_refl. Qed.
Lemma D_3492c : decode_any W_3492c = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

Definition W_34930 : bv 32 := 0x7dc53503.
Lemma F_34930 : fetch_word Plain.M.loaded_segments (0x34988 : word) = Some W_34930.
Proof. vm_refl. Qed.
Lemma D_34930 : decode_any W_34930 = Some (Load SZ8 true 10 10 2012, 4%Z).
Proof. vm_refl. Qed.

Definition W_34934 : bv 32 := 0x00053503.
Lemma F_34934 : fetch_word Plain.M.loaded_segments (0x3498c : word) = Some W_34934.
Proof. vm_refl. Qed.
Lemma D_34934 : decode_any W_34934 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34938 : bv 32 := 0x3a06c0ef.
Lemma F_34938 : fetch_word Plain.M.loaded_segments (0x34990 : word) = Some W_34938.
Proof. vm_refl. Qed.
Lemma D_34938 : decode_any W_34938 = Some (Jal 1 443296, 4%Z).
Proof. vm_refl. Qed.

Definition W_3493c : bv 32 := 0x04d00513.
Lemma F_3493c : fetch_word Plain.M.loaded_segments (0x34994 : word) = Some W_3493c.
Proof. vm_refl. Qed.
Lemma D_3493c : decode_any W_3493c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_34940 : bv 32 := 0x18d7c0ef.
Lemma F_34940 : fetch_word Plain.M.loaded_segments (0x34998 : word) = Some W_34940.
Proof. vm_refl. Qed.
Lemma D_34940 : decode_any W_34940 = Some (Jal 1 510348, 4%Z).
Proof. vm_refl. Qed.
