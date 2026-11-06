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

Definition W_58910 : bv 32 := 0x00054583.
Lemma F_58910 : fetch_word Plain.M.loaded_segments (0x58968 : word) = Some W_58910.
Proof. vm_refl. Qed.
Lemma D_58910 : decode_any W_58910 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58914 : bv 32 := 0x0015f593.
Lemma F_58914 : fetch_word Plain.M.loaded_segments (0x5896c : word) = Some W_58914.
Proof. vm_refl. Qed.
Lemma D_58914 : decode_any W_58914 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58918 : bv 32 := 0x00059463.
Lemma F_58918 : fetch_word Plain.M.loaded_segments (0x58970 : word) = Some W_58918.
Proof. vm_refl. Qed.
Lemma D_58918 : decode_any W_58918 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5891c : bv 32 := 0x00008067.
Lemma F_5891c : fetch_word Plain.M.loaded_segments (0x58974 : word) = Some W_5891c.
Proof. vm_refl. Qed.
Lemma D_5891c : decode_any W_5891c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
