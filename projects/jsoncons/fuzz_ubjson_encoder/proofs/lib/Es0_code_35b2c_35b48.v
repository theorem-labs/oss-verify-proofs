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

Definition W_35b2c : bv 32 := 0x00813827.
Lemma F_35b2c : fetch_word Plain.M.loaded_segments (0x35b84 : word) = Some W_35b2c.
Proof. vm_refl. Qed.
Lemma D_35b2c : decode_any W_35b2c = Some (FStore FMT_D 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b30 : bv 32 := 0x00913427.
Lemma F_35b30 : fetch_word Plain.M.loaded_segments (0x35b88 : word) = Some W_35b30.
Proof. vm_refl. Qed.
Lemma D_35b30 : decode_any W_35b30 = Some (FStore FMT_D 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b34 : bv 32 := 0x00050413.
Lemma F_35b34 : fetch_word Plain.M.loaded_segments (0x35b8c : word) = Some W_35b34.
Proof. vm_refl. Qed.
Lemma D_35b34 : decode_any W_35b34 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b38 : bv 32 := 0x401574d3.
Lemma F_35b38 : fetch_word Plain.M.loaded_segments (0x35b90 : word) = Some W_35b38.
Proof. vm_refl. Qed.
Lemma D_35b38 : decode_any W_35b38 = Some (Fcvt FC_S FC_D 9 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b3c : bv 32 := 0x00853503.
Lemma F_35b3c : fetch_word Plain.M.loaded_segments (0x35b94 : word) = Some W_35b3c.
Proof. vm_refl. Qed.
Lemma D_35b3c : decode_any W_35b3c = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b40 : bv 32 := 0x420487d3.
Lemma F_35b40 : fetch_word Plain.M.loaded_segments (0x35b98 : word) = Some W_35b40.
Proof. vm_refl. Qed.
Lemma D_35b40 : decode_any W_35b40 = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_35b44 : bv 32 := 0xa2f525d3.
Lemma F_35b44 : fetch_word Plain.M.loaded_segments (0x35b9c : word) = Some W_35b44.
Proof. vm_refl. Qed.
Lemma D_35b44 : decode_any W_35b44 = Some (Fcmp F_EQ FMT_D 11 10 15, 4%Z).
Proof. vm_refl. Qed.
