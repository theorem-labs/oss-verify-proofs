(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_36248 : bv 32 := 0x00813827.
Lemma F_36248 : fetch_word Ubsan.M.loaded_segments (0x362a0 : word) = Some W_36248.
Proof. vm_refl. Qed.
Lemma D_36248 : decode_any W_36248 = Some (FStore FMT_D 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3624c : bv 32 := 0x00913427.
Lemma F_3624c : fetch_word Ubsan.M.loaded_segments (0x362a4 : word) = Some W_3624c.
Proof. vm_refl. Qed.
Lemma D_3624c : decode_any W_3624c = Some (FStore FMT_D 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_36250 : bv 32 := 0x00050413.
Lemma F_36250 : fetch_word Ubsan.M.loaded_segments (0x362a8 : word) = Some W_36250.
Proof. vm_refl. Qed.
Lemma D_36250 : decode_any W_36250 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_36254 : bv 32 := 0x401574d3.
Lemma F_36254 : fetch_word Ubsan.M.loaded_segments (0x362ac : word) = Some W_36254.
Proof. vm_refl. Qed.
Lemma D_36254 : decode_any W_36254 = Some (Fcvt FC_S FC_D 9 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_36258 : bv 32 := 0x00853503.
Lemma F_36258 : fetch_word Ubsan.M.loaded_segments (0x362b0 : word) = Some W_36258.
Proof. vm_refl. Qed.
Lemma D_36258 : decode_any W_36258 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3625c : bv 32 := 0x00840493.
Lemma F_3625c : fetch_word Ubsan.M.loaded_segments (0x362b4 : word) = Some W_3625c.
Proof. vm_refl. Qed.
Lemma D_3625c : decode_any W_3625c = Some (OpImm ALU_ADD 9 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_36260 : bv 32 := 0x420487d3.
Lemma F_36260 : fetch_word Ubsan.M.loaded_segments (0x362b8 : word) = Some W_36260.
Proof. vm_refl. Qed.
Lemma D_36260 : decode_any W_36260 = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_36264 : bv 32 := 0xa2f52653.
Lemma F_36264 : fetch_word Ubsan.M.loaded_segments (0x362bc : word) = Some W_36264.
Proof. vm_refl. Qed.
Lemma D_36264 : decode_any W_36264 = Some (Fcmp F_EQ FMT_D 12 10 15, 4%Z).
Proof. vm_refl. Qed.
