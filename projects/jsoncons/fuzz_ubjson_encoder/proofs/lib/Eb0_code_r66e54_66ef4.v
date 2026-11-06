(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_82240 : bv 32 := 0xff010113.
Lemma F_82240 : fetch_word AsanUbsan.M.loaded_segments (0x82290 : word) = Some W_82240.
Proof. vm_refl. Qed.
Lemma D_82240 : decode_any W_82240 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_82244 : bv 32 := 0x00113423.
Lemma F_82244 : fetch_word AsanUbsan.M.loaded_segments (0x82294 : word) = Some W_82244.
Proof. vm_refl. Qed.
Lemma D_82244 : decode_any W_82244 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82248 : bv 32 := 0x00813023.
Lemma F_82248 : fetch_word AsanUbsan.M.loaded_segments (0x82298 : word) = Some W_82248.
Proof. vm_refl. Qed.
Lemma D_82248 : decode_any W_82248 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8224c : bv 32 := 0x000c5517.
Lemma F_8224c : fetch_word AsanUbsan.M.loaded_segments (0x8229c : word) = Some W_8224c.
Proof. vm_refl. Qed.
Lemma D_8224c : decode_any W_8224c = Some (Auipc 10 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_82250 : bv 32 := 0xb3c50413.
Lemma F_82250 : fetch_word AsanUbsan.M.loaded_segments (0x822a0 : word) = Some W_82250.
Proof. vm_refl. Qed.
Lemma D_82250 : decode_any W_82250 = Some (OpImm ALU_ADD 8 10 2876, 4%Z).
Proof. vm_refl. Qed.

Definition W_82254 : bv 32 := 0x00040583.
Lemma F_82254 : fetch_word AsanUbsan.M.loaded_segments (0x822a4 : word) = Some W_82254.
Proof. vm_refl. Qed.
Lemma D_82254 : decode_any W_82254 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82258 : bv 32 := 0x00100513.
Lemma F_82258 : fetch_word AsanUbsan.M.loaded_segments (0x822a8 : word) = Some W_82258.
Proof. vm_refl. Qed.
Lemma D_82258 : decode_any W_82258 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8225c : bv 32 := 0x0230000f.
Lemma F_8225c : fetch_word AsanUbsan.M.loaded_segments (0x822ac : word) = Some W_8225c.
Proof. vm_refl. Qed.
Lemma D_8225c : decode_any W_8225c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82260 : bv 32 := 0x00a59a63.
Lemma F_82260 : fetch_word AsanUbsan.M.loaded_segments (0x822b0 : word) = Some W_82260.
Proof. vm_refl. Qed.
Lemma D_82260 : decode_any W_82260 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82264 : bv 32 := 0x00813083.
Lemma F_82264 : fetch_word AsanUbsan.M.loaded_segments (0x822b4 : word) = Some W_82264.
Proof. vm_refl. Qed.
Lemma D_82264 : decode_any W_82264 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82268 : bv 32 := 0x00013403.
Lemma F_82268 : fetch_word AsanUbsan.M.loaded_segments (0x822b8 : word) = Some W_82268.
Proof. vm_refl. Qed.
Lemma D_82268 : decode_any W_82268 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8226c : bv 32 := 0x01010113.
Lemma F_8226c : fetch_word AsanUbsan.M.loaded_segments (0x822bc : word) = Some W_8226c.
Proof. vm_refl. Qed.
Lemma D_8226c : decode_any W_8226c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82270 : bv 32 := 0x00008067.
Lemma F_82270 : fetch_word AsanUbsan.M.loaded_segments (0x822c0 : word) = Some W_82270.
Proof. vm_refl. Qed.
Lemma D_82270 : decode_any W_82270 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
