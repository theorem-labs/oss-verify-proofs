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

Definition W_9ae38 : bv 32 := 0xfe010113.
Lemma F_9ae38 : fetch_word AsanUbsan.M.loaded_segments (0x9ae88 : word) = Some W_9ae38.
Proof. vm_refl. Qed.
Lemma D_9ae38 : decode_any W_9ae38 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae3c : bv 32 := 0x00113c23.
Lemma F_9ae3c : fetch_word AsanUbsan.M.loaded_segments (0x9ae8c : word) = Some W_9ae3c.
Proof. vm_refl. Qed.
Lemma D_9ae3c : decode_any W_9ae3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae40 : bv 32 := 0x00813823.
Lemma F_9ae40 : fetch_word AsanUbsan.M.loaded_segments (0x9ae90 : word) = Some W_9ae40.
Proof. vm_refl. Qed.
Lemma D_9ae40 : decode_any W_9ae40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae44 : bv 32 := 0x00060593.
Lemma F_9ae44 : fetch_word AsanUbsan.M.loaded_segments (0x9ae94 : word) = Some W_9ae44.
Proof. vm_refl. Qed.
Lemma D_9ae44 : decode_any W_9ae44 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae48 : bv 32 := 0x00050413.
Lemma F_9ae48 : fetch_word AsanUbsan.M.loaded_segments (0x9ae98 : word) = Some W_9ae48.
Proof. vm_refl. Qed.
Lemma D_9ae48 : decode_any W_9ae48 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae4c : bv 32 := 0x00d53023.
Lemma F_9ae4c : fetch_word AsanUbsan.M.loaded_segments (0x9ae9c : word) = Some W_9ae4c.
Proof. vm_refl. Qed.
Lemma D_9ae4c : decode_any W_9ae4c = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae50 : bv 32 := 0x00013423.
Lemma F_9ae50 : fetch_word AsanUbsan.M.loaded_segments (0x9aea0 : word) = Some W_9ae50.
Proof. vm_refl. Qed.
Lemma D_9ae50 : decode_any W_9ae50 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae54 : bv 32 := 0x0017d517.
Lemma F_9ae54 : fetch_word AsanUbsan.M.loaded_segments (0x9aea4 : word) = Some W_9ae54.
Proof. vm_refl. Qed.
Lemma D_9ae54 : decode_any W_9ae54 = Some (Auipc 10 381, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae58 : bv 32 := 0x12450513.
Lemma F_9ae58 : fetch_word AsanUbsan.M.loaded_segments (0x9aea8 : word) = Some W_9ae58.
Proof. vm_refl. Qed.
Lemma D_9ae58 : decode_any W_9ae58 = Some (OpImm ALU_ADD 10 10 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae5c : bv 32 := 0x00810613.
Lemma F_9ae5c : fetch_word AsanUbsan.M.loaded_segments (0x9aeac : word) = Some W_9ae5c.
Proof. vm_refl. Qed.
Lemma D_9ae5c : decode_any W_9ae5c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae60 : bv 32 := 0xcc5fd0ef.
Lemma F_9ae60 : fetch_word AsanUbsan.M.loaded_segments (0x9aeb0 : word) = Some W_9ae60.
Proof. vm_refl. Qed.
Lemma D_9ae60 : decode_any W_9ae60 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae64 : bv 32 := 0x00813583.
Lemma F_9ae64 : fetch_word AsanUbsan.M.loaded_segments (0x9aeb4 : word) = Some W_9ae64.
Proof. vm_refl. Qed.
Lemma D_9ae64 : decode_any W_9ae64 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae68 : bv 32 := 0x00a42623.
Lemma F_9ae68 : fetch_word AsanUbsan.M.loaded_segments (0x9aeb8 : word) = Some W_9ae68.
Proof. vm_refl. Qed.
Lemma D_9ae68 : decode_any W_9ae68 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae6c : bv 32 := 0x00059a63.
Lemma F_9ae6c : fetch_word AsanUbsan.M.loaded_segments (0x9aebc : word) = Some W_9ae6c.
Proof. vm_refl. Qed.
Lemma D_9ae6c : decode_any W_9ae6c = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae70 : bv 32 := 0x01813083.
Lemma F_9ae70 : fetch_word AsanUbsan.M.loaded_segments (0x9aec0 : word) = Some W_9ae70.
Proof. vm_refl. Qed.
Lemma D_9ae70 : decode_any W_9ae70 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae74 : bv 32 := 0x01013403.
Lemma F_9ae74 : fetch_word AsanUbsan.M.loaded_segments (0x9aec4 : word) = Some W_9ae74.
Proof. vm_refl. Qed.
Lemma D_9ae74 : decode_any W_9ae74 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae78 : bv 32 := 0x02010113.
Lemma F_9ae78 : fetch_word AsanUbsan.M.loaded_segments (0x9aec8 : word) = Some W_9ae78.
Proof. vm_refl. Qed.
Lemma D_9ae78 : decode_any W_9ae78 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ae7c : bv 32 := 0x00008067.
Lemma F_9ae7c : fetch_word AsanUbsan.M.loaded_segments (0x9aecc : word) = Some W_9ae7c.
Proof. vm_refl. Qed.
Lemma D_9ae7c : decode_any W_9ae7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
