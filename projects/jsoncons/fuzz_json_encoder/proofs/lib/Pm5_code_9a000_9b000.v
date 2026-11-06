(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9a010 : bv 32 := 0x000b0513.
Lemma F_9a010 : fetch_word AsanUbsan.M.loaded_segments (0x9a058 : word) = Some W_9a010.
Proof. vm_refl. Qed.
Lemma D_9a010 : decode_any W_9a010 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a014 : bv 32 := 0x004a1413.
Lemma F_9a014 : fetch_word AsanUbsan.M.loaded_segments (0x9a05c : word) = Some W_9a014.
Proof. vm_refl. Qed.
Lemma D_9a014 : decode_any W_9a014 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a018 : bv 32 := 0x00850433.
Lemma F_9a018 : fetch_word AsanUbsan.M.loaded_segments (0x9a060 : word) = Some W_9a018.
Proof. vm_refl. Qed.
Lemma D_9a018 : decode_any W_9a018 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a01c : bv 32 := 0x00843503.
Lemma F_9a01c : fetch_word AsanUbsan.M.loaded_segments (0x9a064 : word) = Some W_9a01c.
Proof. vm_refl. Qed.
Lemma D_9a01c : decode_any W_9a01c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a020 : bv 32 := 0x04050263.
Lemma F_9a020 : fetch_word AsanUbsan.M.loaded_segments (0x9a068 : word) = Some W_9a020.
Proof. vm_refl. Qed.
Lemma D_9a020 : decode_any W_9a020 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a024 : bv 32 := 0x00000513.
Lemma F_9a024 : fetch_word AsanUbsan.M.loaded_segments (0x9a06c : word) = Some W_9a024.
Proof. vm_refl. Qed.
Lemma D_9a024 : decode_any W_9a024 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a028 : bv 32 := 0x08813083.
Lemma F_9a028 : fetch_word AsanUbsan.M.loaded_segments (0x9a070 : word) = Some W_9a028.
Proof. vm_refl. Qed.
Lemma D_9a028 : decode_any W_9a028 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a02c : bv 32 := 0x08013403.
Lemma F_9a02c : fetch_word AsanUbsan.M.loaded_segments (0x9a074 : word) = Some W_9a02c.
Proof. vm_refl. Qed.
Lemma D_9a02c : decode_any W_9a02c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a030 : bv 32 := 0x07813483.
Lemma F_9a030 : fetch_word AsanUbsan.M.loaded_segments (0x9a078 : word) = Some W_9a030.
Proof. vm_refl. Qed.
Lemma D_9a030 : decode_any W_9a030 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a034 : bv 32 := 0x07013903.
Lemma F_9a034 : fetch_word AsanUbsan.M.loaded_segments (0x9a07c : word) = Some W_9a034.
Proof. vm_refl. Qed.
Lemma D_9a034 : decode_any W_9a034 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a038 : bv 32 := 0x06813983.
Lemma F_9a038 : fetch_word AsanUbsan.M.loaded_segments (0x9a080 : word) = Some W_9a038.
Proof. vm_refl. Qed.
Lemma D_9a038 : decode_any W_9a038 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a03c : bv 32 := 0x06013a03.
Lemma F_9a03c : fetch_word AsanUbsan.M.loaded_segments (0x9a084 : word) = Some W_9a03c.
Proof. vm_refl. Qed.
Lemma D_9a03c : decode_any W_9a03c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a040 : bv 32 := 0x05813a83.
Lemma F_9a040 : fetch_word AsanUbsan.M.loaded_segments (0x9a088 : word) = Some W_9a040.
Proof. vm_refl. Qed.
Lemma D_9a040 : decode_any W_9a040 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a044 : bv 32 := 0x05013b03.
Lemma F_9a044 : fetch_word AsanUbsan.M.loaded_segments (0x9a08c : word) = Some W_9a044.
Proof. vm_refl. Qed.
Lemma D_9a044 : decode_any W_9a044 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a048 : bv 32 := 0x04813b83.
Lemma F_9a048 : fetch_word AsanUbsan.M.loaded_segments (0x9a090 : word) = Some W_9a048.
Proof. vm_refl. Qed.
Lemma D_9a048 : decode_any W_9a048 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a04c : bv 32 := 0x04013c03.
Lemma F_9a04c : fetch_word AsanUbsan.M.loaded_segments (0x9a094 : word) = Some W_9a04c.
Proof. vm_refl. Qed.
Lemma D_9a04c : decode_any W_9a04c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a050 : bv 32 := 0x03813c83.
Lemma F_9a050 : fetch_word AsanUbsan.M.loaded_segments (0x9a098 : word) = Some W_9a050.
Proof. vm_refl. Qed.
Lemma D_9a050 : decode_any W_9a050 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a054 : bv 32 := 0x03013d03.
Lemma F_9a054 : fetch_word AsanUbsan.M.loaded_segments (0x9a09c : word) = Some W_9a054.
Proof. vm_refl. Qed.
Lemma D_9a054 : decode_any W_9a054 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a058 : bv 32 := 0x02813d83.
Lemma F_9a058 : fetch_word AsanUbsan.M.loaded_segments (0x9a0a0 : word) = Some W_9a058.
Proof. vm_refl. Qed.
Lemma D_9a058 : decode_any W_9a058 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a05c : bv 32 := 0x09010113.
Lemma F_9a05c : fetch_word AsanUbsan.M.loaded_segments (0x9a0a4 : word) = Some W_9a05c.
Proof. vm_refl. Qed.
Lemma D_9a05c : decode_any W_9a05c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a060 : bv 32 := 0x00008067.
Lemma F_9a060 : fetch_word AsanUbsan.M.loaded_segments (0x9a0a8 : word) = Some W_9a060.
Proof. vm_refl. Qed.
Lemma D_9a060 : decode_any W_9a060 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

