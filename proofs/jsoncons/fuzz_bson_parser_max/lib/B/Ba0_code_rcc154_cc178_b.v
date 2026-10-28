(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1282f4 : bv 32 := 0x00020593.
Lemma F_1282f4 : fetch_word AsanUbsan.M.loaded_segments (0x12a8e4 : word) = Some W_1282f4.
Proof. vm_refl. Qed.
Lemma D_1282f4 : decode_any W_1282f4 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282f8 : bv 32 := 0x00053603.
Lemma F_1282f8 : fetch_word AsanUbsan.M.loaded_segments (0x12a8e8 : word) = Some W_1282f8.
Proof. vm_refl. Qed.
Lemma D_1282f8 : decode_any W_1282f8 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282fc : bv 32 := 0xff85b583.
Lemma F_1282fc : fetch_word AsanUbsan.M.loaded_segments (0x12a8ec : word) = Some W_1282fc.
Proof. vm_refl. Qed.
Lemma D_1282fc : decode_any W_1282fc = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_128300 : bv 32 := 0x00853503.
Lemma F_128300 : fetch_word AsanUbsan.M.loaded_segments (0x12a8f0 : word) = Some W_128300.
Proof. vm_refl. Qed.
Lemma D_128300 : decode_any W_128300 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_128304 : bv 32 := 0x00361613.
Lemma F_128304 : fetch_word AsanUbsan.M.loaded_segments (0x12a8f4 : word) = Some W_128304.
Proof. vm_refl. Qed.
Lemma D_128304 : decode_any W_128304 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_128308 : bv 32 := 0x00c585b3.
Lemma F_128308 : fetch_word AsanUbsan.M.loaded_segments (0x12a8f8 : word) = Some W_128308.
Proof. vm_refl. Qed.
Lemma D_128308 : decode_any W_128308 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12830c : bv 32 := 0x0005b583.
Lemma F_12830c : fetch_word AsanUbsan.M.loaded_segments (0x12a8fc : word) = Some W_12830c.
Proof. vm_refl. Qed.
Lemma D_12830c : decode_any W_12830c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_128310 : bv 32 := 0x00b50533.
Lemma F_128310 : fetch_word AsanUbsan.M.loaded_segments (0x12a900 : word) = Some W_128310.
Proof. vm_refl. Qed.
Lemma D_128310 : decode_any W_128310 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_128314 : bv 32 := 0x00008067.
Lemma F_128314 : fetch_word AsanUbsan.M.loaded_segments (0x12a904 : word) = Some W_128314.
Proof. vm_refl. Qed.
Lemma D_128314 : decode_any W_128314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
