(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ebe0 : bv 32 := 0x00108517.
Lemma F_5ebe0 : fetch_word Asan.M.loaded_segments (0x5ec30 : word) = Some W_5ebe0.
Proof. vm_refl. Qed.
Lemma D_5ebe0 : decode_any W_5ebe0 = Some (Auipc 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebe4 : bv 32 := 0xc8853503.
Lemma F_5ebe4 : fetch_word Asan.M.loaded_segments (0x5ec34 : word) = Some W_5ebe4.
Proof. vm_refl. Qed.
Lemma D_5ebe4 : decode_any W_5ebe4 = Some (Load SZ8 true 10 10 3208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebe8 : bv 32 := 0x06a76463.
Lemma F_5ebe8 : fetch_word Asan.M.loaded_segments (0x5ec38 : word) = Some W_5ebe8.
Proof. vm_refl. Qed.
Lemma D_5ebe8 : decode_any W_5ebe8 = Some (Branch BC_LTU 14 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebec : bv 32 := 0x00100593.
Lemma F_5ebec : fetch_word Asan.M.loaded_segments (0x5ec3c : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf0 : bv 32 := 0x02559593.
Lemma F_5ebf0 : fetch_word Asan.M.loaded_segments (0x5ec40 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf4 : bv 32 := 0x00b50533.
Lemma F_5ebf4 : fetch_word Asan.M.loaded_segments (0x5ec44 : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf8 : bv 32 := 0x04a77c63.
Lemma F_5ebf8 : fetch_word Asan.M.loaded_segments (0x5ec48 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (Branch BC_GEU 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec50 : bv 32 := 0x00010513.
Lemma F_5ec50 : fetch_word Asan.M.loaded_segments (0x5eca0 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec54 : bv 32 := 0x00070593.
Lemma F_5ec54 : fetch_word Asan.M.loaded_segments (0x5eca4 : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec58 : bv 32 := 0xe91fd0ef.
Lemma F_5ec58 : fetch_word Asan.M.loaded_segments (0x5eca8 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Jal 1 2088592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec5c : bv 32 := 0x0184b503.
Lemma F_5ec5c : fetch_word Asan.M.loaded_segments (0x5ecac : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec60 : bv 32 := 0x00ab7c63.
Lemma F_5ec60 : fetch_word Asan.M.loaded_segments (0x5ecb0 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (Branch BC_GEU 22 10 24, 4%Z).
Proof. vm_refl. Qed.

