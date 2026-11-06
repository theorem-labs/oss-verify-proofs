(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_147aec : bv 32 := 0x00020593.
Lemma F_147aec : fetch_word Asan.M.loaded_segments (0x147b30 : word) = Some W_147aec.
Proof. vm_refl. Qed.
Lemma D_147aec : decode_any W_147aec = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147af0 : bv 32 := 0xfa85b583.
Lemma F_147af0 : fetch_word Asan.M.loaded_segments (0x147b34 : word) = Some W_147af0.
Proof. vm_refl. Qed.
Lemma D_147af0 : decode_any W_147af0 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_147af4 : bv 32 := 0x02051513.
Lemma F_147af4 : fetch_word Asan.M.loaded_segments (0x147b38 : word) = Some W_147af4.
Proof. vm_refl. Qed.
Lemma D_147af4 : decode_any W_147af4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_147af8 : bv 32 := 0x01d55513.
Lemma F_147af8 : fetch_word Asan.M.loaded_segments (0x147b3c : word) = Some W_147af8.
Proof. vm_refl. Qed.
Lemma D_147af8 : decode_any W_147af8 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_147afc : bv 32 := 0x00a58533.
Lemma F_147afc : fetch_word Asan.M.loaded_segments (0x147b40 : word) = Some W_147afc.
Proof. vm_refl. Qed.
Lemma D_147afc : decode_any W_147afc = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_147b00 : bv 32 := 0x00053503.
Lemma F_147b00 : fetch_word Asan.M.loaded_segments (0x147b44 : word) = Some W_147b00.
Proof. vm_refl. Qed.
Lemma D_147b00 : decode_any W_147b00 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147b04 : bv 32 := 0x00008067.
Lemma F_147b04 : fetch_word Asan.M.loaded_segments (0x147b48 : word) = Some W_147b04.
Proof. vm_refl. Qed.
Lemma D_147b04 : decode_any W_147b04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

