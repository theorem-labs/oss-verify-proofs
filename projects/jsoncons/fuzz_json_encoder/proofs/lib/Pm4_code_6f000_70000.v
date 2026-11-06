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
Definition W_6fa0c : bv 32 := 0x104240ef.
Lemma F_6fa0c : fetch_word Asan.M.loaded_segments (0x6fa5c : word) = Some W_6fa0c.
Proof. vm_refl. Qed.
Lemma D_6fa0c : decode_any W_6fa0c = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa10 : bv 32 := 0x00150b93.
Lemma F_6fa10 : fetch_word Asan.M.loaded_segments (0x6fa60 : word) = Some W_6fa10.
Proof. vm_refl. Qed.
Lemma D_6fa10 : decode_any W_6fa10 = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa14 : bv 32 := 0xfffb4513.
Lemma F_6fa14 : fetch_word Asan.M.loaded_segments (0x6fa64 : word) = Some W_6fa14.
Proof. vm_refl. Qed.
Lemma D_6fa14 : decode_any W_6fa14 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa18 : bv 32 := 0x25756e63.
Lemma F_6fa18 : fetch_word Asan.M.loaded_segments (0x6fa68 : word) = Some W_6fa18.
Proof. vm_refl. Qed.
Lemma D_6fa18 : decode_any W_6fa18 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa1c : bv 32 := 0xfbfb8513.
Lemma F_6fa1c : fetch_word Asan.M.loaded_segments (0x6fa6c : word) = Some W_6fa1c.
Proof. vm_refl. Qed.
Lemma D_6fa1c : decode_any W_6fa1c = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa20 : bv 32 := 0xfbf00593.
Lemma F_6fa20 : fetch_word Asan.M.loaded_segments (0x6fa70 : word) = Some W_6fa20.
Proof. vm_refl. Qed.
Lemma D_6fa20 : decode_any W_6fa20 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa24 : bv 32 := 0x2ca5f063.
Lemma F_6fa24 : fetch_word Asan.M.loaded_segments (0x6fa74 : word) = Some W_6fa24.
Proof. vm_refl. Qed.
Lemma D_6fa24 : decode_any W_6fa24 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa28 : bv 32 := 0x000f1517.
Lemma F_6fa28 : fetch_word Asan.M.loaded_segments (0x6fa78 : word) = Some W_6fa28.
Proof. vm_refl. Qed.
Lemma D_6fa28 : decode_any W_6fa28 = Some (Auipc 10 241, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa2c : bv 32 := 0x1a053503.
Lemma F_6fa2c : fetch_word Asan.M.loaded_segments (0x6fa7c : word) = Some W_6fa2c.
Proof. vm_refl. Qed.
Lemma D_6fa2c : decode_any W_6fa2c = Some (Load SZ8 true 10 10 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa30 : bv 32 := 0x017b0633.
Lemma F_6fa30 : fetch_word Asan.M.loaded_segments (0x6fa80 : word) = Some W_6fa30.
Proof. vm_refl. Qed.
Lemma D_6fa30 : decode_any W_6fa30 = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa34 : bv 32 := 0x00053583.
Lemma F_6fa34 : fetch_word Asan.M.loaded_segments (0x6fa84 : word) = Some W_6fa34.
Proof. vm_refl. Qed.
Lemma D_6fa34 : decode_any W_6fa34 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa38 : bv 32 := 0x003b5513.
Lemma F_6fa38 : fetch_word Asan.M.loaded_segments (0x6fa88 : word) = Some W_6fa38.
Proof. vm_refl. Qed.
Lemma D_6fa38 : decode_any W_6fa38 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa3c : bv 32 := 0xfff60613.
Lemma F_6fa3c : fetch_word Asan.M.loaded_segments (0x6fa8c : word) = Some W_6fa3c.
Proof. vm_refl. Qed.
Lemma D_6fa3c : decode_any W_6fa3c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa40 : bv 32 := 0x00365693.
Lemma F_6fa40 : fetch_word Asan.M.loaded_segments (0x6fa90 : word) = Some W_6fa40.
Proof. vm_refl. Qed.
Lemma D_6fa40 : decode_any W_6fa40 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa44 : bv 32 := 0x00a58533.
Lemma F_6fa44 : fetch_word Asan.M.loaded_segments (0x6fa94 : word) = Some W_6fa44.
Proof. vm_refl. Qed.
Lemma D_6fa44 : decode_any W_6fa44 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa48 : bv 32 := 0x00d585b3.
Lemma F_6fa48 : fetch_word Asan.M.loaded_segments (0x6fa98 : word) = Some W_6fa48.
Proof. vm_refl. Qed.
Lemma D_6fa48 : decode_any W_6fa48 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa4c : bv 32 := 0xff857693.
Lemma F_6fa4c : fetch_word Asan.M.loaded_segments (0x6fa9c : word) = Some W_6fa4c.
Proof. vm_refl. Qed.
Lemma D_6fa4c : decode_any W_6fa4c = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa50 : bv 32 := 0xff85f713.
Lemma F_6fa50 : fetch_word Asan.M.loaded_segments (0x6faa0 : word) = Some W_6fa50.
Proof. vm_refl. Qed.
Lemma D_6fa50 : decode_any W_6fa50 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa54 : bv 32 := 0x0006b683.
Lemma F_6fa54 : fetch_word Asan.M.loaded_segments (0x6faa4 : word) = Some W_6fa54.
Proof. vm_refl. Qed.
Lemma D_6fa54 : decode_any W_6fa54 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa58 : bv 32 := 0x00073703.
Lemma F_6fa58 : fetch_word Asan.M.loaded_segments (0x6faa8 : word) = Some W_6fa58.
Proof. vm_refl. Qed.
Lemma D_6fa58 : decode_any W_6fa58 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa5c : bv 32 := 0x00d766b3.
Lemma F_6fa5c : fetch_word Asan.M.loaded_segments (0x6faac : word) = Some W_6fa5c.
Proof. vm_refl. Qed.
Lemma D_6fa5c : decode_any W_6fa5c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa60 : bv 32 := 0xf00688e3.
Lemma F_6fa60 : fetch_word Asan.M.loaded_segments (0x6fab0 : word) = Some W_6fa60.
Proof. vm_refl. Qed.
Lemma D_6fa60 : decode_any W_6fa60 = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa98 : bv 32 := 0x000b0513.
Lemma F_6fa98 : fetch_word Asan.M.loaded_segments (0x6fae8 : word) = Some W_6fa98.
Proof. vm_refl. Qed.
Lemma D_6fa98 : decode_any W_6fa98 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fa9c : bv 32 := 0x000b8593.
Lemma F_6fa9c : fetch_word Asan.M.loaded_segments (0x6faec : word) = Some W_6fa9c.
Proof. vm_refl. Qed.
Lemma D_6fa9c : decode_any W_6fa9c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faa0 : bv 32 := 0x77d130ef.
Lemma F_6faa0 : fetch_word Asan.M.loaded_segments (0x6faf0 : word) = Some W_6faa0.
Proof. vm_refl. Qed.
Lemma D_6faa0 : decode_any W_6faa0 = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faa4 : bv 32 := 0xec0506e3.
Lemma F_6faa4 : fetch_word Asan.M.loaded_segments (0x6faf4 : word) = Some W_6faa4.
Proof. vm_refl. Qed.
Lemma D_6faa4 : decode_any W_6faa4 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fce4 : bv 32 := 0xda0b9ae3.
Lemma F_6fce4 : fetch_word Asan.M.loaded_segments (0x6fd34 : word) = Some W_6fce4.
Proof. vm_refl. Qed.
Lemma D_6fce4 : decode_any W_6fce4 = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

