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
Definition W_159460 : bv 32 := 0xff010113.
Lemma F_159460 : fetch_word Asan.M.loaded_segments (0x1594a4 : word) = Some W_159460.
Proof. vm_refl. Qed.
Lemma D_159460 : decode_any W_159460 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159464 : bv 32 := 0x00113423.
Lemma F_159464 : fetch_word Asan.M.loaded_segments (0x1594a8 : word) = Some W_159464.
Proof. vm_refl. Qed.
Lemma D_159464 : decode_any W_159464 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159468 : bv 32 := 0x00060693.
Lemma F_159468 : fetch_word Asan.M.loaded_segments (0x1594ac : word) = Some W_159468.
Proof. vm_refl. Qed.
Lemma D_159468 : decode_any W_159468 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15946c : bv 32 := 0x00058613.
Lemma F_15946c : fetch_word Asan.M.loaded_segments (0x1594b0 : word) = Some W_15946c.
Proof. vm_refl. Qed.
Lemma D_15946c : decode_any W_15946c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159470 : bv 32 := 0x00050593.
Lemma F_159470 : fetch_word Asan.M.loaded_segments (0x1594b4 : word) = Some W_159470.
Proof. vm_refl. Qed.
Lemma D_159470 : decode_any W_159470 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159474 : bv 32 := 0x03f00513.
Lemma F_159474 : fetch_word Asan.M.loaded_segments (0x1594b8 : word) = Some W_159474.
Proof. vm_refl. Qed.
Lemma D_159474 : decode_any W_159474 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159478 : bv 32 := 0x00000713.
Lemma F_159478 : fetch_word Asan.M.loaded_segments (0x1594bc : word) = Some W_159478.
Proof. vm_refl. Qed.
Lemma D_159478 : decode_any W_159478 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15947c : bv 32 := 0x00000793.
Lemma F_15947c : fetch_word Asan.M.loaded_segments (0x1594c0 : word) = Some W_15947c.
Proof. vm_refl. Qed.
Lemma D_15947c : decode_any W_15947c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159480 : bv 32 := 0x00000813.
Lemma F_159480 : fetch_word Asan.M.loaded_segments (0x1594c4 : word) = Some W_159480.
Proof. vm_refl. Qed.
Lemma D_159480 : decode_any W_159480 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159484 : bv 32 := 0xdb8fa0ef.
Lemma F_159484 : fetch_word Asan.M.loaded_segments (0x1594c8 : word) = Some W_159484.
Proof. vm_refl. Qed.
Lemma D_159484 : decode_any W_159484 = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159488 : bv 32 := 0x00813083.
Lemma F_159488 : fetch_word Asan.M.loaded_segments (0x1594cc : word) = Some W_159488.
Proof. vm_refl. Qed.
Lemma D_159488 : decode_any W_159488 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15948c : bv 32 := 0x01010113.
Lemma F_15948c : fetch_word Asan.M.loaded_segments (0x1594d0 : word) = Some W_15948c.
Proof. vm_refl. Qed.
Lemma D_15948c : decode_any W_15948c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159490 : bv 32 := 0x899e806f.
Lemma F_159490 : fetch_word Asan.M.loaded_segments (0x1594d4 : word) = Some W_159490.
Proof. vm_refl. Qed.
Lemma D_159490 : decode_any W_159490 = Some (Jal 0 2001048, 4%Z).
Proof. vm_refl. Qed.

