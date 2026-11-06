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
Definition W_15ce80 : bv 32 := 0xff010113.
Lemma F_15ce80 : fetch_word AsanUbsan.M.loaded_segments (0x15cebc : word) = Some W_15ce80.
Proof. vm_refl. Qed.
Lemma D_15ce80 : decode_any W_15ce80 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce84 : bv 32 := 0x00113423.
Lemma F_15ce84 : fetch_word AsanUbsan.M.loaded_segments (0x15cec0 : word) = Some W_15ce84.
Proof. vm_refl. Qed.
Lemma D_15ce84 : decode_any W_15ce84 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce88 : bv 32 := 0x00060693.
Lemma F_15ce88 : fetch_word AsanUbsan.M.loaded_segments (0x15cec4 : word) = Some W_15ce88.
Proof. vm_refl. Qed.
Lemma D_15ce88 : decode_any W_15ce88 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce8c : bv 32 := 0x00058613.
Lemma F_15ce8c : fetch_word AsanUbsan.M.loaded_segments (0x15cec8 : word) = Some W_15ce8c.
Proof. vm_refl. Qed.
Lemma D_15ce8c : decode_any W_15ce8c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce90 : bv 32 := 0x00050593.
Lemma F_15ce90 : fetch_word AsanUbsan.M.loaded_segments (0x15cecc : word) = Some W_15ce90.
Proof. vm_refl. Qed.
Lemma D_15ce90 : decode_any W_15ce90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce94 : bv 32 := 0x03f00513.
Lemma F_15ce94 : fetch_word AsanUbsan.M.loaded_segments (0x15ced0 : word) = Some W_15ce94.
Proof. vm_refl. Qed.
Lemma D_15ce94 : decode_any W_15ce94 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce98 : bv 32 := 0x00000713.
Lemma F_15ce98 : fetch_word AsanUbsan.M.loaded_segments (0x15ced4 : word) = Some W_15ce98.
Proof. vm_refl. Qed.
Lemma D_15ce98 : decode_any W_15ce98 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce9c : bv 32 := 0x00000793.
Lemma F_15ce9c : fetch_word AsanUbsan.M.loaded_segments (0x15ced8 : word) = Some W_15ce9c.
Proof. vm_refl. Qed.
Lemma D_15ce9c : decode_any W_15ce9c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cea0 : bv 32 := 0x00000813.
Lemma F_15cea0 : fetch_word AsanUbsan.M.loaded_segments (0x15cedc : word) = Some W_15cea0.
Proof. vm_refl. Qed.
Lemma D_15cea0 : decode_any W_15cea0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cea4 : bv 32 := 0xdb8fa0ef.
Lemma F_15cea4 : fetch_word AsanUbsan.M.loaded_segments (0x15cee0 : word) = Some W_15cea4.
Proof. vm_refl. Qed.
Lemma D_15cea4 : decode_any W_15cea4 = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cea8 : bv 32 := 0x00813083.
Lemma F_15cea8 : fetch_word AsanUbsan.M.loaded_segments (0x15cee4 : word) = Some W_15cea8.
Proof. vm_refl. Qed.
Lemma D_15cea8 : decode_any W_15cea8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ceac : bv 32 := 0x01010113.
Lemma F_15ceac : fetch_word AsanUbsan.M.loaded_segments (0x15cee8 : word) = Some W_15ceac.
Proof. vm_refl. Qed.
Lemma D_15ceac : decode_any W_15ceac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ceb0 : bv 32 := 0xff8e806f.
Lemma F_15ceb0 : fetch_word AsanUbsan.M.loaded_segments (0x15ceec : word) = Some W_15ceb0.
Proof. vm_refl. Qed.
Lemma D_15ceb0 : decode_any W_15ceb0 = Some (Jal 0 2000888, 4%Z).
Proof. vm_refl. Qed.

