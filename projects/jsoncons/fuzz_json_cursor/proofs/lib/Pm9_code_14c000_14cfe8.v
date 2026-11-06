(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14ce88 : bv 32 := 0xff010113.
Lemma F_14ce88 : fetch_word AsanUbsan.M.loaded_segments (0x14cec4 : word) = Some W_14ce88.
Proof. vm_refl. Qed.
Lemma D_14ce88 : decode_any W_14ce88 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce8c : bv 32 := 0x00113423.
Lemma F_14ce8c : fetch_word AsanUbsan.M.loaded_segments (0x14cec8 : word) = Some W_14ce8c.
Proof. vm_refl. Qed.
Lemma D_14ce8c : decode_any W_14ce8c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce90 : bv 32 := 0x00060693.
Lemma F_14ce90 : fetch_word AsanUbsan.M.loaded_segments (0x14cecc : word) = Some W_14ce90.
Proof. vm_refl. Qed.
Lemma D_14ce90 : decode_any W_14ce90 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce94 : bv 32 := 0x00058613.
Lemma F_14ce94 : fetch_word AsanUbsan.M.loaded_segments (0x14ced0 : word) = Some W_14ce94.
Proof. vm_refl. Qed.
Lemma D_14ce94 : decode_any W_14ce94 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce98 : bv 32 := 0x00050593.
Lemma F_14ce98 : fetch_word AsanUbsan.M.loaded_segments (0x14ced4 : word) = Some W_14ce98.
Proof. vm_refl. Qed.
Lemma D_14ce98 : decode_any W_14ce98 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce9c : bv 32 := 0x03f00513.
Lemma F_14ce9c : fetch_word AsanUbsan.M.loaded_segments (0x14ced8 : word) = Some W_14ce9c.
Proof. vm_refl. Qed.
Lemma D_14ce9c : decode_any W_14ce9c = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cea0 : bv 32 := 0x00000713.
Lemma F_14cea0 : fetch_word AsanUbsan.M.loaded_segments (0x14cedc : word) = Some W_14cea0.
Proof. vm_refl. Qed.
Lemma D_14cea0 : decode_any W_14cea0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cea4 : bv 32 := 0x00000793.
Lemma F_14cea4 : fetch_word AsanUbsan.M.loaded_segments (0x14cee0 : word) = Some W_14cea4.
Proof. vm_refl. Qed.
Lemma D_14cea4 : decode_any W_14cea4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cea8 : bv 32 := 0x00000813.
Lemma F_14cea8 : fetch_word AsanUbsan.M.loaded_segments (0x14cee4 : word) = Some W_14cea8.
Proof. vm_refl. Qed.
Lemma D_14cea8 : decode_any W_14cea8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ceac : bv 32 := 0xdb8fa0ef.
Lemma F_14ceac : fetch_word AsanUbsan.M.loaded_segments (0x14cee8 : word) = Some W_14ceac.
Proof. vm_refl. Qed.
Lemma D_14ceac : decode_any W_14ceac = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ceb0 : bv 32 := 0x00813083.
Lemma F_14ceb0 : fetch_word AsanUbsan.M.loaded_segments (0x14ceec : word) = Some W_14ceb0.
Proof. vm_refl. Qed.
Lemma D_14ceb0 : decode_any W_14ceb0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ceb4 : bv 32 := 0x01010113.
Lemma F_14ceb4 : fetch_word AsanUbsan.M.loaded_segments (0x14cef0 : word) = Some W_14ceb4.
Proof. vm_refl. Qed.
Lemma D_14ceb4 : decode_any W_14ceb4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ceb8 : bv 32 := 0xff8e806f.
Lemma F_14ceb8 : fetch_word AsanUbsan.M.loaded_segments (0x14cef4 : word) = Some W_14ceb8.
Proof. vm_refl. Qed.
Lemma D_14ceb8 : decode_any W_14ceb8 = Some (Jal 0 2000888, 4%Z).
Proof. vm_refl. Qed.

