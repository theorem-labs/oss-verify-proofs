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

Definition W_8d3cc : bv 32 := 0x00153517.
Lemma F_8d3cc : fetch_word AsanUbsan.M.loaded_segments (0x8d414 : word) = Some W_8d3cc.
Proof. vm_refl. Qed.
Lemma D_8d3cc : decode_any W_8d3cc = Some (Auipc 10 339, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3d0 : bv 32 := 0xb4d50503.
Lemma F_8d3d0 : fetch_word AsanUbsan.M.loaded_segments (0x8d418 : word) = Some W_8d3d0.
Proof. vm_refl. Qed.
Lemma D_8d3d0 : decode_any W_8d3d0 = Some (Load SZ1 true 10 10 2893, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3d4 : bv 32 := 0x00a03533.
Lemma F_8d3d4 : fetch_word AsanUbsan.M.loaded_segments (0x8d41c : word) = Some W_8d3d4.
Proof. vm_refl. Qed.
Lemma D_8d3d4 : decode_any W_8d3d4 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3d8 : bv 32 := 0x00008067.
Lemma F_8d3d8 : fetch_word AsanUbsan.M.loaded_segments (0x8d420 : word) = Some W_8d3d8.
Proof. vm_refl. Qed.
Lemma D_8d3d8 : decode_any W_8d3d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3f4 : bv 32 := 0x00153517.
Lemma F_8d3f4 : fetch_word AsanUbsan.M.loaded_segments (0x8d43c : word) = Some W_8d3f4.
Proof. vm_refl. Qed.
Lemma D_8d3f4 : decode_any W_8d3f4 = Some (Auipc 10 339, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3f8 : bv 32 := 0xb2650503.
Lemma F_8d3f8 : fetch_word AsanUbsan.M.loaded_segments (0x8d440 : word) = Some W_8d3f8.
Proof. vm_refl. Qed.
Lemma D_8d3f8 : decode_any W_8d3f8 = Some (Load SZ1 true 10 10 2854, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3fc : bv 32 := 0x00a03533.
Lemma F_8d3fc : fetch_word AsanUbsan.M.loaded_segments (0x8d444 : word) = Some W_8d3fc.
Proof. vm_refl. Qed.
Lemma D_8d3fc : decode_any W_8d3fc = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d400 : bv 32 := 0x00008067.
Lemma F_8d400 : fetch_word AsanUbsan.M.loaded_segments (0x8d448 : word) = Some W_8d400.
Proof. vm_refl. Qed.
Lemma D_8d400 : decode_any W_8d400 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

