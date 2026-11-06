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
Definition W_5f4b8 : bv 32 := 0x0010b517.
Lemma F_5f4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f500 : word) = Some W_5f4b8.
Proof. vm_refl. Qed.
Lemma D_5f4b8 : decode_any W_5f4b8 = Some (Auipc 10 267, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4bc : bv 32 := 0xc7853503.
Lemma F_5f4bc : fetch_word AsanUbsan.M.loaded_segments (0x5f504 : word) = Some W_5f4bc.
Proof. vm_refl. Qed.
Lemma D_5f4bc : decode_any W_5f4bc = Some (Load SZ8 true 10 10 3192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c0 : bv 32 := 0x06a76463.
Lemma F_5f4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f508 : word) = Some W_5f4c0.
Proof. vm_refl. Qed.
Lemma D_5f4c0 : decode_any W_5f4c0 = Some (Branch BC_LTU 14 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c4 : bv 32 := 0x00100593.
Lemma F_5f4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f50c : word) = Some W_5f4c4.
Proof. vm_refl. Qed.
Lemma D_5f4c4 : decode_any W_5f4c4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c8 : bv 32 := 0x02559593.
Lemma F_5f4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f510 : word) = Some W_5f4c8.
Proof. vm_refl. Qed.
Lemma D_5f4c8 : decode_any W_5f4c8 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4cc : bv 32 := 0x00b50533.
Lemma F_5f4cc : fetch_word AsanUbsan.M.loaded_segments (0x5f514 : word) = Some W_5f4cc.
Proof. vm_refl. Qed.
Lemma D_5f4cc : decode_any W_5f4cc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4d0 : bv 32 := 0x04a77c63.
Lemma F_5f4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f518 : word) = Some W_5f4d0.
Proof. vm_refl. Qed.
Lemma D_5f4d0 : decode_any W_5f4d0 = Some (Branch BC_GEU 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f528 : bv 32 := 0x00010513.
Lemma F_5f528 : fetch_word AsanUbsan.M.loaded_segments (0x5f570 : word) = Some W_5f528.
Proof. vm_refl. Qed.
Lemma D_5f528 : decode_any W_5f528 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f52c : bv 32 := 0x00070593.
Lemma F_5f52c : fetch_word AsanUbsan.M.loaded_segments (0x5f574 : word) = Some W_5f52c.
Proof. vm_refl. Qed.
Lemma D_5f52c : decode_any W_5f52c = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f530 : bv 32 := 0xe91fd0ef.
Lemma F_5f530 : fetch_word AsanUbsan.M.loaded_segments (0x5f578 : word) = Some W_5f530.
Proof. vm_refl. Qed.
Lemma D_5f530 : decode_any W_5f530 = Some (Jal 1 2088592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f534 : bv 32 := 0x0184b503.
Lemma F_5f534 : fetch_word AsanUbsan.M.loaded_segments (0x5f57c : word) = Some W_5f534.
Proof. vm_refl. Qed.
Lemma D_5f534 : decode_any W_5f534 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f538 : bv 32 := 0x00ab7c63.
Lemma F_5f538 : fetch_word AsanUbsan.M.loaded_segments (0x5f580 : word) = Some W_5f538.
Proof. vm_refl. Qed.
Lemma D_5f538 : decode_any W_5f538 = Some (Branch BC_GEU 22 10 24, 4%Z).
Proof. vm_refl. Qed.

