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
Definition W_1165e0 : bv 32 := 0xfffff5b7.
Lemma F_1165e0 : fetch_word AsanUbsan.M.loaded_segments (0x118bd0 : word) = Some W_1165e0.
Proof. vm_refl. Qed.
Lemma D_1165e0 : decode_any W_1165e0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165e4 : bv 32 := 0x0015859b.
Lemma F_1165e4 : fetch_word AsanUbsan.M.loaded_segments (0x118bd4 : word) = Some W_1165e4.
Proof. vm_refl. Qed.
Lemma D_1165e4 : decode_any W_1165e4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165e8 : bv 32 := 0x02b56663.
Lemma F_1165e8 : fetch_word AsanUbsan.M.loaded_segments (0x118bd8 : word) = Some W_1165e8.
Proof. vm_refl. Qed.
Lemma D_1165e8 : decode_any W_1165e8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165ec : bv 32 := 0xff010113.
Lemma F_1165ec : fetch_word AsanUbsan.M.loaded_segments (0x118bdc : word) = Some W_1165ec.
Proof. vm_refl. Qed.
Lemma D_1165ec : decode_any W_1165ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165f0 : bv 32 := 0x00113423.
Lemma F_1165f0 : fetch_word AsanUbsan.M.loaded_segments (0x118be0 : word) = Some W_1165f0.
Proof. vm_refl. Qed.
Lemma D_1165f0 : decode_any W_1165f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165f4 : bv 32 := 0x00813023.
Lemma F_1165f4 : fetch_word AsanUbsan.M.loaded_segments (0x118be4 : word) = Some W_1165f4.
Proof. vm_refl. Qed.
Lemma D_1165f4 : decode_any W_1165f4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165f8 : bv 32 := 0x40a0043b.
Lemma F_1165f8 : fetch_word AsanUbsan.M.loaded_segments (0x118be8 : word) = Some W_1165f8.
Proof. vm_refl. Qed.
Lemma D_1165f8 : decode_any W_1165f8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1165fc : bv 32 := 0x8b9ff0ef.
Lemma F_1165fc : fetch_word AsanUbsan.M.loaded_segments (0x118bec : word) = Some W_1165fc.
Proof. vm_refl. Qed.
Lemma D_1165fc : decode_any W_1165fc = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116600 : bv 32 := 0x00852023.
Lemma F_116600 : fetch_word AsanUbsan.M.loaded_segments (0x118bf0 : word) = Some W_116600.
Proof. vm_refl. Qed.
Lemma D_116600 : decode_any W_116600 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116604 : bv 32 := 0xfff00513.
Lemma F_116604 : fetch_word AsanUbsan.M.loaded_segments (0x118bf4 : word) = Some W_116604.
Proof. vm_refl. Qed.
Lemma D_116604 : decode_any W_116604 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116608 : bv 32 := 0x00813083.
Lemma F_116608 : fetch_word AsanUbsan.M.loaded_segments (0x118bf8 : word) = Some W_116608.
Proof. vm_refl. Qed.
Lemma D_116608 : decode_any W_116608 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11660c : bv 32 := 0x00013403.
Lemma F_11660c : fetch_word AsanUbsan.M.loaded_segments (0x118bfc : word) = Some W_11660c.
Proof. vm_refl. Qed.
Lemma D_11660c : decode_any W_11660c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116610 : bv 32 := 0x01010113.
Lemma F_116610 : fetch_word AsanUbsan.M.loaded_segments (0x118c00 : word) = Some W_116610.
Proof. vm_refl. Qed.
Lemma D_116610 : decode_any W_116610 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_116614 : bv 32 := 0x00008067.
Lemma F_116614 : fetch_word AsanUbsan.M.loaded_segments (0x118c04 : word) = Some W_116614.
Proof. vm_refl. Qed.
Lemma D_116614 : decode_any W_116614 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
