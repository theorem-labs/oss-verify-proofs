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
Definition W_1157d0 : bv 32 := 0x0004b503.
Lemma F_1157d0 : fetch_word AsanUbsan.M.loaded_segments (0x117dcc : word) = Some W_1157d0.
Proof. vm_refl. Qed.
Lemma D_1157d0 : decode_any W_1157d0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1157d4 : bv 32 := 0x00848493.
Lemma F_1157d4 : fetch_word AsanUbsan.M.loaded_segments (0x117dd0 : word) = Some W_1157d4.
Proof. vm_refl. Qed.
Lemma D_1157d4 : decode_any W_1157d4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1157d8 : bv 32 := 0xfe051ce3.
Lemma F_1157d8 : fetch_word AsanUbsan.M.loaded_segments (0x117dd4 : word) = Some W_1157d8.
Proof. vm_refl. Qed.
Lemma D_1157d8 : decode_any W_1157d8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11588c : bv 32 := 0x00b53023.
Lemma F_11588c : fetch_word AsanUbsan.M.loaded_segments (0x117e88 : word) = Some W_11588c.
Proof. vm_refl. Qed.
Lemma D_11588c : decode_any W_11588c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115890 : bv 32 := 0x00158593.
Lemma F_115890 : fetch_word AsanUbsan.M.loaded_segments (0x117e8c : word) = Some W_115890.
Proof. vm_refl. Qed.
Lemma D_115890 : decode_any W_115890 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115894 : bv 32 := 0xfff5c683.
Lemma F_115894 : fetch_word AsanUbsan.M.loaded_segments (0x117e90 : word) = Some W_115894.
Proof. vm_refl. Qed.
Lemma D_115894 : decode_any W_115894 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115898 : bv 32 := 0xfec68ae3.
Lemma F_115898 : fetch_word AsanUbsan.M.loaded_segments (0x117e94 : word) = Some W_115898.
Proof. vm_refl. Qed.
Lemma D_115898 : decode_any W_115898 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11589c : bv 32 := 0xfe069ae3.
Lemma F_11589c : fetch_word AsanUbsan.M.loaded_segments (0x117e98 : word) = Some W_11589c.
Proof. vm_refl. Qed.
Lemma D_11589c : decode_any W_11589c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
