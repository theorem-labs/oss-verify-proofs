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
Definition W_9a340 : bv 32 := 0xfd010113.
Lemma F_9a340 : fetch_word AsanUbsan.M.loaded_segments (0x9a758 : word) = Some W_9a340.
Proof. vm_refl. Qed.
Lemma D_9a340 : decode_any W_9a340 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a344 : bv 32 := 0x02113423.
Lemma F_9a344 : fetch_word AsanUbsan.M.loaded_segments (0x9a75c : word) = Some W_9a344.
Proof. vm_refl. Qed.
Lemma D_9a344 : decode_any W_9a344 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a348 : bv 32 := 0x02813023.
Lemma F_9a348 : fetch_word AsanUbsan.M.loaded_segments (0x9a760 : word) = Some W_9a348.
Proof. vm_refl. Qed.
Lemma D_9a348 : decode_any W_9a348 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a34c : bv 32 := 0x00913c23.
Lemma F_9a34c : fetch_word AsanUbsan.M.loaded_segments (0x9a764 : word) = Some W_9a34c.
Proof. vm_refl. Qed.
Lemma D_9a34c : decode_any W_9a34c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a350 : bv 32 := 0x01213823.
Lemma F_9a350 : fetch_word AsanUbsan.M.loaded_segments (0x9a768 : word) = Some W_9a350.
Proof. vm_refl. Qed.
Lemma D_9a350 : decode_any W_9a350 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a354 : bv 32 := 0x01313423.
Lemma F_9a354 : fetch_word AsanUbsan.M.loaded_segments (0x9a76c : word) = Some W_9a354.
Proof. vm_refl. Qed.
Lemma D_9a354 : decode_any W_9a354 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a358 : bv 32 := 0x00050413.
Lemma F_9a358 : fetch_word AsanUbsan.M.loaded_segments (0x9a770 : word) = Some W_9a358.
Proof. vm_refl. Qed.
Lemma D_9a358 : decode_any W_9a358 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a35c : bv 32 := 0x00000593.
Lemma F_9a35c : fetch_word AsanUbsan.M.loaded_segments (0x9a774 : word) = Some W_9a35c.
Proof. vm_refl. Qed.
Lemma D_9a35c : decode_any W_9a35c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a360 : bv 32 := 0x800004b7.
Lemma F_9a360 : fetch_word AsanUbsan.M.loaded_segments (0x9a778 : word) = Some W_9a360.
Proof. vm_refl. Qed.
Lemma D_9a360 : decode_any W_9a360 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a364 : bv 32 := 0x00900913.
Lemma F_9a364 : fetch_word AsanUbsan.M.loaded_segments (0x9a77c : word) = Some W_9a364.
Proof. vm_refl. Qed.
Lemma D_9a364 : decode_any W_9a364 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a368 : bv 32 := 0x00052503.
Lemma F_9a368 : fetch_word AsanUbsan.M.loaded_segments (0x9a780 : word) = Some W_9a368.
Proof. vm_refl. Qed.
Lemma D_9a368 : decode_any W_9a368 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a36c : bv 32 := 0x00055a63.
Lemma F_9a36c : fetch_word AsanUbsan.M.loaded_segments (0x9a784 : word) = Some W_9a36c.
Proof. vm_refl. Qed.
Lemma D_9a36c : decode_any W_9a36c = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a380 : bv 32 := 0x00956633.
Lemma F_9a380 : fetch_word AsanUbsan.M.loaded_segments (0x9a798 : word) = Some W_9a380.
Proof. vm_refl. Qed.
Lemma D_9a380 : decode_any W_9a380 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a384 : bv 32 := 0x160426af.
Lemma F_9a384 : fetch_word AsanUbsan.M.loaded_segments (0x9a79c : word) = Some W_9a384.
Proof. vm_refl. Qed.
Lemma D_9a384 : decode_any W_9a384 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a388 : bv 32 := 0x00a69663.
Lemma F_9a388 : fetch_word AsanUbsan.M.loaded_segments (0x9a7a0 : word) = Some W_9a388.
Proof. vm_refl. Qed.
Lemma D_9a388 : decode_any W_9a388 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a38c : bv 32 := 0x1ac4272f.
Lemma F_9a38c : fetch_word AsanUbsan.M.loaded_segments (0x9a7a4 : word) = Some W_9a38c.
Proof. vm_refl. Qed.
Lemma D_9a38c : decode_any W_9a38c = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a390 : bv 32 := 0xfe071ae3.
Lemma F_9a390 : fetch_word AsanUbsan.M.loaded_segments (0x9a7a8 : word) = Some W_9a390.
Proof. vm_refl. Qed.
Lemma D_9a390 : decode_any W_9a390 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a394 : bv 32 := 0x02a68063.
Lemma F_9a394 : fetch_word AsanUbsan.M.loaded_segments (0x9a7ac : word) = Some W_9a394.
Proof. vm_refl. Qed.
Lemma D_9a394 : decode_any W_9a394 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3b4 : bv 32 := 0x02813083.
Lemma F_9a3b4 : fetch_word AsanUbsan.M.loaded_segments (0x9a7cc : word) = Some W_9a3b4.
Proof. vm_refl. Qed.
Lemma D_9a3b4 : decode_any W_9a3b4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3b8 : bv 32 := 0x02013403.
Lemma F_9a3b8 : fetch_word AsanUbsan.M.loaded_segments (0x9a7d0 : word) = Some W_9a3b8.
Proof. vm_refl. Qed.
Lemma D_9a3b8 : decode_any W_9a3b8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3bc : bv 32 := 0x01813483.
Lemma F_9a3bc : fetch_word AsanUbsan.M.loaded_segments (0x9a7d4 : word) = Some W_9a3bc.
Proof. vm_refl. Qed.
Lemma D_9a3bc : decode_any W_9a3bc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3c0 : bv 32 := 0x01013903.
Lemma F_9a3c0 : fetch_word AsanUbsan.M.loaded_segments (0x9a7d8 : word) = Some W_9a3c0.
Proof. vm_refl. Qed.
Lemma D_9a3c0 : decode_any W_9a3c0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3c4 : bv 32 := 0x00813983.
Lemma F_9a3c4 : fetch_word AsanUbsan.M.loaded_segments (0x9a7dc : word) = Some W_9a3c4.
Proof. vm_refl. Qed.
Lemma D_9a3c4 : decode_any W_9a3c4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3c8 : bv 32 := 0x03010113.
Lemma F_9a3c8 : fetch_word AsanUbsan.M.loaded_segments (0x9a7e0 : word) = Some W_9a3c8.
Proof. vm_refl. Qed.
Lemma D_9a3c8 : decode_any W_9a3c8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a3cc : bv 32 := 0x00008067.
Lemma F_9a3cc : fetch_word AsanUbsan.M.loaded_segments (0x9a7e4 : word) = Some W_9a3cc.
Proof. vm_refl. Qed.
Lemma D_9a3cc : decode_any W_9a3cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
