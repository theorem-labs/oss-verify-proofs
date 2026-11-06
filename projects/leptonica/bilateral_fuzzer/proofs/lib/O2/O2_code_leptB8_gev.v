(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_19390 : bv 32 := 0x00050663.
Lemma F_19390 : fetch_word Plain.M.loaded_segments (0x193e8 : word) = Some W_19390.
Proof. vm_refl. Qed.
Lemma D_19390 : decode_any W_19390 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19394 : bv 32 := 0x01052503.
Lemma F_19394 : fetch_word Plain.M.loaded_segments (0x193ec : word) = Some W_19394.
Proof. vm_refl. Qed.
Lemma D_19394 : decode_any W_19394 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19398 : bv 32 := 0x00008067.
Lemma F_19398 : fetch_word Plain.M.loaded_segments (0x193f0 : word) = Some W_19398.
Proof. vm_refl. Qed.
Lemma D_19398 : decode_any W_19398 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1968c : bv 32 := 0x00058463.
Lemma F_1968c : fetch_word Plain.M.loaded_segments (0x196e4 : word) = Some W_1968c.
Proof. vm_refl. Qed.
Lemma D_1968c : decode_any W_1968c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19690 : bv 32 := 0x0005a023.
Lemma F_19690 : fetch_word Plain.M.loaded_segments (0x196e8 : word) = Some W_19690.
Proof. vm_refl. Qed.
Lemma D_19690 : decode_any W_19690 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19694 : bv 32 := 0x00060463.
Lemma F_19694 : fetch_word Plain.M.loaded_segments (0x196ec : word) = Some W_19694.
Proof. vm_refl. Qed.
Lemma D_19694 : decode_any W_19694 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19698 : bv 32 := 0x00062023.
Lemma F_19698 : fetch_word Plain.M.loaded_segments (0x196f0 : word) = Some W_19698.
Proof. vm_refl. Qed.
Lemma D_19698 : decode_any W_19698 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1969c : bv 32 := 0x00068463.
Lemma F_1969c : fetch_word Plain.M.loaded_segments (0x196f4 : word) = Some W_1969c.
Proof. vm_refl. Qed.
Lemma D_1969c : decode_any W_1969c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a0 : bv 32 := 0x0006a023.
Lemma F_196a0 : fetch_word Plain.M.loaded_segments (0x196f8 : word) = Some W_196a0.
Proof. vm_refl. Qed.
Lemma D_196a0 : decode_any W_196a0 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a4 : bv 32 := 0x02050a63.
Lemma F_196a4 : fetch_word Plain.M.loaded_segments (0x196fc : word) = Some W_196a4.
Proof. vm_refl. Qed.
Lemma D_196a4 : decode_any W_196a4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a8 : bv 32 := 0x00058663.
Lemma F_196a8 : fetch_word Plain.M.loaded_segments (0x19700 : word) = Some W_196a8.
Proof. vm_refl. Qed.
Lemma D_196a8 : decode_any W_196a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196ac : bv 32 := 0x00052703.
Lemma F_196ac : fetch_word Plain.M.loaded_segments (0x19704 : word) = Some W_196ac.
Proof. vm_refl. Qed.
Lemma D_196ac : decode_any W_196ac = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b0 : bv 32 := 0x00e5a023.
Lemma F_196b0 : fetch_word Plain.M.loaded_segments (0x19708 : word) = Some W_196b0.
Proof. vm_refl. Qed.
Lemma D_196b0 : decode_any W_196b0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b4 : bv 32 := 0x00060663.
Lemma F_196b4 : fetch_word Plain.M.loaded_segments (0x1970c : word) = Some W_196b4.
Proof. vm_refl. Qed.
Lemma D_196b4 : decode_any W_196b4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b8 : bv 32 := 0x00452583.
Lemma F_196b8 : fetch_word Plain.M.loaded_segments (0x19710 : word) = Some W_196b8.
Proof. vm_refl. Qed.
Lemma D_196b8 : decode_any W_196b8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196bc : bv 32 := 0x00b62023.
Lemma F_196bc : fetch_word Plain.M.loaded_segments (0x19714 : word) = Some W_196bc.
Proof. vm_refl. Qed.
Lemma D_196bc : decode_any W_196bc = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c0 : bv 32 := 0x00000593.
Lemma F_196c0 : fetch_word Plain.M.loaded_segments (0x19718 : word) = Some W_196c0.
Proof. vm_refl. Qed.
Lemma D_196c0 : decode_any W_196c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c4 : bv 32 := 0x00068663.
Lemma F_196c4 : fetch_word Plain.M.loaded_segments (0x1971c : word) = Some W_196c4.
Proof. vm_refl. Qed.
Lemma D_196c4 : decode_any W_196c4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c8 : bv 32 := 0x00852503.
Lemma F_196c8 : fetch_word Plain.M.loaded_segments (0x19720 : word) = Some W_196c8.
Proof. vm_refl. Qed.
Lemma D_196c8 : decode_any W_196c8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196cc : bv 32 := 0x00a6a023.
Lemma F_196cc : fetch_word Plain.M.loaded_segments (0x19724 : word) = Some W_196cc.
Proof. vm_refl. Qed.
Lemma D_196cc : decode_any W_196cc = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d0 : bv 32 := 0x00058513.
Lemma F_196d0 : fetch_word Plain.M.loaded_segments (0x19728 : word) = Some W_196d0.
Proof. vm_refl. Qed.
Lemma D_196d0 : decode_any W_196d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d4 : bv 32 := 0x00008067.
Lemma F_196d4 : fetch_word Plain.M.loaded_segments (0x1972c : word) = Some W_196d4.
Proof. vm_refl. Qed.
Lemma D_196d4 : decode_any W_196d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a204 : bv 32 := 0x00050663.
Lemma F_1a204 : fetch_word Plain.M.loaded_segments (0x1a25c : word) = Some W_1a204.
Proof. vm_refl. Qed.
Lemma D_1a204 : decode_any W_1a204 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a208 : bv 32 := 0x03853503.
Lemma F_1a208 : fetch_word Plain.M.loaded_segments (0x1a260 : word) = Some W_1a208.
Proof. vm_refl. Qed.
Lemma D_1a208 : decode_any W_1a208 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a20c : bv 32 := 0x00008067.
Lemma F_1a20c : fetch_word Plain.M.loaded_segments (0x1a264 : word) = Some W_1a20c.
Proof. vm_refl. Qed.
Lemma D_1a20c : decode_any W_1a20c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a244 : bv 32 := 0x00050663.
Lemma F_1a244 : fetch_word Plain.M.loaded_segments (0x1a29c : word) = Some W_1a244.
Proof. vm_refl. Qed.
Lemma D_1a244 : decode_any W_1a244 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a248 : bv 32 := 0x03053503.
Lemma F_1a248 : fetch_word Plain.M.loaded_segments (0x1a2a0 : word) = Some W_1a248.
Proof. vm_refl. Qed.
Lemma D_1a248 : decode_any W_1a248 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a24c : bv 32 := 0x00008067.
Lemma F_1a24c : fetch_word Plain.M.loaded_segments (0x1a2a4 : word) = Some W_1a24c.
Proof. vm_refl. Qed.
Lemma D_1a24c : decode_any W_1a24c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d898 : bv 32 := 0xfa010113.
Lemma F_1d898 : fetch_word Plain.M.loaded_segments (0x1d8f0 : word) = Some W_1d898.
Proof. vm_refl. Qed.
Lemma D_1d898 : decode_any W_1d898 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d89c : bv 32 := 0x04113c23.
Lemma F_1d89c : fetch_word Plain.M.loaded_segments (0x1d8f4 : word) = Some W_1d89c.
Proof. vm_refl. Qed.
Lemma D_1d89c : decode_any W_1d89c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a0 : bv 32 := 0x04813823.
Lemma F_1d8a0 : fetch_word Plain.M.loaded_segments (0x1d8f8 : word) = Some W_1d8a0.
Proof. vm_refl. Qed.
Lemma D_1d8a0 : decode_any W_1d8a0 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a4 : bv 32 := 0x04913423.
Lemma F_1d8a4 : fetch_word Plain.M.loaded_segments (0x1d8fc : word) = Some W_1d8a4.
Proof. vm_refl. Qed.
Lemma D_1d8a4 : decode_any W_1d8a4 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a8 : bv 32 := 0x05213023.
Lemma F_1d8a8 : fetch_word Plain.M.loaded_segments (0x1d900 : word) = Some W_1d8a8.
Proof. vm_refl. Qed.
Lemma D_1d8a8 : decode_any W_1d8a8 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8ac : bv 32 := 0x03313c23.
Lemma F_1d8ac : fetch_word Plain.M.loaded_segments (0x1d904 : word) = Some W_1d8ac.
Proof. vm_refl. Qed.
Lemma D_1d8ac : decode_any W_1d8ac = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b0 : bv 32 := 0x03413823.
Lemma F_1d8b0 : fetch_word Plain.M.loaded_segments (0x1d908 : word) = Some W_1d8b0.
Proof. vm_refl. Qed.
Lemma D_1d8b0 : decode_any W_1d8b0 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b4 : bv 32 := 0x03513423.
Lemma F_1d8b4 : fetch_word Plain.M.loaded_segments (0x1d90c : word) = Some W_1d8b4.
Proof. vm_refl. Qed.
Lemma D_1d8b4 : decode_any W_1d8b4 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b8 : bv 32 := 0x03613023.
Lemma F_1d8b8 : fetch_word Plain.M.loaded_segments (0x1d910 : word) = Some W_1d8b8.
Proof. vm_refl. Qed.
Lemma D_1d8b8 : decode_any W_1d8b8 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8bc : bv 32 := 0x01713c23.
Lemma F_1d8bc : fetch_word Plain.M.loaded_segments (0x1d914 : word) = Some W_1d8bc.
Proof. vm_refl. Qed.
Lemma D_1d8bc : decode_any W_1d8bc = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8c0 : bv 32 := 0x00068663.
Lemma F_1d8c0 : fetch_word Plain.M.loaded_segments (0x1d918 : word) = Some W_1d8c0.
Proof. vm_refl. Qed.
Lemma D_1d8c0 : decode_any W_1d8c0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8cc : bv 32 := 0x00070663.
Lemma F_1d8cc : fetch_word Plain.M.loaded_segments (0x1d924 : word) = Some W_1d8cc.
Proof. vm_refl. Qed.
Lemma D_1d8cc : decode_any W_1d8cc = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8d8 : bv 32 := 0x00078663.
Lemma F_1d8d8 : fetch_word Plain.M.loaded_segments (0x1d930 : word) = Some W_1d8d8.
Proof. vm_refl. Qed.
Lemma D_1d8d8 : decode_any W_1d8d8 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8e4 : bv 32 := 0x00080663.
Lemma F_1d8e4 : fetch_word Plain.M.loaded_segments (0x1d93c : word) = Some W_1d8e4.
Proof. vm_refl. Qed.
Lemma D_1d8e4 : decode_any W_1d8e4 = Some (Branch BC_EQ 16 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8e8 : bv 32 := 0xfff00893.
Lemma F_1d8e8 : fetch_word Plain.M.loaded_segments (0x1d940 : word) = Some W_1d8e8.
Proof. vm_refl. Qed.
Lemma D_1d8e8 : decode_any W_1d8e8 = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8ec : bv 32 := 0x01182023.
Lemma F_1d8ec : fetch_word Plain.M.loaded_segments (0x1d944 : word) = Some W_1d8ec.
Proof. vm_refl. Qed.
Lemma D_1d8ec : decode_any W_1d8ec = Some (Store SZ4 16 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f0 : bv 32 := 0x02050c63.
Lemma F_1d8f0 : fetch_word Plain.M.loaded_segments (0x1d948 : word) = Some W_1d8f0.
Proof. vm_refl. Qed.
Lemma D_1d8f0 : decode_any W_1d8f0 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f4 : bv 32 := 0xffa6089b.
Lemma F_1d8f4 : fetch_word Plain.M.loaded_segments (0x1d94c : word) = Some W_1d8f4.
Proof. vm_refl. Qed.
Lemma D_1d8f4 : decode_any W_1d8f4 = Some (OpImm32 17 12 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f8 : bv 32 := 0xffd00293.
Lemma F_1d8f8 : fetch_word Plain.M.loaded_segments (0x1d950 : word) = Some W_1d8f8.
Proof. vm_refl. Qed.
Lemma D_1d8f8 : decode_any W_1d8f8 = Some (OpImm ALU_ADD 5 0 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8fc : bv 32 := 0x0912e063.
Lemma F_1d8fc : fetch_word Plain.M.loaded_segments (0x1d954 : word) = Some W_1d8fc.
Proof. vm_refl. Qed.
Lemma D_1d8fc : decode_any W_1d8fc = Some (Branch BC_LTU 5 17 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d97c : bv 32 := 0x00080b13.
Lemma F_1d97c : fetch_word Plain.M.loaded_segments (0x1d9d4 : word) = Some W_1d97c.
Proof. vm_refl. Qed.
Lemma D_1d97c : decode_any W_1d97c = Some (OpImm ALU_ADD 22 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d980 : bv 32 := 0x00068a13.
Lemma F_1d980 : fetch_word Plain.M.loaded_segments (0x1d9d8 : word) = Some W_1d980.
Proof. vm_refl. Qed.
Lemma D_1d980 : decode_any W_1d980 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d984 : bv 32 := 0x00058a93.
Lemma F_1d984 : fetch_word Plain.M.loaded_segments (0x1d9dc : word) = Some W_1d984.
Proof. vm_refl. Qed.
Lemma D_1d984 : decode_any W_1d984 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d988 : bv 32 := 0x00070993.
Lemma F_1d988 : fetch_word Plain.M.loaded_segments (0x1d9e0 : word) = Some W_1d988.
Proof. vm_refl. Qed.
Lemma D_1d988 : decode_any W_1d988 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d98c : bv 32 := 0x00060b93.
Lemma F_1d98c : fetch_word Plain.M.loaded_segments (0x1d9e4 : word) = Some W_1d98c.
Proof. vm_refl. Qed.
Lemma D_1d98c : decode_any W_1d98c = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d990 : bv 32 := 0x00078913.
Lemma F_1d990 : fetch_word Plain.M.loaded_segments (0x1d9e8 : word) = Some W_1d990.
Proof. vm_refl. Qed.
Lemma D_1d990 : decode_any W_1d990 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d994 : bv 32 := 0x00050493.
Lemma F_1d994 : fetch_word Plain.M.loaded_segments (0x1d9ec : word) = Some W_1d994.
Proof. vm_refl. Qed.
Lemma D_1d994 : decode_any W_1d994 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d998 : bv 32 := 0x8adfc0ef.
Lemma F_1d998 : fetch_word Plain.M.loaded_segments (0x1d9f0 : word) = Some W_1d998.
Proof. vm_refl. Qed.
Lemma D_1d998 : decode_any W_1d998 = Some (Jal 1 2082988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d99c : bv 32 := 0x06050463.
Lemma F_1d99c : fetch_word Plain.M.loaded_segments (0x1d9f4 : word) = Some W_1d99c.
Proof. vm_refl. Qed.
Lemma D_1d99c : decode_any W_1d99c = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da04 : bv 32 := 0x01410593.
Lemma F_1da04 : fetch_word Plain.M.loaded_segments (0x1da5c : word) = Some W_1da04.
Proof. vm_refl. Qed.
Lemma D_1da04 : decode_any W_1da04 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da08 : bv 32 := 0x01010613.
Lemma F_1da08 : fetch_word Plain.M.loaded_segments (0x1da60 : word) = Some W_1da08.
Proof. vm_refl. Qed.
Lemma D_1da08 : decode_any W_1da08 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da0c : bv 32 := 0x00c10693.
Lemma F_1da0c : fetch_word Plain.M.loaded_segments (0x1da64 : word) = Some W_1da0c.
Proof. vm_refl. Qed.
Lemma D_1da0c : decode_any W_1da0c = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da10 : bv 32 := 0x00048513.
Lemma F_1da10 : fetch_word Plain.M.loaded_segments (0x1da68 : word) = Some W_1da10.
Proof. vm_refl. Qed.
Lemma D_1da10 : decode_any W_1da10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da14 : bv 32 := 0xc79fb0ef.
Lemma F_1da14 : fetch_word Plain.M.loaded_segments (0x1da6c : word) = Some W_1da14.
Proof. vm_refl. Qed.
Lemma D_1da14 : decode_any W_1da14 = Some (Jal 1 2079864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da18 : bv 32 := 0x0d505063.
Lemma F_1da18 : fetch_word Plain.M.loaded_segments (0x1da70 : word) = Some W_1da18.
Proof. vm_refl. Qed.
Lemma D_1da18 : decode_any W_1da18 = Some (Branch BC_GE 0 21 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da1c : bv 32 := 0x00c12503.
Lemma F_1da1c : fetch_word Plain.M.loaded_segments (0x1da74 : word) = Some W_1da1c.
Proof. vm_refl. Qed.
Lemma D_1da1c : decode_any W_1da1c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da20 : bv 32 := 0x00800613.
Lemma F_1da20 : fetch_word Plain.M.loaded_segments (0x1da78 : word) = Some W_1da20.
Proof. vm_refl. Qed.
Lemma D_1da20 : decode_any W_1da20 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da24 : bv 32 := 0x00098593.
Lemma F_1da24 : fetch_word Plain.M.loaded_segments (0x1da7c : word) = Some W_1da24.
Proof. vm_refl. Qed.
Lemma D_1da24 : decode_any W_1da24 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da28 : bv 32 := 0x00c50663.
Lemma F_1da28 : fetch_word Plain.M.loaded_segments (0x1da80 : word) = Some W_1da28.
Proof. vm_refl. Qed.
Lemma D_1da28 : decode_any W_1da28 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1da34 : bv 32 := 0x0c0b1663.
Lemma F_1da34 : fetch_word Plain.M.loaded_segments (0x1da8c : word) = Some W_1da34.
Proof. vm_refl. Qed.
Lemma D_1da34 : decode_any W_1da34 = Some (Branch BC_NE 22 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db00 : bv 32 := 0x08091e63.
Lemma F_1db00 : fetch_word Plain.M.loaded_segments (0x1db58 : word) = Some W_1db00.
Proof. vm_refl. Qed.
Lemma D_1db00 : decode_any W_1db00 = Some (Branch BC_NE 18 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db04 : bv 32 := 0x08059c63.
Lemma F_1db04 : fetch_word Plain.M.loaded_segments (0x1db5c : word) = Some W_1db04.
Proof. vm_refl. Qed.
Lemma D_1db04 : decode_any W_1db04 = Some (Branch BC_NE 11 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db08 : bv 32 := 0x080a1a63.
Lemma F_1db08 : fetch_word Plain.M.loaded_segments (0x1db60 : word) = Some W_1db08.
Proof. vm_refl. Qed.
Lemma D_1db08 : decode_any W_1db08 = Some (Branch BC_NE 20 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db0c : bv 32 := 0x02000593.
Lemma F_1db0c : fetch_word Plain.M.loaded_segments (0x1db64 : word) = Some W_1db0c.
Proof. vm_refl. Qed.
Lemma D_1db0c : decode_any W_1db0c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db10 : bv 32 := 0x08b51663.
Lemma F_1db10 : fetch_word Plain.M.loaded_segments (0x1db68 : word) = Some W_1db10.
Proof. vm_refl. Qed.
Lemma D_1db10 : decode_any W_1db10 = Some (Branch BC_NE 10 11 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db70 : bv 32 := 0x05813083.
Lemma F_1db70 : fetch_word Plain.M.loaded_segments (0x1dbc8 : word) = Some W_1db70.
Proof. vm_refl. Qed.
Lemma D_1db70 : decode_any W_1db70 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db74 : bv 32 := 0x05013403.
Lemma F_1db74 : fetch_word Plain.M.loaded_segments (0x1dbcc : word) = Some W_1db74.
Proof. vm_refl. Qed.
Lemma D_1db74 : decode_any W_1db74 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db78 : bv 32 := 0x04813483.
Lemma F_1db78 : fetch_word Plain.M.loaded_segments (0x1dbd0 : word) = Some W_1db78.
Proof. vm_refl. Qed.
Lemma D_1db78 : decode_any W_1db78 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db7c : bv 32 := 0x04013903.
Lemma F_1db7c : fetch_word Plain.M.loaded_segments (0x1dbd4 : word) = Some W_1db7c.
Proof. vm_refl. Qed.
Lemma D_1db7c : decode_any W_1db7c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db80 : bv 32 := 0x03813983.
Lemma F_1db80 : fetch_word Plain.M.loaded_segments (0x1dbd8 : word) = Some W_1db80.
Proof. vm_refl. Qed.
Lemma D_1db80 : decode_any W_1db80 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db84 : bv 32 := 0x03013a03.
Lemma F_1db84 : fetch_word Plain.M.loaded_segments (0x1dbdc : word) = Some W_1db84.
Proof. vm_refl. Qed.
Lemma D_1db84 : decode_any W_1db84 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db88 : bv 32 := 0x02813a83.
Lemma F_1db88 : fetch_word Plain.M.loaded_segments (0x1dbe0 : word) = Some W_1db88.
Proof. vm_refl. Qed.
Lemma D_1db88 : decode_any W_1db88 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db8c : bv 32 := 0x02013b03.
Lemma F_1db8c : fetch_word Plain.M.loaded_segments (0x1dbe4 : word) = Some W_1db8c.
Proof. vm_refl. Qed.
Lemma D_1db8c : decode_any W_1db8c = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db90 : bv 32 := 0x01813b83.
Lemma F_1db90 : fetch_word Plain.M.loaded_segments (0x1dbe8 : word) = Some W_1db90.
Proof. vm_refl. Qed.
Lemma D_1db90 : decode_any W_1db90 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db94 : bv 32 := 0x06010113.
Lemma F_1db94 : fetch_word Plain.M.loaded_segments (0x1dbec : word) = Some W_1db94.
Proof. vm_refl. Qed.
Lemma D_1db94 : decode_any W_1db94 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db98 : bv 32 := 0x00008067.
Lemma F_1db98 : fetch_word Plain.M.loaded_segments (0x1dbf0 : word) = Some W_1db98.
Proof. vm_refl. Qed.
Lemma D_1db98 : decode_any W_1db98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1db9c : bv 32 := 0x00048513.
Lemma F_1db9c : fetch_word Plain.M.loaded_segments (0x1dbf4 : word) = Some W_1db9c.
Proof. vm_refl. Qed.
Lemma D_1db9c : decode_any W_1db9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dba0 : bv 32 := 0xe64fc0ef.
Lemma F_1dba0 : fetch_word Plain.M.loaded_segments (0x1dbf8 : word) = Some W_1dba0.
Proof. vm_refl. Qed.
Lemma D_1dba0 : decode_any W_1dba0 = Some (Jal 1 2082404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dba4 : bv 32 := 0x00050413.
Lemma F_1dba4 : fetch_word Plain.M.loaded_segments (0x1dbfc : word) = Some W_1dba4.
Proof. vm_refl. Qed.
Lemma D_1dba4 : decode_any W_1dba4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dba8 : bv 32 := 0x00048513.
Lemma F_1dba8 : fetch_word Plain.M.loaded_segments (0x1dc00 : word) = Some W_1dba8.
Proof. vm_refl. Qed.
Lemma D_1dba8 : decode_any W_1dba8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbac : bv 32 := 0xfe4fb0ef.
Lemma F_1dbac : fetch_word Plain.M.loaded_segments (0x1dc04 : word) = Some W_1dbac.
Proof. vm_refl. Qed.
Lemma D_1dbac : decode_any W_1dbac = Some (Jal 1 2078692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbb0 : bv 32 := 0x00c12703.
Lemma F_1dbb0 : fetch_word Plain.M.loaded_segments (0x1dc08 : word) = Some W_1dbb0.
Proof. vm_refl. Qed.
Lemma D_1dbb0 : decode_any W_1dbb0 = Some (Load SZ4 true 14 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbb4 : bv 32 := 0x000b8593.
Lemma F_1dbb4 : fetch_word Plain.M.loaded_segments (0x1dc0c : word) = Some W_1dbb4.
Proof. vm_refl. Qed.
Lemma D_1dbb4 : decode_any W_1dbb4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbb8 : bv 32 := 0xffcb8693.
Lemma F_1dbb8 : fetch_word Plain.M.loaded_segments (0x1dc10 : word) = Some W_1dbb8.
Proof. vm_refl. Qed.
Lemma D_1dbb8 : decode_any W_1dbb8 = Some (OpImm ALU_ADD 13 23 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbbc : bv 32 := 0x000187b7.
Lemma F_1dbbc : fetch_word Plain.M.loaded_segments (0x1dc14 : word) = Some W_1dbbc.
Proof. vm_refl. Qed.
Lemma D_1dbbc : decode_any W_1dbbc = Some (Lui 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbc0 : bv 32 := 0x01012603.
Lemma F_1dbc0 : fetch_word Plain.M.loaded_segments (0x1dc18 : word) = Some W_1dbc0.
Proof. vm_refl. Qed.
Lemma D_1dbc0 : decode_any W_1dbc0 = Some (Load SZ4 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbc4 : bv 32 := 0x0016b693.
Lemma F_1dbc4 : fetch_word Plain.M.loaded_segments (0x1dc1c : word) = Some W_1dbc4.
Proof. vm_refl. Qed.
Lemma D_1dbc4 : decode_any W_1dbc4 = Some (OpImm ALU_SLTU 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbc8 : bv 32 := 0xfff6869b.
Lemma F_1dbc8 : fetch_word Plain.M.loaded_segments (0x1dc20 : word) = Some W_1dbc8.
Proof. vm_refl. Qed.
Lemma D_1dbc8 : decode_any W_1dbc8 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbcc : bv 32 := 0x6a07879b.
Lemma F_1dbcc : fetch_word Plain.M.loaded_segments (0x1dc24 : word) = Some W_1dbcc.
Proof. vm_refl. Qed.
Lemma D_1dbcc : decode_any W_1dbcc = Some (OpImm32 15 15 1696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbd0 : bv 32 := 0x00800813.
Lemma F_1dbd0 : fetch_word Plain.M.loaded_segments (0x1dc28 : word) = Some W_1dbd0.
Proof. vm_refl. Qed.
Lemma D_1dbd0 : decode_any W_1dbd0 = Some (OpImm ALU_ADD 16 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbd4 : bv 32 := 0x00f6e6b3.
Lemma F_1dbd4 : fetch_word Plain.M.loaded_segments (0x1dc2c : word) = Some W_1dbd4.
Proof. vm_refl. Qed.
Lemma D_1dbd4 : decode_any W_1dbd4 = Some (Op ALU_OR 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbd8 : bv 32 := 0x09071a63.
Lemma F_1dbd8 : fetch_word Plain.M.loaded_segments (0x1dc30 : word) = Some W_1dbd8.
Proof. vm_refl. Qed.
Lemma D_1dbd8 : decode_any W_1dbd8 = Some (Branch BC_NE 14 16 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbdc : bv 32 := 0x1ac05463.
Lemma F_1dbdc : fetch_word Plain.M.loaded_segments (0x1dc34 : word) = Some W_1dbdc.
Proof. vm_refl. Qed.
Lemma D_1dbdc : decode_any W_1dbdc = Some (Branch BC_GE 0 12 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbe0 : bv 32 := 0x00000713.
Lemma F_1dbe0 : fetch_word Plain.M.loaded_segments (0x1dc38 : word) = Some W_1dbe0.
Proof. vm_refl. Qed.
Lemma D_1dbe0 : decode_any W_1dbe0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbe4 : bv 32 := 0x01412783.
Lemma F_1dbe4 : fetch_word Plain.M.loaded_segments (0x1dc3c : word) = Some W_1dbe4.
Proof. vm_refl. Qed.
Lemma D_1dbe4 : decode_any W_1dbe4 = Some (Load SZ4 true 15 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbe8 : bv 32 := 0x020a9813.
Lemma F_1dbe8 : fetch_word Plain.M.loaded_segments (0x1dc40 : word) = Some W_1dbe8.
Proof. vm_refl. Qed.
Lemma D_1dbe8 : decode_any W_1dbe8 = Some (ShiftImm ALU_SLL 16 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbec : bv 32 := 0x02085813.
Lemma F_1dbec : fetch_word Plain.M.loaded_segments (0x1dc44 : word) = Some W_1dbec.
Proof. vm_refl. Qed.
Lemma D_1dbec : decode_any W_1dbec = Some (ShiftImm ALU_SRL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbf0 : bv 32 := 0x03050533.
Lemma F_1dbf0 : fetch_word Plain.M.loaded_segments (0x1dc48 : word) = Some W_1dbf0.
Proof. vm_refl. Qed.
Lemma D_1dbf0 : decode_any W_1dbf0 = Some (Mul M_MUL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbf4 : bv 32 := 0x00251513.
Lemma F_1dbf4 : fetch_word Plain.M.loaded_segments (0x1dc4c : word) = Some W_1dbf4.
Proof. vm_refl. Qed.
Lemma D_1dbf4 : decode_any W_1dbf4 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dbf8 : bv 32 := 0x0180006f.
Lemma F_1dbf8 : fetch_word Plain.M.loaded_segments (0x1dc50 : word) = Some W_1dbf8.
Proof. vm_refl. Qed.
Lemma D_1dbf8 : decode_any W_1dbf8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc00 : bv 32 := 0x01570733.
Lemma F_1dc00 : fetch_word Plain.M.loaded_segments (0x1dc58 : word) = Some W_1dc00.
Proof. vm_refl. Qed.
Lemma D_1dc00 : decode_any W_1dc00 = Some (Op ALU_ADD 14 14 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc04 : bv 32 := 0x00a40433.
Lemma F_1dc04 : fetch_word Plain.M.loaded_segments (0x1dc5c : word) = Some W_1dc04.
Proof. vm_refl. Qed.
Lemma D_1dc04 : decode_any W_1dc04 = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc08 : bv 32 := 0x00028693.
Lemma F_1dc08 : fetch_word Plain.M.loaded_segments (0x1dc60 : word) = Some W_1dc08.
Proof. vm_refl. Qed.
Lemma D_1dc08 : decode_any W_1dc08 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc0c : bv 32 := 0x16c77e63.
Lemma F_1dc0c : fetch_word Plain.M.loaded_segments (0x1dc64 : word) = Some W_1dc0c.
Proof. vm_refl. Qed.
Lemma D_1dc0c : decode_any W_1dc0c = Some (Branch BC_GEU 14 12 380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc10 : bv 32 := 0xfef056e3.
Lemma F_1dc10 : fetch_word Plain.M.loaded_segments (0x1dc68 : word) = Some W_1dc10.
Proof. vm_refl. Qed.
Lemma D_1dc10 : decode_any W_1dc10 = Some (Branch BC_GE 0 15 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc14 : bv 32 := 0x00000893.
Lemma F_1dc14 : fetch_word Plain.M.loaded_segments (0x1dc6c : word) = Some W_1dc14.
Proof. vm_refl. Qed.
Lemma D_1dc14 : decode_any W_1dc14 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc18 : bv 32 := 0x00040313.
Lemma F_1dc18 : fetch_word Plain.M.loaded_segments (0x1dc70 : word) = Some W_1dc18.
Proof. vm_refl. Qed.
Lemma D_1dc18 : decode_any W_1dc18 = Some (OpImm ALU_ADD 6 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc1c : bv 32 := 0x0140006f.
Lemma F_1dc1c : fetch_word Plain.M.loaded_segments (0x1dc74 : word) = Some W_1dc1c.
Proof. vm_refl. Qed.
Lemma D_1dc1c : decode_any W_1dc1c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc20 : bv 32 := 0x015888bb.
Lemma F_1dc20 : fetch_word Plain.M.loaded_segments (0x1dc78 : word) = Some W_1dc20.
Proof. vm_refl. Qed.
Lemma D_1dc20 : decode_any W_1dc20 = Some (Op32 ALU_ADD 17 17 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc24 : bv 32 := 0x01030333.
Lemma F_1dc24 : fetch_word Plain.M.loaded_segments (0x1dc7c : word) = Some W_1dc24.
Proof. vm_refl. Qed.
Lemma D_1dc24 : decode_any W_1dc24 = Some (Op ALU_ADD 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc28 : bv 32 := 0x00028693.
Lemma F_1dc28 : fetch_word Plain.M.loaded_segments (0x1dc80 : word) = Some W_1dc28.
Proof. vm_refl. Qed.
Lemma D_1dc28 : decode_any W_1dc28 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc2c : bv 32 := 0xfcf8dae3.
Lemma F_1dc2c : fetch_word Plain.M.loaded_segments (0x1dc84 : word) = Some W_1dc2c.
Proof. vm_refl. Qed.
Lemma D_1dc2c : decode_any W_1dc2c = Some (Branch BC_GE 17 15 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc30 : bv 32 := 0xffb58293.
Lemma F_1dc30 : fetch_word Plain.M.loaded_segments (0x1dc88 : word) = Some W_1dc30.
Proof. vm_refl. Qed.
Lemma D_1dc30 : decode_any W_1dc30 = Some (OpImm ALU_ADD 5 11 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc34 : bv 32 := 0x00334393.
Lemma F_1dc34 : fetch_word Plain.M.loaded_segments (0x1dc8c : word) = Some W_1dc34.
Proof. vm_refl. Qed.
Lemma D_1dc34 : decode_any W_1dc34 = Some (OpImm ALU_XOR 7 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc38 : bv 32 := 0x0003c383.
Lemma F_1dc38 : fetch_word Plain.M.loaded_segments (0x1dc90 : word) = Some W_1dc38.
Proof. vm_refl. Qed.
Lemma D_1dc38 : decode_any W_1dc38 = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc3c : bv 32 := 0xffc58e13.
Lemma F_1dc3c : fetch_word Plain.M.loaded_segments (0x1dc94 : word) = Some W_1dc3c.
Proof. vm_refl. Qed.
Lemma D_1dc3c : decode_any W_1dc3c = Some (OpImm ALU_ADD 28 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc40 : bv 32 := 0x0012be93.
Lemma F_1dc40 : fetch_word Plain.M.loaded_segments (0x1dc98 : word) = Some W_1dc40.
Proof. vm_refl. Qed.
Lemma D_1dc40 : decode_any W_1dc40 = Some (OpImm ALU_SLTU 29 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc44 : bv 32 := 0x001e3e13.
Lemma F_1dc44 : fetch_word Plain.M.loaded_segments (0x1dc9c : word) = Some W_1dc44.
Proof. vm_refl. Qed.
Lemma D_1dc44 : decode_any W_1dc44 = Some (OpImm ALU_SLTU 28 28 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc48 : bv 32 := 0x0ff3f293.
Lemma F_1dc48 : fetch_word Plain.M.loaded_segments (0x1dca0 : word) = Some W_1dc48.
Proof. vm_refl. Qed.
Lemma D_1dc48 : decode_any W_1dc48 = Some (OpImm ALU_AND 5 7 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc4c : bv 32 := 0x00d2a3b3.
Lemma F_1dc4c : fetch_word Plain.M.loaded_segments (0x1dca4 : word) = Some W_1dc4c.
Proof. vm_refl. Qed.
Lemma D_1dc4c : decode_any W_1dc4c = Some (Op ALU_SLT 7 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc50 : bv 32 := 0x007e73b3.
Lemma F_1dc50 : fetch_word Plain.M.loaded_segments (0x1dca8 : word) = Some W_1dc50.
Proof. vm_refl. Qed.
Lemma D_1dc50 : decode_any W_1dc50 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc54 : bv 32 := 0x0056ae33.
Lemma F_1dc54 : fetch_word Plain.M.loaded_segments (0x1dcac : word) = Some W_1dc54.
Proof. vm_refl. Qed.
Lemma D_1dc54 : decode_any W_1dc54 = Some (Op ALU_SLT 28 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc58 : bv 32 := 0x01cefe33.
Lemma F_1dc58 : fetch_word Plain.M.loaded_segments (0x1dcb0 : word) = Some W_1dc58.
Proof. vm_refl. Qed.
Lemma D_1dc58 : decode_any W_1dc58 = Some (Op ALU_AND 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc5c : bv 32 := 0x01c3e3b3.
Lemma F_1dc5c : fetch_word Plain.M.loaded_segments (0x1dcb4 : word) = Some W_1dc5c.
Proof. vm_refl. Qed.
Lemma D_1dc5c : decode_any W_1dc5c = Some (Op ALU_OR 7 7 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc60 : bv 32 := 0xfc0390e3.
Lemma F_1dc60 : fetch_word Plain.M.loaded_segments (0x1dcb8 : word) = Some W_1dc60.
Proof. vm_refl. Qed.
Lemma D_1dc60 : decode_any W_1dc60 = Some (Branch BC_NE 7 0 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc64 : bv 32 := 0x00068293.
Lemma F_1dc64 : fetch_word Plain.M.loaded_segments (0x1dcbc : word) = Some W_1dc64.
Proof. vm_refl. Qed.
Lemma D_1dc64 : decode_any W_1dc64 = Some (OpImm ALU_ADD 5 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dc68 : bv 32 := 0xfb9ff06f.
Lemma F_1dc68 : fetch_word Plain.M.loaded_segments (0x1dcc0 : word) = Some W_1dc68.
Proof. vm_refl. Qed.
Lemma D_1dc68 : decode_any W_1dc68 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd88 : bv 32 := 0x00000513.
Lemma F_1dd88 : fetch_word Plain.M.loaded_segments (0x1dde0 : word) = Some W_1dd88.
Proof. vm_refl. Qed.
Lemma D_1dd88 : decode_any W_1dd88 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd8c : bv 32 := 0x005b2023.
Lemma F_1dd8c : fetch_word Plain.M.loaded_segments (0x1dde4 : word) = Some W_1dd8c.
Proof. vm_refl. Qed.
Lemma D_1dd8c : decode_any W_1dd8c = Some (Store SZ4 22 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd90 : bv 32 := 0xde1ff06f.
Lemma F_1dd90 : fetch_word Plain.M.loaded_segments (0x1dde8 : word) = Some W_1dd90.
Proof. vm_refl. Qed.
Lemma D_1dd90 : decode_any W_1dd90 = Some (Jal 0 2096608, 4%Z).
Proof. vm_refl. Qed.

