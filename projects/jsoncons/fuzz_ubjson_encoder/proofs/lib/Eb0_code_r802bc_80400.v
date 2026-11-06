(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9b8b4 : bv 32 := 0xfd010113.
Lemma F_9b8b4 : fetch_word AsanUbsan.M.loaded_segments (0x9b904 : word) = Some W_9b8b4.
Proof. vm_refl. Qed.
Lemma D_9b8b4 : decode_any W_9b8b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8b8 : bv 32 := 0x02113423.
Lemma F_9b8b8 : fetch_word AsanUbsan.M.loaded_segments (0x9b908 : word) = Some W_9b8b8.
Proof. vm_refl. Qed.
Lemma D_9b8b8 : decode_any W_9b8b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8bc : bv 32 := 0x02813023.
Lemma F_9b8bc : fetch_word AsanUbsan.M.loaded_segments (0x9b90c : word) = Some W_9b8bc.
Proof. vm_refl. Qed.
Lemma D_9b8bc : decode_any W_9b8bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8c0 : bv 32 := 0x00913c23.
Lemma F_9b8c0 : fetch_word AsanUbsan.M.loaded_segments (0x9b910 : word) = Some W_9b8c0.
Proof. vm_refl. Qed.
Lemma D_9b8c0 : decode_any W_9b8c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8c4 : bv 32 := 0x01213823.
Lemma F_9b8c4 : fetch_word AsanUbsan.M.loaded_segments (0x9b914 : word) = Some W_9b8c4.
Proof. vm_refl. Qed.
Lemma D_9b8c4 : decode_any W_9b8c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8c8 : bv 32 := 0x01313423.
Lemma F_9b8c8 : fetch_word AsanUbsan.M.loaded_segments (0x9b918 : word) = Some W_9b8c8.
Proof. vm_refl. Qed.
Lemma D_9b8c8 : decode_any W_9b8c8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8cc : bv 32 := 0x00050413.
Lemma F_9b8cc : fetch_word AsanUbsan.M.loaded_segments (0x9b91c : word) = Some W_9b8cc.
Proof. vm_refl. Qed.
Lemma D_9b8cc : decode_any W_9b8cc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8d0 : bv 32 := 0x00000593.
Lemma F_9b8d0 : fetch_word AsanUbsan.M.loaded_segments (0x9b920 : word) = Some W_9b8d0.
Proof. vm_refl. Qed.
Lemma D_9b8d0 : decode_any W_9b8d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8d4 : bv 32 := 0x800004b7.
Lemma F_9b8d4 : fetch_word AsanUbsan.M.loaded_segments (0x9b924 : word) = Some W_9b8d4.
Proof. vm_refl. Qed.
Lemma D_9b8d4 : decode_any W_9b8d4 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8d8 : bv 32 := 0x00900913.
Lemma F_9b8d8 : fetch_word AsanUbsan.M.loaded_segments (0x9b928 : word) = Some W_9b8d8.
Proof. vm_refl. Qed.
Lemma D_9b8d8 : decode_any W_9b8d8 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8dc : bv 32 := 0x00052503.
Lemma F_9b8dc : fetch_word AsanUbsan.M.loaded_segments (0x9b92c : word) = Some W_9b8dc.
Proof. vm_refl. Qed.
Lemma D_9b8dc : decode_any W_9b8dc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8e0 : bv 32 := 0x00055a63.
Lemma F_9b8e0 : fetch_word AsanUbsan.M.loaded_segments (0x9b930 : word) = Some W_9b8e0.
Proof. vm_refl. Qed.
Lemma D_9b8e0 : decode_any W_9b8e0 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8f4 : bv 32 := 0x00956633.
Lemma F_9b8f4 : fetch_word AsanUbsan.M.loaded_segments (0x9b944 : word) = Some W_9b8f4.
Proof. vm_refl. Qed.
Lemma D_9b8f4 : decode_any W_9b8f4 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8f8 : bv 32 := 0x160426af.
Lemma F_9b8f8 : fetch_word AsanUbsan.M.loaded_segments (0x9b948 : word) = Some W_9b8f8.
Proof. vm_refl. Qed.
Lemma D_9b8f8 : decode_any W_9b8f8 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8fc : bv 32 := 0x00a69663.
Lemma F_9b8fc : fetch_word AsanUbsan.M.loaded_segments (0x9b94c : word) = Some W_9b8fc.
Proof. vm_refl. Qed.
Lemma D_9b8fc : decode_any W_9b8fc = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b900 : bv 32 := 0x1ac4272f.
Lemma F_9b900 : fetch_word AsanUbsan.M.loaded_segments (0x9b950 : word) = Some W_9b900.
Proof. vm_refl. Qed.
Lemma D_9b900 : decode_any W_9b900 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b904 : bv 32 := 0xfe071ae3.
Lemma F_9b904 : fetch_word AsanUbsan.M.loaded_segments (0x9b954 : word) = Some W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : decode_any W_9b904 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b908 : bv 32 := 0x02a68063.
Lemma F_9b908 : fetch_word AsanUbsan.M.loaded_segments (0x9b958 : word) = Some W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : decode_any W_9b908 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b928 : bv 32 := 0x02813083.
Lemma F_9b928 : fetch_word AsanUbsan.M.loaded_segments (0x9b978 : word) = Some W_9b928.
Proof. vm_refl. Qed.
Lemma D_9b928 : decode_any W_9b928 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b92c : bv 32 := 0x02013403.
Lemma F_9b92c : fetch_word AsanUbsan.M.loaded_segments (0x9b97c : word) = Some W_9b92c.
Proof. vm_refl. Qed.
Lemma D_9b92c : decode_any W_9b92c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b930 : bv 32 := 0x01813483.
Lemma F_9b930 : fetch_word AsanUbsan.M.loaded_segments (0x9b980 : word) = Some W_9b930.
Proof. vm_refl. Qed.
Lemma D_9b930 : decode_any W_9b930 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b934 : bv 32 := 0x01013903.
Lemma F_9b934 : fetch_word AsanUbsan.M.loaded_segments (0x9b984 : word) = Some W_9b934.
Proof. vm_refl. Qed.
Lemma D_9b934 : decode_any W_9b934 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b938 : bv 32 := 0x00813983.
Lemma F_9b938 : fetch_word AsanUbsan.M.loaded_segments (0x9b988 : word) = Some W_9b938.
Proof. vm_refl. Qed.
Lemma D_9b938 : decode_any W_9b938 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b93c : bv 32 := 0x03010113.
Lemma F_9b93c : fetch_word AsanUbsan.M.loaded_segments (0x9b98c : word) = Some W_9b93c.
Proof. vm_refl. Qed.
Lemma D_9b93c : decode_any W_9b93c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b940 : bv 32 := 0x00008067.
Lemma F_9b940 : fetch_word AsanUbsan.M.loaded_segments (0x9b990 : word) = Some W_9b940.
Proof. vm_refl. Qed.
Lemma D_9b940 : decode_any W_9b940 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
