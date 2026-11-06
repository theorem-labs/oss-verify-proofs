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
Definition W_958f8 : bv 32 := 0x00155593.
Lemma F_958f8 : fetch_word AsanUbsan.M.loaded_segments (0x95940 : word) = Some W_958f8.
Proof. vm_refl. Qed.
Lemma D_958f8 : decode_any W_958f8 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_958fc : bv 32 := 0x55555637.
Lemma F_958fc : fetch_word AsanUbsan.M.loaded_segments (0x95944 : word) = Some W_958fc.
Proof. vm_refl. Qed.
Lemma D_958fc : decode_any W_958fc = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95900 : bv 32 := 0x333336b7.
Lemma F_95900 : fetch_word AsanUbsan.M.loaded_segments (0x95948 : word) = Some W_95900.
Proof. vm_refl. Qed.
Lemma D_95900 : decode_any W_95900 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95904 : bv 32 := 0x0f0f1737.
Lemma F_95904 : fetch_word AsanUbsan.M.loaded_segments (0x9594c : word) = Some W_95904.
Proof. vm_refl. Qed.
Lemma D_95904 : decode_any W_95904 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95908 : bv 32 := 0x010107b7.
Lemma F_95908 : fetch_word AsanUbsan.M.loaded_segments (0x95950 : word) = Some W_95908.
Proof. vm_refl. Qed.
Lemma D_95908 : decode_any W_95908 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9590c : bv 32 := 0x00b56533.
Lemma F_9590c : fetch_word AsanUbsan.M.loaded_segments (0x95954 : word) = Some W_9590c.
Proof. vm_refl. Qed.
Lemma D_9590c : decode_any W_9590c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95910 : bv 32 := 0x5556059b.
Lemma F_95910 : fetch_word AsanUbsan.M.loaded_segments (0x95958 : word) = Some W_95910.
Proof. vm_refl. Qed.
Lemma D_95910 : decode_any W_95910 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95914 : bv 32 := 0x3336861b.
Lemma F_95914 : fetch_word AsanUbsan.M.loaded_segments (0x9595c : word) = Some W_95914.
Proof. vm_refl. Qed.
Lemma D_95914 : decode_any W_95914 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95918 : bv 32 := 0xf0f7069b.
Lemma F_95918 : fetch_word AsanUbsan.M.loaded_segments (0x95960 : word) = Some W_95918.
Proof. vm_refl. Qed.
Lemma D_95918 : decode_any W_95918 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9591c : bv 32 := 0x1017871b.
Lemma F_9591c : fetch_word AsanUbsan.M.loaded_segments (0x95964 : word) = Some W_9591c.
Proof. vm_refl. Qed.
Lemma D_9591c : decode_any W_9591c = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95920 : bv 32 := 0x00255793.
Lemma F_95920 : fetch_word AsanUbsan.M.loaded_segments (0x95968 : word) = Some W_95920.
Proof. vm_refl. Qed.
Lemma D_95920 : decode_any W_95920 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95924 : bv 32 := 0x00f56533.
Lemma F_95924 : fetch_word AsanUbsan.M.loaded_segments (0x9596c : word) = Some W_95924.
Proof. vm_refl. Qed.
Lemma D_95924 : decode_any W_95924 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95928 : bv 32 := 0x02059793.
Lemma F_95928 : fetch_word AsanUbsan.M.loaded_segments (0x95970 : word) = Some W_95928.
Proof. vm_refl. Qed.
Lemma D_95928 : decode_any W_95928 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9592c : bv 32 := 0x00f585b3.
Lemma F_9592c : fetch_word AsanUbsan.M.loaded_segments (0x95974 : word) = Some W_9592c.
Proof. vm_refl. Qed.
Lemma D_9592c : decode_any W_9592c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95930 : bv 32 := 0x02061793.
Lemma F_95930 : fetch_word AsanUbsan.M.loaded_segments (0x95978 : word) = Some W_95930.
Proof. vm_refl. Qed.
Lemma D_95930 : decode_any W_95930 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95934 : bv 32 := 0x00f60633.
Lemma F_95934 : fetch_word AsanUbsan.M.loaded_segments (0x9597c : word) = Some W_95934.
Proof. vm_refl. Qed.
Lemma D_95934 : decode_any W_95934 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95938 : bv 32 := 0x02069793.
Lemma F_95938 : fetch_word AsanUbsan.M.loaded_segments (0x95980 : word) = Some W_95938.
Proof. vm_refl. Qed.
Lemma D_95938 : decode_any W_95938 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9593c : bv 32 := 0x00f686b3.
Lemma F_9593c : fetch_word AsanUbsan.M.loaded_segments (0x95984 : word) = Some W_9593c.
Proof. vm_refl. Qed.
Lemma D_9593c : decode_any W_9593c = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95940 : bv 32 := 0x02071793.
Lemma F_95940 : fetch_word AsanUbsan.M.loaded_segments (0x95988 : word) = Some W_95940.
Proof. vm_refl. Qed.
Lemma D_95940 : decode_any W_95940 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95944 : bv 32 := 0x00f70733.
Lemma F_95944 : fetch_word AsanUbsan.M.loaded_segments (0x9598c : word) = Some W_95944.
Proof. vm_refl. Qed.
Lemma D_95944 : decode_any W_95944 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95948 : bv 32 := 0x00455793.
Lemma F_95948 : fetch_word AsanUbsan.M.loaded_segments (0x95990 : word) = Some W_95948.
Proof. vm_refl. Qed.
Lemma D_95948 : decode_any W_95948 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9594c : bv 32 := 0x00f56533.
Lemma F_9594c : fetch_word AsanUbsan.M.loaded_segments (0x95994 : word) = Some W_9594c.
Proof. vm_refl. Qed.
Lemma D_9594c : decode_any W_9594c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95950 : bv 32 := 0x00855793.
Lemma F_95950 : fetch_word AsanUbsan.M.loaded_segments (0x95998 : word) = Some W_95950.
Proof. vm_refl. Qed.
Lemma D_95950 : decode_any W_95950 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95954 : bv 32 := 0x00f56533.
Lemma F_95954 : fetch_word AsanUbsan.M.loaded_segments (0x9599c : word) = Some W_95954.
Proof. vm_refl. Qed.
Lemma D_95954 : decode_any W_95954 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95958 : bv 32 := 0x01055793.
Lemma F_95958 : fetch_word AsanUbsan.M.loaded_segments (0x959a0 : word) = Some W_95958.
Proof. vm_refl. Qed.
Lemma D_95958 : decode_any W_95958 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9595c : bv 32 := 0x00f56533.
Lemma F_9595c : fetch_word AsanUbsan.M.loaded_segments (0x959a4 : word) = Some W_9595c.
Proof. vm_refl. Qed.
Lemma D_9595c : decode_any W_9595c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95960 : bv 32 := 0x02055793.
Lemma F_95960 : fetch_word AsanUbsan.M.loaded_segments (0x959a8 : word) = Some W_95960.
Proof. vm_refl. Qed.
Lemma D_95960 : decode_any W_95960 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95964 : bv 32 := 0x00f56533.
Lemma F_95964 : fetch_word AsanUbsan.M.loaded_segments (0x959ac : word) = Some W_95964.
Proof. vm_refl. Qed.
Lemma D_95964 : decode_any W_95964 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95968 : bv 32 := 0xfff54513.
Lemma F_95968 : fetch_word AsanUbsan.M.loaded_segments (0x959b0 : word) = Some W_95968.
Proof. vm_refl. Qed.
Lemma D_95968 : decode_any W_95968 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9596c : bv 32 := 0x00155793.
Lemma F_9596c : fetch_word AsanUbsan.M.loaded_segments (0x959b4 : word) = Some W_9596c.
Proof. vm_refl. Qed.
Lemma D_9596c : decode_any W_9596c = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95970 : bv 32 := 0x00b7f5b3.
Lemma F_95970 : fetch_word AsanUbsan.M.loaded_segments (0x959b8 : word) = Some W_95970.
Proof. vm_refl. Qed.
Lemma D_95970 : decode_any W_95970 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95974 : bv 32 := 0x40b50533.
Lemma F_95974 : fetch_word AsanUbsan.M.loaded_segments (0x959bc : word) = Some W_95974.
Proof. vm_refl. Qed.
Lemma D_95974 : decode_any W_95974 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95978 : bv 32 := 0x00c575b3.
Lemma F_95978 : fetch_word AsanUbsan.M.loaded_segments (0x959c0 : word) = Some W_95978.
Proof. vm_refl. Qed.
Lemma D_95978 : decode_any W_95978 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9597c : bv 32 := 0x00255513.
Lemma F_9597c : fetch_word AsanUbsan.M.loaded_segments (0x959c4 : word) = Some W_9597c.
Proof. vm_refl. Qed.
Lemma D_9597c : decode_any W_9597c = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95980 : bv 32 := 0x00c57533.
Lemma F_95980 : fetch_word AsanUbsan.M.loaded_segments (0x959c8 : word) = Some W_95980.
Proof. vm_refl. Qed.
Lemma D_95980 : decode_any W_95980 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95984 : bv 32 := 0x00a58533.
Lemma F_95984 : fetch_word AsanUbsan.M.loaded_segments (0x959cc : word) = Some W_95984.
Proof. vm_refl. Qed.
Lemma D_95984 : decode_any W_95984 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95988 : bv 32 := 0x00455593.
Lemma F_95988 : fetch_word AsanUbsan.M.loaded_segments (0x959d0 : word) = Some W_95988.
Proof. vm_refl. Qed.
Lemma D_95988 : decode_any W_95988 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9598c : bv 32 := 0x00b50533.
Lemma F_9598c : fetch_word AsanUbsan.M.loaded_segments (0x959d4 : word) = Some W_9598c.
Proof. vm_refl. Qed.
Lemma D_9598c : decode_any W_9598c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95990 : bv 32 := 0x00d57533.
Lemma F_95990 : fetch_word AsanUbsan.M.loaded_segments (0x959d8 : word) = Some W_95990.
Proof. vm_refl. Qed.
Lemma D_95990 : decode_any W_95990 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95994 : bv 32 := 0x02e50533.
Lemma F_95994 : fetch_word AsanUbsan.M.loaded_segments (0x959dc : word) = Some W_95994.
Proof. vm_refl. Qed.
Lemma D_95994 : decode_any W_95994 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95998 : bv 32 := 0x03855513.
Lemma F_95998 : fetch_word AsanUbsan.M.loaded_segments (0x959e0 : word) = Some W_95998.
Proof. vm_refl. Qed.
Lemma D_95998 : decode_any W_95998 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9599c : bv 32 := 0x40a0053b.
Lemma F_9599c : fetch_word AsanUbsan.M.loaded_segments (0x959e4 : word) = Some W_9599c.
Proof. vm_refl. Qed.
Lemma D_9599c : decode_any W_9599c = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a0 : bv 32 := 0xfff00593.
Lemma F_959a0 : fetch_word AsanUbsan.M.loaded_segments (0x959e8 : word) = Some W_959a0.
Proof. vm_refl. Qed.
Lemma D_959a0 : decode_any W_959a0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a4 : bv 32 := 0x00a59533.
Lemma F_959a4 : fetch_word AsanUbsan.M.loaded_segments (0x959ec : word) = Some W_959a4.
Proof. vm_refl. Qed.
Lemma D_959a4 : decode_any W_959a4 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a8 : bv 32 := 0xfff54513.
Lemma F_959a8 : fetch_word AsanUbsan.M.loaded_segments (0x959f0 : word) = Some W_959a8.
Proof. vm_refl. Qed.
Lemma D_959a8 : decode_any W_959a8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

