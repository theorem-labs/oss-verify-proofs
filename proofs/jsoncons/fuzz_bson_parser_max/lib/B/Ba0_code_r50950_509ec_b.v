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
Definition W_67098 : bv 32 := 0x104240ef.
Lemma F_67098 : fetch_word AsanUbsan.M.loaded_segments (0x674b0 : word) = Some W_67098.
Proof. vm_refl. Qed.
Lemma D_67098 : decode_any W_67098 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6709c : bv 32 := 0x00150b93.
Lemma F_6709c : fetch_word AsanUbsan.M.loaded_segments (0x674b4 : word) = Some W_6709c.
Proof. vm_refl. Qed.
Lemma D_6709c : decode_any W_6709c = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a0 : bv 32 := 0xfffb4513.
Lemma F_670a0 : fetch_word AsanUbsan.M.loaded_segments (0x674b8 : word) = Some W_670a0.
Proof. vm_refl. Qed.
Lemma D_670a0 : decode_any W_670a0 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a4 : bv 32 := 0x25756e63.
Lemma F_670a4 : fetch_word AsanUbsan.M.loaded_segments (0x674bc : word) = Some W_670a4.
Proof. vm_refl. Qed.
Lemma D_670a4 : decode_any W_670a4 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a8 : bv 32 := 0xfbfb8513.
Lemma F_670a8 : fetch_word AsanUbsan.M.loaded_segments (0x674c0 : word) = Some W_670a8.
Proof. vm_refl. Qed.
Lemma D_670a8 : decode_any W_670a8 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ac : bv 32 := 0xfbf00593.
Lemma F_670ac : fetch_word AsanUbsan.M.loaded_segments (0x674c4 : word) = Some W_670ac.
Proof. vm_refl. Qed.
Lemma D_670ac : decode_any W_670ac = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b0 : bv 32 := 0x2ca5f063.
Lemma F_670b0 : fetch_word AsanUbsan.M.loaded_segments (0x674c8 : word) = Some W_670b0.
Proof. vm_refl. Qed.
Lemma D_670b0 : decode_any W_670b0 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b4 : bv 32 := 0x000d0517.
Lemma F_670b4 : fetch_word AsanUbsan.M.loaded_segments (0x674cc : word) = Some W_670b4.
Proof. vm_refl. Qed.
Lemma D_670b4 : decode_any W_670b4 = Some (Auipc 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b8 : bv 32 := 0xff453503.
Lemma F_670b8 : fetch_word AsanUbsan.M.loaded_segments (0x674d0 : word) = Some W_670b8.
Proof. vm_refl. Qed.
Lemma D_670b8 : decode_any W_670b8 = Some (Load SZ8 true 10 10 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670bc : bv 32 := 0x017b0633.
Lemma F_670bc : fetch_word AsanUbsan.M.loaded_segments (0x674d4 : word) = Some W_670bc.
Proof. vm_refl. Qed.
Lemma D_670bc : decode_any W_670bc = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c0 : bv 32 := 0x00053583.
Lemma F_670c0 : fetch_word AsanUbsan.M.loaded_segments (0x674d8 : word) = Some W_670c0.
Proof. vm_refl. Qed.
Lemma D_670c0 : decode_any W_670c0 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c4 : bv 32 := 0x003b5513.
Lemma F_670c4 : fetch_word AsanUbsan.M.loaded_segments (0x674dc : word) = Some W_670c4.
Proof. vm_refl. Qed.
Lemma D_670c4 : decode_any W_670c4 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c8 : bv 32 := 0xfff60613.
Lemma F_670c8 : fetch_word AsanUbsan.M.loaded_segments (0x674e0 : word) = Some W_670c8.
Proof. vm_refl. Qed.
Lemma D_670c8 : decode_any W_670c8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670cc : bv 32 := 0x00365693.
Lemma F_670cc : fetch_word AsanUbsan.M.loaded_segments (0x674e4 : word) = Some W_670cc.
Proof. vm_refl. Qed.
Lemma D_670cc : decode_any W_670cc = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d0 : bv 32 := 0x00a58533.
Lemma F_670d0 : fetch_word AsanUbsan.M.loaded_segments (0x674e8 : word) = Some W_670d0.
Proof. vm_refl. Qed.
Lemma D_670d0 : decode_any W_670d0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d4 : bv 32 := 0x00d585b3.
Lemma F_670d4 : fetch_word AsanUbsan.M.loaded_segments (0x674ec : word) = Some W_670d4.
Proof. vm_refl. Qed.
Lemma D_670d4 : decode_any W_670d4 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d8 : bv 32 := 0xff857693.
Lemma F_670d8 : fetch_word AsanUbsan.M.loaded_segments (0x674f0 : word) = Some W_670d8.
Proof. vm_refl. Qed.
Lemma D_670d8 : decode_any W_670d8 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670dc : bv 32 := 0xff85f713.
Lemma F_670dc : fetch_word AsanUbsan.M.loaded_segments (0x674f4 : word) = Some W_670dc.
Proof. vm_refl. Qed.
Lemma D_670dc : decode_any W_670dc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e0 : bv 32 := 0x0006b683.
Lemma F_670e0 : fetch_word AsanUbsan.M.loaded_segments (0x674f8 : word) = Some W_670e0.
Proof. vm_refl. Qed.
Lemma D_670e0 : decode_any W_670e0 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e4 : bv 32 := 0x00073703.
Lemma F_670e4 : fetch_word AsanUbsan.M.loaded_segments (0x674fc : word) = Some W_670e4.
Proof. vm_refl. Qed.
Lemma D_670e4 : decode_any W_670e4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e8 : bv 32 := 0x00d766b3.
Lemma F_670e8 : fetch_word AsanUbsan.M.loaded_segments (0x67500 : word) = Some W_670e8.
Proof. vm_refl. Qed.
Lemma D_670e8 : decode_any W_670e8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ec : bv 32 := 0xf00688e3.
Lemma F_670ec : fetch_word AsanUbsan.M.loaded_segments (0x67504 : word) = Some W_670ec.
Proof. vm_refl. Qed.
Lemma D_670ec : decode_any W_670ec = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67124 : bv 32 := 0x000b0513.
Lemma F_67124 : fetch_word AsanUbsan.M.loaded_segments (0x6753c : word) = Some W_67124.
Proof. vm_refl. Qed.
Lemma D_67124 : decode_any W_67124 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67128 : bv 32 := 0x000b8593.
Lemma F_67128 : fetch_word AsanUbsan.M.loaded_segments (0x67540 : word) = Some W_67128.
Proof. vm_refl. Qed.
Lemma D_67128 : decode_any W_67128 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6712c : bv 32 := 0x77d130ef.
Lemma F_6712c : fetch_word AsanUbsan.M.loaded_segments (0x67544 : word) = Some W_6712c.
Proof. vm_refl. Qed.
Lemma D_6712c : decode_any W_6712c = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67130 : bv 32 := 0xec0506e3.
Lemma F_67130 : fetch_word AsanUbsan.M.loaded_segments (0x67548 : word) = Some W_67130.
Proof. vm_refl. Qed.
Lemma D_67130 : decode_any W_67130 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.
