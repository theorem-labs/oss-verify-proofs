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
Definition W_8c6ac : bv 32 := 0x00155593.
Lemma F_8c6ac : fetch_word AsanUbsan.M.loaded_segments (0x8cac4 : word) = Some W_8c6ac.
Proof. vm_refl. Qed.
Lemma D_8c6ac : decode_any W_8c6ac = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6b0 : bv 32 := 0x55555637.
Lemma F_8c6b0 : fetch_word AsanUbsan.M.loaded_segments (0x8cac8 : word) = Some W_8c6b0.
Proof. vm_refl. Qed.
Lemma D_8c6b0 : decode_any W_8c6b0 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6b4 : bv 32 := 0x333336b7.
Lemma F_8c6b4 : fetch_word AsanUbsan.M.loaded_segments (0x8cacc : word) = Some W_8c6b4.
Proof. vm_refl. Qed.
Lemma D_8c6b4 : decode_any W_8c6b4 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6b8 : bv 32 := 0x0f0f1737.
Lemma F_8c6b8 : fetch_word AsanUbsan.M.loaded_segments (0x8cad0 : word) = Some W_8c6b8.
Proof. vm_refl. Qed.
Lemma D_8c6b8 : decode_any W_8c6b8 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6bc : bv 32 := 0x010107b7.
Lemma F_8c6bc : fetch_word AsanUbsan.M.loaded_segments (0x8cad4 : word) = Some W_8c6bc.
Proof. vm_refl. Qed.
Lemma D_8c6bc : decode_any W_8c6bc = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6c0 : bv 32 := 0x00b56533.
Lemma F_8c6c0 : fetch_word AsanUbsan.M.loaded_segments (0x8cad8 : word) = Some W_8c6c0.
Proof. vm_refl. Qed.
Lemma D_8c6c0 : decode_any W_8c6c0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6c4 : bv 32 := 0x5556059b.
Lemma F_8c6c4 : fetch_word AsanUbsan.M.loaded_segments (0x8cadc : word) = Some W_8c6c4.
Proof. vm_refl. Qed.
Lemma D_8c6c4 : decode_any W_8c6c4 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6c8 : bv 32 := 0x3336861b.
Lemma F_8c6c8 : fetch_word AsanUbsan.M.loaded_segments (0x8cae0 : word) = Some W_8c6c8.
Proof. vm_refl. Qed.
Lemma D_8c6c8 : decode_any W_8c6c8 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6cc : bv 32 := 0xf0f7069b.
Lemma F_8c6cc : fetch_word AsanUbsan.M.loaded_segments (0x8cae4 : word) = Some W_8c6cc.
Proof. vm_refl. Qed.
Lemma D_8c6cc : decode_any W_8c6cc = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6d0 : bv 32 := 0x1017871b.
Lemma F_8c6d0 : fetch_word AsanUbsan.M.loaded_segments (0x8cae8 : word) = Some W_8c6d0.
Proof. vm_refl. Qed.
Lemma D_8c6d0 : decode_any W_8c6d0 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6d4 : bv 32 := 0x00255793.
Lemma F_8c6d4 : fetch_word AsanUbsan.M.loaded_segments (0x8caec : word) = Some W_8c6d4.
Proof. vm_refl. Qed.
Lemma D_8c6d4 : decode_any W_8c6d4 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6d8 : bv 32 := 0x00f56533.
Lemma F_8c6d8 : fetch_word AsanUbsan.M.loaded_segments (0x8caf0 : word) = Some W_8c6d8.
Proof. vm_refl. Qed.
Lemma D_8c6d8 : decode_any W_8c6d8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6dc : bv 32 := 0x02059793.
Lemma F_8c6dc : fetch_word AsanUbsan.M.loaded_segments (0x8caf4 : word) = Some W_8c6dc.
Proof. vm_refl. Qed.
Lemma D_8c6dc : decode_any W_8c6dc = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6e0 : bv 32 := 0x00f585b3.
Lemma F_8c6e0 : fetch_word AsanUbsan.M.loaded_segments (0x8caf8 : word) = Some W_8c6e0.
Proof. vm_refl. Qed.
Lemma D_8c6e0 : decode_any W_8c6e0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6e4 : bv 32 := 0x02061793.
Lemma F_8c6e4 : fetch_word AsanUbsan.M.loaded_segments (0x8cafc : word) = Some W_8c6e4.
Proof. vm_refl. Qed.
Lemma D_8c6e4 : decode_any W_8c6e4 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6e8 : bv 32 := 0x00f60633.
Lemma F_8c6e8 : fetch_word AsanUbsan.M.loaded_segments (0x8cb00 : word) = Some W_8c6e8.
Proof. vm_refl. Qed.
Lemma D_8c6e8 : decode_any W_8c6e8 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6ec : bv 32 := 0x02069793.
Lemma F_8c6ec : fetch_word AsanUbsan.M.loaded_segments (0x8cb04 : word) = Some W_8c6ec.
Proof. vm_refl. Qed.
Lemma D_8c6ec : decode_any W_8c6ec = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6f0 : bv 32 := 0x00f686b3.
Lemma F_8c6f0 : fetch_word AsanUbsan.M.loaded_segments (0x8cb08 : word) = Some W_8c6f0.
Proof. vm_refl. Qed.
Lemma D_8c6f0 : decode_any W_8c6f0 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6f4 : bv 32 := 0x02071793.
Lemma F_8c6f4 : fetch_word AsanUbsan.M.loaded_segments (0x8cb0c : word) = Some W_8c6f4.
Proof. vm_refl. Qed.
Lemma D_8c6f4 : decode_any W_8c6f4 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6f8 : bv 32 := 0x00f70733.
Lemma F_8c6f8 : fetch_word AsanUbsan.M.loaded_segments (0x8cb10 : word) = Some W_8c6f8.
Proof. vm_refl. Qed.
Lemma D_8c6f8 : decode_any W_8c6f8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c6fc : bv 32 := 0x00455793.
Lemma F_8c6fc : fetch_word AsanUbsan.M.loaded_segments (0x8cb14 : word) = Some W_8c6fc.
Proof. vm_refl. Qed.
Lemma D_8c6fc : decode_any W_8c6fc = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c700 : bv 32 := 0x00f56533.
Lemma F_8c700 : fetch_word AsanUbsan.M.loaded_segments (0x8cb18 : word) = Some W_8c700.
Proof. vm_refl. Qed.
Lemma D_8c700 : decode_any W_8c700 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c704 : bv 32 := 0x00855793.
Lemma F_8c704 : fetch_word AsanUbsan.M.loaded_segments (0x8cb1c : word) = Some W_8c704.
Proof. vm_refl. Qed.
Lemma D_8c704 : decode_any W_8c704 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c708 : bv 32 := 0x00f56533.
Lemma F_8c708 : fetch_word AsanUbsan.M.loaded_segments (0x8cb20 : word) = Some W_8c708.
Proof. vm_refl. Qed.
Lemma D_8c708 : decode_any W_8c708 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c70c : bv 32 := 0x01055793.
Lemma F_8c70c : fetch_word AsanUbsan.M.loaded_segments (0x8cb24 : word) = Some W_8c70c.
Proof. vm_refl. Qed.
Lemma D_8c70c : decode_any W_8c70c = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c710 : bv 32 := 0x00f56533.
Lemma F_8c710 : fetch_word AsanUbsan.M.loaded_segments (0x8cb28 : word) = Some W_8c710.
Proof. vm_refl. Qed.
Lemma D_8c710 : decode_any W_8c710 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c714 : bv 32 := 0x02055793.
Lemma F_8c714 : fetch_word AsanUbsan.M.loaded_segments (0x8cb2c : word) = Some W_8c714.
Proof. vm_refl. Qed.
Lemma D_8c714 : decode_any W_8c714 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c718 : bv 32 := 0x00f56533.
Lemma F_8c718 : fetch_word AsanUbsan.M.loaded_segments (0x8cb30 : word) = Some W_8c718.
Proof. vm_refl. Qed.
Lemma D_8c718 : decode_any W_8c718 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c71c : bv 32 := 0xfff54513.
Lemma F_8c71c : fetch_word AsanUbsan.M.loaded_segments (0x8cb34 : word) = Some W_8c71c.
Proof. vm_refl. Qed.
Lemma D_8c71c : decode_any W_8c71c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c720 : bv 32 := 0x00155793.
Lemma F_8c720 : fetch_word AsanUbsan.M.loaded_segments (0x8cb38 : word) = Some W_8c720.
Proof. vm_refl. Qed.
Lemma D_8c720 : decode_any W_8c720 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c724 : bv 32 := 0x00b7f5b3.
Lemma F_8c724 : fetch_word AsanUbsan.M.loaded_segments (0x8cb3c : word) = Some W_8c724.
Proof. vm_refl. Qed.
Lemma D_8c724 : decode_any W_8c724 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c728 : bv 32 := 0x40b50533.
Lemma F_8c728 : fetch_word AsanUbsan.M.loaded_segments (0x8cb40 : word) = Some W_8c728.
Proof. vm_refl. Qed.
Lemma D_8c728 : decode_any W_8c728 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c72c : bv 32 := 0x00c575b3.
Lemma F_8c72c : fetch_word AsanUbsan.M.loaded_segments (0x8cb44 : word) = Some W_8c72c.
Proof. vm_refl. Qed.
Lemma D_8c72c : decode_any W_8c72c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c730 : bv 32 := 0x00255513.
Lemma F_8c730 : fetch_word AsanUbsan.M.loaded_segments (0x8cb48 : word) = Some W_8c730.
Proof. vm_refl. Qed.
Lemma D_8c730 : decode_any W_8c730 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c734 : bv 32 := 0x00c57533.
Lemma F_8c734 : fetch_word AsanUbsan.M.loaded_segments (0x8cb4c : word) = Some W_8c734.
Proof. vm_refl. Qed.
Lemma D_8c734 : decode_any W_8c734 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c738 : bv 32 := 0x00a58533.
Lemma F_8c738 : fetch_word AsanUbsan.M.loaded_segments (0x8cb50 : word) = Some W_8c738.
Proof. vm_refl. Qed.
Lemma D_8c738 : decode_any W_8c738 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c73c : bv 32 := 0x00455593.
Lemma F_8c73c : fetch_word AsanUbsan.M.loaded_segments (0x8cb54 : word) = Some W_8c73c.
Proof. vm_refl. Qed.
Lemma D_8c73c : decode_any W_8c73c = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c740 : bv 32 := 0x00b50533.
Lemma F_8c740 : fetch_word AsanUbsan.M.loaded_segments (0x8cb58 : word) = Some W_8c740.
Proof. vm_refl. Qed.
Lemma D_8c740 : decode_any W_8c740 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c744 : bv 32 := 0x00d57533.
Lemma F_8c744 : fetch_word AsanUbsan.M.loaded_segments (0x8cb5c : word) = Some W_8c744.
Proof. vm_refl. Qed.
Lemma D_8c744 : decode_any W_8c744 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c748 : bv 32 := 0x02e50533.
Lemma F_8c748 : fetch_word AsanUbsan.M.loaded_segments (0x8cb60 : word) = Some W_8c748.
Proof. vm_refl. Qed.
Lemma D_8c748 : decode_any W_8c748 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c74c : bv 32 := 0x03855513.
Lemma F_8c74c : fetch_word AsanUbsan.M.loaded_segments (0x8cb64 : word) = Some W_8c74c.
Proof. vm_refl. Qed.
Lemma D_8c74c : decode_any W_8c74c = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c750 : bv 32 := 0x40a0053b.
Lemma F_8c750 : fetch_word AsanUbsan.M.loaded_segments (0x8cb68 : word) = Some W_8c750.
Proof. vm_refl. Qed.
Lemma D_8c750 : decode_any W_8c750 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c754 : bv 32 := 0xfff00593.
Lemma F_8c754 : fetch_word AsanUbsan.M.loaded_segments (0x8cb6c : word) = Some W_8c754.
Proof. vm_refl. Qed.
Lemma D_8c754 : decode_any W_8c754 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c758 : bv 32 := 0x00a59533.
Lemma F_8c758 : fetch_word AsanUbsan.M.loaded_segments (0x8cb70 : word) = Some W_8c758.
Proof. vm_refl. Qed.
Lemma D_8c758 : decode_any W_8c758 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c75c : bv 32 := 0xfff54513.
Lemma F_8c75c : fetch_word AsanUbsan.M.loaded_segments (0x8cb74 : word) = Some W_8c75c.
Proof. vm_refl. Qed.
Lemma D_8c75c : decode_any W_8c75c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
