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
Definition W_64c68 : bv 32 := 0x060a0063.
Lemma F_64c68 : fetch_word AsanUbsan.M.loaded_segments (0x65080 : word) = Some W_64c68.
Proof. vm_refl. Qed.
Lemma D_64c68 : decode_any W_64c68 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c6c : bv 32 := 0x0a051c63.
Lemma F_64c6c : fetch_word AsanUbsan.M.loaded_segments (0x65084 : word) = Some W_64c6c.
Proof. vm_refl. Qed.
Lemma D_64c6c : decode_any W_64c6c = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c80 : bv 32 := 0xfbf48593.
Lemma F_64c80 : fetch_word AsanUbsan.M.loaded_segments (0x65098 : word) = Some W_64c80.
Proof. vm_refl. Qed.
Lemma D_64c80 : decode_any W_64c80 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c84 : bv 32 := 0xfbf00613.
Lemma F_64c84 : fetch_word AsanUbsan.M.loaded_segments (0x6509c : word) = Some W_64c84.
Proof. vm_refl. Qed.
Lemma D_64c84 : decode_any W_64c84 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c88 : bv 32 := 0x12b67663.
Lemma F_64c88 : fetch_word AsanUbsan.M.loaded_segments (0x650a0 : word) = Some W_64c88.
Proof. vm_refl. Qed.
Lemma D_64c88 : decode_any W_64c88 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c8c : bv 32 := 0x000d2597.
Lemma F_64c8c : fetch_word AsanUbsan.M.loaded_segments (0x650a4 : word) = Some W_64c8c.
Proof. vm_refl. Qed.
Lemma D_64c8c : decode_any W_64c8c = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c90 : bv 32 := 0x41c5b583.
Lemma F_64c90 : fetch_word AsanUbsan.M.loaded_segments (0x650a8 : word) = Some W_64c90.
Proof. vm_refl. Qed.
Lemma D_64c90 : decode_any W_64c90 = Some (Load SZ8 true 11 11 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c94 : bv 32 := 0x009906b3.
Lemma F_64c94 : fetch_word AsanUbsan.M.loaded_segments (0x650ac : word) = Some W_64c94.
Proof. vm_refl. Qed.
Lemma D_64c94 : decode_any W_64c94 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c98 : bv 32 := 0x0005b603.
Lemma F_64c98 : fetch_word AsanUbsan.M.loaded_segments (0x650b0 : word) = Some W_64c98.
Proof. vm_refl. Qed.
Lemma D_64c98 : decode_any W_64c98 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c9c : bv 32 := 0x00395593.
Lemma F_64c9c : fetch_word AsanUbsan.M.loaded_segments (0x650b4 : word) = Some W_64c9c.
Proof. vm_refl. Qed.
Lemma D_64c9c : decode_any W_64c9c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca0 : bv 32 := 0xfff68693.
Lemma F_64ca0 : fetch_word AsanUbsan.M.loaded_segments (0x650b8 : word) = Some W_64ca0.
Proof. vm_refl. Qed.
Lemma D_64ca0 : decode_any W_64ca0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca4 : bv 32 := 0x0036d713.
Lemma F_64ca4 : fetch_word AsanUbsan.M.loaded_segments (0x650bc : word) = Some W_64ca4.
Proof. vm_refl. Qed.
Lemma D_64ca4 : decode_any W_64ca4 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca8 : bv 32 := 0x00b605b3.
Lemma F_64ca8 : fetch_word AsanUbsan.M.loaded_segments (0x650c0 : word) = Some W_64ca8.
Proof. vm_refl. Qed.
Lemma D_64ca8 : decode_any W_64ca8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cac : bv 32 := 0x00e60633.
Lemma F_64cac : fetch_word AsanUbsan.M.loaded_segments (0x650c4 : word) = Some W_64cac.
Proof. vm_refl. Qed.
Lemma D_64cac : decode_any W_64cac = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb0 : bv 32 := 0xff85f713.
Lemma F_64cb0 : fetch_word AsanUbsan.M.loaded_segments (0x650c8 : word) = Some W_64cb0.
Proof. vm_refl. Qed.
Lemma D_64cb0 : decode_any W_64cb0 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb4 : bv 32 := 0xff867793.
Lemma F_64cb4 : fetch_word AsanUbsan.M.loaded_segments (0x650cc : word) = Some W_64cb4.
Proof. vm_refl. Qed.
Lemma D_64cb4 : decode_any W_64cb4 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb8 : bv 32 := 0x00073703.
Lemma F_64cb8 : fetch_word AsanUbsan.M.loaded_segments (0x650d0 : word) = Some W_64cb8.
Proof. vm_refl. Qed.
Lemma D_64cb8 : decode_any W_64cb8 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cbc : bv 32 := 0x0007b783.
Lemma F_64cbc : fetch_word AsanUbsan.M.loaded_segments (0x650d4 : word) = Some W_64cbc.
Proof. vm_refl. Qed.
Lemma D_64cbc : decode_any W_64cbc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc0 : bv 32 := 0x00e7e733.
Lemma F_64cc0 : fetch_word AsanUbsan.M.loaded_segments (0x650d8 : word) = Some W_64cc0.
Proof. vm_refl. Qed.
Lemma D_64cc0 : decode_any W_64cc0 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc4 : bv 32 := 0x0e071c63.
Lemma F_64cc4 : fetch_word AsanUbsan.M.loaded_segments (0x650dc : word) = Some W_64cc4.
Proof. vm_refl. Qed.
Lemma D_64cc4 : decode_any W_64cc4 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d24 : bv 32 := 0x412504b3.
Lemma F_64d24 : fetch_word AsanUbsan.M.loaded_segments (0x6513c : word) = Some W_64d24.
Proof. vm_refl. Qed.
Lemma D_64d24 : decode_any W_64d24 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d28 : bv 32 := 0x00148493.
Lemma F_64d28 : fetch_word AsanUbsan.M.loaded_segments (0x65140 : word) = Some W_64d28.
Proof. vm_refl. Qed.
Lemma D_64d28 : decode_any W_64d28 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d2c : bv 32 := 0xfff94593.
Lemma F_64d2c : fetch_word AsanUbsan.M.loaded_segments (0x65144 : word) = Some W_64d2c.
Proof. vm_refl. Qed.
Lemma D_64d2c : decode_any W_64d2c = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d30 : bv 32 := 0x80040a13.
Lemma F_64d30 : fetch_word AsanUbsan.M.loaded_segments (0x65148 : word) = Some W_64d30.
Proof. vm_refl. Qed.
Lemma D_64d30 : decode_any W_64d30 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d34 : bv 32 := 0xfb0a0a13.
Lemma F_64d34 : fetch_word AsanUbsan.M.loaded_segments (0x6514c : word) = Some W_64d34.
Proof. vm_refl. Qed.
Lemma D_64d34 : decode_any W_64d34 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64d38 : bv 32 := 0xf495f4e3.
Lemma F_64d38 : fetch_word AsanUbsan.M.loaded_segments (0x65150 : word) = Some W_64d38.
Proof. vm_refl. Qed.
Lemma D_64d38 : decode_any W_64d38 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64db4 : bv 32 := 0x02049e63.
Lemma F_64db4 : fetch_word AsanUbsan.M.loaded_segments (0x651cc : word) = Some W_64db4.
Proof. vm_refl. Qed.
Lemma D_64db4 : decode_any W_64db4 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64df0 : bv 32 := 0x00050a93.
Lemma F_64df0 : fetch_word AsanUbsan.M.loaded_segments (0x65208 : word) = Some W_64df0.
Proof. vm_refl. Qed.
Lemma D_64df0 : decode_any W_64df0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64df4 : bv 32 := 0x00090513.
Lemma F_64df4 : fetch_word AsanUbsan.M.loaded_segments (0x6520c : word) = Some W_64df4.
Proof. vm_refl. Qed.
Lemma D_64df4 : decode_any W_64df4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64df8 : bv 32 := 0x00048593.
Lemma F_64df8 : fetch_word AsanUbsan.M.loaded_segments (0x65210 : word) = Some W_64df8.
Proof. vm_refl. Qed.
Lemma D_64df8 : decode_any W_64df8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64dfc : bv 32 := 0x2ac160ef.
Lemma F_64dfc : fetch_word AsanUbsan.M.loaded_segments (0x65214 : word) = Some W_64dfc.
Proof. vm_refl. Qed.
Lemma D_64dfc : decode_any W_64dfc = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e00 : bv 32 := 0x00050913.
Lemma F_64e00 : fetch_word AsanUbsan.M.loaded_segments (0x65218 : word) = Some W_64e00.
Proof. vm_refl. Qed.
Lemma D_64e00 : decode_any W_64e00 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e04 : bv 32 := 0x000a8513.
Lemma F_64e04 : fetch_word AsanUbsan.M.loaded_segments (0x6521c : word) = Some W_64e04.
Proof. vm_refl. Qed.
Lemma D_64e04 : decode_any W_64e04 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64e08 : bv 32 := 0xec0900e3.
Lemma F_64e08 : fetch_word AsanUbsan.M.loaded_segments (0x65220 : word) = Some W_64e08.
Proof. vm_refl. Qed.
Lemma D_64e08 : decode_any W_64e08 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.
