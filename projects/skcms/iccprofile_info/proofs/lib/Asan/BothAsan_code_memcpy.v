(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_98c4c : bv 32 := 0x0035f693.
Lemma F_98c4c : fetch_word AsanUbsan.M.loaded_segments (0x98c4c : word) = Some W_98c4c.
Proof. vm_refl. Qed.
Lemma D_98c4c : decode_any W_98c4c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c50 : bv 32 := 0x10068863.
Lemma F_98c50 : fetch_word AsanUbsan.M.loaded_segments (0x98c50 : word) = Some W_98c50.
Proof. vm_refl. Qed.
Lemma D_98c50 : decode_any W_98c50 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c54 : bv 32 := 0x02060e63.
Lemma F_98c54 : fetch_word AsanUbsan.M.loaded_segments (0x98c54 : word) = Some W_98c54.
Proof. vm_refl. Qed.
Lemma D_98c54 : decode_any W_98c54 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c58 : bv 32 := 0x00158713.
Lemma F_98c58 : fetch_word AsanUbsan.M.loaded_segments (0x98c58 : word) = Some W_98c58.
Proof. vm_refl. Qed.
Lemma D_98c58 : decode_any W_98c58 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c5c : bv 32 := 0x00100793.
Lemma F_98c5c : fetch_word AsanUbsan.M.loaded_segments (0x98c5c : word) = Some W_98c5c.
Proof. vm_refl. Qed.
Lemma D_98c5c : decode_any W_98c5c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c60 : bv 32 := 0x00050693.
Lemma F_98c60 : fetch_word AsanUbsan.M.loaded_segments (0x98c60 : word) = Some W_98c60.
Proof. vm_refl. Qed.
Lemma D_98c60 : decode_any W_98c60 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c64 : bv 32 := 0x0005c883.
Lemma F_98c64 : fetch_word AsanUbsan.M.loaded_segments (0x98c64 : word) = Some W_98c64.
Proof. vm_refl. Qed.
Lemma D_98c64 : decode_any W_98c64 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c68 : bv 32 := 0x00060813.
Lemma F_98c68 : fetch_word AsanUbsan.M.loaded_segments (0x98c68 : word) = Some W_98c68.
Proof. vm_refl. Qed.
Lemma D_98c68 : decode_any W_98c68 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c6c : bv 32 := 0x00158593.
Lemma F_98c6c : fetch_word AsanUbsan.M.loaded_segments (0x98c6c : word) = Some W_98c6c.
Proof. vm_refl. Qed.
Lemma D_98c6c : decode_any W_98c6c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c70 : bv 32 := 0x00377293.
Lemma F_98c70 : fetch_word AsanUbsan.M.loaded_segments (0x98c70 : word) = Some W_98c70.
Proof. vm_refl. Qed.
Lemma D_98c70 : decode_any W_98c70 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c74 : bv 32 := 0x01168023.
Lemma F_98c74 : fetch_word AsanUbsan.M.loaded_segments (0x98c74 : word) = Some W_98c74.
Proof. vm_refl. Qed.
Lemma D_98c74 : decode_any W_98c74 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c78 : bv 32 := 0x00168693.
Lemma F_98c78 : fetch_word AsanUbsan.M.loaded_segments (0x98c78 : word) = Some W_98c78.
Proof. vm_refl. Qed.
Lemma D_98c78 : decode_any W_98c78 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c7c : bv 32 := 0xfff60613.
Lemma F_98c7c : fetch_word AsanUbsan.M.loaded_segments (0x98c7c : word) = Some W_98c7c.
Proof. vm_refl. Qed.
Lemma D_98c7c : decode_any W_98c7c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c80 : bv 32 := 0x00028a63.
Lemma F_98c80 : fetch_word AsanUbsan.M.loaded_segments (0x98c80 : word) = Some W_98c80.
Proof. vm_refl. Qed.
Lemma D_98c80 : decode_any W_98c80 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c84 : bv 32 := 0x00170713.
Lemma F_98c84 : fetch_word AsanUbsan.M.loaded_segments (0x98c84 : word) = Some W_98c84.
Proof. vm_refl. Qed.
Lemma D_98c84 : decode_any W_98c84 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c88 : bv 32 := 0xfcf81ee3.
Lemma F_98c88 : fetch_word AsanUbsan.M.loaded_segments (0x98c88 : word) = Some W_98c88.
Proof. vm_refl. Qed.
Lemma D_98c88 : decode_any W_98c88 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c8c : bv 32 := 0x0080006f.
Lemma F_98c8c : fetch_word AsanUbsan.M.loaded_segments (0x98c8c : word) = Some W_98c8c.
Proof. vm_refl. Qed.
Lemma D_98c8c : decode_any W_98c8c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c90 : bv 32 := 0x00050693.
Lemma F_98c90 : fetch_word AsanUbsan.M.loaded_segments (0x98c90 : word) = Some W_98c90.
Proof. vm_refl. Qed.
Lemma D_98c90 : decode_any W_98c90 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c94 : bv 32 := 0x0036f793.
Lemma F_98c94 : fetch_word AsanUbsan.M.loaded_segments (0x98c94 : word) = Some W_98c94.
Proof. vm_refl. Qed.
Lemma D_98c94 : decode_any W_98c94 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c98 : bv 32 := 0x0c078a63.
Lemma F_98c98 : fetch_word AsanUbsan.M.loaded_segments (0x98c98 : word) = Some W_98c98.
Proof. vm_refl. Qed.
Lemma D_98c98 : decode_any W_98c98 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c9c : bv 32 := 0x02000713.
Lemma F_98c9c : fetch_word AsanUbsan.M.loaded_segments (0x98c9c : word) = Some W_98c9c.
Proof. vm_refl. Qed.
Lemma D_98c9c : decode_any W_98c9c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ca0 : bv 32 := 0x02e67063.
Lemma F_98ca0 : fetch_word AsanUbsan.M.loaded_segments (0x98ca0 : word) = Some W_98ca0.
Proof. vm_refl. Qed.
Lemma D_98ca0 : decode_any W_98ca0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ca4 : bv 32 := 0x01000713.
Lemma F_98ca4 : fetch_word AsanUbsan.M.loaded_segments (0x98ca4 : word) = Some W_98ca4.
Proof. vm_refl. Qed.
Lemma D_98ca4 : decode_any W_98ca4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ca8 : bv 32 := 0x24e67863.
Lemma F_98ca8 : fetch_word AsanUbsan.M.loaded_segments (0x98ca8 : word) = Some W_98ca8.
Proof. vm_refl. Qed.
Lemma D_98ca8 : decode_any W_98ca8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cac : bv 32 := 0x00867713.
Lemma F_98cac : fetch_word AsanUbsan.M.loaded_segments (0x98cac : word) = Some W_98cac.
Proof. vm_refl. Qed.
Lemma D_98cac : decode_any W_98cac = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb0 : bv 32 := 0x2c071e63.
Lemma F_98cb0 : fetch_word AsanUbsan.M.loaded_segments (0x98cb0 : word) = Some W_98cb0.
Proof. vm_refl. Qed.
Lemma D_98cb0 : decode_any W_98cb0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb4 : bv 32 := 0x00467713.
Lemma F_98cb4 : fetch_word AsanUbsan.M.loaded_segments (0x98cb4 : word) = Some W_98cb4.
Proof. vm_refl. Qed.
Lemma D_98cb4 : decode_any W_98cb4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cb8 : bv 32 := 0x32071463.
Lemma F_98cb8 : fetch_word AsanUbsan.M.loaded_segments (0x98cb8 : word) = Some W_98cb8.
Proof. vm_refl. Qed.
Lemma D_98cb8 : decode_any W_98cb8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cbc : bv 32 := 0x3500006f.
Lemma F_98cbc : fetch_word AsanUbsan.M.loaded_segments (0x98cbc : word) = Some W_98cbc.
Proof. vm_refl. Qed.
Lemma D_98cbc : decode_any W_98cbc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cc0 : bv 32 := 0x0005a703.
Lemma F_98cc0 : fetch_word AsanUbsan.M.loaded_segments (0x98cc0 : word) = Some W_98cc0.
Proof. vm_refl. Qed.
Lemma D_98cc0 : decode_any W_98cc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cc4 : bv 32 := 0x00300813.
Lemma F_98cc4 : fetch_word AsanUbsan.M.loaded_segments (0x98cc4 : word) = Some W_98cc4.
Proof. vm_refl. Qed.
Lemma D_98cc4 : decode_any W_98cc4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cc8 : bv 32 := 0x11078e63.
Lemma F_98cc8 : fetch_word AsanUbsan.M.loaded_segments (0x98cc8 : word) = Some W_98cc8.
Proof. vm_refl. Qed.
Lemma D_98cc8 : decode_any W_98cc8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ccc : bv 32 := 0x00200813.
Lemma F_98ccc : fetch_word AsanUbsan.M.loaded_segments (0x98ccc : word) = Some W_98ccc.
Proof. vm_refl. Qed.
Lemma D_98ccc : decode_any W_98ccc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd0 : bv 32 := 0x19079c63.
Lemma F_98cd0 : fetch_word AsanUbsan.M.loaded_segments (0x98cd0 : word) = Some W_98cd0.
Proof. vm_refl. Qed.
Lemma D_98cd0 : decode_any W_98cd0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd4 : bv 32 := 0x00875793.
Lemma F_98cd4 : fetch_word AsanUbsan.M.loaded_segments (0x98cd4 : word) = Some W_98cd4.
Proof. vm_refl. Qed.
Lemma D_98cd4 : decode_any W_98cd4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cd8 : bv 32 := 0xffe60613.
Lemma F_98cd8 : fetch_word AsanUbsan.M.loaded_segments (0x98cd8 : word) = Some W_98cd8.
Proof. vm_refl. Qed.
Lemma D_98cd8 : decode_any W_98cd8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cdc : bv 32 := 0x00e68023.
Lemma F_98cdc : fetch_word AsanUbsan.M.loaded_segments (0x98cdc : word) = Some W_98cdc.
Proof. vm_refl. Qed.
Lemma D_98cdc : decode_any W_98cdc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce0 : bv 32 := 0x00f680a3.
Lemma F_98ce0 : fetch_word AsanUbsan.M.loaded_segments (0x98ce0 : word) = Some W_98ce0.
Proof. vm_refl. Qed.
Lemma D_98ce0 : decode_any W_98ce0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce4 : bv 32 := 0x00268693.
Lemma F_98ce4 : fetch_word AsanUbsan.M.loaded_segments (0x98ce4 : word) = Some W_98ce4.
Proof. vm_refl. Qed.
Lemma D_98ce4 : decode_any W_98ce4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ce8 : bv 32 := 0x01058593.
Lemma F_98ce8 : fetch_word AsanUbsan.M.loaded_segments (0x98ce8 : word) = Some W_98ce8.
Proof. vm_refl. Qed.
Lemma D_98ce8 : decode_any W_98ce8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cec : bv 32 := 0x01100793.
Lemma F_98cec : fetch_word AsanUbsan.M.loaded_segments (0x98cec : word) = Some W_98cec.
Proof. vm_refl. Qed.
Lemma D_98cec : decode_any W_98cec = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cf0 : bv 32 := 0x0107581b.
Lemma F_98cf0 : fetch_word AsanUbsan.M.loaded_segments (0x98cf0 : word) = Some W_98cf0.
Proof. vm_refl. Qed.
Lemma D_98cf0 : decode_any W_98cf0 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cf4 : bv 32 := 0xff45a883.
Lemma F_98cf4 : fetch_word AsanUbsan.M.loaded_segments (0x98cf4 : word) = Some W_98cf4.
Proof. vm_refl. Qed.
Lemma D_98cf4 : decode_any W_98cf4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cf8 : bv 32 := 0xff85a283.
Lemma F_98cf8 : fetch_word AsanUbsan.M.loaded_segments (0x98cf8 : word) = Some W_98cf8.
Proof. vm_refl. Qed.
Lemma D_98cf8 : decode_any W_98cf8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98cfc : bv 32 := 0xffc5a303.
Lemma F_98cfc : fetch_word AsanUbsan.M.loaded_segments (0x98cfc : word) = Some W_98cfc.
Proof. vm_refl. Qed.
Lemma D_98cfc : decode_any W_98cfc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d00 : bv 32 := 0x0005a703.
Lemma F_98d00 : fetch_word AsanUbsan.M.loaded_segments (0x98d00 : word) = Some W_98d00.
Proof. vm_refl. Qed.
Lemma D_98d00 : decode_any W_98d00 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d04 : bv 32 := 0x01089393.
Lemma F_98d04 : fetch_word AsanUbsan.M.loaded_segments (0x98d04 : word) = Some W_98d04.
Proof. vm_refl. Qed.
Lemma D_98d04 : decode_any W_98d04 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d08 : bv 32 := 0x0108d89b.
Lemma F_98d08 : fetch_word AsanUbsan.M.loaded_segments (0x98d08 : word) = Some W_98d08.
Proof. vm_refl. Qed.
Lemma D_98d08 : decode_any W_98d08 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d0c : bv 32 := 0x0103e833.
Lemma F_98d0c : fetch_word AsanUbsan.M.loaded_segments (0x98d0c : word) = Some W_98d0c.
Proof. vm_refl. Qed.
Lemma D_98d0c : decode_any W_98d0c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d10 : bv 32 := 0x01029393.
Lemma F_98d10 : fetch_word AsanUbsan.M.loaded_segments (0x98d10 : word) = Some W_98d10.
Proof. vm_refl. Qed.
Lemma D_98d10 : decode_any W_98d10 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d14 : bv 32 := 0x0102d29b.
Lemma F_98d14 : fetch_word AsanUbsan.M.loaded_segments (0x98d14 : word) = Some W_98d14.
Proof. vm_refl. Qed.
Lemma D_98d14 : decode_any W_98d14 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d18 : bv 32 := 0x0113e8b3.
Lemma F_98d18 : fetch_word AsanUbsan.M.loaded_segments (0x98d18 : word) = Some W_98d18.
Proof. vm_refl. Qed.
Lemma D_98d18 : decode_any W_98d18 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d1c : bv 32 := 0x01031393.
Lemma F_98d1c : fetch_word AsanUbsan.M.loaded_segments (0x98d1c : word) = Some W_98d1c.
Proof. vm_refl. Qed.
Lemma D_98d1c : decode_any W_98d1c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d20 : bv 32 := 0x0103531b.
Lemma F_98d20 : fetch_word AsanUbsan.M.loaded_segments (0x98d20 : word) = Some W_98d20.
Proof. vm_refl. Qed.
Lemma D_98d20 : decode_any W_98d20 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d24 : bv 32 := 0x0053e2b3.
Lemma F_98d24 : fetch_word AsanUbsan.M.loaded_segments (0x98d24 : word) = Some W_98d24.
Proof. vm_refl. Qed.
Lemma D_98d24 : decode_any W_98d24 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d28 : bv 32 := 0x01071393.
Lemma F_98d28 : fetch_word AsanUbsan.M.loaded_segments (0x98d28 : word) = Some W_98d28.
Proof. vm_refl. Qed.
Lemma D_98d28 : decode_any W_98d28 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d2c : bv 32 := 0x0063e333.
Lemma F_98d2c : fetch_word AsanUbsan.M.loaded_segments (0x98d2c : word) = Some W_98d2c.
Proof. vm_refl. Qed.
Lemma D_98d2c : decode_any W_98d2c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d30 : bv 32 := 0xff060613.
Lemma F_98d30 : fetch_word AsanUbsan.M.loaded_segments (0x98d30 : word) = Some W_98d30.
Proof. vm_refl. Qed.
Lemma D_98d30 : decode_any W_98d30 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d34 : bv 32 := 0x0106a023.
Lemma F_98d34 : fetch_word AsanUbsan.M.loaded_segments (0x98d34 : word) = Some W_98d34.
Proof. vm_refl. Qed.
Lemma D_98d34 : decode_any W_98d34 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d38 : bv 32 := 0x0116a223.
Lemma F_98d38 : fetch_word AsanUbsan.M.loaded_segments (0x98d38 : word) = Some W_98d38.
Proof. vm_refl. Qed.
Lemma D_98d38 : decode_any W_98d38 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d3c : bv 32 := 0x0056a423.
Lemma F_98d3c : fetch_word AsanUbsan.M.loaded_segments (0x98d3c : word) = Some W_98d3c.
Proof. vm_refl. Qed.
Lemma D_98d3c : decode_any W_98d3c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d40 : bv 32 := 0x0066a623.
Lemma F_98d40 : fetch_word AsanUbsan.M.loaded_segments (0x98d40 : word) = Some W_98d40.
Proof. vm_refl. Qed.
Lemma D_98d40 : decode_any W_98d40 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d44 : bv 32 := 0x01068693.
Lemma F_98d44 : fetch_word AsanUbsan.M.loaded_segments (0x98d44 : word) = Some W_98d44.
Proof. vm_refl. Qed.
Lemma D_98d44 : decode_any W_98d44 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d48 : bv 32 := 0x01058593.
Lemma F_98d48 : fetch_word AsanUbsan.M.loaded_segments (0x98d48 : word) = Some W_98d48.
Proof. vm_refl. Qed.
Lemma D_98d48 : decode_any W_98d48 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d4c : bv 32 := 0xfac7e2e3.
Lemma F_98d4c : fetch_word AsanUbsan.M.loaded_segments (0x98d4c : word) = Some W_98d4c.
Proof. vm_refl. Qed.
Lemma D_98d4c : decode_any W_98d4c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d50 : bv 32 := 0xff258593.
Lemma F_98d50 : fetch_word AsanUbsan.M.loaded_segments (0x98d50 : word) = Some W_98d50.
Proof. vm_refl. Qed.
Lemma D_98d50 : decode_any W_98d50 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d54 : bv 32 := 0x01000713.
Lemma F_98d54 : fetch_word AsanUbsan.M.loaded_segments (0x98d54 : word) = Some W_98d54.
Proof. vm_refl. Qed.
Lemma D_98d54 : decode_any W_98d54 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d58 : bv 32 := 0xf4e66ae3.
Lemma F_98d58 : fetch_word AsanUbsan.M.loaded_segments (0x98d58 : word) = Some W_98d58.
Proof. vm_refl. Qed.
Lemma D_98d58 : decode_any W_98d58 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d5c : bv 32 := 0x19c0006f.
Lemma F_98d5c : fetch_word AsanUbsan.M.loaded_segments (0x98d5c : word) = Some W_98d5c.
Proof. vm_refl. Qed.
Lemma D_98d5c : decode_any W_98d5c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d60 : bv 32 := 0x00050693.
Lemma F_98d60 : fetch_word AsanUbsan.M.loaded_segments (0x98d60 : word) = Some W_98d60.
Proof. vm_refl. Qed.
Lemma D_98d60 : decode_any W_98d60 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d64 : bv 32 := 0x00357793.
Lemma F_98d64 : fetch_word AsanUbsan.M.loaded_segments (0x98d64 : word) = Some W_98d64.
Proof. vm_refl. Qed.
Lemma D_98d64 : decode_any W_98d64 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d68 : bv 32 := 0xf2079ae3.
Lemma F_98d68 : fetch_word AsanUbsan.M.loaded_segments (0x98d68 : word) = Some W_98d68.
Proof. vm_refl. Qed.
Lemma D_98d68 : decode_any W_98d68 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d6c : bv 32 := 0x01000713.
Lemma F_98d6c : fetch_word AsanUbsan.M.loaded_segments (0x98d6c : word) = Some W_98d6c.
Proof. vm_refl. Qed.
Lemma D_98d6c : decode_any W_98d6c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d70 : bv 32 := 0x02e66c63.
Lemma F_98d70 : fetch_word AsanUbsan.M.loaded_segments (0x98d70 : word) = Some W_98d70.
Proof. vm_refl. Qed.
Lemma D_98d70 : decode_any W_98d70 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d74 : bv 32 := 0x00f00713.
Lemma F_98d74 : fetch_word AsanUbsan.M.loaded_segments (0x98d74 : word) = Some W_98d74.
Proof. vm_refl. Qed.
Lemma D_98d74 : decode_any W_98d74 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d78 : bv 32 := 0x0005a783.
Lemma F_98d78 : fetch_word AsanUbsan.M.loaded_segments (0x98d78 : word) = Some W_98d78.
Proof. vm_refl. Qed.
Lemma D_98d78 : decode_any W_98d78 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d7c : bv 32 := 0x0045a803.
Lemma F_98d7c : fetch_word AsanUbsan.M.loaded_segments (0x98d7c : word) = Some W_98d7c.
Proof. vm_refl. Qed.
Lemma D_98d7c : decode_any W_98d7c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d80 : bv 32 := 0x0085a883.
Lemma F_98d80 : fetch_word AsanUbsan.M.loaded_segments (0x98d80 : word) = Some W_98d80.
Proof. vm_refl. Qed.
Lemma D_98d80 : decode_any W_98d80 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d84 : bv 32 := 0x00c5a283.
Lemma F_98d84 : fetch_word AsanUbsan.M.loaded_segments (0x98d84 : word) = Some W_98d84.
Proof. vm_refl. Qed.
Lemma D_98d84 : decode_any W_98d84 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d88 : bv 32 := 0x01058593.
Lemma F_98d88 : fetch_word AsanUbsan.M.loaded_segments (0x98d88 : word) = Some W_98d88.
Proof. vm_refl. Qed.
Lemma D_98d88 : decode_any W_98d88 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d8c : bv 32 := 0xff060613.
Lemma F_98d8c : fetch_word AsanUbsan.M.loaded_segments (0x98d8c : word) = Some W_98d8c.
Proof. vm_refl. Qed.
Lemma D_98d8c : decode_any W_98d8c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d90 : bv 32 := 0x00f6a023.
Lemma F_98d90 : fetch_word AsanUbsan.M.loaded_segments (0x98d90 : word) = Some W_98d90.
Proof. vm_refl. Qed.
Lemma D_98d90 : decode_any W_98d90 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d94 : bv 32 := 0x0106a223.
Lemma F_98d94 : fetch_word AsanUbsan.M.loaded_segments (0x98d94 : word) = Some W_98d94.
Proof. vm_refl. Qed.
Lemma D_98d94 : decode_any W_98d94 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d98 : bv 32 := 0x0116a423.
Lemma F_98d98 : fetch_word AsanUbsan.M.loaded_segments (0x98d98 : word) = Some W_98d98.
Proof. vm_refl. Qed.
Lemma D_98d98 : decode_any W_98d98 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98d9c : bv 32 := 0x0056a623.
Lemma F_98d9c : fetch_word AsanUbsan.M.loaded_segments (0x98d9c : word) = Some W_98d9c.
Proof. vm_refl. Qed.
Lemma D_98d9c : decode_any W_98d9c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98da0 : bv 32 := 0x01068693.
Lemma F_98da0 : fetch_word AsanUbsan.M.loaded_segments (0x98da0 : word) = Some W_98da0.
Proof. vm_refl. Qed.
Lemma D_98da0 : decode_any W_98da0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98da4 : bv 32 := 0xfcc76ae3.
Lemma F_98da4 : fetch_word AsanUbsan.M.loaded_segments (0x98da4 : word) = Some W_98da4.
Proof. vm_refl. Qed.
Lemma D_98da4 : decode_any W_98da4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98da8 : bv 32 := 0x00800713.
Lemma F_98da8 : fetch_word AsanUbsan.M.loaded_segments (0x98da8 : word) = Some W_98da8.
Proof. vm_refl. Qed.
Lemma D_98da8 : decode_any W_98da8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dac : bv 32 := 0x00e66e63.
Lemma F_98dac : fetch_word AsanUbsan.M.loaded_segments (0x98dac : word) = Some W_98dac.
Proof. vm_refl. Qed.
Lemma D_98dac : decode_any W_98dac = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98db0 : bv 32 := 0x0005a703.
Lemma F_98db0 : fetch_word AsanUbsan.M.loaded_segments (0x98db0 : word) = Some W_98db0.
Proof. vm_refl. Qed.
Lemma D_98db0 : decode_any W_98db0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98db4 : bv 32 := 0x0045a783.
Lemma F_98db4 : fetch_word AsanUbsan.M.loaded_segments (0x98db4 : word) = Some W_98db4.
Proof. vm_refl. Qed.
Lemma D_98db4 : decode_any W_98db4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98db8 : bv 32 := 0x00e6a023.
Lemma F_98db8 : fetch_word AsanUbsan.M.loaded_segments (0x98db8 : word) = Some W_98db8.
Proof. vm_refl. Qed.
Lemma D_98db8 : decode_any W_98db8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dbc : bv 32 := 0x00f6a223.
Lemma F_98dbc : fetch_word AsanUbsan.M.loaded_segments (0x98dbc : word) = Some W_98dbc.
Proof. vm_refl. Qed.
Lemma D_98dbc : decode_any W_98dbc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dc0 : bv 32 := 0x00868693.
Lemma F_98dc0 : fetch_word AsanUbsan.M.loaded_segments (0x98dc0 : word) = Some W_98dc0.
Proof. vm_refl. Qed.
Lemma D_98dc0 : decode_any W_98dc0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dc4 : bv 32 := 0x00858593.
Lemma F_98dc4 : fetch_word AsanUbsan.M.loaded_segments (0x98dc4 : word) = Some W_98dc4.
Proof. vm_refl. Qed.
Lemma D_98dc4 : decode_any W_98dc4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dc8 : bv 32 := 0x00467713.
Lemma F_98dc8 : fetch_word AsanUbsan.M.loaded_segments (0x98dc8 : word) = Some W_98dc8.
Proof. vm_refl. Qed.
Lemma D_98dc8 : decode_any W_98dc8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dcc : bv 32 := 0x24070063.
Lemma F_98dcc : fetch_word AsanUbsan.M.loaded_segments (0x98dcc : word) = Some W_98dcc.
Proof. vm_refl. Qed.
Lemma D_98dcc : decode_any W_98dcc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dd0 : bv 32 := 0x0005a703.
Lemma F_98dd0 : fetch_word AsanUbsan.M.loaded_segments (0x98dd0 : word) = Some W_98dd0.
Proof. vm_refl. Qed.
Lemma D_98dd0 : decode_any W_98dd0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dd4 : bv 32 := 0x00458593.
Lemma F_98dd4 : fetch_word AsanUbsan.M.loaded_segments (0x98dd4 : word) = Some W_98dd4.
Proof. vm_refl. Qed.
Lemma D_98dd4 : decode_any W_98dd4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dd8 : bv 32 := 0x00e6a023.
Lemma F_98dd8 : fetch_word AsanUbsan.M.loaded_segments (0x98dd8 : word) = Some W_98dd8.
Proof. vm_refl. Qed.
Lemma D_98dd8 : decode_any W_98dd8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ddc : bv 32 := 0x00468693.
Lemma F_98ddc : fetch_word AsanUbsan.M.loaded_segments (0x98ddc : word) = Some W_98ddc.
Proof. vm_refl. Qed.
Lemma D_98ddc : decode_any W_98ddc = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98de0 : bv 32 := 0x22c0006f.
Lemma F_98de0 : fetch_word AsanUbsan.M.loaded_segments (0x98de0 : word) = Some W_98de0.
Proof. vm_refl. Qed.
Lemma D_98de0 : decode_any W_98de0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98de4 : bv 32 := 0x00e68023.
Lemma F_98de4 : fetch_word AsanUbsan.M.loaded_segments (0x98de4 : word) = Some W_98de4.
Proof. vm_refl. Qed.
Lemma D_98de4 : decode_any W_98de4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98de8 : bv 32 := 0x00168693.
Lemma F_98de8 : fetch_word AsanUbsan.M.loaded_segments (0x98de8 : word) = Some W_98de8.
Proof. vm_refl. Qed.
Lemma D_98de8 : decode_any W_98de8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dec : bv 32 := 0xfff60613.
Lemma F_98dec : fetch_word AsanUbsan.M.loaded_segments (0x98dec : word) = Some W_98dec.
Proof. vm_refl. Qed.
Lemma D_98dec : decode_any W_98dec = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98df0 : bv 32 := 0x01058593.
Lemma F_98df0 : fetch_word AsanUbsan.M.loaded_segments (0x98df0 : word) = Some W_98df0.
Proof. vm_refl. Qed.
Lemma D_98df0 : decode_any W_98df0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98df4 : bv 32 := 0x01200793.
Lemma F_98df4 : fetch_word AsanUbsan.M.loaded_segments (0x98df4 : word) = Some W_98df4.
Proof. vm_refl. Qed.
Lemma D_98df4 : decode_any W_98df4 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98df8 : bv 32 := 0x0087581b.
Lemma F_98df8 : fetch_word AsanUbsan.M.loaded_segments (0x98df8 : word) = Some W_98df8.
Proof. vm_refl. Qed.
Lemma D_98df8 : decode_any W_98df8 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98dfc : bv 32 := 0xff45a883.
Lemma F_98dfc : fetch_word AsanUbsan.M.loaded_segments (0x98dfc : word) = Some W_98dfc.
Proof. vm_refl. Qed.
Lemma D_98dfc : decode_any W_98dfc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e00 : bv 32 := 0xff85a283.
Lemma F_98e00 : fetch_word AsanUbsan.M.loaded_segments (0x98e00 : word) = Some W_98e00.
Proof. vm_refl. Qed.
Lemma D_98e00 : decode_any W_98e00 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e04 : bv 32 := 0xffc5a303.
Lemma F_98e04 : fetch_word AsanUbsan.M.loaded_segments (0x98e04 : word) = Some W_98e04.
Proof. vm_refl. Qed.
Lemma D_98e04 : decode_any W_98e04 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e08 : bv 32 := 0x0005a703.
Lemma F_98e08 : fetch_word AsanUbsan.M.loaded_segments (0x98e08 : word) = Some W_98e08.
Proof. vm_refl. Qed.
Lemma D_98e08 : decode_any W_98e08 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e0c : bv 32 := 0x01889393.
Lemma F_98e0c : fetch_word AsanUbsan.M.loaded_segments (0x98e0c : word) = Some W_98e0c.
Proof. vm_refl. Qed.
Lemma D_98e0c : decode_any W_98e0c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e10 : bv 32 := 0x0088d89b.
Lemma F_98e10 : fetch_word AsanUbsan.M.loaded_segments (0x98e10 : word) = Some W_98e10.
Proof. vm_refl. Qed.
Lemma D_98e10 : decode_any W_98e10 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e14 : bv 32 := 0x0103e833.
Lemma F_98e14 : fetch_word AsanUbsan.M.loaded_segments (0x98e14 : word) = Some W_98e14.
Proof. vm_refl. Qed.
Lemma D_98e14 : decode_any W_98e14 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e18 : bv 32 := 0x01829393.
Lemma F_98e18 : fetch_word AsanUbsan.M.loaded_segments (0x98e18 : word) = Some W_98e18.
Proof. vm_refl. Qed.
Lemma D_98e18 : decode_any W_98e18 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e1c : bv 32 := 0x0082d29b.
Lemma F_98e1c : fetch_word AsanUbsan.M.loaded_segments (0x98e1c : word) = Some W_98e1c.
Proof. vm_refl. Qed.
Lemma D_98e1c : decode_any W_98e1c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e20 : bv 32 := 0x0113e8b3.
Lemma F_98e20 : fetch_word AsanUbsan.M.loaded_segments (0x98e20 : word) = Some W_98e20.
Proof. vm_refl. Qed.
Lemma D_98e20 : decode_any W_98e20 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e24 : bv 32 := 0x01831393.
Lemma F_98e24 : fetch_word AsanUbsan.M.loaded_segments (0x98e24 : word) = Some W_98e24.
Proof. vm_refl. Qed.
Lemma D_98e24 : decode_any W_98e24 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e28 : bv 32 := 0x0083531b.
Lemma F_98e28 : fetch_word AsanUbsan.M.loaded_segments (0x98e28 : word) = Some W_98e28.
Proof. vm_refl. Qed.
Lemma D_98e28 : decode_any W_98e28 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e2c : bv 32 := 0x0053e2b3.
Lemma F_98e2c : fetch_word AsanUbsan.M.loaded_segments (0x98e2c : word) = Some W_98e2c.
Proof. vm_refl. Qed.
Lemma D_98e2c : decode_any W_98e2c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e30 : bv 32 := 0x01871393.
Lemma F_98e30 : fetch_word AsanUbsan.M.loaded_segments (0x98e30 : word) = Some W_98e30.
Proof. vm_refl. Qed.
Lemma D_98e30 : decode_any W_98e30 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e34 : bv 32 := 0x0063e333.
Lemma F_98e34 : fetch_word AsanUbsan.M.loaded_segments (0x98e34 : word) = Some W_98e34.
Proof. vm_refl. Qed.
Lemma D_98e34 : decode_any W_98e34 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e38 : bv 32 := 0xff060613.
Lemma F_98e38 : fetch_word AsanUbsan.M.loaded_segments (0x98e38 : word) = Some W_98e38.
Proof. vm_refl. Qed.
Lemma D_98e38 : decode_any W_98e38 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e3c : bv 32 := 0x0106a023.
Lemma F_98e3c : fetch_word AsanUbsan.M.loaded_segments (0x98e3c : word) = Some W_98e3c.
Proof. vm_refl. Qed.
Lemma D_98e3c : decode_any W_98e3c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e40 : bv 32 := 0x0116a223.
Lemma F_98e40 : fetch_word AsanUbsan.M.loaded_segments (0x98e40 : word) = Some W_98e40.
Proof. vm_refl. Qed.
Lemma D_98e40 : decode_any W_98e40 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e44 : bv 32 := 0x0056a423.
Lemma F_98e44 : fetch_word AsanUbsan.M.loaded_segments (0x98e44 : word) = Some W_98e44.
Proof. vm_refl. Qed.
Lemma D_98e44 : decode_any W_98e44 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e48 : bv 32 := 0x0066a623.
Lemma F_98e48 : fetch_word AsanUbsan.M.loaded_segments (0x98e48 : word) = Some W_98e48.
Proof. vm_refl. Qed.
Lemma D_98e48 : decode_any W_98e48 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e4c : bv 32 := 0x01068693.
Lemma F_98e4c : fetch_word AsanUbsan.M.loaded_segments (0x98e4c : word) = Some W_98e4c.
Proof. vm_refl. Qed.
Lemma D_98e4c : decode_any W_98e4c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e50 : bv 32 := 0x01058593.
Lemma F_98e50 : fetch_word AsanUbsan.M.loaded_segments (0x98e50 : word) = Some W_98e50.
Proof. vm_refl. Qed.
Lemma D_98e50 : decode_any W_98e50 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e54 : bv 32 := 0xfac7e2e3.
Lemma F_98e54 : fetch_word AsanUbsan.M.loaded_segments (0x98e54 : word) = Some W_98e54.
Proof. vm_refl. Qed.
Lemma D_98e54 : decode_any W_98e54 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e58 : bv 32 := 0xff158593.
Lemma F_98e58 : fetch_word AsanUbsan.M.loaded_segments (0x98e58 : word) = Some W_98e58.
Proof. vm_refl. Qed.
Lemma D_98e58 : decode_any W_98e58 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e5c : bv 32 := 0x01000713.
Lemma F_98e5c : fetch_word AsanUbsan.M.loaded_segments (0x98e5c : word) = Some W_98e5c.
Proof. vm_refl. Qed.
Lemma D_98e5c : decode_any W_98e5c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e60 : bv 32 := 0xe4e666e3.
Lemma F_98e60 : fetch_word AsanUbsan.M.loaded_segments (0x98e60 : word) = Some W_98e60.
Proof. vm_refl. Qed.
Lemma D_98e60 : decode_any W_98e60 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e64 : bv 32 := 0x0940006f.
Lemma F_98e64 : fetch_word AsanUbsan.M.loaded_segments (0x98e64 : word) = Some W_98e64.
Proof. vm_refl. Qed.
Lemma D_98e64 : decode_any W_98e64 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e68 : bv 32 := 0x00875793.
Lemma F_98e68 : fetch_word AsanUbsan.M.loaded_segments (0x98e68 : word) = Some W_98e68.
Proof. vm_refl. Qed.
Lemma D_98e68 : decode_any W_98e68 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e6c : bv 32 := 0x01075813.
Lemma F_98e6c : fetch_word AsanUbsan.M.loaded_segments (0x98e6c : word) = Some W_98e6c.
Proof. vm_refl. Qed.
Lemma D_98e6c : decode_any W_98e6c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e70 : bv 32 := 0xffd60613.
Lemma F_98e70 : fetch_word AsanUbsan.M.loaded_segments (0x98e70 : word) = Some W_98e70.
Proof. vm_refl. Qed.
Lemma D_98e70 : decode_any W_98e70 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e74 : bv 32 := 0x00e68023.
Lemma F_98e74 : fetch_word AsanUbsan.M.loaded_segments (0x98e74 : word) = Some W_98e74.
Proof. vm_refl. Qed.
Lemma D_98e74 : decode_any W_98e74 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e78 : bv 32 := 0x00f680a3.
Lemma F_98e78 : fetch_word AsanUbsan.M.loaded_segments (0x98e78 : word) = Some W_98e78.
Proof. vm_refl. Qed.
Lemma D_98e78 : decode_any W_98e78 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e7c : bv 32 := 0x01068123.
Lemma F_98e7c : fetch_word AsanUbsan.M.loaded_segments (0x98e7c : word) = Some W_98e7c.
Proof. vm_refl. Qed.
Lemma D_98e7c : decode_any W_98e7c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e80 : bv 32 := 0x00368693.
Lemma F_98e80 : fetch_word AsanUbsan.M.loaded_segments (0x98e80 : word) = Some W_98e80.
Proof. vm_refl. Qed.
Lemma D_98e80 : decode_any W_98e80 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e84 : bv 32 := 0x01058593.
Lemma F_98e84 : fetch_word AsanUbsan.M.loaded_segments (0x98e84 : word) = Some W_98e84.
Proof. vm_refl. Qed.
Lemma D_98e84 : decode_any W_98e84 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e88 : bv 32 := 0x01000793.
Lemma F_98e88 : fetch_word AsanUbsan.M.loaded_segments (0x98e88 : word) = Some W_98e88.
Proof. vm_refl. Qed.
Lemma D_98e88 : decode_any W_98e88 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e8c : bv 32 := 0x0187581b.
Lemma F_98e8c : fetch_word AsanUbsan.M.loaded_segments (0x98e8c : word) = Some W_98e8c.
Proof. vm_refl. Qed.
Lemma D_98e8c : decode_any W_98e8c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e90 : bv 32 := 0xff45a883.
Lemma F_98e90 : fetch_word AsanUbsan.M.loaded_segments (0x98e90 : word) = Some W_98e90.
Proof. vm_refl. Qed.
Lemma D_98e90 : decode_any W_98e90 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e94 : bv 32 := 0xff85a283.
Lemma F_98e94 : fetch_word AsanUbsan.M.loaded_segments (0x98e94 : word) = Some W_98e94.
Proof. vm_refl. Qed.
Lemma D_98e94 : decode_any W_98e94 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e98 : bv 32 := 0xffc5a303.
Lemma F_98e98 : fetch_word AsanUbsan.M.loaded_segments (0x98e98 : word) = Some W_98e98.
Proof. vm_refl. Qed.
Lemma D_98e98 : decode_any W_98e98 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98e9c : bv 32 := 0x0005a703.
Lemma F_98e9c : fetch_word AsanUbsan.M.loaded_segments (0x98e9c : word) = Some W_98e9c.
Proof. vm_refl. Qed.
Lemma D_98e9c : decode_any W_98e9c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea0 : bv 32 := 0x00889393.
Lemma F_98ea0 : fetch_word AsanUbsan.M.loaded_segments (0x98ea0 : word) = Some W_98ea0.
Proof. vm_refl. Qed.
Lemma D_98ea0 : decode_any W_98ea0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea4 : bv 32 := 0x0188d89b.
Lemma F_98ea4 : fetch_word AsanUbsan.M.loaded_segments (0x98ea4 : word) = Some W_98ea4.
Proof. vm_refl. Qed.
Lemma D_98ea4 : decode_any W_98ea4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ea8 : bv 32 := 0x0103e833.
Lemma F_98ea8 : fetch_word AsanUbsan.M.loaded_segments (0x98ea8 : word) = Some W_98ea8.
Proof. vm_refl. Qed.
Lemma D_98ea8 : decode_any W_98ea8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eac : bv 32 := 0x00829393.
Lemma F_98eac : fetch_word AsanUbsan.M.loaded_segments (0x98eac : word) = Some W_98eac.
Proof. vm_refl. Qed.
Lemma D_98eac : decode_any W_98eac = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb0 : bv 32 := 0x0182d29b.
Lemma F_98eb0 : fetch_word AsanUbsan.M.loaded_segments (0x98eb0 : word) = Some W_98eb0.
Proof. vm_refl. Qed.
Lemma D_98eb0 : decode_any W_98eb0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb4 : bv 32 := 0x0113e8b3.
Lemma F_98eb4 : fetch_word AsanUbsan.M.loaded_segments (0x98eb4 : word) = Some W_98eb4.
Proof. vm_refl. Qed.
Lemma D_98eb4 : decode_any W_98eb4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eb8 : bv 32 := 0x00831393.
Lemma F_98eb8 : fetch_word AsanUbsan.M.loaded_segments (0x98eb8 : word) = Some W_98eb8.
Proof. vm_refl. Qed.
Lemma D_98eb8 : decode_any W_98eb8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ebc : bv 32 := 0x0183531b.
Lemma F_98ebc : fetch_word AsanUbsan.M.loaded_segments (0x98ebc : word) = Some W_98ebc.
Proof. vm_refl. Qed.
Lemma D_98ebc : decode_any W_98ebc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec0 : bv 32 := 0x0053e2b3.
Lemma F_98ec0 : fetch_word AsanUbsan.M.loaded_segments (0x98ec0 : word) = Some W_98ec0.
Proof. vm_refl. Qed.
Lemma D_98ec0 : decode_any W_98ec0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec4 : bv 32 := 0x00871393.
Lemma F_98ec4 : fetch_word AsanUbsan.M.loaded_segments (0x98ec4 : word) = Some W_98ec4.
Proof. vm_refl. Qed.
Lemma D_98ec4 : decode_any W_98ec4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ec8 : bv 32 := 0x0063e333.
Lemma F_98ec8 : fetch_word AsanUbsan.M.loaded_segments (0x98ec8 : word) = Some W_98ec8.
Proof. vm_refl. Qed.
Lemma D_98ec8 : decode_any W_98ec8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ecc : bv 32 := 0xff060613.
Lemma F_98ecc : fetch_word AsanUbsan.M.loaded_segments (0x98ecc : word) = Some W_98ecc.
Proof. vm_refl. Qed.
Lemma D_98ecc : decode_any W_98ecc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed0 : bv 32 := 0x0106a023.
Lemma F_98ed0 : fetch_word AsanUbsan.M.loaded_segments (0x98ed0 : word) = Some W_98ed0.
Proof. vm_refl. Qed.
Lemma D_98ed0 : decode_any W_98ed0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed4 : bv 32 := 0x0116a223.
Lemma F_98ed4 : fetch_word AsanUbsan.M.loaded_segments (0x98ed4 : word) = Some W_98ed4.
Proof. vm_refl. Qed.
Lemma D_98ed4 : decode_any W_98ed4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ed8 : bv 32 := 0x0056a423.
Lemma F_98ed8 : fetch_word AsanUbsan.M.loaded_segments (0x98ed8 : word) = Some W_98ed8.
Proof. vm_refl. Qed.
Lemma D_98ed8 : decode_any W_98ed8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98edc : bv 32 := 0x0066a623.
Lemma F_98edc : fetch_word AsanUbsan.M.loaded_segments (0x98edc : word) = Some W_98edc.
Proof. vm_refl. Qed.
Lemma D_98edc : decode_any W_98edc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ee0 : bv 32 := 0x01068693.
Lemma F_98ee0 : fetch_word AsanUbsan.M.loaded_segments (0x98ee0 : word) = Some W_98ee0.
Proof. vm_refl. Qed.
Lemma D_98ee0 : decode_any W_98ee0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ee4 : bv 32 := 0x01058593.
Lemma F_98ee4 : fetch_word AsanUbsan.M.loaded_segments (0x98ee4 : word) = Some W_98ee4.
Proof. vm_refl. Qed.
Lemma D_98ee4 : decode_any W_98ee4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ee8 : bv 32 := 0xfac7e2e3.
Lemma F_98ee8 : fetch_word AsanUbsan.M.loaded_segments (0x98ee8 : word) = Some W_98ee8.
Proof. vm_refl. Qed.
Lemma D_98ee8 : decode_any W_98ee8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98eec : bv 32 := 0xff358593.
Lemma F_98eec : fetch_word AsanUbsan.M.loaded_segments (0x98eec : word) = Some W_98eec.
Proof. vm_refl. Qed.
Lemma D_98eec : decode_any W_98eec = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ef0 : bv 32 := 0x01000713.
Lemma F_98ef0 : fetch_word AsanUbsan.M.loaded_segments (0x98ef0 : word) = Some W_98ef0.
Proof. vm_refl. Qed.
Lemma D_98ef0 : decode_any W_98ef0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ef4 : bv 32 := 0xdae66ce3.
Lemma F_98ef4 : fetch_word AsanUbsan.M.loaded_segments (0x98ef4 : word) = Some W_98ef4.
Proof. vm_refl. Qed.
Lemma D_98ef4 : decode_any W_98ef4 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ef8 : bv 32 := 0x0005c703.
Lemma F_98ef8 : fetch_word AsanUbsan.M.loaded_segments (0x98ef8 : word) = Some W_98ef8.
Proof. vm_refl. Qed.
Lemma D_98ef8 : decode_any W_98ef8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98efc : bv 32 := 0x0015c783.
Lemma F_98efc : fetch_word AsanUbsan.M.loaded_segments (0x98efc : word) = Some W_98efc.
Proof. vm_refl. Qed.
Lemma D_98efc : decode_any W_98efc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f00 : bv 32 := 0x0025c803.
Lemma F_98f00 : fetch_word AsanUbsan.M.loaded_segments (0x98f00 : word) = Some W_98f00.
Proof. vm_refl. Qed.
Lemma D_98f00 : decode_any W_98f00 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f04 : bv 32 := 0x0035c883.
Lemma F_98f04 : fetch_word AsanUbsan.M.loaded_segments (0x98f04 : word) = Some W_98f04.
Proof. vm_refl. Qed.
Lemma D_98f04 : decode_any W_98f04 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f08 : bv 32 := 0x0045c283.
Lemma F_98f08 : fetch_word AsanUbsan.M.loaded_segments (0x98f08 : word) = Some W_98f08.
Proof. vm_refl. Qed.
Lemma D_98f08 : decode_any W_98f08 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f0c : bv 32 := 0x0055c303.
Lemma F_98f0c : fetch_word AsanUbsan.M.loaded_segments (0x98f0c : word) = Some W_98f0c.
Proof. vm_refl. Qed.
Lemma D_98f0c : decode_any W_98f0c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f10 : bv 32 := 0x0065c383.
Lemma F_98f10 : fetch_word AsanUbsan.M.loaded_segments (0x98f10 : word) = Some W_98f10.
Proof. vm_refl. Qed.
Lemma D_98f10 : decode_any W_98f10 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f14 : bv 32 := 0x0075ce03.
Lemma F_98f14 : fetch_word AsanUbsan.M.loaded_segments (0x98f14 : word) = Some W_98f14.
Proof. vm_refl. Qed.
Lemma D_98f14 : decode_any W_98f14 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f18 : bv 32 := 0x00e68023.
Lemma F_98f18 : fetch_word AsanUbsan.M.loaded_segments (0x98f18 : word) = Some W_98f18.
Proof. vm_refl. Qed.
Lemma D_98f18 : decode_any W_98f18 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f1c : bv 32 := 0x00f680a3.
Lemma F_98f1c : fetch_word AsanUbsan.M.loaded_segments (0x98f1c : word) = Some W_98f1c.
Proof. vm_refl. Qed.
Lemma D_98f1c : decode_any W_98f1c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f20 : bv 32 := 0x01068123.
Lemma F_98f20 : fetch_word AsanUbsan.M.loaded_segments (0x98f20 : word) = Some W_98f20.
Proof. vm_refl. Qed.
Lemma D_98f20 : decode_any W_98f20 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f24 : bv 32 := 0x011681a3.
Lemma F_98f24 : fetch_word AsanUbsan.M.loaded_segments (0x98f24 : word) = Some W_98f24.
Proof. vm_refl. Qed.
Lemma D_98f24 : decode_any W_98f24 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f28 : bv 32 := 0x0085c703.
Lemma F_98f28 : fetch_word AsanUbsan.M.loaded_segments (0x98f28 : word) = Some W_98f28.
Proof. vm_refl. Qed.
Lemma D_98f28 : decode_any W_98f28 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f2c : bv 32 := 0x0095c783.
Lemma F_98f2c : fetch_word AsanUbsan.M.loaded_segments (0x98f2c : word) = Some W_98f2c.
Proof. vm_refl. Qed.
Lemma D_98f2c : decode_any W_98f2c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f30 : bv 32 := 0x00a5c803.
Lemma F_98f30 : fetch_word AsanUbsan.M.loaded_segments (0x98f30 : word) = Some W_98f30.
Proof. vm_refl. Qed.
Lemma D_98f30 : decode_any W_98f30 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f34 : bv 32 := 0x00b5c883.
Lemma F_98f34 : fetch_word AsanUbsan.M.loaded_segments (0x98f34 : word) = Some W_98f34.
Proof. vm_refl. Qed.
Lemma D_98f34 : decode_any W_98f34 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f38 : bv 32 := 0x00568223.
Lemma F_98f38 : fetch_word AsanUbsan.M.loaded_segments (0x98f38 : word) = Some W_98f38.
Proof. vm_refl. Qed.
Lemma D_98f38 : decode_any W_98f38 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f3c : bv 32 := 0x006682a3.
Lemma F_98f3c : fetch_word AsanUbsan.M.loaded_segments (0x98f3c : word) = Some W_98f3c.
Proof. vm_refl. Qed.
Lemma D_98f3c : decode_any W_98f3c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f40 : bv 32 := 0x00768323.
Lemma F_98f40 : fetch_word AsanUbsan.M.loaded_segments (0x98f40 : word) = Some W_98f40.
Proof. vm_refl. Qed.
Lemma D_98f40 : decode_any W_98f40 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f44 : bv 32 := 0x01c683a3.
Lemma F_98f44 : fetch_word AsanUbsan.M.loaded_segments (0x98f44 : word) = Some W_98f44.
Proof. vm_refl. Qed.
Lemma D_98f44 : decode_any W_98f44 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f48 : bv 32 := 0x00c5c283.
Lemma F_98f48 : fetch_word AsanUbsan.M.loaded_segments (0x98f48 : word) = Some W_98f48.
Proof. vm_refl. Qed.
Lemma D_98f48 : decode_any W_98f48 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f4c : bv 32 := 0x00d5c303.
Lemma F_98f4c : fetch_word AsanUbsan.M.loaded_segments (0x98f4c : word) = Some W_98f4c.
Proof. vm_refl. Qed.
Lemma D_98f4c : decode_any W_98f4c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f50 : bv 32 := 0x00e5c383.
Lemma F_98f50 : fetch_word AsanUbsan.M.loaded_segments (0x98f50 : word) = Some W_98f50.
Proof. vm_refl. Qed.
Lemma D_98f50 : decode_any W_98f50 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f54 : bv 32 := 0x00f5ce03.
Lemma F_98f54 : fetch_word AsanUbsan.M.loaded_segments (0x98f54 : word) = Some W_98f54.
Proof. vm_refl. Qed.
Lemma D_98f54 : decode_any W_98f54 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f58 : bv 32 := 0x01058593.
Lemma F_98f58 : fetch_word AsanUbsan.M.loaded_segments (0x98f58 : word) = Some W_98f58.
Proof. vm_refl. Qed.
Lemma D_98f58 : decode_any W_98f58 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f5c : bv 32 := 0x00e68423.
Lemma F_98f5c : fetch_word AsanUbsan.M.loaded_segments (0x98f5c : word) = Some W_98f5c.
Proof. vm_refl. Qed.
Lemma D_98f5c : decode_any W_98f5c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f60 : bv 32 := 0x00f684a3.
Lemma F_98f60 : fetch_word AsanUbsan.M.loaded_segments (0x98f60 : word) = Some W_98f60.
Proof. vm_refl. Qed.
Lemma D_98f60 : decode_any W_98f60 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f64 : bv 32 := 0x01068523.
Lemma F_98f64 : fetch_word AsanUbsan.M.loaded_segments (0x98f64 : word) = Some W_98f64.
Proof. vm_refl. Qed.
Lemma D_98f64 : decode_any W_98f64 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f68 : bv 32 := 0x011685a3.
Lemma F_98f68 : fetch_word AsanUbsan.M.loaded_segments (0x98f68 : word) = Some W_98f68.
Proof. vm_refl. Qed.
Lemma D_98f68 : decode_any W_98f68 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f6c : bv 32 := 0x01068713.
Lemma F_98f6c : fetch_word AsanUbsan.M.loaded_segments (0x98f6c : word) = Some W_98f6c.
Proof. vm_refl. Qed.
Lemma D_98f6c : decode_any W_98f6c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f70 : bv 32 := 0x00568623.
Lemma F_98f70 : fetch_word AsanUbsan.M.loaded_segments (0x98f70 : word) = Some W_98f70.
Proof. vm_refl. Qed.
Lemma D_98f70 : decode_any W_98f70 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f74 : bv 32 := 0x006686a3.
Lemma F_98f74 : fetch_word AsanUbsan.M.loaded_segments (0x98f74 : word) = Some W_98f74.
Proof. vm_refl. Qed.
Lemma D_98f74 : decode_any W_98f74 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f78 : bv 32 := 0x00768723.
Lemma F_98f78 : fetch_word AsanUbsan.M.loaded_segments (0x98f78 : word) = Some W_98f78.
Proof. vm_refl. Qed.
Lemma D_98f78 : decode_any W_98f78 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f7c : bv 32 := 0x01c687a3.
Lemma F_98f7c : fetch_word AsanUbsan.M.loaded_segments (0x98f7c : word) = Some W_98f7c.
Proof. vm_refl. Qed.
Lemma D_98f7c : decode_any W_98f7c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f80 : bv 32 := 0x00070693.
Lemma F_98f80 : fetch_word AsanUbsan.M.loaded_segments (0x98f80 : word) = Some W_98f80.
Proof. vm_refl. Qed.
Lemma D_98f80 : decode_any W_98f80 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f84 : bv 32 := 0x00867713.
Lemma F_98f84 : fetch_word AsanUbsan.M.loaded_segments (0x98f84 : word) = Some W_98f84.
Proof. vm_refl. Qed.
Lemma D_98f84 : decode_any W_98f84 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f88 : bv 32 := 0xd20706e3.
Lemma F_98f88 : fetch_word AsanUbsan.M.loaded_segments (0x98f88 : word) = Some W_98f88.
Proof. vm_refl. Qed.
Lemma D_98f88 : decode_any W_98f88 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f8c : bv 32 := 0x0005c703.
Lemma F_98f8c : fetch_word AsanUbsan.M.loaded_segments (0x98f8c : word) = Some W_98f8c.
Proof. vm_refl. Qed.
Lemma D_98f8c : decode_any W_98f8c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f90 : bv 32 := 0x0015c783.
Lemma F_98f90 : fetch_word AsanUbsan.M.loaded_segments (0x98f90 : word) = Some W_98f90.
Proof. vm_refl. Qed.
Lemma D_98f90 : decode_any W_98f90 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f94 : bv 32 := 0x0025c803.
Lemma F_98f94 : fetch_word AsanUbsan.M.loaded_segments (0x98f94 : word) = Some W_98f94.
Proof. vm_refl. Qed.
Lemma D_98f94 : decode_any W_98f94 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f98 : bv 32 := 0x0035c883.
Lemma F_98f98 : fetch_word AsanUbsan.M.loaded_segments (0x98f98 : word) = Some W_98f98.
Proof. vm_refl. Qed.
Lemma D_98f98 : decode_any W_98f98 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98f9c : bv 32 := 0x0045c283.
Lemma F_98f9c : fetch_word AsanUbsan.M.loaded_segments (0x98f9c : word) = Some W_98f9c.
Proof. vm_refl. Qed.
Lemma D_98f9c : decode_any W_98f9c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fa0 : bv 32 := 0x0055c303.
Lemma F_98fa0 : fetch_word AsanUbsan.M.loaded_segments (0x98fa0 : word) = Some W_98fa0.
Proof. vm_refl. Qed.
Lemma D_98fa0 : decode_any W_98fa0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fa4 : bv 32 := 0x0065c383.
Lemma F_98fa4 : fetch_word AsanUbsan.M.loaded_segments (0x98fa4 : word) = Some W_98fa4.
Proof. vm_refl. Qed.
Lemma D_98fa4 : decode_any W_98fa4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fa8 : bv 32 := 0x0075ce03.
Lemma F_98fa8 : fetch_word AsanUbsan.M.loaded_segments (0x98fa8 : word) = Some W_98fa8.
Proof. vm_refl. Qed.
Lemma D_98fa8 : decode_any W_98fa8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fac : bv 32 := 0x00858593.
Lemma F_98fac : fetch_word AsanUbsan.M.loaded_segments (0x98fac : word) = Some W_98fac.
Proof. vm_refl. Qed.
Lemma D_98fac : decode_any W_98fac = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fb0 : bv 32 := 0x00e68023.
Lemma F_98fb0 : fetch_word AsanUbsan.M.loaded_segments (0x98fb0 : word) = Some W_98fb0.
Proof. vm_refl. Qed.
Lemma D_98fb0 : decode_any W_98fb0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fb4 : bv 32 := 0x00f680a3.
Lemma F_98fb4 : fetch_word AsanUbsan.M.loaded_segments (0x98fb4 : word) = Some W_98fb4.
Proof. vm_refl. Qed.
Lemma D_98fb4 : decode_any W_98fb4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fb8 : bv 32 := 0x01068123.
Lemma F_98fb8 : fetch_word AsanUbsan.M.loaded_segments (0x98fb8 : word) = Some W_98fb8.
Proof. vm_refl. Qed.
Lemma D_98fb8 : decode_any W_98fb8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fbc : bv 32 := 0x011681a3.
Lemma F_98fbc : fetch_word AsanUbsan.M.loaded_segments (0x98fbc : word) = Some W_98fbc.
Proof. vm_refl. Qed.
Lemma D_98fbc : decode_any W_98fbc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fc0 : bv 32 := 0x00868713.
Lemma F_98fc0 : fetch_word AsanUbsan.M.loaded_segments (0x98fc0 : word) = Some W_98fc0.
Proof. vm_refl. Qed.
Lemma D_98fc0 : decode_any W_98fc0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fc4 : bv 32 := 0x00568223.
Lemma F_98fc4 : fetch_word AsanUbsan.M.loaded_segments (0x98fc4 : word) = Some W_98fc4.
Proof. vm_refl. Qed.
Lemma D_98fc4 : decode_any W_98fc4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fc8 : bv 32 := 0x006682a3.
Lemma F_98fc8 : fetch_word AsanUbsan.M.loaded_segments (0x98fc8 : word) = Some W_98fc8.
Proof. vm_refl. Qed.
Lemma D_98fc8 : decode_any W_98fc8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fcc : bv 32 := 0x00768323.
Lemma F_98fcc : fetch_word AsanUbsan.M.loaded_segments (0x98fcc : word) = Some W_98fcc.
Proof. vm_refl. Qed.
Lemma D_98fcc : decode_any W_98fcc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fd0 : bv 32 := 0x01c683a3.
Lemma F_98fd0 : fetch_word AsanUbsan.M.loaded_segments (0x98fd0 : word) = Some W_98fd0.
Proof. vm_refl. Qed.
Lemma D_98fd0 : decode_any W_98fd0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fd4 : bv 32 := 0x00070693.
Lemma F_98fd4 : fetch_word AsanUbsan.M.loaded_segments (0x98fd4 : word) = Some W_98fd4.
Proof. vm_refl. Qed.
Lemma D_98fd4 : decode_any W_98fd4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fd8 : bv 32 := 0x00467713.
Lemma F_98fd8 : fetch_word AsanUbsan.M.loaded_segments (0x98fd8 : word) = Some W_98fd8.
Proof. vm_refl. Qed.
Lemma D_98fd8 : decode_any W_98fd8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fdc : bv 32 := 0x02070863.
Lemma F_98fdc : fetch_word AsanUbsan.M.loaded_segments (0x98fdc : word) = Some W_98fdc.
Proof. vm_refl. Qed.
Lemma D_98fdc : decode_any W_98fdc = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fe0 : bv 32 := 0x0005c703.
Lemma F_98fe0 : fetch_word AsanUbsan.M.loaded_segments (0x98fe0 : word) = Some W_98fe0.
Proof. vm_refl. Qed.
Lemma D_98fe0 : decode_any W_98fe0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fe4 : bv 32 := 0x0015c783.
Lemma F_98fe4 : fetch_word AsanUbsan.M.loaded_segments (0x98fe4 : word) = Some W_98fe4.
Proof. vm_refl. Qed.
Lemma D_98fe4 : decode_any W_98fe4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fe8 : bv 32 := 0x0025c803.
Lemma F_98fe8 : fetch_word AsanUbsan.M.loaded_segments (0x98fe8 : word) = Some W_98fe8.
Proof. vm_refl. Qed.
Lemma D_98fe8 : decode_any W_98fe8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98fec : bv 32 := 0x0035c883.
Lemma F_98fec : fetch_word AsanUbsan.M.loaded_segments (0x98fec : word) = Some W_98fec.
Proof. vm_refl. Qed.
Lemma D_98fec : decode_any W_98fec = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ff0 : bv 32 := 0x00458593.
Lemma F_98ff0 : fetch_word AsanUbsan.M.loaded_segments (0x98ff0 : word) = Some W_98ff0.
Proof. vm_refl. Qed.
Lemma D_98ff0 : decode_any W_98ff0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ff4 : bv 32 := 0x00468293.
Lemma F_98ff4 : fetch_word AsanUbsan.M.loaded_segments (0x98ff4 : word) = Some W_98ff4.
Proof. vm_refl. Qed.
Lemma D_98ff4 : decode_any W_98ff4 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ff8 : bv 32 := 0x00e68023.
Lemma F_98ff8 : fetch_word AsanUbsan.M.loaded_segments (0x98ff8 : word) = Some W_98ff8.
Proof. vm_refl. Qed.
Lemma D_98ff8 : decode_any W_98ff8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ffc : bv 32 := 0x00f680a3.
Lemma F_98ffc : fetch_word AsanUbsan.M.loaded_segments (0x98ffc : word) = Some W_98ffc.
Proof. vm_refl. Qed.
Lemma D_98ffc : decode_any W_98ffc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99000 : bv 32 := 0x01068123.
Lemma F_99000 : fetch_word AsanUbsan.M.loaded_segments (0x99000 : word) = Some W_99000.
Proof. vm_refl. Qed.
Lemma D_99000 : decode_any W_99000 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99004 : bv 32 := 0x011681a3.
Lemma F_99004 : fetch_word AsanUbsan.M.loaded_segments (0x99004 : word) = Some W_99004.
Proof. vm_refl. Qed.
Lemma D_99004 : decode_any W_99004 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99008 : bv 32 := 0x00028693.
Lemma F_99008 : fetch_word AsanUbsan.M.loaded_segments (0x99008 : word) = Some W_99008.
Proof. vm_refl. Qed.
Lemma D_99008 : decode_any W_99008 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9900c : bv 32 := 0x00267713.
Lemma F_9900c : fetch_word AsanUbsan.M.loaded_segments (0x9900c : word) = Some W_9900c.
Proof. vm_refl. Qed.
Lemma D_9900c : decode_any W_9900c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99010 : bv 32 := 0x00071863.
Lemma F_99010 : fetch_word AsanUbsan.M.loaded_segments (0x99010 : word) = Some W_99010.
Proof. vm_refl. Qed.
Lemma D_99010 : decode_any W_99010 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99014 : bv 32 := 0x00167613.
Lemma F_99014 : fetch_word AsanUbsan.M.loaded_segments (0x99014 : word) = Some W_99014.
Proof. vm_refl. Qed.
Lemma D_99014 : decode_any W_99014 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99018 : bv 32 := 0x02061663.
Lemma F_99018 : fetch_word AsanUbsan.M.loaded_segments (0x99018 : word) = Some W_99018.
Proof. vm_refl. Qed.
Lemma D_99018 : decode_any W_99018 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9901c : bv 32 := 0x00008067.
Lemma F_9901c : fetch_word AsanUbsan.M.loaded_segments (0x9901c : word) = Some W_9901c.
Proof. vm_refl. Qed.
Lemma D_9901c : decode_any W_9901c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99020 : bv 32 := 0x0005c703.
Lemma F_99020 : fetch_word AsanUbsan.M.loaded_segments (0x99020 : word) = Some W_99020.
Proof. vm_refl. Qed.
Lemma D_99020 : decode_any W_99020 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99024 : bv 32 := 0x0015c783.
Lemma F_99024 : fetch_word AsanUbsan.M.loaded_segments (0x99024 : word) = Some W_99024.
Proof. vm_refl. Qed.
Lemma D_99024 : decode_any W_99024 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99028 : bv 32 := 0x00258593.
Lemma F_99028 : fetch_word AsanUbsan.M.loaded_segments (0x99028 : word) = Some W_99028.
Proof. vm_refl. Qed.
Lemma D_99028 : decode_any W_99028 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9902c : bv 32 := 0x00268813.
Lemma F_9902c : fetch_word AsanUbsan.M.loaded_segments (0x9902c : word) = Some W_9902c.
Proof. vm_refl. Qed.
Lemma D_9902c : decode_any W_9902c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99030 : bv 32 := 0x00e68023.
Lemma F_99030 : fetch_word AsanUbsan.M.loaded_segments (0x99030 : word) = Some W_99030.
Proof. vm_refl. Qed.
Lemma D_99030 : decode_any W_99030 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99034 : bv 32 := 0x00f680a3.
Lemma F_99034 : fetch_word AsanUbsan.M.loaded_segments (0x99034 : word) = Some W_99034.
Proof. vm_refl. Qed.
Lemma D_99034 : decode_any W_99034 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99038 : bv 32 := 0x00080693.
Lemma F_99038 : fetch_word AsanUbsan.M.loaded_segments (0x99038 : word) = Some W_99038.
Proof. vm_refl. Qed.
Lemma D_99038 : decode_any W_99038 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9903c : bv 32 := 0x00167613.
Lemma F_9903c : fetch_word AsanUbsan.M.loaded_segments (0x9903c : word) = Some W_9903c.
Proof. vm_refl. Qed.
Lemma D_9903c : decode_any W_9903c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99040 : bv 32 := 0xfc060ee3.
Lemma F_99040 : fetch_word AsanUbsan.M.loaded_segments (0x99040 : word) = Some W_99040.
Proof. vm_refl. Qed.
Lemma D_99040 : decode_any W_99040 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99044 : bv 32 := 0x0005c583.
Lemma F_99044 : fetch_word AsanUbsan.M.loaded_segments (0x99044 : word) = Some W_99044.
Proof. vm_refl. Qed.
Lemma D_99044 : decode_any W_99044 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99048 : bv 32 := 0x00b68023.
Lemma F_99048 : fetch_word AsanUbsan.M.loaded_segments (0x99048 : word) = Some W_99048.
Proof. vm_refl. Qed.
Lemma D_99048 : decode_any W_99048 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9904c : bv 32 := 0x00008067.
Lemma F_9904c : fetch_word AsanUbsan.M.loaded_segments (0x9904c : word) = Some W_9904c.
Proof. vm_refl. Qed.
Lemma D_9904c : decode_any W_9904c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
