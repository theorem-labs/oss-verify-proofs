(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_97e1c : bv 32 := 0x0035f693.
Lemma F_97e1c : fetch_word Asan.M.loaded_segments (0x97e1c : word) = Some W_97e1c.
Proof. vm_refl. Qed.
Lemma D_97e1c : decode_any W_97e1c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e20 : bv 32 := 0x10068863.
Lemma F_97e20 : fetch_word Asan.M.loaded_segments (0x97e20 : word) = Some W_97e20.
Proof. vm_refl. Qed.
Lemma D_97e20 : decode_any W_97e20 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e24 : bv 32 := 0x02060e63.
Lemma F_97e24 : fetch_word Asan.M.loaded_segments (0x97e24 : word) = Some W_97e24.
Proof. vm_refl. Qed.
Lemma D_97e24 : decode_any W_97e24 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e28 : bv 32 := 0x00158713.
Lemma F_97e28 : fetch_word Asan.M.loaded_segments (0x97e28 : word) = Some W_97e28.
Proof. vm_refl. Qed.
Lemma D_97e28 : decode_any W_97e28 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e2c : bv 32 := 0x00100793.
Lemma F_97e2c : fetch_word Asan.M.loaded_segments (0x97e2c : word) = Some W_97e2c.
Proof. vm_refl. Qed.
Lemma D_97e2c : decode_any W_97e2c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e30 : bv 32 := 0x00050693.
Lemma F_97e30 : fetch_word Asan.M.loaded_segments (0x97e30 : word) = Some W_97e30.
Proof. vm_refl. Qed.
Lemma D_97e30 : decode_any W_97e30 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e34 : bv 32 := 0x0005c883.
Lemma F_97e34 : fetch_word Asan.M.loaded_segments (0x97e34 : word) = Some W_97e34.
Proof. vm_refl. Qed.
Lemma D_97e34 : decode_any W_97e34 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e38 : bv 32 := 0x00060813.
Lemma F_97e38 : fetch_word Asan.M.loaded_segments (0x97e38 : word) = Some W_97e38.
Proof. vm_refl. Qed.
Lemma D_97e38 : decode_any W_97e38 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e3c : bv 32 := 0x00158593.
Lemma F_97e3c : fetch_word Asan.M.loaded_segments (0x97e3c : word) = Some W_97e3c.
Proof. vm_refl. Qed.
Lemma D_97e3c : decode_any W_97e3c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e40 : bv 32 := 0x00377293.
Lemma F_97e40 : fetch_word Asan.M.loaded_segments (0x97e40 : word) = Some W_97e40.
Proof. vm_refl. Qed.
Lemma D_97e40 : decode_any W_97e40 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e44 : bv 32 := 0x01168023.
Lemma F_97e44 : fetch_word Asan.M.loaded_segments (0x97e44 : word) = Some W_97e44.
Proof. vm_refl. Qed.
Lemma D_97e44 : decode_any W_97e44 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e48 : bv 32 := 0x00168693.
Lemma F_97e48 : fetch_word Asan.M.loaded_segments (0x97e48 : word) = Some W_97e48.
Proof. vm_refl. Qed.
Lemma D_97e48 : decode_any W_97e48 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e4c : bv 32 := 0xfff60613.
Lemma F_97e4c : fetch_word Asan.M.loaded_segments (0x97e4c : word) = Some W_97e4c.
Proof. vm_refl. Qed.
Lemma D_97e4c : decode_any W_97e4c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e50 : bv 32 := 0x00028a63.
Lemma F_97e50 : fetch_word Asan.M.loaded_segments (0x97e50 : word) = Some W_97e50.
Proof. vm_refl. Qed.
Lemma D_97e50 : decode_any W_97e50 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e54 : bv 32 := 0x00170713.
Lemma F_97e54 : fetch_word Asan.M.loaded_segments (0x97e54 : word) = Some W_97e54.
Proof. vm_refl. Qed.
Lemma D_97e54 : decode_any W_97e54 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e58 : bv 32 := 0xfcf81ee3.
Lemma F_97e58 : fetch_word Asan.M.loaded_segments (0x97e58 : word) = Some W_97e58.
Proof. vm_refl. Qed.
Lemma D_97e58 : decode_any W_97e58 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e5c : bv 32 := 0x0080006f.
Lemma F_97e5c : fetch_word Asan.M.loaded_segments (0x97e5c : word) = Some W_97e5c.
Proof. vm_refl. Qed.
Lemma D_97e5c : decode_any W_97e5c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e60 : bv 32 := 0x00050693.
Lemma F_97e60 : fetch_word Asan.M.loaded_segments (0x97e60 : word) = Some W_97e60.
Proof. vm_refl. Qed.
Lemma D_97e60 : decode_any W_97e60 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e64 : bv 32 := 0x0036f793.
Lemma F_97e64 : fetch_word Asan.M.loaded_segments (0x97e64 : word) = Some W_97e64.
Proof. vm_refl. Qed.
Lemma D_97e64 : decode_any W_97e64 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e68 : bv 32 := 0x0c078a63.
Lemma F_97e68 : fetch_word Asan.M.loaded_segments (0x97e68 : word) = Some W_97e68.
Proof. vm_refl. Qed.
Lemma D_97e68 : decode_any W_97e68 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e6c : bv 32 := 0x02000713.
Lemma F_97e6c : fetch_word Asan.M.loaded_segments (0x97e6c : word) = Some W_97e6c.
Proof. vm_refl. Qed.
Lemma D_97e6c : decode_any W_97e6c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e70 : bv 32 := 0x02e67063.
Lemma F_97e70 : fetch_word Asan.M.loaded_segments (0x97e70 : word) = Some W_97e70.
Proof. vm_refl. Qed.
Lemma D_97e70 : decode_any W_97e70 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e74 : bv 32 := 0x01000713.
Lemma F_97e74 : fetch_word Asan.M.loaded_segments (0x97e74 : word) = Some W_97e74.
Proof. vm_refl. Qed.
Lemma D_97e74 : decode_any W_97e74 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e78 : bv 32 := 0x24e67863.
Lemma F_97e78 : fetch_word Asan.M.loaded_segments (0x97e78 : word) = Some W_97e78.
Proof. vm_refl. Qed.
Lemma D_97e78 : decode_any W_97e78 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e7c : bv 32 := 0x00867713.
Lemma F_97e7c : fetch_word Asan.M.loaded_segments (0x97e7c : word) = Some W_97e7c.
Proof. vm_refl. Qed.
Lemma D_97e7c : decode_any W_97e7c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e80 : bv 32 := 0x2c071e63.
Lemma F_97e80 : fetch_word Asan.M.loaded_segments (0x97e80 : word) = Some W_97e80.
Proof. vm_refl. Qed.
Lemma D_97e80 : decode_any W_97e80 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e84 : bv 32 := 0x00467713.
Lemma F_97e84 : fetch_word Asan.M.loaded_segments (0x97e84 : word) = Some W_97e84.
Proof. vm_refl. Qed.
Lemma D_97e84 : decode_any W_97e84 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e88 : bv 32 := 0x32071463.
Lemma F_97e88 : fetch_word Asan.M.loaded_segments (0x97e88 : word) = Some W_97e88.
Proof. vm_refl. Qed.
Lemma D_97e88 : decode_any W_97e88 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e8c : bv 32 := 0x3500006f.
Lemma F_97e8c : fetch_word Asan.M.loaded_segments (0x97e8c : word) = Some W_97e8c.
Proof. vm_refl. Qed.
Lemma D_97e8c : decode_any W_97e8c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e90 : bv 32 := 0x0005a703.
Lemma F_97e90 : fetch_word Asan.M.loaded_segments (0x97e90 : word) = Some W_97e90.
Proof. vm_refl. Qed.
Lemma D_97e90 : decode_any W_97e90 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e94 : bv 32 := 0x00300813.
Lemma F_97e94 : fetch_word Asan.M.loaded_segments (0x97e94 : word) = Some W_97e94.
Proof. vm_refl. Qed.
Lemma D_97e94 : decode_any W_97e94 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e98 : bv 32 := 0x11078e63.
Lemma F_97e98 : fetch_word Asan.M.loaded_segments (0x97e98 : word) = Some W_97e98.
Proof. vm_refl. Qed.
Lemma D_97e98 : decode_any W_97e98 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97e9c : bv 32 := 0x00200813.
Lemma F_97e9c : fetch_word Asan.M.loaded_segments (0x97e9c : word) = Some W_97e9c.
Proof. vm_refl. Qed.
Lemma D_97e9c : decode_any W_97e9c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ea0 : bv 32 := 0x19079c63.
Lemma F_97ea0 : fetch_word Asan.M.loaded_segments (0x97ea0 : word) = Some W_97ea0.
Proof. vm_refl. Qed.
Lemma D_97ea0 : decode_any W_97ea0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ea4 : bv 32 := 0x00875793.
Lemma F_97ea4 : fetch_word Asan.M.loaded_segments (0x97ea4 : word) = Some W_97ea4.
Proof. vm_refl. Qed.
Lemma D_97ea4 : decode_any W_97ea4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ea8 : bv 32 := 0xffe60613.
Lemma F_97ea8 : fetch_word Asan.M.loaded_segments (0x97ea8 : word) = Some W_97ea8.
Proof. vm_refl. Qed.
Lemma D_97ea8 : decode_any W_97ea8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97eac : bv 32 := 0x00e68023.
Lemma F_97eac : fetch_word Asan.M.loaded_segments (0x97eac : word) = Some W_97eac.
Proof. vm_refl. Qed.
Lemma D_97eac : decode_any W_97eac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97eb0 : bv 32 := 0x00f680a3.
Lemma F_97eb0 : fetch_word Asan.M.loaded_segments (0x97eb0 : word) = Some W_97eb0.
Proof. vm_refl. Qed.
Lemma D_97eb0 : decode_any W_97eb0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97eb4 : bv 32 := 0x00268693.
Lemma F_97eb4 : fetch_word Asan.M.loaded_segments (0x97eb4 : word) = Some W_97eb4.
Proof. vm_refl. Qed.
Lemma D_97eb4 : decode_any W_97eb4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97eb8 : bv 32 := 0x01058593.
Lemma F_97eb8 : fetch_word Asan.M.loaded_segments (0x97eb8 : word) = Some W_97eb8.
Proof. vm_refl. Qed.
Lemma D_97eb8 : decode_any W_97eb8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ebc : bv 32 := 0x01100793.
Lemma F_97ebc : fetch_word Asan.M.loaded_segments (0x97ebc : word) = Some W_97ebc.
Proof. vm_refl. Qed.
Lemma D_97ebc : decode_any W_97ebc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ec0 : bv 32 := 0x0107581b.
Lemma F_97ec0 : fetch_word Asan.M.loaded_segments (0x97ec0 : word) = Some W_97ec0.
Proof. vm_refl. Qed.
Lemma D_97ec0 : decode_any W_97ec0 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ec4 : bv 32 := 0xff45a883.
Lemma F_97ec4 : fetch_word Asan.M.loaded_segments (0x97ec4 : word) = Some W_97ec4.
Proof. vm_refl. Qed.
Lemma D_97ec4 : decode_any W_97ec4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ec8 : bv 32 := 0xff85a283.
Lemma F_97ec8 : fetch_word Asan.M.loaded_segments (0x97ec8 : word) = Some W_97ec8.
Proof. vm_refl. Qed.
Lemma D_97ec8 : decode_any W_97ec8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ecc : bv 32 := 0xffc5a303.
Lemma F_97ecc : fetch_word Asan.M.loaded_segments (0x97ecc : word) = Some W_97ecc.
Proof. vm_refl. Qed.
Lemma D_97ecc : decode_any W_97ecc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ed0 : bv 32 := 0x0005a703.
Lemma F_97ed0 : fetch_word Asan.M.loaded_segments (0x97ed0 : word) = Some W_97ed0.
Proof. vm_refl. Qed.
Lemma D_97ed0 : decode_any W_97ed0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ed4 : bv 32 := 0x01089393.
Lemma F_97ed4 : fetch_word Asan.M.loaded_segments (0x97ed4 : word) = Some W_97ed4.
Proof. vm_refl. Qed.
Lemma D_97ed4 : decode_any W_97ed4 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ed8 : bv 32 := 0x0108d89b.
Lemma F_97ed8 : fetch_word Asan.M.loaded_segments (0x97ed8 : word) = Some W_97ed8.
Proof. vm_refl. Qed.
Lemma D_97ed8 : decode_any W_97ed8 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97edc : bv 32 := 0x0103e833.
Lemma F_97edc : fetch_word Asan.M.loaded_segments (0x97edc : word) = Some W_97edc.
Proof. vm_refl. Qed.
Lemma D_97edc : decode_any W_97edc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ee0 : bv 32 := 0x01029393.
Lemma F_97ee0 : fetch_word Asan.M.loaded_segments (0x97ee0 : word) = Some W_97ee0.
Proof. vm_refl. Qed.
Lemma D_97ee0 : decode_any W_97ee0 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ee4 : bv 32 := 0x0102d29b.
Lemma F_97ee4 : fetch_word Asan.M.loaded_segments (0x97ee4 : word) = Some W_97ee4.
Proof. vm_refl. Qed.
Lemma D_97ee4 : decode_any W_97ee4 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ee8 : bv 32 := 0x0113e8b3.
Lemma F_97ee8 : fetch_word Asan.M.loaded_segments (0x97ee8 : word) = Some W_97ee8.
Proof. vm_refl. Qed.
Lemma D_97ee8 : decode_any W_97ee8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97eec : bv 32 := 0x01031393.
Lemma F_97eec : fetch_word Asan.M.loaded_segments (0x97eec : word) = Some W_97eec.
Proof. vm_refl. Qed.
Lemma D_97eec : decode_any W_97eec = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ef0 : bv 32 := 0x0103531b.
Lemma F_97ef0 : fetch_word Asan.M.loaded_segments (0x97ef0 : word) = Some W_97ef0.
Proof. vm_refl. Qed.
Lemma D_97ef0 : decode_any W_97ef0 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ef4 : bv 32 := 0x0053e2b3.
Lemma F_97ef4 : fetch_word Asan.M.loaded_segments (0x97ef4 : word) = Some W_97ef4.
Proof. vm_refl. Qed.
Lemma D_97ef4 : decode_any W_97ef4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ef8 : bv 32 := 0x01071393.
Lemma F_97ef8 : fetch_word Asan.M.loaded_segments (0x97ef8 : word) = Some W_97ef8.
Proof. vm_refl. Qed.
Lemma D_97ef8 : decode_any W_97ef8 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97efc : bv 32 := 0x0063e333.
Lemma F_97efc : fetch_word Asan.M.loaded_segments (0x97efc : word) = Some W_97efc.
Proof. vm_refl. Qed.
Lemma D_97efc : decode_any W_97efc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f00 : bv 32 := 0xff060613.
Lemma F_97f00 : fetch_word Asan.M.loaded_segments (0x97f00 : word) = Some W_97f00.
Proof. vm_refl. Qed.
Lemma D_97f00 : decode_any W_97f00 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f04 : bv 32 := 0x0106a023.
Lemma F_97f04 : fetch_word Asan.M.loaded_segments (0x97f04 : word) = Some W_97f04.
Proof. vm_refl. Qed.
Lemma D_97f04 : decode_any W_97f04 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f08 : bv 32 := 0x0116a223.
Lemma F_97f08 : fetch_word Asan.M.loaded_segments (0x97f08 : word) = Some W_97f08.
Proof. vm_refl. Qed.
Lemma D_97f08 : decode_any W_97f08 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f0c : bv 32 := 0x0056a423.
Lemma F_97f0c : fetch_word Asan.M.loaded_segments (0x97f0c : word) = Some W_97f0c.
Proof. vm_refl. Qed.
Lemma D_97f0c : decode_any W_97f0c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f10 : bv 32 := 0x0066a623.
Lemma F_97f10 : fetch_word Asan.M.loaded_segments (0x97f10 : word) = Some W_97f10.
Proof. vm_refl. Qed.
Lemma D_97f10 : decode_any W_97f10 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f14 : bv 32 := 0x01068693.
Lemma F_97f14 : fetch_word Asan.M.loaded_segments (0x97f14 : word) = Some W_97f14.
Proof. vm_refl. Qed.
Lemma D_97f14 : decode_any W_97f14 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f18 : bv 32 := 0x01058593.
Lemma F_97f18 : fetch_word Asan.M.loaded_segments (0x97f18 : word) = Some W_97f18.
Proof. vm_refl. Qed.
Lemma D_97f18 : decode_any W_97f18 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f1c : bv 32 := 0xfac7e2e3.
Lemma F_97f1c : fetch_word Asan.M.loaded_segments (0x97f1c : word) = Some W_97f1c.
Proof. vm_refl. Qed.
Lemma D_97f1c : decode_any W_97f1c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f20 : bv 32 := 0xff258593.
Lemma F_97f20 : fetch_word Asan.M.loaded_segments (0x97f20 : word) = Some W_97f20.
Proof. vm_refl. Qed.
Lemma D_97f20 : decode_any W_97f20 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f24 : bv 32 := 0x01000713.
Lemma F_97f24 : fetch_word Asan.M.loaded_segments (0x97f24 : word) = Some W_97f24.
Proof. vm_refl. Qed.
Lemma D_97f24 : decode_any W_97f24 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f28 : bv 32 := 0xf4e66ae3.
Lemma F_97f28 : fetch_word Asan.M.loaded_segments (0x97f28 : word) = Some W_97f28.
Proof. vm_refl. Qed.
Lemma D_97f28 : decode_any W_97f28 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f2c : bv 32 := 0x19c0006f.
Lemma F_97f2c : fetch_word Asan.M.loaded_segments (0x97f2c : word) = Some W_97f2c.
Proof. vm_refl. Qed.
Lemma D_97f2c : decode_any W_97f2c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f30 : bv 32 := 0x00050693.
Lemma F_97f30 : fetch_word Asan.M.loaded_segments (0x97f30 : word) = Some W_97f30.
Proof. vm_refl. Qed.
Lemma D_97f30 : decode_any W_97f30 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f34 : bv 32 := 0x00357793.
Lemma F_97f34 : fetch_word Asan.M.loaded_segments (0x97f34 : word) = Some W_97f34.
Proof. vm_refl. Qed.
Lemma D_97f34 : decode_any W_97f34 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f38 : bv 32 := 0xf2079ae3.
Lemma F_97f38 : fetch_word Asan.M.loaded_segments (0x97f38 : word) = Some W_97f38.
Proof. vm_refl. Qed.
Lemma D_97f38 : decode_any W_97f38 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f3c : bv 32 := 0x01000713.
Lemma F_97f3c : fetch_word Asan.M.loaded_segments (0x97f3c : word) = Some W_97f3c.
Proof. vm_refl. Qed.
Lemma D_97f3c : decode_any W_97f3c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f40 : bv 32 := 0x02e66c63.
Lemma F_97f40 : fetch_word Asan.M.loaded_segments (0x97f40 : word) = Some W_97f40.
Proof. vm_refl. Qed.
Lemma D_97f40 : decode_any W_97f40 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f44 : bv 32 := 0x00f00713.
Lemma F_97f44 : fetch_word Asan.M.loaded_segments (0x97f44 : word) = Some W_97f44.
Proof. vm_refl. Qed.
Lemma D_97f44 : decode_any W_97f44 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f48 : bv 32 := 0x0005a783.
Lemma F_97f48 : fetch_word Asan.M.loaded_segments (0x97f48 : word) = Some W_97f48.
Proof. vm_refl. Qed.
Lemma D_97f48 : decode_any W_97f48 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f4c : bv 32 := 0x0045a803.
Lemma F_97f4c : fetch_word Asan.M.loaded_segments (0x97f4c : word) = Some W_97f4c.
Proof. vm_refl. Qed.
Lemma D_97f4c : decode_any W_97f4c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f50 : bv 32 := 0x0085a883.
Lemma F_97f50 : fetch_word Asan.M.loaded_segments (0x97f50 : word) = Some W_97f50.
Proof. vm_refl. Qed.
Lemma D_97f50 : decode_any W_97f50 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f54 : bv 32 := 0x00c5a283.
Lemma F_97f54 : fetch_word Asan.M.loaded_segments (0x97f54 : word) = Some W_97f54.
Proof. vm_refl. Qed.
Lemma D_97f54 : decode_any W_97f54 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f58 : bv 32 := 0x01058593.
Lemma F_97f58 : fetch_word Asan.M.loaded_segments (0x97f58 : word) = Some W_97f58.
Proof. vm_refl. Qed.
Lemma D_97f58 : decode_any W_97f58 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f5c : bv 32 := 0xff060613.
Lemma F_97f5c : fetch_word Asan.M.loaded_segments (0x97f5c : word) = Some W_97f5c.
Proof. vm_refl. Qed.
Lemma D_97f5c : decode_any W_97f5c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f60 : bv 32 := 0x00f6a023.
Lemma F_97f60 : fetch_word Asan.M.loaded_segments (0x97f60 : word) = Some W_97f60.
Proof. vm_refl. Qed.
Lemma D_97f60 : decode_any W_97f60 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f64 : bv 32 := 0x0106a223.
Lemma F_97f64 : fetch_word Asan.M.loaded_segments (0x97f64 : word) = Some W_97f64.
Proof. vm_refl. Qed.
Lemma D_97f64 : decode_any W_97f64 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f68 : bv 32 := 0x0116a423.
Lemma F_97f68 : fetch_word Asan.M.loaded_segments (0x97f68 : word) = Some W_97f68.
Proof. vm_refl. Qed.
Lemma D_97f68 : decode_any W_97f68 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f6c : bv 32 := 0x0056a623.
Lemma F_97f6c : fetch_word Asan.M.loaded_segments (0x97f6c : word) = Some W_97f6c.
Proof. vm_refl. Qed.
Lemma D_97f6c : decode_any W_97f6c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f70 : bv 32 := 0x01068693.
Lemma F_97f70 : fetch_word Asan.M.loaded_segments (0x97f70 : word) = Some W_97f70.
Proof. vm_refl. Qed.
Lemma D_97f70 : decode_any W_97f70 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f74 : bv 32 := 0xfcc76ae3.
Lemma F_97f74 : fetch_word Asan.M.loaded_segments (0x97f74 : word) = Some W_97f74.
Proof. vm_refl. Qed.
Lemma D_97f74 : decode_any W_97f74 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f78 : bv 32 := 0x00800713.
Lemma F_97f78 : fetch_word Asan.M.loaded_segments (0x97f78 : word) = Some W_97f78.
Proof. vm_refl. Qed.
Lemma D_97f78 : decode_any W_97f78 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f7c : bv 32 := 0x00e66e63.
Lemma F_97f7c : fetch_word Asan.M.loaded_segments (0x97f7c : word) = Some W_97f7c.
Proof. vm_refl. Qed.
Lemma D_97f7c : decode_any W_97f7c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f80 : bv 32 := 0x0005a703.
Lemma F_97f80 : fetch_word Asan.M.loaded_segments (0x97f80 : word) = Some W_97f80.
Proof. vm_refl. Qed.
Lemma D_97f80 : decode_any W_97f80 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f84 : bv 32 := 0x0045a783.
Lemma F_97f84 : fetch_word Asan.M.loaded_segments (0x97f84 : word) = Some W_97f84.
Proof. vm_refl. Qed.
Lemma D_97f84 : decode_any W_97f84 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f88 : bv 32 := 0x00e6a023.
Lemma F_97f88 : fetch_word Asan.M.loaded_segments (0x97f88 : word) = Some W_97f88.
Proof. vm_refl. Qed.
Lemma D_97f88 : decode_any W_97f88 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f8c : bv 32 := 0x00f6a223.
Lemma F_97f8c : fetch_word Asan.M.loaded_segments (0x97f8c : word) = Some W_97f8c.
Proof. vm_refl. Qed.
Lemma D_97f8c : decode_any W_97f8c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f90 : bv 32 := 0x00868693.
Lemma F_97f90 : fetch_word Asan.M.loaded_segments (0x97f90 : word) = Some W_97f90.
Proof. vm_refl. Qed.
Lemma D_97f90 : decode_any W_97f90 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f94 : bv 32 := 0x00858593.
Lemma F_97f94 : fetch_word Asan.M.loaded_segments (0x97f94 : word) = Some W_97f94.
Proof. vm_refl. Qed.
Lemma D_97f94 : decode_any W_97f94 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f98 : bv 32 := 0x00467713.
Lemma F_97f98 : fetch_word Asan.M.loaded_segments (0x97f98 : word) = Some W_97f98.
Proof. vm_refl. Qed.
Lemma D_97f98 : decode_any W_97f98 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97f9c : bv 32 := 0x24070063.
Lemma F_97f9c : fetch_word Asan.M.loaded_segments (0x97f9c : word) = Some W_97f9c.
Proof. vm_refl. Qed.
Lemma D_97f9c : decode_any W_97f9c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fa0 : bv 32 := 0x0005a703.
Lemma F_97fa0 : fetch_word Asan.M.loaded_segments (0x97fa0 : word) = Some W_97fa0.
Proof. vm_refl. Qed.
Lemma D_97fa0 : decode_any W_97fa0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fa4 : bv 32 := 0x00458593.
Lemma F_97fa4 : fetch_word Asan.M.loaded_segments (0x97fa4 : word) = Some W_97fa4.
Proof. vm_refl. Qed.
Lemma D_97fa4 : decode_any W_97fa4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fa8 : bv 32 := 0x00e6a023.
Lemma F_97fa8 : fetch_word Asan.M.loaded_segments (0x97fa8 : word) = Some W_97fa8.
Proof. vm_refl. Qed.
Lemma D_97fa8 : decode_any W_97fa8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fac : bv 32 := 0x00468693.
Lemma F_97fac : fetch_word Asan.M.loaded_segments (0x97fac : word) = Some W_97fac.
Proof. vm_refl. Qed.
Lemma D_97fac : decode_any W_97fac = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fb0 : bv 32 := 0x22c0006f.
Lemma F_97fb0 : fetch_word Asan.M.loaded_segments (0x97fb0 : word) = Some W_97fb0.
Proof. vm_refl. Qed.
Lemma D_97fb0 : decode_any W_97fb0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fb4 : bv 32 := 0x00e68023.
Lemma F_97fb4 : fetch_word Asan.M.loaded_segments (0x97fb4 : word) = Some W_97fb4.
Proof. vm_refl. Qed.
Lemma D_97fb4 : decode_any W_97fb4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fb8 : bv 32 := 0x00168693.
Lemma F_97fb8 : fetch_word Asan.M.loaded_segments (0x97fb8 : word) = Some W_97fb8.
Proof. vm_refl. Qed.
Lemma D_97fb8 : decode_any W_97fb8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fbc : bv 32 := 0xfff60613.
Lemma F_97fbc : fetch_word Asan.M.loaded_segments (0x97fbc : word) = Some W_97fbc.
Proof. vm_refl. Qed.
Lemma D_97fbc : decode_any W_97fbc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fc0 : bv 32 := 0x01058593.
Lemma F_97fc0 : fetch_word Asan.M.loaded_segments (0x97fc0 : word) = Some W_97fc0.
Proof. vm_refl. Qed.
Lemma D_97fc0 : decode_any W_97fc0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fc4 : bv 32 := 0x01200793.
Lemma F_97fc4 : fetch_word Asan.M.loaded_segments (0x97fc4 : word) = Some W_97fc4.
Proof. vm_refl. Qed.
Lemma D_97fc4 : decode_any W_97fc4 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fc8 : bv 32 := 0x0087581b.
Lemma F_97fc8 : fetch_word Asan.M.loaded_segments (0x97fc8 : word) = Some W_97fc8.
Proof. vm_refl. Qed.
Lemma D_97fc8 : decode_any W_97fc8 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fcc : bv 32 := 0xff45a883.
Lemma F_97fcc : fetch_word Asan.M.loaded_segments (0x97fcc : word) = Some W_97fcc.
Proof. vm_refl. Qed.
Lemma D_97fcc : decode_any W_97fcc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fd0 : bv 32 := 0xff85a283.
Lemma F_97fd0 : fetch_word Asan.M.loaded_segments (0x97fd0 : word) = Some W_97fd0.
Proof. vm_refl. Qed.
Lemma D_97fd0 : decode_any W_97fd0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fd4 : bv 32 := 0xffc5a303.
Lemma F_97fd4 : fetch_word Asan.M.loaded_segments (0x97fd4 : word) = Some W_97fd4.
Proof. vm_refl. Qed.
Lemma D_97fd4 : decode_any W_97fd4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fd8 : bv 32 := 0x0005a703.
Lemma F_97fd8 : fetch_word Asan.M.loaded_segments (0x97fd8 : word) = Some W_97fd8.
Proof. vm_refl. Qed.
Lemma D_97fd8 : decode_any W_97fd8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fdc : bv 32 := 0x01889393.
Lemma F_97fdc : fetch_word Asan.M.loaded_segments (0x97fdc : word) = Some W_97fdc.
Proof. vm_refl. Qed.
Lemma D_97fdc : decode_any W_97fdc = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fe0 : bv 32 := 0x0088d89b.
Lemma F_97fe0 : fetch_word Asan.M.loaded_segments (0x97fe0 : word) = Some W_97fe0.
Proof. vm_refl. Qed.
Lemma D_97fe0 : decode_any W_97fe0 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fe4 : bv 32 := 0x0103e833.
Lemma F_97fe4 : fetch_word Asan.M.loaded_segments (0x97fe4 : word) = Some W_97fe4.
Proof. vm_refl. Qed.
Lemma D_97fe4 : decode_any W_97fe4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fe8 : bv 32 := 0x01829393.
Lemma F_97fe8 : fetch_word Asan.M.loaded_segments (0x97fe8 : word) = Some W_97fe8.
Proof. vm_refl. Qed.
Lemma D_97fe8 : decode_any W_97fe8 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97fec : bv 32 := 0x0082d29b.
Lemma F_97fec : fetch_word Asan.M.loaded_segments (0x97fec : word) = Some W_97fec.
Proof. vm_refl. Qed.
Lemma D_97fec : decode_any W_97fec = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ff0 : bv 32 := 0x0113e8b3.
Lemma F_97ff0 : fetch_word Asan.M.loaded_segments (0x97ff0 : word) = Some W_97ff0.
Proof. vm_refl. Qed.
Lemma D_97ff0 : decode_any W_97ff0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ff4 : bv 32 := 0x01831393.
Lemma F_97ff4 : fetch_word Asan.M.loaded_segments (0x97ff4 : word) = Some W_97ff4.
Proof. vm_refl. Qed.
Lemma D_97ff4 : decode_any W_97ff4 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ff8 : bv 32 := 0x0083531b.
Lemma F_97ff8 : fetch_word Asan.M.loaded_segments (0x97ff8 : word) = Some W_97ff8.
Proof. vm_refl. Qed.
Lemma D_97ff8 : decode_any W_97ff8 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ffc : bv 32 := 0x0053e2b3.
Lemma F_97ffc : fetch_word Asan.M.loaded_segments (0x97ffc : word) = Some W_97ffc.
Proof. vm_refl. Qed.
Lemma D_97ffc : decode_any W_97ffc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98000 : bv 32 := 0x01871393.
Lemma F_98000 : fetch_word Asan.M.loaded_segments (0x98000 : word) = Some W_98000.
Proof. vm_refl. Qed.
Lemma D_98000 : decode_any W_98000 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98004 : bv 32 := 0x0063e333.
Lemma F_98004 : fetch_word Asan.M.loaded_segments (0x98004 : word) = Some W_98004.
Proof. vm_refl. Qed.
Lemma D_98004 : decode_any W_98004 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98008 : bv 32 := 0xff060613.
Lemma F_98008 : fetch_word Asan.M.loaded_segments (0x98008 : word) = Some W_98008.
Proof. vm_refl. Qed.
Lemma D_98008 : decode_any W_98008 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9800c : bv 32 := 0x0106a023.
Lemma F_9800c : fetch_word Asan.M.loaded_segments (0x9800c : word) = Some W_9800c.
Proof. vm_refl. Qed.
Lemma D_9800c : decode_any W_9800c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98010 : bv 32 := 0x0116a223.
Lemma F_98010 : fetch_word Asan.M.loaded_segments (0x98010 : word) = Some W_98010.
Proof. vm_refl. Qed.
Lemma D_98010 : decode_any W_98010 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98014 : bv 32 := 0x0056a423.
Lemma F_98014 : fetch_word Asan.M.loaded_segments (0x98014 : word) = Some W_98014.
Proof. vm_refl. Qed.
Lemma D_98014 : decode_any W_98014 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98018 : bv 32 := 0x0066a623.
Lemma F_98018 : fetch_word Asan.M.loaded_segments (0x98018 : word) = Some W_98018.
Proof. vm_refl. Qed.
Lemma D_98018 : decode_any W_98018 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9801c : bv 32 := 0x01068693.
Lemma F_9801c : fetch_word Asan.M.loaded_segments (0x9801c : word) = Some W_9801c.
Proof. vm_refl. Qed.
Lemma D_9801c : decode_any W_9801c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98020 : bv 32 := 0x01058593.
Lemma F_98020 : fetch_word Asan.M.loaded_segments (0x98020 : word) = Some W_98020.
Proof. vm_refl. Qed.
Lemma D_98020 : decode_any W_98020 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98024 : bv 32 := 0xfac7e2e3.
Lemma F_98024 : fetch_word Asan.M.loaded_segments (0x98024 : word) = Some W_98024.
Proof. vm_refl. Qed.
Lemma D_98024 : decode_any W_98024 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98028 : bv 32 := 0xff158593.
Lemma F_98028 : fetch_word Asan.M.loaded_segments (0x98028 : word) = Some W_98028.
Proof. vm_refl. Qed.
Lemma D_98028 : decode_any W_98028 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9802c : bv 32 := 0x01000713.
Lemma F_9802c : fetch_word Asan.M.loaded_segments (0x9802c : word) = Some W_9802c.
Proof. vm_refl. Qed.
Lemma D_9802c : decode_any W_9802c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98030 : bv 32 := 0xe4e666e3.
Lemma F_98030 : fetch_word Asan.M.loaded_segments (0x98030 : word) = Some W_98030.
Proof. vm_refl. Qed.
Lemma D_98030 : decode_any W_98030 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98034 : bv 32 := 0x0940006f.
Lemma F_98034 : fetch_word Asan.M.loaded_segments (0x98034 : word) = Some W_98034.
Proof. vm_refl. Qed.
Lemma D_98034 : decode_any W_98034 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98038 : bv 32 := 0x00875793.
Lemma F_98038 : fetch_word Asan.M.loaded_segments (0x98038 : word) = Some W_98038.
Proof. vm_refl. Qed.
Lemma D_98038 : decode_any W_98038 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9803c : bv 32 := 0x01075813.
Lemma F_9803c : fetch_word Asan.M.loaded_segments (0x9803c : word) = Some W_9803c.
Proof. vm_refl. Qed.
Lemma D_9803c : decode_any W_9803c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98040 : bv 32 := 0xffd60613.
Lemma F_98040 : fetch_word Asan.M.loaded_segments (0x98040 : word) = Some W_98040.
Proof. vm_refl. Qed.
Lemma D_98040 : decode_any W_98040 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98044 : bv 32 := 0x00e68023.
Lemma F_98044 : fetch_word Asan.M.loaded_segments (0x98044 : word) = Some W_98044.
Proof. vm_refl. Qed.
Lemma D_98044 : decode_any W_98044 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98048 : bv 32 := 0x00f680a3.
Lemma F_98048 : fetch_word Asan.M.loaded_segments (0x98048 : word) = Some W_98048.
Proof. vm_refl. Qed.
Lemma D_98048 : decode_any W_98048 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9804c : bv 32 := 0x01068123.
Lemma F_9804c : fetch_word Asan.M.loaded_segments (0x9804c : word) = Some W_9804c.
Proof. vm_refl. Qed.
Lemma D_9804c : decode_any W_9804c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98050 : bv 32 := 0x00368693.
Lemma F_98050 : fetch_word Asan.M.loaded_segments (0x98050 : word) = Some W_98050.
Proof. vm_refl. Qed.
Lemma D_98050 : decode_any W_98050 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98054 : bv 32 := 0x01058593.
Lemma F_98054 : fetch_word Asan.M.loaded_segments (0x98054 : word) = Some W_98054.
Proof. vm_refl. Qed.
Lemma D_98054 : decode_any W_98054 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98058 : bv 32 := 0x01000793.
Lemma F_98058 : fetch_word Asan.M.loaded_segments (0x98058 : word) = Some W_98058.
Proof. vm_refl. Qed.
Lemma D_98058 : decode_any W_98058 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9805c : bv 32 := 0x0187581b.
Lemma F_9805c : fetch_word Asan.M.loaded_segments (0x9805c : word) = Some W_9805c.
Proof. vm_refl. Qed.
Lemma D_9805c : decode_any W_9805c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98060 : bv 32 := 0xff45a883.
Lemma F_98060 : fetch_word Asan.M.loaded_segments (0x98060 : word) = Some W_98060.
Proof. vm_refl. Qed.
Lemma D_98060 : decode_any W_98060 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98064 : bv 32 := 0xff85a283.
Lemma F_98064 : fetch_word Asan.M.loaded_segments (0x98064 : word) = Some W_98064.
Proof. vm_refl. Qed.
Lemma D_98064 : decode_any W_98064 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98068 : bv 32 := 0xffc5a303.
Lemma F_98068 : fetch_word Asan.M.loaded_segments (0x98068 : word) = Some W_98068.
Proof. vm_refl. Qed.
Lemma D_98068 : decode_any W_98068 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9806c : bv 32 := 0x0005a703.
Lemma F_9806c : fetch_word Asan.M.loaded_segments (0x9806c : word) = Some W_9806c.
Proof. vm_refl. Qed.
Lemma D_9806c : decode_any W_9806c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98070 : bv 32 := 0x00889393.
Lemma F_98070 : fetch_word Asan.M.loaded_segments (0x98070 : word) = Some W_98070.
Proof. vm_refl. Qed.
Lemma D_98070 : decode_any W_98070 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98074 : bv 32 := 0x0188d89b.
Lemma F_98074 : fetch_word Asan.M.loaded_segments (0x98074 : word) = Some W_98074.
Proof. vm_refl. Qed.
Lemma D_98074 : decode_any W_98074 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98078 : bv 32 := 0x0103e833.
Lemma F_98078 : fetch_word Asan.M.loaded_segments (0x98078 : word) = Some W_98078.
Proof. vm_refl. Qed.
Lemma D_98078 : decode_any W_98078 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9807c : bv 32 := 0x00829393.
Lemma F_9807c : fetch_word Asan.M.loaded_segments (0x9807c : word) = Some W_9807c.
Proof. vm_refl. Qed.
Lemma D_9807c : decode_any W_9807c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98080 : bv 32 := 0x0182d29b.
Lemma F_98080 : fetch_word Asan.M.loaded_segments (0x98080 : word) = Some W_98080.
Proof. vm_refl. Qed.
Lemma D_98080 : decode_any W_98080 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98084 : bv 32 := 0x0113e8b3.
Lemma F_98084 : fetch_word Asan.M.loaded_segments (0x98084 : word) = Some W_98084.
Proof. vm_refl. Qed.
Lemma D_98084 : decode_any W_98084 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98088 : bv 32 := 0x00831393.
Lemma F_98088 : fetch_word Asan.M.loaded_segments (0x98088 : word) = Some W_98088.
Proof. vm_refl. Qed.
Lemma D_98088 : decode_any W_98088 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9808c : bv 32 := 0x0183531b.
Lemma F_9808c : fetch_word Asan.M.loaded_segments (0x9808c : word) = Some W_9808c.
Proof. vm_refl. Qed.
Lemma D_9808c : decode_any W_9808c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98090 : bv 32 := 0x0053e2b3.
Lemma F_98090 : fetch_word Asan.M.loaded_segments (0x98090 : word) = Some W_98090.
Proof. vm_refl. Qed.
Lemma D_98090 : decode_any W_98090 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98094 : bv 32 := 0x00871393.
Lemma F_98094 : fetch_word Asan.M.loaded_segments (0x98094 : word) = Some W_98094.
Proof. vm_refl. Qed.
Lemma D_98094 : decode_any W_98094 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98098 : bv 32 := 0x0063e333.
Lemma F_98098 : fetch_word Asan.M.loaded_segments (0x98098 : word) = Some W_98098.
Proof. vm_refl. Qed.
Lemma D_98098 : decode_any W_98098 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9809c : bv 32 := 0xff060613.
Lemma F_9809c : fetch_word Asan.M.loaded_segments (0x9809c : word) = Some W_9809c.
Proof. vm_refl. Qed.
Lemma D_9809c : decode_any W_9809c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980a0 : bv 32 := 0x0106a023.
Lemma F_980a0 : fetch_word Asan.M.loaded_segments (0x980a0 : word) = Some W_980a0.
Proof. vm_refl. Qed.
Lemma D_980a0 : decode_any W_980a0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980a4 : bv 32 := 0x0116a223.
Lemma F_980a4 : fetch_word Asan.M.loaded_segments (0x980a4 : word) = Some W_980a4.
Proof. vm_refl. Qed.
Lemma D_980a4 : decode_any W_980a4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980a8 : bv 32 := 0x0056a423.
Lemma F_980a8 : fetch_word Asan.M.loaded_segments (0x980a8 : word) = Some W_980a8.
Proof. vm_refl. Qed.
Lemma D_980a8 : decode_any W_980a8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980ac : bv 32 := 0x0066a623.
Lemma F_980ac : fetch_word Asan.M.loaded_segments (0x980ac : word) = Some W_980ac.
Proof. vm_refl. Qed.
Lemma D_980ac : decode_any W_980ac = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980b0 : bv 32 := 0x01068693.
Lemma F_980b0 : fetch_word Asan.M.loaded_segments (0x980b0 : word) = Some W_980b0.
Proof. vm_refl. Qed.
Lemma D_980b0 : decode_any W_980b0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980b4 : bv 32 := 0x01058593.
Lemma F_980b4 : fetch_word Asan.M.loaded_segments (0x980b4 : word) = Some W_980b4.
Proof. vm_refl. Qed.
Lemma D_980b4 : decode_any W_980b4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980b8 : bv 32 := 0xfac7e2e3.
Lemma F_980b8 : fetch_word Asan.M.loaded_segments (0x980b8 : word) = Some W_980b8.
Proof. vm_refl. Qed.
Lemma D_980b8 : decode_any W_980b8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980bc : bv 32 := 0xff358593.
Lemma F_980bc : fetch_word Asan.M.loaded_segments (0x980bc : word) = Some W_980bc.
Proof. vm_refl. Qed.
Lemma D_980bc : decode_any W_980bc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980c0 : bv 32 := 0x01000713.
Lemma F_980c0 : fetch_word Asan.M.loaded_segments (0x980c0 : word) = Some W_980c0.
Proof. vm_refl. Qed.
Lemma D_980c0 : decode_any W_980c0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980c4 : bv 32 := 0xdae66ce3.
Lemma F_980c4 : fetch_word Asan.M.loaded_segments (0x980c4 : word) = Some W_980c4.
Proof. vm_refl. Qed.
Lemma D_980c4 : decode_any W_980c4 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980c8 : bv 32 := 0x0005c703.
Lemma F_980c8 : fetch_word Asan.M.loaded_segments (0x980c8 : word) = Some W_980c8.
Proof. vm_refl. Qed.
Lemma D_980c8 : decode_any W_980c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980cc : bv 32 := 0x0015c783.
Lemma F_980cc : fetch_word Asan.M.loaded_segments (0x980cc : word) = Some W_980cc.
Proof. vm_refl. Qed.
Lemma D_980cc : decode_any W_980cc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980d0 : bv 32 := 0x0025c803.
Lemma F_980d0 : fetch_word Asan.M.loaded_segments (0x980d0 : word) = Some W_980d0.
Proof. vm_refl. Qed.
Lemma D_980d0 : decode_any W_980d0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980d4 : bv 32 := 0x0035c883.
Lemma F_980d4 : fetch_word Asan.M.loaded_segments (0x980d4 : word) = Some W_980d4.
Proof. vm_refl. Qed.
Lemma D_980d4 : decode_any W_980d4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980d8 : bv 32 := 0x0045c283.
Lemma F_980d8 : fetch_word Asan.M.loaded_segments (0x980d8 : word) = Some W_980d8.
Proof. vm_refl. Qed.
Lemma D_980d8 : decode_any W_980d8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980dc : bv 32 := 0x0055c303.
Lemma F_980dc : fetch_word Asan.M.loaded_segments (0x980dc : word) = Some W_980dc.
Proof. vm_refl. Qed.
Lemma D_980dc : decode_any W_980dc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980e0 : bv 32 := 0x0065c383.
Lemma F_980e0 : fetch_word Asan.M.loaded_segments (0x980e0 : word) = Some W_980e0.
Proof. vm_refl. Qed.
Lemma D_980e0 : decode_any W_980e0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980e4 : bv 32 := 0x0075ce03.
Lemma F_980e4 : fetch_word Asan.M.loaded_segments (0x980e4 : word) = Some W_980e4.
Proof. vm_refl. Qed.
Lemma D_980e4 : decode_any W_980e4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980e8 : bv 32 := 0x00e68023.
Lemma F_980e8 : fetch_word Asan.M.loaded_segments (0x980e8 : word) = Some W_980e8.
Proof. vm_refl. Qed.
Lemma D_980e8 : decode_any W_980e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980ec : bv 32 := 0x00f680a3.
Lemma F_980ec : fetch_word Asan.M.loaded_segments (0x980ec : word) = Some W_980ec.
Proof. vm_refl. Qed.
Lemma D_980ec : decode_any W_980ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980f0 : bv 32 := 0x01068123.
Lemma F_980f0 : fetch_word Asan.M.loaded_segments (0x980f0 : word) = Some W_980f0.
Proof. vm_refl. Qed.
Lemma D_980f0 : decode_any W_980f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980f4 : bv 32 := 0x011681a3.
Lemma F_980f4 : fetch_word Asan.M.loaded_segments (0x980f4 : word) = Some W_980f4.
Proof. vm_refl. Qed.
Lemma D_980f4 : decode_any W_980f4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980f8 : bv 32 := 0x0085c703.
Lemma F_980f8 : fetch_word Asan.M.loaded_segments (0x980f8 : word) = Some W_980f8.
Proof. vm_refl. Qed.
Lemma D_980f8 : decode_any W_980f8 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_980fc : bv 32 := 0x0095c783.
Lemma F_980fc : fetch_word Asan.M.loaded_segments (0x980fc : word) = Some W_980fc.
Proof. vm_refl. Qed.
Lemma D_980fc : decode_any W_980fc = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98100 : bv 32 := 0x00a5c803.
Lemma F_98100 : fetch_word Asan.M.loaded_segments (0x98100 : word) = Some W_98100.
Proof. vm_refl. Qed.
Lemma D_98100 : decode_any W_98100 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98104 : bv 32 := 0x00b5c883.
Lemma F_98104 : fetch_word Asan.M.loaded_segments (0x98104 : word) = Some W_98104.
Proof. vm_refl. Qed.
Lemma D_98104 : decode_any W_98104 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98108 : bv 32 := 0x00568223.
Lemma F_98108 : fetch_word Asan.M.loaded_segments (0x98108 : word) = Some W_98108.
Proof. vm_refl. Qed.
Lemma D_98108 : decode_any W_98108 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9810c : bv 32 := 0x006682a3.
Lemma F_9810c : fetch_word Asan.M.loaded_segments (0x9810c : word) = Some W_9810c.
Proof. vm_refl. Qed.
Lemma D_9810c : decode_any W_9810c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98110 : bv 32 := 0x00768323.
Lemma F_98110 : fetch_word Asan.M.loaded_segments (0x98110 : word) = Some W_98110.
Proof. vm_refl. Qed.
Lemma D_98110 : decode_any W_98110 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98114 : bv 32 := 0x01c683a3.
Lemma F_98114 : fetch_word Asan.M.loaded_segments (0x98114 : word) = Some W_98114.
Proof. vm_refl. Qed.
Lemma D_98114 : decode_any W_98114 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98118 : bv 32 := 0x00c5c283.
Lemma F_98118 : fetch_word Asan.M.loaded_segments (0x98118 : word) = Some W_98118.
Proof. vm_refl. Qed.
Lemma D_98118 : decode_any W_98118 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9811c : bv 32 := 0x00d5c303.
Lemma F_9811c : fetch_word Asan.M.loaded_segments (0x9811c : word) = Some W_9811c.
Proof. vm_refl. Qed.
Lemma D_9811c : decode_any W_9811c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98120 : bv 32 := 0x00e5c383.
Lemma F_98120 : fetch_word Asan.M.loaded_segments (0x98120 : word) = Some W_98120.
Proof. vm_refl. Qed.
Lemma D_98120 : decode_any W_98120 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98124 : bv 32 := 0x00f5ce03.
Lemma F_98124 : fetch_word Asan.M.loaded_segments (0x98124 : word) = Some W_98124.
Proof. vm_refl. Qed.
Lemma D_98124 : decode_any W_98124 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98128 : bv 32 := 0x01058593.
Lemma F_98128 : fetch_word Asan.M.loaded_segments (0x98128 : word) = Some W_98128.
Proof. vm_refl. Qed.
Lemma D_98128 : decode_any W_98128 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9812c : bv 32 := 0x00e68423.
Lemma F_9812c : fetch_word Asan.M.loaded_segments (0x9812c : word) = Some W_9812c.
Proof. vm_refl. Qed.
Lemma D_9812c : decode_any W_9812c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98130 : bv 32 := 0x00f684a3.
Lemma F_98130 : fetch_word Asan.M.loaded_segments (0x98130 : word) = Some W_98130.
Proof. vm_refl. Qed.
Lemma D_98130 : decode_any W_98130 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98134 : bv 32 := 0x01068523.
Lemma F_98134 : fetch_word Asan.M.loaded_segments (0x98134 : word) = Some W_98134.
Proof. vm_refl. Qed.
Lemma D_98134 : decode_any W_98134 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98138 : bv 32 := 0x011685a3.
Lemma F_98138 : fetch_word Asan.M.loaded_segments (0x98138 : word) = Some W_98138.
Proof. vm_refl. Qed.
Lemma D_98138 : decode_any W_98138 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9813c : bv 32 := 0x01068713.
Lemma F_9813c : fetch_word Asan.M.loaded_segments (0x9813c : word) = Some W_9813c.
Proof. vm_refl. Qed.
Lemma D_9813c : decode_any W_9813c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98140 : bv 32 := 0x00568623.
Lemma F_98140 : fetch_word Asan.M.loaded_segments (0x98140 : word) = Some W_98140.
Proof. vm_refl. Qed.
Lemma D_98140 : decode_any W_98140 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98144 : bv 32 := 0x006686a3.
Lemma F_98144 : fetch_word Asan.M.loaded_segments (0x98144 : word) = Some W_98144.
Proof. vm_refl. Qed.
Lemma D_98144 : decode_any W_98144 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98148 : bv 32 := 0x00768723.
Lemma F_98148 : fetch_word Asan.M.loaded_segments (0x98148 : word) = Some W_98148.
Proof. vm_refl. Qed.
Lemma D_98148 : decode_any W_98148 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9814c : bv 32 := 0x01c687a3.
Lemma F_9814c : fetch_word Asan.M.loaded_segments (0x9814c : word) = Some W_9814c.
Proof. vm_refl. Qed.
Lemma D_9814c : decode_any W_9814c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98150 : bv 32 := 0x00070693.
Lemma F_98150 : fetch_word Asan.M.loaded_segments (0x98150 : word) = Some W_98150.
Proof. vm_refl. Qed.
Lemma D_98150 : decode_any W_98150 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98154 : bv 32 := 0x00867713.
Lemma F_98154 : fetch_word Asan.M.loaded_segments (0x98154 : word) = Some W_98154.
Proof. vm_refl. Qed.
Lemma D_98154 : decode_any W_98154 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98158 : bv 32 := 0xd20706e3.
Lemma F_98158 : fetch_word Asan.M.loaded_segments (0x98158 : word) = Some W_98158.
Proof. vm_refl. Qed.
Lemma D_98158 : decode_any W_98158 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9815c : bv 32 := 0x0005c703.
Lemma F_9815c : fetch_word Asan.M.loaded_segments (0x9815c : word) = Some W_9815c.
Proof. vm_refl. Qed.
Lemma D_9815c : decode_any W_9815c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98160 : bv 32 := 0x0015c783.
Lemma F_98160 : fetch_word Asan.M.loaded_segments (0x98160 : word) = Some W_98160.
Proof. vm_refl. Qed.
Lemma D_98160 : decode_any W_98160 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98164 : bv 32 := 0x0025c803.
Lemma F_98164 : fetch_word Asan.M.loaded_segments (0x98164 : word) = Some W_98164.
Proof. vm_refl. Qed.
Lemma D_98164 : decode_any W_98164 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98168 : bv 32 := 0x0035c883.
Lemma F_98168 : fetch_word Asan.M.loaded_segments (0x98168 : word) = Some W_98168.
Proof. vm_refl. Qed.
Lemma D_98168 : decode_any W_98168 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9816c : bv 32 := 0x0045c283.
Lemma F_9816c : fetch_word Asan.M.loaded_segments (0x9816c : word) = Some W_9816c.
Proof. vm_refl. Qed.
Lemma D_9816c : decode_any W_9816c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98170 : bv 32 := 0x0055c303.
Lemma F_98170 : fetch_word Asan.M.loaded_segments (0x98170 : word) = Some W_98170.
Proof. vm_refl. Qed.
Lemma D_98170 : decode_any W_98170 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98174 : bv 32 := 0x0065c383.
Lemma F_98174 : fetch_word Asan.M.loaded_segments (0x98174 : word) = Some W_98174.
Proof. vm_refl. Qed.
Lemma D_98174 : decode_any W_98174 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98178 : bv 32 := 0x0075ce03.
Lemma F_98178 : fetch_word Asan.M.loaded_segments (0x98178 : word) = Some W_98178.
Proof. vm_refl. Qed.
Lemma D_98178 : decode_any W_98178 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9817c : bv 32 := 0x00858593.
Lemma F_9817c : fetch_word Asan.M.loaded_segments (0x9817c : word) = Some W_9817c.
Proof. vm_refl. Qed.
Lemma D_9817c : decode_any W_9817c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98180 : bv 32 := 0x00e68023.
Lemma F_98180 : fetch_word Asan.M.loaded_segments (0x98180 : word) = Some W_98180.
Proof. vm_refl. Qed.
Lemma D_98180 : decode_any W_98180 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98184 : bv 32 := 0x00f680a3.
Lemma F_98184 : fetch_word Asan.M.loaded_segments (0x98184 : word) = Some W_98184.
Proof. vm_refl. Qed.
Lemma D_98184 : decode_any W_98184 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98188 : bv 32 := 0x01068123.
Lemma F_98188 : fetch_word Asan.M.loaded_segments (0x98188 : word) = Some W_98188.
Proof. vm_refl. Qed.
Lemma D_98188 : decode_any W_98188 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9818c : bv 32 := 0x011681a3.
Lemma F_9818c : fetch_word Asan.M.loaded_segments (0x9818c : word) = Some W_9818c.
Proof. vm_refl. Qed.
Lemma D_9818c : decode_any W_9818c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98190 : bv 32 := 0x00868713.
Lemma F_98190 : fetch_word Asan.M.loaded_segments (0x98190 : word) = Some W_98190.
Proof. vm_refl. Qed.
Lemma D_98190 : decode_any W_98190 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98194 : bv 32 := 0x00568223.
Lemma F_98194 : fetch_word Asan.M.loaded_segments (0x98194 : word) = Some W_98194.
Proof. vm_refl. Qed.
Lemma D_98194 : decode_any W_98194 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98198 : bv 32 := 0x006682a3.
Lemma F_98198 : fetch_word Asan.M.loaded_segments (0x98198 : word) = Some W_98198.
Proof. vm_refl. Qed.
Lemma D_98198 : decode_any W_98198 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9819c : bv 32 := 0x00768323.
Lemma F_9819c : fetch_word Asan.M.loaded_segments (0x9819c : word) = Some W_9819c.
Proof. vm_refl. Qed.
Lemma D_9819c : decode_any W_9819c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981a0 : bv 32 := 0x01c683a3.
Lemma F_981a0 : fetch_word Asan.M.loaded_segments (0x981a0 : word) = Some W_981a0.
Proof. vm_refl. Qed.
Lemma D_981a0 : decode_any W_981a0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981a4 : bv 32 := 0x00070693.
Lemma F_981a4 : fetch_word Asan.M.loaded_segments (0x981a4 : word) = Some W_981a4.
Proof. vm_refl. Qed.
Lemma D_981a4 : decode_any W_981a4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981a8 : bv 32 := 0x00467713.
Lemma F_981a8 : fetch_word Asan.M.loaded_segments (0x981a8 : word) = Some W_981a8.
Proof. vm_refl. Qed.
Lemma D_981a8 : decode_any W_981a8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981ac : bv 32 := 0x02070863.
Lemma F_981ac : fetch_word Asan.M.loaded_segments (0x981ac : word) = Some W_981ac.
Proof. vm_refl. Qed.
Lemma D_981ac : decode_any W_981ac = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981b0 : bv 32 := 0x0005c703.
Lemma F_981b0 : fetch_word Asan.M.loaded_segments (0x981b0 : word) = Some W_981b0.
Proof. vm_refl. Qed.
Lemma D_981b0 : decode_any W_981b0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981b4 : bv 32 := 0x0015c783.
Lemma F_981b4 : fetch_word Asan.M.loaded_segments (0x981b4 : word) = Some W_981b4.
Proof. vm_refl. Qed.
Lemma D_981b4 : decode_any W_981b4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981b8 : bv 32 := 0x0025c803.
Lemma F_981b8 : fetch_word Asan.M.loaded_segments (0x981b8 : word) = Some W_981b8.
Proof. vm_refl. Qed.
Lemma D_981b8 : decode_any W_981b8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981bc : bv 32 := 0x0035c883.
Lemma F_981bc : fetch_word Asan.M.loaded_segments (0x981bc : word) = Some W_981bc.
Proof. vm_refl. Qed.
Lemma D_981bc : decode_any W_981bc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981c0 : bv 32 := 0x00458593.
Lemma F_981c0 : fetch_word Asan.M.loaded_segments (0x981c0 : word) = Some W_981c0.
Proof. vm_refl. Qed.
Lemma D_981c0 : decode_any W_981c0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981c4 : bv 32 := 0x00468293.
Lemma F_981c4 : fetch_word Asan.M.loaded_segments (0x981c4 : word) = Some W_981c4.
Proof. vm_refl. Qed.
Lemma D_981c4 : decode_any W_981c4 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981c8 : bv 32 := 0x00e68023.
Lemma F_981c8 : fetch_word Asan.M.loaded_segments (0x981c8 : word) = Some W_981c8.
Proof. vm_refl. Qed.
Lemma D_981c8 : decode_any W_981c8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981cc : bv 32 := 0x00f680a3.
Lemma F_981cc : fetch_word Asan.M.loaded_segments (0x981cc : word) = Some W_981cc.
Proof. vm_refl. Qed.
Lemma D_981cc : decode_any W_981cc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981d0 : bv 32 := 0x01068123.
Lemma F_981d0 : fetch_word Asan.M.loaded_segments (0x981d0 : word) = Some W_981d0.
Proof. vm_refl. Qed.
Lemma D_981d0 : decode_any W_981d0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981d4 : bv 32 := 0x011681a3.
Lemma F_981d4 : fetch_word Asan.M.loaded_segments (0x981d4 : word) = Some W_981d4.
Proof. vm_refl. Qed.
Lemma D_981d4 : decode_any W_981d4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981d8 : bv 32 := 0x00028693.
Lemma F_981d8 : fetch_word Asan.M.loaded_segments (0x981d8 : word) = Some W_981d8.
Proof. vm_refl. Qed.
Lemma D_981d8 : decode_any W_981d8 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981dc : bv 32 := 0x00267713.
Lemma F_981dc : fetch_word Asan.M.loaded_segments (0x981dc : word) = Some W_981dc.
Proof. vm_refl. Qed.
Lemma D_981dc : decode_any W_981dc = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981e0 : bv 32 := 0x00071863.
Lemma F_981e0 : fetch_word Asan.M.loaded_segments (0x981e0 : word) = Some W_981e0.
Proof. vm_refl. Qed.
Lemma D_981e0 : decode_any W_981e0 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981e4 : bv 32 := 0x00167613.
Lemma F_981e4 : fetch_word Asan.M.loaded_segments (0x981e4 : word) = Some W_981e4.
Proof. vm_refl. Qed.
Lemma D_981e4 : decode_any W_981e4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981e8 : bv 32 := 0x02061663.
Lemma F_981e8 : fetch_word Asan.M.loaded_segments (0x981e8 : word) = Some W_981e8.
Proof. vm_refl. Qed.
Lemma D_981e8 : decode_any W_981e8 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981ec : bv 32 := 0x00008067.
Lemma F_981ec : fetch_word Asan.M.loaded_segments (0x981ec : word) = Some W_981ec.
Proof. vm_refl. Qed.
Lemma D_981ec : decode_any W_981ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981f0 : bv 32 := 0x0005c703.
Lemma F_981f0 : fetch_word Asan.M.loaded_segments (0x981f0 : word) = Some W_981f0.
Proof. vm_refl. Qed.
Lemma D_981f0 : decode_any W_981f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981f4 : bv 32 := 0x0015c783.
Lemma F_981f4 : fetch_word Asan.M.loaded_segments (0x981f4 : word) = Some W_981f4.
Proof. vm_refl. Qed.
Lemma D_981f4 : decode_any W_981f4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981f8 : bv 32 := 0x00258593.
Lemma F_981f8 : fetch_word Asan.M.loaded_segments (0x981f8 : word) = Some W_981f8.
Proof. vm_refl. Qed.
Lemma D_981f8 : decode_any W_981f8 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_981fc : bv 32 := 0x00268813.
Lemma F_981fc : fetch_word Asan.M.loaded_segments (0x981fc : word) = Some W_981fc.
Proof. vm_refl. Qed.
Lemma D_981fc : decode_any W_981fc = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98200 : bv 32 := 0x00e68023.
Lemma F_98200 : fetch_word Asan.M.loaded_segments (0x98200 : word) = Some W_98200.
Proof. vm_refl. Qed.
Lemma D_98200 : decode_any W_98200 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98204 : bv 32 := 0x00f680a3.
Lemma F_98204 : fetch_word Asan.M.loaded_segments (0x98204 : word) = Some W_98204.
Proof. vm_refl. Qed.
Lemma D_98204 : decode_any W_98204 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98208 : bv 32 := 0x00080693.
Lemma F_98208 : fetch_word Asan.M.loaded_segments (0x98208 : word) = Some W_98208.
Proof. vm_refl. Qed.
Lemma D_98208 : decode_any W_98208 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9820c : bv 32 := 0x00167613.
Lemma F_9820c : fetch_word Asan.M.loaded_segments (0x9820c : word) = Some W_9820c.
Proof. vm_refl. Qed.
Lemma D_9820c : decode_any W_9820c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98210 : bv 32 := 0xfc060ee3.
Lemma F_98210 : fetch_word Asan.M.loaded_segments (0x98210 : word) = Some W_98210.
Proof. vm_refl. Qed.
Lemma D_98210 : decode_any W_98210 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98214 : bv 32 := 0x0005c583.
Lemma F_98214 : fetch_word Asan.M.loaded_segments (0x98214 : word) = Some W_98214.
Proof. vm_refl. Qed.
Lemma D_98214 : decode_any W_98214 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98218 : bv 32 := 0x00b68023.
Lemma F_98218 : fetch_word Asan.M.loaded_segments (0x98218 : word) = Some W_98218.
Proof. vm_refl. Qed.
Lemma D_98218 : decode_any W_98218 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9821c : bv 32 := 0x00008067.
Lemma F_9821c : fetch_word Asan.M.loaded_segments (0x9821c : word) = Some W_9821c.
Proof. vm_refl. Qed.
Lemma D_9821c : decode_any W_9821c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
