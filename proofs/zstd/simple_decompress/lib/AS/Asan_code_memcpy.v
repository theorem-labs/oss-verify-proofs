(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c4ec8 : bv 32 := 0x0035f693.
Lemma F_c4ec8 : fetch_word Asan.M.loaded_segments (0xc0638 : word) = Some W_c4ec8.
Proof. vm_refl. Qed.
Lemma D_c4ec8 : decode_any W_c4ec8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ecc : bv 32 := 0x10068863.
Lemma F_c4ecc : fetch_word Asan.M.loaded_segments (0xc063c : word) = Some W_c4ecc.
Proof. vm_refl. Qed.
Lemma D_c4ecc : decode_any W_c4ecc = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ed0 : bv 32 := 0x02060e63.
Lemma F_c4ed0 : fetch_word Asan.M.loaded_segments (0xc0640 : word) = Some W_c4ed0.
Proof. vm_refl. Qed.
Lemma D_c4ed0 : decode_any W_c4ed0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ed4 : bv 32 := 0x00158713.
Lemma F_c4ed4 : fetch_word Asan.M.loaded_segments (0xc0644 : word) = Some W_c4ed4.
Proof. vm_refl. Qed.
Lemma D_c4ed4 : decode_any W_c4ed4 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ed8 : bv 32 := 0x00100793.
Lemma F_c4ed8 : fetch_word Asan.M.loaded_segments (0xc0648 : word) = Some W_c4ed8.
Proof. vm_refl. Qed.
Lemma D_c4ed8 : decode_any W_c4ed8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4edc : bv 32 := 0x00050693.
Lemma F_c4edc : fetch_word Asan.M.loaded_segments (0xc064c : word) = Some W_c4edc.
Proof. vm_refl. Qed.
Lemma D_c4edc : decode_any W_c4edc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ee0 : bv 32 := 0x0005c883.
Lemma F_c4ee0 : fetch_word Asan.M.loaded_segments (0xc0650 : word) = Some W_c4ee0.
Proof. vm_refl. Qed.
Lemma D_c4ee0 : decode_any W_c4ee0 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ee4 : bv 32 := 0x00060813.
Lemma F_c4ee4 : fetch_word Asan.M.loaded_segments (0xc0654 : word) = Some W_c4ee4.
Proof. vm_refl. Qed.
Lemma D_c4ee4 : decode_any W_c4ee4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ee8 : bv 32 := 0x00158593.
Lemma F_c4ee8 : fetch_word Asan.M.loaded_segments (0xc0658 : word) = Some W_c4ee8.
Proof. vm_refl. Qed.
Lemma D_c4ee8 : decode_any W_c4ee8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4eec : bv 32 := 0x00377293.
Lemma F_c4eec : fetch_word Asan.M.loaded_segments (0xc065c : word) = Some W_c4eec.
Proof. vm_refl. Qed.
Lemma D_c4eec : decode_any W_c4eec = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ef0 : bv 32 := 0x01168023.
Lemma F_c4ef0 : fetch_word Asan.M.loaded_segments (0xc0660 : word) = Some W_c4ef0.
Proof. vm_refl. Qed.
Lemma D_c4ef0 : decode_any W_c4ef0 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ef4 : bv 32 := 0x00168693.
Lemma F_c4ef4 : fetch_word Asan.M.loaded_segments (0xc0664 : word) = Some W_c4ef4.
Proof. vm_refl. Qed.
Lemma D_c4ef4 : decode_any W_c4ef4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ef8 : bv 32 := 0xfff60613.
Lemma F_c4ef8 : fetch_word Asan.M.loaded_segments (0xc0668 : word) = Some W_c4ef8.
Proof. vm_refl. Qed.
Lemma D_c4ef8 : decode_any W_c4ef8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4efc : bv 32 := 0x00028a63.
Lemma F_c4efc : fetch_word Asan.M.loaded_segments (0xc066c : word) = Some W_c4efc.
Proof. vm_refl. Qed.
Lemma D_c4efc : decode_any W_c4efc = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f00 : bv 32 := 0x00170713.
Lemma F_c4f00 : fetch_word Asan.M.loaded_segments (0xc0670 : word) = Some W_c4f00.
Proof. vm_refl. Qed.
Lemma D_c4f00 : decode_any W_c4f00 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f04 : bv 32 := 0xfcf81ee3.
Lemma F_c4f04 : fetch_word Asan.M.loaded_segments (0xc0674 : word) = Some W_c4f04.
Proof. vm_refl. Qed.
Lemma D_c4f04 : decode_any W_c4f04 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f08 : bv 32 := 0x0080006f.
Lemma F_c4f08 : fetch_word Asan.M.loaded_segments (0xc0678 : word) = Some W_c4f08.
Proof. vm_refl. Qed.
Lemma D_c4f08 : decode_any W_c4f08 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f0c : bv 32 := 0x00050693.
Lemma F_c4f0c : fetch_word Asan.M.loaded_segments (0xc067c : word) = Some W_c4f0c.
Proof. vm_refl. Qed.
Lemma D_c4f0c : decode_any W_c4f0c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f10 : bv 32 := 0x0036f793.
Lemma F_c4f10 : fetch_word Asan.M.loaded_segments (0xc0680 : word) = Some W_c4f10.
Proof. vm_refl. Qed.
Lemma D_c4f10 : decode_any W_c4f10 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f14 : bv 32 := 0x0c078a63.
Lemma F_c4f14 : fetch_word Asan.M.loaded_segments (0xc0684 : word) = Some W_c4f14.
Proof. vm_refl. Qed.
Lemma D_c4f14 : decode_any W_c4f14 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f18 : bv 32 := 0x02000713.
Lemma F_c4f18 : fetch_word Asan.M.loaded_segments (0xc0688 : word) = Some W_c4f18.
Proof. vm_refl. Qed.
Lemma D_c4f18 : decode_any W_c4f18 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f1c : bv 32 := 0x02e67063.
Lemma F_c4f1c : fetch_word Asan.M.loaded_segments (0xc068c : word) = Some W_c4f1c.
Proof. vm_refl. Qed.
Lemma D_c4f1c : decode_any W_c4f1c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f20 : bv 32 := 0x01000713.
Lemma F_c4f20 : fetch_word Asan.M.loaded_segments (0xc0690 : word) = Some W_c4f20.
Proof. vm_refl. Qed.
Lemma D_c4f20 : decode_any W_c4f20 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f24 : bv 32 := 0x24e67863.
Lemma F_c4f24 : fetch_word Asan.M.loaded_segments (0xc0694 : word) = Some W_c4f24.
Proof. vm_refl. Qed.
Lemma D_c4f24 : decode_any W_c4f24 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f28 : bv 32 := 0x00867713.
Lemma F_c4f28 : fetch_word Asan.M.loaded_segments (0xc0698 : word) = Some W_c4f28.
Proof. vm_refl. Qed.
Lemma D_c4f28 : decode_any W_c4f28 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f2c : bv 32 := 0x2c071e63.
Lemma F_c4f2c : fetch_word Asan.M.loaded_segments (0xc069c : word) = Some W_c4f2c.
Proof. vm_refl. Qed.
Lemma D_c4f2c : decode_any W_c4f2c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f30 : bv 32 := 0x00467713.
Lemma F_c4f30 : fetch_word Asan.M.loaded_segments (0xc06a0 : word) = Some W_c4f30.
Proof. vm_refl. Qed.
Lemma D_c4f30 : decode_any W_c4f30 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f34 : bv 32 := 0x32071463.
Lemma F_c4f34 : fetch_word Asan.M.loaded_segments (0xc06a4 : word) = Some W_c4f34.
Proof. vm_refl. Qed.
Lemma D_c4f34 : decode_any W_c4f34 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f38 : bv 32 := 0x3500006f.
Lemma F_c4f38 : fetch_word Asan.M.loaded_segments (0xc06a8 : word) = Some W_c4f38.
Proof. vm_refl. Qed.
Lemma D_c4f38 : decode_any W_c4f38 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f3c : bv 32 := 0x0005a703.
Lemma F_c4f3c : fetch_word Asan.M.loaded_segments (0xc06ac : word) = Some W_c4f3c.
Proof. vm_refl. Qed.
Lemma D_c4f3c : decode_any W_c4f3c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f40 : bv 32 := 0x00300813.
Lemma F_c4f40 : fetch_word Asan.M.loaded_segments (0xc06b0 : word) = Some W_c4f40.
Proof. vm_refl. Qed.
Lemma D_c4f40 : decode_any W_c4f40 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f44 : bv 32 := 0x11078e63.
Lemma F_c4f44 : fetch_word Asan.M.loaded_segments (0xc06b4 : word) = Some W_c4f44.
Proof. vm_refl. Qed.
Lemma D_c4f44 : decode_any W_c4f44 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f48 : bv 32 := 0x00200813.
Lemma F_c4f48 : fetch_word Asan.M.loaded_segments (0xc06b8 : word) = Some W_c4f48.
Proof. vm_refl. Qed.
Lemma D_c4f48 : decode_any W_c4f48 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f4c : bv 32 := 0x19079c63.
Lemma F_c4f4c : fetch_word Asan.M.loaded_segments (0xc06bc : word) = Some W_c4f4c.
Proof. vm_refl. Qed.
Lemma D_c4f4c : decode_any W_c4f4c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f50 : bv 32 := 0x00875793.
Lemma F_c4f50 : fetch_word Asan.M.loaded_segments (0xc06c0 : word) = Some W_c4f50.
Proof. vm_refl. Qed.
Lemma D_c4f50 : decode_any W_c4f50 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f54 : bv 32 := 0xffe60613.
Lemma F_c4f54 : fetch_word Asan.M.loaded_segments (0xc06c4 : word) = Some W_c4f54.
Proof. vm_refl. Qed.
Lemma D_c4f54 : decode_any W_c4f54 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f58 : bv 32 := 0x00e68023.
Lemma F_c4f58 : fetch_word Asan.M.loaded_segments (0xc06c8 : word) = Some W_c4f58.
Proof. vm_refl. Qed.
Lemma D_c4f58 : decode_any W_c4f58 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f5c : bv 32 := 0x00f680a3.
Lemma F_c4f5c : fetch_word Asan.M.loaded_segments (0xc06cc : word) = Some W_c4f5c.
Proof. vm_refl. Qed.
Lemma D_c4f5c : decode_any W_c4f5c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f60 : bv 32 := 0x00268693.
Lemma F_c4f60 : fetch_word Asan.M.loaded_segments (0xc06d0 : word) = Some W_c4f60.
Proof. vm_refl. Qed.
Lemma D_c4f60 : decode_any W_c4f60 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f64 : bv 32 := 0x01058593.
Lemma F_c4f64 : fetch_word Asan.M.loaded_segments (0xc06d4 : word) = Some W_c4f64.
Proof. vm_refl. Qed.
Lemma D_c4f64 : decode_any W_c4f64 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f68 : bv 32 := 0x01100793.
Lemma F_c4f68 : fetch_word Asan.M.loaded_segments (0xc06d8 : word) = Some W_c4f68.
Proof. vm_refl. Qed.
Lemma D_c4f68 : decode_any W_c4f68 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f6c : bv 32 := 0x0107581b.
Lemma F_c4f6c : fetch_word Asan.M.loaded_segments (0xc06dc : word) = Some W_c4f6c.
Proof. vm_refl. Qed.
Lemma D_c4f6c : decode_any W_c4f6c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f70 : bv 32 := 0xff45a883.
Lemma F_c4f70 : fetch_word Asan.M.loaded_segments (0xc06e0 : word) = Some W_c4f70.
Proof. vm_refl. Qed.
Lemma D_c4f70 : decode_any W_c4f70 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f74 : bv 32 := 0xff85a283.
Lemma F_c4f74 : fetch_word Asan.M.loaded_segments (0xc06e4 : word) = Some W_c4f74.
Proof. vm_refl. Qed.
Lemma D_c4f74 : decode_any W_c4f74 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f78 : bv 32 := 0xffc5a303.
Lemma F_c4f78 : fetch_word Asan.M.loaded_segments (0xc06e8 : word) = Some W_c4f78.
Proof. vm_refl. Qed.
Lemma D_c4f78 : decode_any W_c4f78 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f7c : bv 32 := 0x0005a703.
Lemma F_c4f7c : fetch_word Asan.M.loaded_segments (0xc06ec : word) = Some W_c4f7c.
Proof. vm_refl. Qed.
Lemma D_c4f7c : decode_any W_c4f7c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f80 : bv 32 := 0x01089393.
Lemma F_c4f80 : fetch_word Asan.M.loaded_segments (0xc06f0 : word) = Some W_c4f80.
Proof. vm_refl. Qed.
Lemma D_c4f80 : decode_any W_c4f80 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f84 : bv 32 := 0x0108d89b.
Lemma F_c4f84 : fetch_word Asan.M.loaded_segments (0xc06f4 : word) = Some W_c4f84.
Proof. vm_refl. Qed.
Lemma D_c4f84 : decode_any W_c4f84 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f88 : bv 32 := 0x0103e833.
Lemma F_c4f88 : fetch_word Asan.M.loaded_segments (0xc06f8 : word) = Some W_c4f88.
Proof. vm_refl. Qed.
Lemma D_c4f88 : decode_any W_c4f88 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f8c : bv 32 := 0x01029393.
Lemma F_c4f8c : fetch_word Asan.M.loaded_segments (0xc06fc : word) = Some W_c4f8c.
Proof. vm_refl. Qed.
Lemma D_c4f8c : decode_any W_c4f8c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f90 : bv 32 := 0x0102d29b.
Lemma F_c4f90 : fetch_word Asan.M.loaded_segments (0xc0700 : word) = Some W_c4f90.
Proof. vm_refl. Qed.
Lemma D_c4f90 : decode_any W_c4f90 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f94 : bv 32 := 0x0113e8b3.
Lemma F_c4f94 : fetch_word Asan.M.loaded_segments (0xc0704 : word) = Some W_c4f94.
Proof. vm_refl. Qed.
Lemma D_c4f94 : decode_any W_c4f94 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f98 : bv 32 := 0x01031393.
Lemma F_c4f98 : fetch_word Asan.M.loaded_segments (0xc0708 : word) = Some W_c4f98.
Proof. vm_refl. Qed.
Lemma D_c4f98 : decode_any W_c4f98 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4f9c : bv 32 := 0x0103531b.
Lemma F_c4f9c : fetch_word Asan.M.loaded_segments (0xc070c : word) = Some W_c4f9c.
Proof. vm_refl. Qed.
Lemma D_c4f9c : decode_any W_c4f9c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fa0 : bv 32 := 0x0053e2b3.
Lemma F_c4fa0 : fetch_word Asan.M.loaded_segments (0xc0710 : word) = Some W_c4fa0.
Proof. vm_refl. Qed.
Lemma D_c4fa0 : decode_any W_c4fa0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fa4 : bv 32 := 0x01071393.
Lemma F_c4fa4 : fetch_word Asan.M.loaded_segments (0xc0714 : word) = Some W_c4fa4.
Proof. vm_refl. Qed.
Lemma D_c4fa4 : decode_any W_c4fa4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fa8 : bv 32 := 0x0063e333.
Lemma F_c4fa8 : fetch_word Asan.M.loaded_segments (0xc0718 : word) = Some W_c4fa8.
Proof. vm_refl. Qed.
Lemma D_c4fa8 : decode_any W_c4fa8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fac : bv 32 := 0xff060613.
Lemma F_c4fac : fetch_word Asan.M.loaded_segments (0xc071c : word) = Some W_c4fac.
Proof. vm_refl. Qed.
Lemma D_c4fac : decode_any W_c4fac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fb0 : bv 32 := 0x0106a023.
Lemma F_c4fb0 : fetch_word Asan.M.loaded_segments (0xc0720 : word) = Some W_c4fb0.
Proof. vm_refl. Qed.
Lemma D_c4fb0 : decode_any W_c4fb0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fb4 : bv 32 := 0x0116a223.
Lemma F_c4fb4 : fetch_word Asan.M.loaded_segments (0xc0724 : word) = Some W_c4fb4.
Proof. vm_refl. Qed.
Lemma D_c4fb4 : decode_any W_c4fb4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fb8 : bv 32 := 0x0056a423.
Lemma F_c4fb8 : fetch_word Asan.M.loaded_segments (0xc0728 : word) = Some W_c4fb8.
Proof. vm_refl. Qed.
Lemma D_c4fb8 : decode_any W_c4fb8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fbc : bv 32 := 0x0066a623.
Lemma F_c4fbc : fetch_word Asan.M.loaded_segments (0xc072c : word) = Some W_c4fbc.
Proof. vm_refl. Qed.
Lemma D_c4fbc : decode_any W_c4fbc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fc0 : bv 32 := 0x01068693.
Lemma F_c4fc0 : fetch_word Asan.M.loaded_segments (0xc0730 : word) = Some W_c4fc0.
Proof. vm_refl. Qed.
Lemma D_c4fc0 : decode_any W_c4fc0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fc4 : bv 32 := 0x01058593.
Lemma F_c4fc4 : fetch_word Asan.M.loaded_segments (0xc0734 : word) = Some W_c4fc4.
Proof. vm_refl. Qed.
Lemma D_c4fc4 : decode_any W_c4fc4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fc8 : bv 32 := 0xfac7e2e3.
Lemma F_c4fc8 : fetch_word Asan.M.loaded_segments (0xc0738 : word) = Some W_c4fc8.
Proof. vm_refl. Qed.
Lemma D_c4fc8 : decode_any W_c4fc8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fcc : bv 32 := 0xff258593.
Lemma F_c4fcc : fetch_word Asan.M.loaded_segments (0xc073c : word) = Some W_c4fcc.
Proof. vm_refl. Qed.
Lemma D_c4fcc : decode_any W_c4fcc = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fd0 : bv 32 := 0x01000713.
Lemma F_c4fd0 : fetch_word Asan.M.loaded_segments (0xc0740 : word) = Some W_c4fd0.
Proof. vm_refl. Qed.
Lemma D_c4fd0 : decode_any W_c4fd0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fd4 : bv 32 := 0xf4e66ae3.
Lemma F_c4fd4 : fetch_word Asan.M.loaded_segments (0xc0744 : word) = Some W_c4fd4.
Proof. vm_refl. Qed.
Lemma D_c4fd4 : decode_any W_c4fd4 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fd8 : bv 32 := 0x19c0006f.
Lemma F_c4fd8 : fetch_word Asan.M.loaded_segments (0xc0748 : word) = Some W_c4fd8.
Proof. vm_refl. Qed.
Lemma D_c4fd8 : decode_any W_c4fd8 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fdc : bv 32 := 0x00050693.
Lemma F_c4fdc : fetch_word Asan.M.loaded_segments (0xc074c : word) = Some W_c4fdc.
Proof. vm_refl. Qed.
Lemma D_c4fdc : decode_any W_c4fdc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fe0 : bv 32 := 0x00357793.
Lemma F_c4fe0 : fetch_word Asan.M.loaded_segments (0xc0750 : word) = Some W_c4fe0.
Proof. vm_refl. Qed.
Lemma D_c4fe0 : decode_any W_c4fe0 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fe4 : bv 32 := 0xf2079ae3.
Lemma F_c4fe4 : fetch_word Asan.M.loaded_segments (0xc0754 : word) = Some W_c4fe4.
Proof. vm_refl. Qed.
Lemma D_c4fe4 : decode_any W_c4fe4 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fe8 : bv 32 := 0x01000713.
Lemma F_c4fe8 : fetch_word Asan.M.loaded_segments (0xc0758 : word) = Some W_c4fe8.
Proof. vm_refl. Qed.
Lemma D_c4fe8 : decode_any W_c4fe8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4fec : bv 32 := 0x02e66c63.
Lemma F_c4fec : fetch_word Asan.M.loaded_segments (0xc075c : word) = Some W_c4fec.
Proof. vm_refl. Qed.
Lemma D_c4fec : decode_any W_c4fec = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ff0 : bv 32 := 0x00f00713.
Lemma F_c4ff0 : fetch_word Asan.M.loaded_segments (0xc0760 : word) = Some W_c4ff0.
Proof. vm_refl. Qed.
Lemma D_c4ff0 : decode_any W_c4ff0 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ff4 : bv 32 := 0x0005a783.
Lemma F_c4ff4 : fetch_word Asan.M.loaded_segments (0xc0764 : word) = Some W_c4ff4.
Proof. vm_refl. Qed.
Lemma D_c4ff4 : decode_any W_c4ff4 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ff8 : bv 32 := 0x0045a803.
Lemma F_c4ff8 : fetch_word Asan.M.loaded_segments (0xc0768 : word) = Some W_c4ff8.
Proof. vm_refl. Qed.
Lemma D_c4ff8 : decode_any W_c4ff8 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4ffc : bv 32 := 0x0085a883.
Lemma F_c4ffc : fetch_word Asan.M.loaded_segments (0xc076c : word) = Some W_c4ffc.
Proof. vm_refl. Qed.
Lemma D_c4ffc : decode_any W_c4ffc = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5000 : bv 32 := 0x00c5a283.
Lemma F_c5000 : fetch_word Asan.M.loaded_segments (0xc0770 : word) = Some W_c5000.
Proof. vm_refl. Qed.
Lemma D_c5000 : decode_any W_c5000 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5004 : bv 32 := 0x01058593.
Lemma F_c5004 : fetch_word Asan.M.loaded_segments (0xc0774 : word) = Some W_c5004.
Proof. vm_refl. Qed.
Lemma D_c5004 : decode_any W_c5004 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5008 : bv 32 := 0xff060613.
Lemma F_c5008 : fetch_word Asan.M.loaded_segments (0xc0778 : word) = Some W_c5008.
Proof. vm_refl. Qed.
Lemma D_c5008 : decode_any W_c5008 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c500c : bv 32 := 0x00f6a023.
Lemma F_c500c : fetch_word Asan.M.loaded_segments (0xc077c : word) = Some W_c500c.
Proof. vm_refl. Qed.
Lemma D_c500c : decode_any W_c500c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5010 : bv 32 := 0x0106a223.
Lemma F_c5010 : fetch_word Asan.M.loaded_segments (0xc0780 : word) = Some W_c5010.
Proof. vm_refl. Qed.
Lemma D_c5010 : decode_any W_c5010 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5014 : bv 32 := 0x0116a423.
Lemma F_c5014 : fetch_word Asan.M.loaded_segments (0xc0784 : word) = Some W_c5014.
Proof. vm_refl. Qed.
Lemma D_c5014 : decode_any W_c5014 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5018 : bv 32 := 0x0056a623.
Lemma F_c5018 : fetch_word Asan.M.loaded_segments (0xc0788 : word) = Some W_c5018.
Proof. vm_refl. Qed.
Lemma D_c5018 : decode_any W_c5018 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c501c : bv 32 := 0x01068693.
Lemma F_c501c : fetch_word Asan.M.loaded_segments (0xc078c : word) = Some W_c501c.
Proof. vm_refl. Qed.
Lemma D_c501c : decode_any W_c501c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5020 : bv 32 := 0xfcc76ae3.
Lemma F_c5020 : fetch_word Asan.M.loaded_segments (0xc0790 : word) = Some W_c5020.
Proof. vm_refl. Qed.
Lemma D_c5020 : decode_any W_c5020 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5024 : bv 32 := 0x00800713.
Lemma F_c5024 : fetch_word Asan.M.loaded_segments (0xc0794 : word) = Some W_c5024.
Proof. vm_refl. Qed.
Lemma D_c5024 : decode_any W_c5024 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5028 : bv 32 := 0x00e66e63.
Lemma F_c5028 : fetch_word Asan.M.loaded_segments (0xc0798 : word) = Some W_c5028.
Proof. vm_refl. Qed.
Lemma D_c5028 : decode_any W_c5028 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c502c : bv 32 := 0x0005a703.
Lemma F_c502c : fetch_word Asan.M.loaded_segments (0xc079c : word) = Some W_c502c.
Proof. vm_refl. Qed.
Lemma D_c502c : decode_any W_c502c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5030 : bv 32 := 0x0045a783.
Lemma F_c5030 : fetch_word Asan.M.loaded_segments (0xc07a0 : word) = Some W_c5030.
Proof. vm_refl. Qed.
Lemma D_c5030 : decode_any W_c5030 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5034 : bv 32 := 0x00e6a023.
Lemma F_c5034 : fetch_word Asan.M.loaded_segments (0xc07a4 : word) = Some W_c5034.
Proof. vm_refl. Qed.
Lemma D_c5034 : decode_any W_c5034 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5038 : bv 32 := 0x00f6a223.
Lemma F_c5038 : fetch_word Asan.M.loaded_segments (0xc07a8 : word) = Some W_c5038.
Proof. vm_refl. Qed.
Lemma D_c5038 : decode_any W_c5038 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c503c : bv 32 := 0x00868693.
Lemma F_c503c : fetch_word Asan.M.loaded_segments (0xc07ac : word) = Some W_c503c.
Proof. vm_refl. Qed.
Lemma D_c503c : decode_any W_c503c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5040 : bv 32 := 0x00858593.
Lemma F_c5040 : fetch_word Asan.M.loaded_segments (0xc07b0 : word) = Some W_c5040.
Proof. vm_refl. Qed.
Lemma D_c5040 : decode_any W_c5040 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5044 : bv 32 := 0x00467713.
Lemma F_c5044 : fetch_word Asan.M.loaded_segments (0xc07b4 : word) = Some W_c5044.
Proof. vm_refl. Qed.
Lemma D_c5044 : decode_any W_c5044 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5048 : bv 32 := 0x24070063.
Lemma F_c5048 : fetch_word Asan.M.loaded_segments (0xc07b8 : word) = Some W_c5048.
Proof. vm_refl. Qed.
Lemma D_c5048 : decode_any W_c5048 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c504c : bv 32 := 0x0005a703.
Lemma F_c504c : fetch_word Asan.M.loaded_segments (0xc07bc : word) = Some W_c504c.
Proof. vm_refl. Qed.
Lemma D_c504c : decode_any W_c504c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5050 : bv 32 := 0x00458593.
Lemma F_c5050 : fetch_word Asan.M.loaded_segments (0xc07c0 : word) = Some W_c5050.
Proof. vm_refl. Qed.
Lemma D_c5050 : decode_any W_c5050 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5054 : bv 32 := 0x00e6a023.
Lemma F_c5054 : fetch_word Asan.M.loaded_segments (0xc07c4 : word) = Some W_c5054.
Proof. vm_refl. Qed.
Lemma D_c5054 : decode_any W_c5054 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5058 : bv 32 := 0x00468693.
Lemma F_c5058 : fetch_word Asan.M.loaded_segments (0xc07c8 : word) = Some W_c5058.
Proof. vm_refl. Qed.
Lemma D_c5058 : decode_any W_c5058 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c505c : bv 32 := 0x22c0006f.
Lemma F_c505c : fetch_word Asan.M.loaded_segments (0xc07cc : word) = Some W_c505c.
Proof. vm_refl. Qed.
Lemma D_c505c : decode_any W_c505c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5060 : bv 32 := 0x00e68023.
Lemma F_c5060 : fetch_word Asan.M.loaded_segments (0xc07d0 : word) = Some W_c5060.
Proof. vm_refl. Qed.
Lemma D_c5060 : decode_any W_c5060 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5064 : bv 32 := 0x00168693.
Lemma F_c5064 : fetch_word Asan.M.loaded_segments (0xc07d4 : word) = Some W_c5064.
Proof. vm_refl. Qed.
Lemma D_c5064 : decode_any W_c5064 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5068 : bv 32 := 0xfff60613.
Lemma F_c5068 : fetch_word Asan.M.loaded_segments (0xc07d8 : word) = Some W_c5068.
Proof. vm_refl. Qed.
Lemma D_c5068 : decode_any W_c5068 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c506c : bv 32 := 0x01058593.
Lemma F_c506c : fetch_word Asan.M.loaded_segments (0xc07dc : word) = Some W_c506c.
Proof. vm_refl. Qed.
Lemma D_c506c : decode_any W_c506c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5070 : bv 32 := 0x01200793.
Lemma F_c5070 : fetch_word Asan.M.loaded_segments (0xc07e0 : word) = Some W_c5070.
Proof. vm_refl. Qed.
Lemma D_c5070 : decode_any W_c5070 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5074 : bv 32 := 0x0087581b.
Lemma F_c5074 : fetch_word Asan.M.loaded_segments (0xc07e4 : word) = Some W_c5074.
Proof. vm_refl. Qed.
Lemma D_c5074 : decode_any W_c5074 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5078 : bv 32 := 0xff45a883.
Lemma F_c5078 : fetch_word Asan.M.loaded_segments (0xc07e8 : word) = Some W_c5078.
Proof. vm_refl. Qed.
Lemma D_c5078 : decode_any W_c5078 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c507c : bv 32 := 0xff85a283.
Lemma F_c507c : fetch_word Asan.M.loaded_segments (0xc07ec : word) = Some W_c507c.
Proof. vm_refl. Qed.
Lemma D_c507c : decode_any W_c507c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5080 : bv 32 := 0xffc5a303.
Lemma F_c5080 : fetch_word Asan.M.loaded_segments (0xc07f0 : word) = Some W_c5080.
Proof. vm_refl. Qed.
Lemma D_c5080 : decode_any W_c5080 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5084 : bv 32 := 0x0005a703.
Lemma F_c5084 : fetch_word Asan.M.loaded_segments (0xc07f4 : word) = Some W_c5084.
Proof. vm_refl. Qed.
Lemma D_c5084 : decode_any W_c5084 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5088 : bv 32 := 0x01889393.
Lemma F_c5088 : fetch_word Asan.M.loaded_segments (0xc07f8 : word) = Some W_c5088.
Proof. vm_refl. Qed.
Lemma D_c5088 : decode_any W_c5088 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c508c : bv 32 := 0x0088d89b.
Lemma F_c508c : fetch_word Asan.M.loaded_segments (0xc07fc : word) = Some W_c508c.
Proof. vm_refl. Qed.
Lemma D_c508c : decode_any W_c508c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5090 : bv 32 := 0x0103e833.
Lemma F_c5090 : fetch_word Asan.M.loaded_segments (0xc0800 : word) = Some W_c5090.
Proof. vm_refl. Qed.
Lemma D_c5090 : decode_any W_c5090 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5094 : bv 32 := 0x01829393.
Lemma F_c5094 : fetch_word Asan.M.loaded_segments (0xc0804 : word) = Some W_c5094.
Proof. vm_refl. Qed.
Lemma D_c5094 : decode_any W_c5094 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5098 : bv 32 := 0x0082d29b.
Lemma F_c5098 : fetch_word Asan.M.loaded_segments (0xc0808 : word) = Some W_c5098.
Proof. vm_refl. Qed.
Lemma D_c5098 : decode_any W_c5098 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c509c : bv 32 := 0x0113e8b3.
Lemma F_c509c : fetch_word Asan.M.loaded_segments (0xc080c : word) = Some W_c509c.
Proof. vm_refl. Qed.
Lemma D_c509c : decode_any W_c509c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50a0 : bv 32 := 0x01831393.
Lemma F_c50a0 : fetch_word Asan.M.loaded_segments (0xc0810 : word) = Some W_c50a0.
Proof. vm_refl. Qed.
Lemma D_c50a0 : decode_any W_c50a0 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50a4 : bv 32 := 0x0083531b.
Lemma F_c50a4 : fetch_word Asan.M.loaded_segments (0xc0814 : word) = Some W_c50a4.
Proof. vm_refl. Qed.
Lemma D_c50a4 : decode_any W_c50a4 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50a8 : bv 32 := 0x0053e2b3.
Lemma F_c50a8 : fetch_word Asan.M.loaded_segments (0xc0818 : word) = Some W_c50a8.
Proof. vm_refl. Qed.
Lemma D_c50a8 : decode_any W_c50a8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50ac : bv 32 := 0x01871393.
Lemma F_c50ac : fetch_word Asan.M.loaded_segments (0xc081c : word) = Some W_c50ac.
Proof. vm_refl. Qed.
Lemma D_c50ac : decode_any W_c50ac = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50b0 : bv 32 := 0x0063e333.
Lemma F_c50b0 : fetch_word Asan.M.loaded_segments (0xc0820 : word) = Some W_c50b0.
Proof. vm_refl. Qed.
Lemma D_c50b0 : decode_any W_c50b0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50b4 : bv 32 := 0xff060613.
Lemma F_c50b4 : fetch_word Asan.M.loaded_segments (0xc0824 : word) = Some W_c50b4.
Proof. vm_refl. Qed.
Lemma D_c50b4 : decode_any W_c50b4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50b8 : bv 32 := 0x0106a023.
Lemma F_c50b8 : fetch_word Asan.M.loaded_segments (0xc0828 : word) = Some W_c50b8.
Proof. vm_refl. Qed.
Lemma D_c50b8 : decode_any W_c50b8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50bc : bv 32 := 0x0116a223.
Lemma F_c50bc : fetch_word Asan.M.loaded_segments (0xc082c : word) = Some W_c50bc.
Proof. vm_refl. Qed.
Lemma D_c50bc : decode_any W_c50bc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50c0 : bv 32 := 0x0056a423.
Lemma F_c50c0 : fetch_word Asan.M.loaded_segments (0xc0830 : word) = Some W_c50c0.
Proof. vm_refl. Qed.
Lemma D_c50c0 : decode_any W_c50c0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50c4 : bv 32 := 0x0066a623.
Lemma F_c50c4 : fetch_word Asan.M.loaded_segments (0xc0834 : word) = Some W_c50c4.
Proof. vm_refl. Qed.
Lemma D_c50c4 : decode_any W_c50c4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50c8 : bv 32 := 0x01068693.
Lemma F_c50c8 : fetch_word Asan.M.loaded_segments (0xc0838 : word) = Some W_c50c8.
Proof. vm_refl. Qed.
Lemma D_c50c8 : decode_any W_c50c8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50cc : bv 32 := 0x01058593.
Lemma F_c50cc : fetch_word Asan.M.loaded_segments (0xc083c : word) = Some W_c50cc.
Proof. vm_refl. Qed.
Lemma D_c50cc : decode_any W_c50cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50d0 : bv 32 := 0xfac7e2e3.
Lemma F_c50d0 : fetch_word Asan.M.loaded_segments (0xc0840 : word) = Some W_c50d0.
Proof. vm_refl. Qed.
Lemma D_c50d0 : decode_any W_c50d0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50d4 : bv 32 := 0xff158593.
Lemma F_c50d4 : fetch_word Asan.M.loaded_segments (0xc0844 : word) = Some W_c50d4.
Proof. vm_refl. Qed.
Lemma D_c50d4 : decode_any W_c50d4 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50d8 : bv 32 := 0x01000713.
Lemma F_c50d8 : fetch_word Asan.M.loaded_segments (0xc0848 : word) = Some W_c50d8.
Proof. vm_refl. Qed.
Lemma D_c50d8 : decode_any W_c50d8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50dc : bv 32 := 0xe4e666e3.
Lemma F_c50dc : fetch_word Asan.M.loaded_segments (0xc084c : word) = Some W_c50dc.
Proof. vm_refl. Qed.
Lemma D_c50dc : decode_any W_c50dc = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50e0 : bv 32 := 0x0940006f.
Lemma F_c50e0 : fetch_word Asan.M.loaded_segments (0xc0850 : word) = Some W_c50e0.
Proof. vm_refl. Qed.
Lemma D_c50e0 : decode_any W_c50e0 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50e4 : bv 32 := 0x00875793.
Lemma F_c50e4 : fetch_word Asan.M.loaded_segments (0xc0854 : word) = Some W_c50e4.
Proof. vm_refl. Qed.
Lemma D_c50e4 : decode_any W_c50e4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50e8 : bv 32 := 0x01075813.
Lemma F_c50e8 : fetch_word Asan.M.loaded_segments (0xc0858 : word) = Some W_c50e8.
Proof. vm_refl. Qed.
Lemma D_c50e8 : decode_any W_c50e8 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50ec : bv 32 := 0xffd60613.
Lemma F_c50ec : fetch_word Asan.M.loaded_segments (0xc085c : word) = Some W_c50ec.
Proof. vm_refl. Qed.
Lemma D_c50ec : decode_any W_c50ec = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50f0 : bv 32 := 0x00e68023.
Lemma F_c50f0 : fetch_word Asan.M.loaded_segments (0xc0860 : word) = Some W_c50f0.
Proof. vm_refl. Qed.
Lemma D_c50f0 : decode_any W_c50f0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50f4 : bv 32 := 0x00f680a3.
Lemma F_c50f4 : fetch_word Asan.M.loaded_segments (0xc0864 : word) = Some W_c50f4.
Proof. vm_refl. Qed.
Lemma D_c50f4 : decode_any W_c50f4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50f8 : bv 32 := 0x01068123.
Lemma F_c50f8 : fetch_word Asan.M.loaded_segments (0xc0868 : word) = Some W_c50f8.
Proof. vm_refl. Qed.
Lemma D_c50f8 : decode_any W_c50f8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c50fc : bv 32 := 0x00368693.
Lemma F_c50fc : fetch_word Asan.M.loaded_segments (0xc086c : word) = Some W_c50fc.
Proof. vm_refl. Qed.
Lemma D_c50fc : decode_any W_c50fc = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5100 : bv 32 := 0x01058593.
Lemma F_c5100 : fetch_word Asan.M.loaded_segments (0xc0870 : word) = Some W_c5100.
Proof. vm_refl. Qed.
Lemma D_c5100 : decode_any W_c5100 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5104 : bv 32 := 0x01000793.
Lemma F_c5104 : fetch_word Asan.M.loaded_segments (0xc0874 : word) = Some W_c5104.
Proof. vm_refl. Qed.
Lemma D_c5104 : decode_any W_c5104 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5108 : bv 32 := 0x0187581b.
Lemma F_c5108 : fetch_word Asan.M.loaded_segments (0xc0878 : word) = Some W_c5108.
Proof. vm_refl. Qed.
Lemma D_c5108 : decode_any W_c5108 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c510c : bv 32 := 0xff45a883.
Lemma F_c510c : fetch_word Asan.M.loaded_segments (0xc087c : word) = Some W_c510c.
Proof. vm_refl. Qed.
Lemma D_c510c : decode_any W_c510c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5110 : bv 32 := 0xff85a283.
Lemma F_c5110 : fetch_word Asan.M.loaded_segments (0xc0880 : word) = Some W_c5110.
Proof. vm_refl. Qed.
Lemma D_c5110 : decode_any W_c5110 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5114 : bv 32 := 0xffc5a303.
Lemma F_c5114 : fetch_word Asan.M.loaded_segments (0xc0884 : word) = Some W_c5114.
Proof. vm_refl. Qed.
Lemma D_c5114 : decode_any W_c5114 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5118 : bv 32 := 0x0005a703.
Lemma F_c5118 : fetch_word Asan.M.loaded_segments (0xc0888 : word) = Some W_c5118.
Proof. vm_refl. Qed.
Lemma D_c5118 : decode_any W_c5118 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c511c : bv 32 := 0x00889393.
Lemma F_c511c : fetch_word Asan.M.loaded_segments (0xc088c : word) = Some W_c511c.
Proof. vm_refl. Qed.
Lemma D_c511c : decode_any W_c511c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5120 : bv 32 := 0x0188d89b.
Lemma F_c5120 : fetch_word Asan.M.loaded_segments (0xc0890 : word) = Some W_c5120.
Proof. vm_refl. Qed.
Lemma D_c5120 : decode_any W_c5120 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5124 : bv 32 := 0x0103e833.
Lemma F_c5124 : fetch_word Asan.M.loaded_segments (0xc0894 : word) = Some W_c5124.
Proof. vm_refl. Qed.
Lemma D_c5124 : decode_any W_c5124 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5128 : bv 32 := 0x00829393.
Lemma F_c5128 : fetch_word Asan.M.loaded_segments (0xc0898 : word) = Some W_c5128.
Proof. vm_refl. Qed.
Lemma D_c5128 : decode_any W_c5128 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c512c : bv 32 := 0x0182d29b.
Lemma F_c512c : fetch_word Asan.M.loaded_segments (0xc089c : word) = Some W_c512c.
Proof. vm_refl. Qed.
Lemma D_c512c : decode_any W_c512c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5130 : bv 32 := 0x0113e8b3.
Lemma F_c5130 : fetch_word Asan.M.loaded_segments (0xc08a0 : word) = Some W_c5130.
Proof. vm_refl. Qed.
Lemma D_c5130 : decode_any W_c5130 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5134 : bv 32 := 0x00831393.
Lemma F_c5134 : fetch_word Asan.M.loaded_segments (0xc08a4 : word) = Some W_c5134.
Proof. vm_refl. Qed.
Lemma D_c5134 : decode_any W_c5134 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5138 : bv 32 := 0x0183531b.
Lemma F_c5138 : fetch_word Asan.M.loaded_segments (0xc08a8 : word) = Some W_c5138.
Proof. vm_refl. Qed.
Lemma D_c5138 : decode_any W_c5138 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c513c : bv 32 := 0x0053e2b3.
Lemma F_c513c : fetch_word Asan.M.loaded_segments (0xc08ac : word) = Some W_c513c.
Proof. vm_refl. Qed.
Lemma D_c513c : decode_any W_c513c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5140 : bv 32 := 0x00871393.
Lemma F_c5140 : fetch_word Asan.M.loaded_segments (0xc08b0 : word) = Some W_c5140.
Proof. vm_refl. Qed.
Lemma D_c5140 : decode_any W_c5140 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5144 : bv 32 := 0x0063e333.
Lemma F_c5144 : fetch_word Asan.M.loaded_segments (0xc08b4 : word) = Some W_c5144.
Proof. vm_refl. Qed.
Lemma D_c5144 : decode_any W_c5144 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5148 : bv 32 := 0xff060613.
Lemma F_c5148 : fetch_word Asan.M.loaded_segments (0xc08b8 : word) = Some W_c5148.
Proof. vm_refl. Qed.
Lemma D_c5148 : decode_any W_c5148 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c514c : bv 32 := 0x0106a023.
Lemma F_c514c : fetch_word Asan.M.loaded_segments (0xc08bc : word) = Some W_c514c.
Proof. vm_refl. Qed.
Lemma D_c514c : decode_any W_c514c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5150 : bv 32 := 0x0116a223.
Lemma F_c5150 : fetch_word Asan.M.loaded_segments (0xc08c0 : word) = Some W_c5150.
Proof. vm_refl. Qed.
Lemma D_c5150 : decode_any W_c5150 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5154 : bv 32 := 0x0056a423.
Lemma F_c5154 : fetch_word Asan.M.loaded_segments (0xc08c4 : word) = Some W_c5154.
Proof. vm_refl. Qed.
Lemma D_c5154 : decode_any W_c5154 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5158 : bv 32 := 0x0066a623.
Lemma F_c5158 : fetch_word Asan.M.loaded_segments (0xc08c8 : word) = Some W_c5158.
Proof. vm_refl. Qed.
Lemma D_c5158 : decode_any W_c5158 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c515c : bv 32 := 0x01068693.
Lemma F_c515c : fetch_word Asan.M.loaded_segments (0xc08cc : word) = Some W_c515c.
Proof. vm_refl. Qed.
Lemma D_c515c : decode_any W_c515c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5160 : bv 32 := 0x01058593.
Lemma F_c5160 : fetch_word Asan.M.loaded_segments (0xc08d0 : word) = Some W_c5160.
Proof. vm_refl. Qed.
Lemma D_c5160 : decode_any W_c5160 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5164 : bv 32 := 0xfac7e2e3.
Lemma F_c5164 : fetch_word Asan.M.loaded_segments (0xc08d4 : word) = Some W_c5164.
Proof. vm_refl. Qed.
Lemma D_c5164 : decode_any W_c5164 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5168 : bv 32 := 0xff358593.
Lemma F_c5168 : fetch_word Asan.M.loaded_segments (0xc08d8 : word) = Some W_c5168.
Proof. vm_refl. Qed.
Lemma D_c5168 : decode_any W_c5168 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c516c : bv 32 := 0x01000713.
Lemma F_c516c : fetch_word Asan.M.loaded_segments (0xc08dc : word) = Some W_c516c.
Proof. vm_refl. Qed.
Lemma D_c516c : decode_any W_c516c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5170 : bv 32 := 0xdae66ce3.
Lemma F_c5170 : fetch_word Asan.M.loaded_segments (0xc08e0 : word) = Some W_c5170.
Proof. vm_refl. Qed.
Lemma D_c5170 : decode_any W_c5170 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5174 : bv 32 := 0x0005c703.
Lemma F_c5174 : fetch_word Asan.M.loaded_segments (0xc08e4 : word) = Some W_c5174.
Proof. vm_refl. Qed.
Lemma D_c5174 : decode_any W_c5174 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5178 : bv 32 := 0x0015c783.
Lemma F_c5178 : fetch_word Asan.M.loaded_segments (0xc08e8 : word) = Some W_c5178.
Proof. vm_refl. Qed.
Lemma D_c5178 : decode_any W_c5178 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c517c : bv 32 := 0x0025c803.
Lemma F_c517c : fetch_word Asan.M.loaded_segments (0xc08ec : word) = Some W_c517c.
Proof. vm_refl. Qed.
Lemma D_c517c : decode_any W_c517c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5180 : bv 32 := 0x0035c883.
Lemma F_c5180 : fetch_word Asan.M.loaded_segments (0xc08f0 : word) = Some W_c5180.
Proof. vm_refl. Qed.
Lemma D_c5180 : decode_any W_c5180 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5184 : bv 32 := 0x0045c283.
Lemma F_c5184 : fetch_word Asan.M.loaded_segments (0xc08f4 : word) = Some W_c5184.
Proof. vm_refl. Qed.
Lemma D_c5184 : decode_any W_c5184 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5188 : bv 32 := 0x0055c303.
Lemma F_c5188 : fetch_word Asan.M.loaded_segments (0xc08f8 : word) = Some W_c5188.
Proof. vm_refl. Qed.
Lemma D_c5188 : decode_any W_c5188 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c518c : bv 32 := 0x0065c383.
Lemma F_c518c : fetch_word Asan.M.loaded_segments (0xc08fc : word) = Some W_c518c.
Proof. vm_refl. Qed.
Lemma D_c518c : decode_any W_c518c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5190 : bv 32 := 0x0075ce03.
Lemma F_c5190 : fetch_word Asan.M.loaded_segments (0xc0900 : word) = Some W_c5190.
Proof. vm_refl. Qed.
Lemma D_c5190 : decode_any W_c5190 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5194 : bv 32 := 0x00e68023.
Lemma F_c5194 : fetch_word Asan.M.loaded_segments (0xc0904 : word) = Some W_c5194.
Proof. vm_refl. Qed.
Lemma D_c5194 : decode_any W_c5194 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5198 : bv 32 := 0x00f680a3.
Lemma F_c5198 : fetch_word Asan.M.loaded_segments (0xc0908 : word) = Some W_c5198.
Proof. vm_refl. Qed.
Lemma D_c5198 : decode_any W_c5198 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c519c : bv 32 := 0x01068123.
Lemma F_c519c : fetch_word Asan.M.loaded_segments (0xc090c : word) = Some W_c519c.
Proof. vm_refl. Qed.
Lemma D_c519c : decode_any W_c519c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51a0 : bv 32 := 0x011681a3.
Lemma F_c51a0 : fetch_word Asan.M.loaded_segments (0xc0910 : word) = Some W_c51a0.
Proof. vm_refl. Qed.
Lemma D_c51a0 : decode_any W_c51a0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51a4 : bv 32 := 0x0085c703.
Lemma F_c51a4 : fetch_word Asan.M.loaded_segments (0xc0914 : word) = Some W_c51a4.
Proof. vm_refl. Qed.
Lemma D_c51a4 : decode_any W_c51a4 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51a8 : bv 32 := 0x0095c783.
Lemma F_c51a8 : fetch_word Asan.M.loaded_segments (0xc0918 : word) = Some W_c51a8.
Proof. vm_refl. Qed.
Lemma D_c51a8 : decode_any W_c51a8 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51ac : bv 32 := 0x00a5c803.
Lemma F_c51ac : fetch_word Asan.M.loaded_segments (0xc091c : word) = Some W_c51ac.
Proof. vm_refl. Qed.
Lemma D_c51ac : decode_any W_c51ac = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51b0 : bv 32 := 0x00b5c883.
Lemma F_c51b0 : fetch_word Asan.M.loaded_segments (0xc0920 : word) = Some W_c51b0.
Proof. vm_refl. Qed.
Lemma D_c51b0 : decode_any W_c51b0 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51b4 : bv 32 := 0x00568223.
Lemma F_c51b4 : fetch_word Asan.M.loaded_segments (0xc0924 : word) = Some W_c51b4.
Proof. vm_refl. Qed.
Lemma D_c51b4 : decode_any W_c51b4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51b8 : bv 32 := 0x006682a3.
Lemma F_c51b8 : fetch_word Asan.M.loaded_segments (0xc0928 : word) = Some W_c51b8.
Proof. vm_refl. Qed.
Lemma D_c51b8 : decode_any W_c51b8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51bc : bv 32 := 0x00768323.
Lemma F_c51bc : fetch_word Asan.M.loaded_segments (0xc092c : word) = Some W_c51bc.
Proof. vm_refl. Qed.
Lemma D_c51bc : decode_any W_c51bc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51c0 : bv 32 := 0x01c683a3.
Lemma F_c51c0 : fetch_word Asan.M.loaded_segments (0xc0930 : word) = Some W_c51c0.
Proof. vm_refl. Qed.
Lemma D_c51c0 : decode_any W_c51c0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51c4 : bv 32 := 0x00c5c283.
Lemma F_c51c4 : fetch_word Asan.M.loaded_segments (0xc0934 : word) = Some W_c51c4.
Proof. vm_refl. Qed.
Lemma D_c51c4 : decode_any W_c51c4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51c8 : bv 32 := 0x00d5c303.
Lemma F_c51c8 : fetch_word Asan.M.loaded_segments (0xc0938 : word) = Some W_c51c8.
Proof. vm_refl. Qed.
Lemma D_c51c8 : decode_any W_c51c8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51cc : bv 32 := 0x00e5c383.
Lemma F_c51cc : fetch_word Asan.M.loaded_segments (0xc093c : word) = Some W_c51cc.
Proof. vm_refl. Qed.
Lemma D_c51cc : decode_any W_c51cc = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51d0 : bv 32 := 0x00f5ce03.
Lemma F_c51d0 : fetch_word Asan.M.loaded_segments (0xc0940 : word) = Some W_c51d0.
Proof. vm_refl. Qed.
Lemma D_c51d0 : decode_any W_c51d0 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51d4 : bv 32 := 0x01058593.
Lemma F_c51d4 : fetch_word Asan.M.loaded_segments (0xc0944 : word) = Some W_c51d4.
Proof. vm_refl. Qed.
Lemma D_c51d4 : decode_any W_c51d4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51d8 : bv 32 := 0x00e68423.
Lemma F_c51d8 : fetch_word Asan.M.loaded_segments (0xc0948 : word) = Some W_c51d8.
Proof. vm_refl. Qed.
Lemma D_c51d8 : decode_any W_c51d8 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51dc : bv 32 := 0x00f684a3.
Lemma F_c51dc : fetch_word Asan.M.loaded_segments (0xc094c : word) = Some W_c51dc.
Proof. vm_refl. Qed.
Lemma D_c51dc : decode_any W_c51dc = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51e0 : bv 32 := 0x01068523.
Lemma F_c51e0 : fetch_word Asan.M.loaded_segments (0xc0950 : word) = Some W_c51e0.
Proof. vm_refl. Qed.
Lemma D_c51e0 : decode_any W_c51e0 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51e4 : bv 32 := 0x011685a3.
Lemma F_c51e4 : fetch_word Asan.M.loaded_segments (0xc0954 : word) = Some W_c51e4.
Proof. vm_refl. Qed.
Lemma D_c51e4 : decode_any W_c51e4 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51e8 : bv 32 := 0x01068713.
Lemma F_c51e8 : fetch_word Asan.M.loaded_segments (0xc0958 : word) = Some W_c51e8.
Proof. vm_refl. Qed.
Lemma D_c51e8 : decode_any W_c51e8 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51ec : bv 32 := 0x00568623.
Lemma F_c51ec : fetch_word Asan.M.loaded_segments (0xc095c : word) = Some W_c51ec.
Proof. vm_refl. Qed.
Lemma D_c51ec : decode_any W_c51ec = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51f0 : bv 32 := 0x006686a3.
Lemma F_c51f0 : fetch_word Asan.M.loaded_segments (0xc0960 : word) = Some W_c51f0.
Proof. vm_refl. Qed.
Lemma D_c51f0 : decode_any W_c51f0 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51f4 : bv 32 := 0x00768723.
Lemma F_c51f4 : fetch_word Asan.M.loaded_segments (0xc0964 : word) = Some W_c51f4.
Proof. vm_refl. Qed.
Lemma D_c51f4 : decode_any W_c51f4 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51f8 : bv 32 := 0x01c687a3.
Lemma F_c51f8 : fetch_word Asan.M.loaded_segments (0xc0968 : word) = Some W_c51f8.
Proof. vm_refl. Qed.
Lemma D_c51f8 : decode_any W_c51f8 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c51fc : bv 32 := 0x00070693.
Lemma F_c51fc : fetch_word Asan.M.loaded_segments (0xc096c : word) = Some W_c51fc.
Proof. vm_refl. Qed.
Lemma D_c51fc : decode_any W_c51fc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5200 : bv 32 := 0x00867713.
Lemma F_c5200 : fetch_word Asan.M.loaded_segments (0xc0970 : word) = Some W_c5200.
Proof. vm_refl. Qed.
Lemma D_c5200 : decode_any W_c5200 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5204 : bv 32 := 0xd20706e3.
Lemma F_c5204 : fetch_word Asan.M.loaded_segments (0xc0974 : word) = Some W_c5204.
Proof. vm_refl. Qed.
Lemma D_c5204 : decode_any W_c5204 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5208 : bv 32 := 0x0005c703.
Lemma F_c5208 : fetch_word Asan.M.loaded_segments (0xc0978 : word) = Some W_c5208.
Proof. vm_refl. Qed.
Lemma D_c5208 : decode_any W_c5208 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c520c : bv 32 := 0x0015c783.
Lemma F_c520c : fetch_word Asan.M.loaded_segments (0xc097c : word) = Some W_c520c.
Proof. vm_refl. Qed.
Lemma D_c520c : decode_any W_c520c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5210 : bv 32 := 0x0025c803.
Lemma F_c5210 : fetch_word Asan.M.loaded_segments (0xc0980 : word) = Some W_c5210.
Proof. vm_refl. Qed.
Lemma D_c5210 : decode_any W_c5210 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5214 : bv 32 := 0x0035c883.
Lemma F_c5214 : fetch_word Asan.M.loaded_segments (0xc0984 : word) = Some W_c5214.
Proof. vm_refl. Qed.
Lemma D_c5214 : decode_any W_c5214 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5218 : bv 32 := 0x0045c283.
Lemma F_c5218 : fetch_word Asan.M.loaded_segments (0xc0988 : word) = Some W_c5218.
Proof. vm_refl. Qed.
Lemma D_c5218 : decode_any W_c5218 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c521c : bv 32 := 0x0055c303.
Lemma F_c521c : fetch_word Asan.M.loaded_segments (0xc098c : word) = Some W_c521c.
Proof. vm_refl. Qed.
Lemma D_c521c : decode_any W_c521c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5220 : bv 32 := 0x0065c383.
Lemma F_c5220 : fetch_word Asan.M.loaded_segments (0xc0990 : word) = Some W_c5220.
Proof. vm_refl. Qed.
Lemma D_c5220 : decode_any W_c5220 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5224 : bv 32 := 0x0075ce03.
Lemma F_c5224 : fetch_word Asan.M.loaded_segments (0xc0994 : word) = Some W_c5224.
Proof. vm_refl. Qed.
Lemma D_c5224 : decode_any W_c5224 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5228 : bv 32 := 0x00858593.
Lemma F_c5228 : fetch_word Asan.M.loaded_segments (0xc0998 : word) = Some W_c5228.
Proof. vm_refl. Qed.
Lemma D_c5228 : decode_any W_c5228 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c522c : bv 32 := 0x00e68023.
Lemma F_c522c : fetch_word Asan.M.loaded_segments (0xc099c : word) = Some W_c522c.
Proof. vm_refl. Qed.
Lemma D_c522c : decode_any W_c522c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5230 : bv 32 := 0x00f680a3.
Lemma F_c5230 : fetch_word Asan.M.loaded_segments (0xc09a0 : word) = Some W_c5230.
Proof. vm_refl. Qed.
Lemma D_c5230 : decode_any W_c5230 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5234 : bv 32 := 0x01068123.
Lemma F_c5234 : fetch_word Asan.M.loaded_segments (0xc09a4 : word) = Some W_c5234.
Proof. vm_refl. Qed.
Lemma D_c5234 : decode_any W_c5234 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5238 : bv 32 := 0x011681a3.
Lemma F_c5238 : fetch_word Asan.M.loaded_segments (0xc09a8 : word) = Some W_c5238.
Proof. vm_refl. Qed.
Lemma D_c5238 : decode_any W_c5238 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c523c : bv 32 := 0x00868713.
Lemma F_c523c : fetch_word Asan.M.loaded_segments (0xc09ac : word) = Some W_c523c.
Proof. vm_refl. Qed.
Lemma D_c523c : decode_any W_c523c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5240 : bv 32 := 0x00568223.
Lemma F_c5240 : fetch_word Asan.M.loaded_segments (0xc09b0 : word) = Some W_c5240.
Proof. vm_refl. Qed.
Lemma D_c5240 : decode_any W_c5240 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5244 : bv 32 := 0x006682a3.
Lemma F_c5244 : fetch_word Asan.M.loaded_segments (0xc09b4 : word) = Some W_c5244.
Proof. vm_refl. Qed.
Lemma D_c5244 : decode_any W_c5244 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5248 : bv 32 := 0x00768323.
Lemma F_c5248 : fetch_word Asan.M.loaded_segments (0xc09b8 : word) = Some W_c5248.
Proof. vm_refl. Qed.
Lemma D_c5248 : decode_any W_c5248 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c524c : bv 32 := 0x01c683a3.
Lemma F_c524c : fetch_word Asan.M.loaded_segments (0xc09bc : word) = Some W_c524c.
Proof. vm_refl. Qed.
Lemma D_c524c : decode_any W_c524c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5250 : bv 32 := 0x00070693.
Lemma F_c5250 : fetch_word Asan.M.loaded_segments (0xc09c0 : word) = Some W_c5250.
Proof. vm_refl. Qed.
Lemma D_c5250 : decode_any W_c5250 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5254 : bv 32 := 0x00467713.
Lemma F_c5254 : fetch_word Asan.M.loaded_segments (0xc09c4 : word) = Some W_c5254.
Proof. vm_refl. Qed.
Lemma D_c5254 : decode_any W_c5254 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5258 : bv 32 := 0x02070863.
Lemma F_c5258 : fetch_word Asan.M.loaded_segments (0xc09c8 : word) = Some W_c5258.
Proof. vm_refl. Qed.
Lemma D_c5258 : decode_any W_c5258 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c525c : bv 32 := 0x0005c703.
Lemma F_c525c : fetch_word Asan.M.loaded_segments (0xc09cc : word) = Some W_c525c.
Proof. vm_refl. Qed.
Lemma D_c525c : decode_any W_c525c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5260 : bv 32 := 0x0015c783.
Lemma F_c5260 : fetch_word Asan.M.loaded_segments (0xc09d0 : word) = Some W_c5260.
Proof. vm_refl. Qed.
Lemma D_c5260 : decode_any W_c5260 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5264 : bv 32 := 0x0025c803.
Lemma F_c5264 : fetch_word Asan.M.loaded_segments (0xc09d4 : word) = Some W_c5264.
Proof. vm_refl. Qed.
Lemma D_c5264 : decode_any W_c5264 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5268 : bv 32 := 0x0035c883.
Lemma F_c5268 : fetch_word Asan.M.loaded_segments (0xc09d8 : word) = Some W_c5268.
Proof. vm_refl. Qed.
Lemma D_c5268 : decode_any W_c5268 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c526c : bv 32 := 0x00458593.
Lemma F_c526c : fetch_word Asan.M.loaded_segments (0xc09dc : word) = Some W_c526c.
Proof. vm_refl. Qed.
Lemma D_c526c : decode_any W_c526c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5270 : bv 32 := 0x00468293.
Lemma F_c5270 : fetch_word Asan.M.loaded_segments (0xc09e0 : word) = Some W_c5270.
Proof. vm_refl. Qed.
Lemma D_c5270 : decode_any W_c5270 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5274 : bv 32 := 0x00e68023.
Lemma F_c5274 : fetch_word Asan.M.loaded_segments (0xc09e4 : word) = Some W_c5274.
Proof. vm_refl. Qed.
Lemma D_c5274 : decode_any W_c5274 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5278 : bv 32 := 0x00f680a3.
Lemma F_c5278 : fetch_word Asan.M.loaded_segments (0xc09e8 : word) = Some W_c5278.
Proof. vm_refl. Qed.
Lemma D_c5278 : decode_any W_c5278 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c527c : bv 32 := 0x01068123.
Lemma F_c527c : fetch_word Asan.M.loaded_segments (0xc09ec : word) = Some W_c527c.
Proof. vm_refl. Qed.
Lemma D_c527c : decode_any W_c527c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5280 : bv 32 := 0x011681a3.
Lemma F_c5280 : fetch_word Asan.M.loaded_segments (0xc09f0 : word) = Some W_c5280.
Proof. vm_refl. Qed.
Lemma D_c5280 : decode_any W_c5280 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5284 : bv 32 := 0x00028693.
Lemma F_c5284 : fetch_word Asan.M.loaded_segments (0xc09f4 : word) = Some W_c5284.
Proof. vm_refl. Qed.
Lemma D_c5284 : decode_any W_c5284 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5288 : bv 32 := 0x00267713.
Lemma F_c5288 : fetch_word Asan.M.loaded_segments (0xc09f8 : word) = Some W_c5288.
Proof. vm_refl. Qed.
Lemma D_c5288 : decode_any W_c5288 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c528c : bv 32 := 0x00071863.
Lemma F_c528c : fetch_word Asan.M.loaded_segments (0xc09fc : word) = Some W_c528c.
Proof. vm_refl. Qed.
Lemma D_c528c : decode_any W_c528c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5290 : bv 32 := 0x00167613.
Lemma F_c5290 : fetch_word Asan.M.loaded_segments (0xc0a00 : word) = Some W_c5290.
Proof. vm_refl. Qed.
Lemma D_c5290 : decode_any W_c5290 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5294 : bv 32 := 0x02061663.
Lemma F_c5294 : fetch_word Asan.M.loaded_segments (0xc0a04 : word) = Some W_c5294.
Proof. vm_refl. Qed.
Lemma D_c5294 : decode_any W_c5294 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5298 : bv 32 := 0x00008067.
Lemma F_c5298 : fetch_word Asan.M.loaded_segments (0xc0a08 : word) = Some W_c5298.
Proof. vm_refl. Qed.
Lemma D_c5298 : decode_any W_c5298 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c529c : bv 32 := 0x0005c703.
Lemma F_c529c : fetch_word Asan.M.loaded_segments (0xc0a0c : word) = Some W_c529c.
Proof. vm_refl. Qed.
Lemma D_c529c : decode_any W_c529c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52a0 : bv 32 := 0x0015c783.
Lemma F_c52a0 : fetch_word Asan.M.loaded_segments (0xc0a10 : word) = Some W_c52a0.
Proof. vm_refl. Qed.
Lemma D_c52a0 : decode_any W_c52a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52a4 : bv 32 := 0x00258593.
Lemma F_c52a4 : fetch_word Asan.M.loaded_segments (0xc0a14 : word) = Some W_c52a4.
Proof. vm_refl. Qed.
Lemma D_c52a4 : decode_any W_c52a4 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52a8 : bv 32 := 0x00268813.
Lemma F_c52a8 : fetch_word Asan.M.loaded_segments (0xc0a18 : word) = Some W_c52a8.
Proof. vm_refl. Qed.
Lemma D_c52a8 : decode_any W_c52a8 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52ac : bv 32 := 0x00e68023.
Lemma F_c52ac : fetch_word Asan.M.loaded_segments (0xc0a1c : word) = Some W_c52ac.
Proof. vm_refl. Qed.
Lemma D_c52ac : decode_any W_c52ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52b0 : bv 32 := 0x00f680a3.
Lemma F_c52b0 : fetch_word Asan.M.loaded_segments (0xc0a20 : word) = Some W_c52b0.
Proof. vm_refl. Qed.
Lemma D_c52b0 : decode_any W_c52b0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52b4 : bv 32 := 0x00080693.
Lemma F_c52b4 : fetch_word Asan.M.loaded_segments (0xc0a24 : word) = Some W_c52b4.
Proof. vm_refl. Qed.
Lemma D_c52b4 : decode_any W_c52b4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52b8 : bv 32 := 0x00167613.
Lemma F_c52b8 : fetch_word Asan.M.loaded_segments (0xc0a28 : word) = Some W_c52b8.
Proof. vm_refl. Qed.
Lemma D_c52b8 : decode_any W_c52b8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52bc : bv 32 := 0xfc060ee3.
Lemma F_c52bc : fetch_word Asan.M.loaded_segments (0xc0a2c : word) = Some W_c52bc.
Proof. vm_refl. Qed.
Lemma D_c52bc : decode_any W_c52bc = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52c0 : bv 32 := 0x0005c583.
Lemma F_c52c0 : fetch_word Asan.M.loaded_segments (0xc0a30 : word) = Some W_c52c0.
Proof. vm_refl. Qed.
Lemma D_c52c0 : decode_any W_c52c0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52c4 : bv 32 := 0x00b68023.
Lemma F_c52c4 : fetch_word Asan.M.loaded_segments (0xc0a34 : word) = Some W_c52c4.
Proof. vm_refl. Qed.
Lemma D_c52c4 : decode_any W_c52c4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52c8 : bv 32 := 0x00008067.
Lemma F_c52c8 : fetch_word Asan.M.loaded_segments (0xc0a38 : word) = Some W_c52c8.
Proof. vm_refl. Qed.
Lemma D_c52c8 : decode_any W_c52c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
