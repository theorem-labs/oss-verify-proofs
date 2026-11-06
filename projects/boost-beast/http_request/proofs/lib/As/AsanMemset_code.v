(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_10db7c : bv 32 := 0x0e060a63.
Lemma F_10db7c : fetch_word Asan.M.loaded_segments (0x10db7c : word) = Some W_10db7c.
Proof. vm_refl. Qed.
Lemma D_10db7c : decode_any W_10db7c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db80 : bv 32 := 0x00b50023.
Lemma F_10db80 : fetch_word Asan.M.loaded_segments (0x10db80 : word) = Some W_10db80.
Proof. vm_refl. Qed.
Lemma D_10db80 : decode_any W_10db80 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db84 : bv 32 := 0x00c506b3.
Lemma F_10db84 : fetch_word Asan.M.loaded_segments (0x10db84 : word) = Some W_10db84.
Proof. vm_refl. Qed.
Lemma D_10db84 : decode_any W_10db84 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db88 : bv 32 := 0x00300713.
Lemma F_10db88 : fetch_word Asan.M.loaded_segments (0x10db88 : word) = Some W_10db88.
Proof. vm_refl. Qed.
Lemma D_10db88 : decode_any W_10db88 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db8c : bv 32 := 0xfeb68fa3.
Lemma F_10db8c : fetch_word Asan.M.loaded_segments (0x10db8c : word) = Some W_10db8c.
Proof. vm_refl. Qed.
Lemma D_10db8c : decode_any W_10db8c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db90 : bv 32 := 0x0ee66063.
Lemma F_10db90 : fetch_word Asan.M.loaded_segments (0x10db90 : word) = Some W_10db90.
Proof. vm_refl. Qed.
Lemma D_10db90 : decode_any W_10db90 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db94 : bv 32 := 0x00b500a3.
Lemma F_10db94 : fetch_word Asan.M.loaded_segments (0x10db94 : word) = Some W_10db94.
Proof. vm_refl. Qed.
Lemma D_10db94 : decode_any W_10db94 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db98 : bv 32 := 0x00b50123.
Lemma F_10db98 : fetch_word Asan.M.loaded_segments (0x10db98 : word) = Some W_10db98.
Proof. vm_refl. Qed.
Lemma D_10db98 : decode_any W_10db98 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10db9c : bv 32 := 0x00700713.
Lemma F_10db9c : fetch_word Asan.M.loaded_segments (0x10db9c : word) = Some W_10db9c.
Proof. vm_refl. Qed.
Lemma D_10db9c : decode_any W_10db9c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dba0 : bv 32 := 0xfeb68ea3.
Lemma F_10dba0 : fetch_word Asan.M.loaded_segments (0x10dba0 : word) = Some W_10dba0.
Proof. vm_refl. Qed.
Lemma D_10dba0 : decode_any W_10dba0 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dba4 : bv 32 := 0xfeb68f23.
Lemma F_10dba4 : fetch_word Asan.M.loaded_segments (0x10dba4 : word) = Some W_10dba4.
Proof. vm_refl. Qed.
Lemma D_10dba4 : decode_any W_10dba4 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dba8 : bv 32 := 0x0ce66463.
Lemma F_10dba8 : fetch_word Asan.M.loaded_segments (0x10dba8 : word) = Some W_10dba8.
Proof. vm_refl. Qed.
Lemma D_10dba8 : decode_any W_10dba8 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbac : bv 32 := 0x00b501a3.
Lemma F_10dbac : fetch_word Asan.M.loaded_segments (0x10dbac : word) = Some W_10dbac.
Proof. vm_refl. Qed.
Lemma D_10dbac : decode_any W_10dbac = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbb0 : bv 32 := 0x00900793.
Lemma F_10dbb0 : fetch_word Asan.M.loaded_segments (0x10dbb0 : word) = Some W_10dbb0.
Proof. vm_refl. Qed.
Lemma D_10dbb0 : decode_any W_10dbb0 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbb4 : bv 32 := 0xfeb68e23.
Lemma F_10dbb4 : fetch_word Asan.M.loaded_segments (0x10dbb4 : word) = Some W_10dbb4.
Proof. vm_refl. Qed.
Lemma D_10dbb4 : decode_any W_10dbb4 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbb8 : bv 32 := 0x0af66c63.
Lemma F_10dbb8 : fetch_word Asan.M.loaded_segments (0x10dbb8 : word) = Some W_10dbb8.
Proof. vm_refl. Qed.
Lemma D_10dbb8 : decode_any W_10dbb8 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbbc : bv 32 := 0x40a006bb.
Lemma F_10dbbc : fetch_word Asan.M.loaded_segments (0x10dbbc : word) = Some W_10dbbc.
Proof. vm_refl. Qed.
Lemma D_10dbbc : decode_any W_10dbbc = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbc0 : bv 32 := 0x03859813.
Lemma F_10dbc0 : fetch_word Asan.M.loaded_segments (0x10dbc0 : word) = Some W_10dbc0.
Proof. vm_refl. Qed.
Lemma D_10dbc0 : decode_any W_10dbc0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbc4 : bv 32 := 0x101015b7.
Lemma F_10dbc4 : fetch_word Asan.M.loaded_segments (0x10dbc4 : word) = Some W_10dbc4.
Proof. vm_refl. Qed.
Lemma D_10dbc4 : decode_any W_10dbc4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbc8 : bv 32 := 0x0036f693.
Lemma F_10dbc8 : fetch_word Asan.M.loaded_segments (0x10dbc8 : word) = Some W_10dbc8.
Proof. vm_refl. Qed.
Lemma D_10dbc8 : decode_any W_10dbc8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbcc : bv 32 := 0x00459713.
Lemma F_10dbcc : fetch_word Asan.M.loaded_segments (0x10dbcc : word) = Some W_10dbcc.
Proof. vm_refl. Qed.
Lemma D_10dbcc : decode_any W_10dbcc = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbd0 : bv 32 := 0x40d60633.
Lemma F_10dbd0 : fetch_word Asan.M.loaded_segments (0x10dbd0 : word) = Some W_10dbd0.
Proof. vm_refl. Qed.
Lemma D_10dbd0 : decode_any W_10dbd0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbd4 : bv 32 := 0x00d505b3.
Lemma F_10dbd4 : fetch_word Asan.M.loaded_segments (0x10dbd4 : word) = Some W_10dbd4.
Proof. vm_refl. Qed.
Lemma D_10dbd4 : decode_any W_10dbd4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbd8 : bv 32 := 0x10070693.
Lemma F_10dbd8 : fetch_word Asan.M.loaded_segments (0x10dbd8 : word) = Some W_10dbd8.
Proof. vm_refl. Qed.
Lemma D_10dbd8 : decode_any W_10dbd8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbdc : bv 32 := 0xffc67713.
Lemma F_10dbdc : fetch_word Asan.M.loaded_segments (0x10dbdc : word) = Some W_10dbdc.
Proof. vm_refl. Qed.
Lemma D_10dbdc : decode_any W_10dbdc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbe0 : bv 32 := 0x02d83633.
Lemma F_10dbe0 : fetch_word Asan.M.loaded_segments (0x10dbe0 : word) = Some W_10dbe0.
Proof. vm_refl. Qed.
Lemma D_10dbe0 : decode_any W_10dbe0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbe4 : bv 32 := 0x00c5a023.
Lemma F_10dbe4 : fetch_word Asan.M.loaded_segments (0x10dbe4 : word) = Some W_10dbe4.
Proof. vm_refl. Qed.
Lemma D_10dbe4 : decode_any W_10dbe4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbe8 : bv 32 := 0x00e586b3.
Lemma F_10dbe8 : fetch_word Asan.M.loaded_segments (0x10dbe8 : word) = Some W_10dbe8.
Proof. vm_refl. Qed.
Lemma D_10dbe8 : decode_any W_10dbe8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbec : bv 32 := 0xfec6ae23.
Lemma F_10dbec : fetch_word Asan.M.loaded_segments (0x10dbec : word) = Some W_10dbec.
Proof. vm_refl. Qed.
Lemma D_10dbec : decode_any W_10dbec = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbf0 : bv 32 := 0x08f76063.
Lemma F_10dbf0 : fetch_word Asan.M.loaded_segments (0x10dbf0 : word) = Some W_10dbf0.
Proof. vm_refl. Qed.
Lemma D_10dbf0 : decode_any W_10dbf0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbf4 : bv 32 := 0x00c5a223.
Lemma F_10dbf4 : fetch_word Asan.M.loaded_segments (0x10dbf4 : word) = Some W_10dbf4.
Proof. vm_refl. Qed.
Lemma D_10dbf4 : decode_any W_10dbf4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbf8 : bv 32 := 0x00c5a423.
Lemma F_10dbf8 : fetch_word Asan.M.loaded_segments (0x10dbf8 : word) = Some W_10dbf8.
Proof. vm_refl. Qed.
Lemma D_10dbf8 : decode_any W_10dbf8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dbfc : bv 32 := 0x01900793.
Lemma F_10dbfc : fetch_word Asan.M.loaded_segments (0x10dbfc : word) = Some W_10dbfc.
Proof. vm_refl. Qed.
Lemma D_10dbfc : decode_any W_10dbfc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc00 : bv 32 := 0xfec6aa23.
Lemma F_10dc00 : fetch_word Asan.M.loaded_segments (0x10dc00 : word) = Some W_10dc00.
Proof. vm_refl. Qed.
Lemma D_10dc00 : decode_any W_10dc00 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc04 : bv 32 := 0xfec6ac23.
Lemma F_10dc04 : fetch_word Asan.M.loaded_segments (0x10dc04 : word) = Some W_10dc04.
Proof. vm_refl. Qed.
Lemma D_10dc04 : decode_any W_10dc04 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc08 : bv 32 := 0x06f76463.
Lemma F_10dc08 : fetch_word Asan.M.loaded_segments (0x10dc08 : word) = Some W_10dc08.
Proof. vm_refl. Qed.
Lemma D_10dc08 : decode_any W_10dc08 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc0c : bv 32 := 0x00c5a623.
Lemma F_10dc0c : fetch_word Asan.M.loaded_segments (0x10dc0c : word) = Some W_10dc0c.
Proof. vm_refl. Qed.
Lemma D_10dc0c : decode_any W_10dc0c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc10 : bv 32 := 0x00c5a823.
Lemma F_10dc10 : fetch_word Asan.M.loaded_segments (0x10dc10 : word) = Some W_10dc10.
Proof. vm_refl. Qed.
Lemma D_10dc10 : decode_any W_10dc10 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc14 : bv 32 := 0x00c5aa23.
Lemma F_10dc14 : fetch_word Asan.M.loaded_segments (0x10dc14 : word) = Some W_10dc14.
Proof. vm_refl. Qed.
Lemma D_10dc14 : decode_any W_10dc14 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc18 : bv 32 := 0x00c5ac23.
Lemma F_10dc18 : fetch_word Asan.M.loaded_segments (0x10dc18 : word) = Some W_10dc18.
Proof. vm_refl. Qed.
Lemma D_10dc18 : decode_any W_10dc18 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc1c : bv 32 := 0x0045f793.
Lemma F_10dc1c : fetch_word Asan.M.loaded_segments (0x10dc1c : word) = Some W_10dc1c.
Proof. vm_refl. Qed.
Lemma D_10dc1c : decode_any W_10dc1c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc20 : bv 32 := 0x02000813.
Lemma F_10dc20 : fetch_word Asan.M.loaded_segments (0x10dc20 : word) = Some W_10dc20.
Proof. vm_refl. Qed.
Lemma D_10dc20 : decode_any W_10dc20 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc24 : bv 32 := 0x01878793.
Lemma F_10dc24 : fetch_word Asan.M.loaded_segments (0x10dc24 : word) = Some W_10dc24.
Proof. vm_refl. Qed.
Lemma D_10dc24 : decode_any W_10dc24 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc28 : bv 32 := 0x40f70733.
Lemma F_10dc28 : fetch_word Asan.M.loaded_segments (0x10dc28 : word) = Some W_10dc28.
Proof. vm_refl. Qed.
Lemma D_10dc28 : decode_any W_10dc28 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc2c : bv 32 := 0xfec6a223.
Lemma F_10dc2c : fetch_word Asan.M.loaded_segments (0x10dc2c : word) = Some W_10dc2c.
Proof. vm_refl. Qed.
Lemma D_10dc2c : decode_any W_10dc2c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc30 : bv 32 := 0xfec6a423.
Lemma F_10dc30 : fetch_word Asan.M.loaded_segments (0x10dc30 : word) = Some W_10dc30.
Proof. vm_refl. Qed.
Lemma D_10dc30 : decode_any W_10dc30 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc34 : bv 32 := 0xfec6a623.
Lemma F_10dc34 : fetch_word Asan.M.loaded_segments (0x10dc34 : word) = Some W_10dc34.
Proof. vm_refl. Qed.
Lemma D_10dc34 : decode_any W_10dc34 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc38 : bv 32 := 0xfec6a823.
Lemma F_10dc38 : fetch_word Asan.M.loaded_segments (0x10dc38 : word) = Some W_10dc38.
Proof. vm_refl. Qed.
Lemma D_10dc38 : decode_any W_10dc38 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc3c : bv 32 := 0x03076a63.
Lemma F_10dc3c : fetch_word Asan.M.loaded_segments (0x10dc3c : word) = Some W_10dc3c.
Proof. vm_refl. Qed.
Lemma D_10dc3c : decode_any W_10dc3c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc40 : bv 32 := 0x02061613.
Lemma F_10dc40 : fetch_word Asan.M.loaded_segments (0x10dc40 : word) = Some W_10dc40.
Proof. vm_refl. Qed.
Lemma D_10dc40 : decode_any W_10dc40 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc44 : bv 32 := 0x00f585b3.
Lemma F_10dc44 : fetch_word Asan.M.loaded_segments (0x10dc44 : word) = Some W_10dc44.
Proof. vm_refl. Qed.
Lemma D_10dc44 : decode_any W_10dc44 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc48 : bv 32 := 0x02065693.
Lemma F_10dc48 : fetch_word Asan.M.loaded_segments (0x10dc48 : word) = Some W_10dc48.
Proof. vm_refl. Qed.
Lemma D_10dc48 : decode_any W_10dc48 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc4c : bv 32 := 0x00d66633.
Lemma F_10dc4c : fetch_word Asan.M.loaded_segments (0x10dc4c : word) = Some W_10dc4c.
Proof. vm_refl. Qed.
Lemma D_10dc4c : decode_any W_10dc4c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc50 : bv 32 := 0x01f00693.
Lemma F_10dc50 : fetch_word Asan.M.loaded_segments (0x10dc50 : word) = Some W_10dc50.
Proof. vm_refl. Qed.
Lemma D_10dc50 : decode_any W_10dc50 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc54 : bv 32 := 0x00c5b023.
Lemma F_10dc54 : fetch_word Asan.M.loaded_segments (0x10dc54 : word) = Some W_10dc54.
Proof. vm_refl. Qed.
Lemma D_10dc54 : decode_any W_10dc54 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc58 : bv 32 := 0x00c5b423.
Lemma F_10dc58 : fetch_word Asan.M.loaded_segments (0x10dc58 : word) = Some W_10dc58.
Proof. vm_refl. Qed.
Lemma D_10dc58 : decode_any W_10dc58 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc5c : bv 32 := 0x00c5b823.
Lemma F_10dc5c : fetch_word Asan.M.loaded_segments (0x10dc5c : word) = Some W_10dc5c.
Proof. vm_refl. Qed.
Lemma D_10dc5c : decode_any W_10dc5c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc60 : bv 32 := 0x00c5bc23.
Lemma F_10dc60 : fetch_word Asan.M.loaded_segments (0x10dc60 : word) = Some W_10dc60.
Proof. vm_refl. Qed.
Lemma D_10dc60 : decode_any W_10dc60 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc64 : bv 32 := 0xfe070713.
Lemma F_10dc64 : fetch_word Asan.M.loaded_segments (0x10dc64 : word) = Some W_10dc64.
Proof. vm_refl. Qed.
Lemma D_10dc64 : decode_any W_10dc64 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc68 : bv 32 := 0x02058593.
Lemma F_10dc68 : fetch_word Asan.M.loaded_segments (0x10dc68 : word) = Some W_10dc68.
Proof. vm_refl. Qed.
Lemma D_10dc68 : decode_any W_10dc68 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc6c : bv 32 := 0xfee6e4e3.
Lemma F_10dc6c : fetch_word Asan.M.loaded_segments (0x10dc6c : word) = Some W_10dc6c.
Proof. vm_refl. Qed.
Lemma D_10dc6c : decode_any W_10dc6c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10dc70 : bv 32 := 0x00008067.
Lemma F_10dc70 : fetch_word Asan.M.loaded_segments (0x10dc70 : word) = Some W_10dc70.
Proof. vm_refl. Qed.
Lemma D_10dc70 : decode_any W_10dc70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x10db7c%Z.
Definition Fo_000 := F_10db7c.
Definition Do_000 := D_10db7c.
Definition Fo_004 := F_10db80.
Definition Do_004 := D_10db80.
Definition Fo_008 := F_10db84.
Definition Do_008 := D_10db84.
Definition Fo_00c := F_10db88.
Definition Do_00c := D_10db88.
Definition Fo_010 := F_10db8c.
Definition Do_010 := D_10db8c.
Definition Fo_014 := F_10db90.
Definition Do_014 := D_10db90.
Definition Fo_018 := F_10db94.
Definition Do_018 := D_10db94.
Definition Fo_01c := F_10db98.
Definition Do_01c := D_10db98.
Definition Fo_020 := F_10db9c.
Definition Do_020 := D_10db9c.
Definition Fo_024 := F_10dba0.
Definition Do_024 := D_10dba0.
Definition Fo_028 := F_10dba4.
Definition Do_028 := D_10dba4.
Definition Fo_02c := F_10dba8.
Definition Do_02c := D_10dba8.
Definition Fo_030 := F_10dbac.
Definition Do_030 := D_10dbac.
Definition Fo_034 := F_10dbb0.
Definition Do_034 := D_10dbb0.
Definition Fo_038 := F_10dbb4.
Definition Do_038 := D_10dbb4.
Definition Fo_03c := F_10dbb8.
Definition Do_03c := D_10dbb8.
Definition Fo_040 := F_10dbbc.
Definition Do_040 := D_10dbbc.
Definition Fo_044 := F_10dbc0.
Definition Do_044 := D_10dbc0.
Definition Fo_048 := F_10dbc4.
Definition Do_048 := D_10dbc4.
Definition Fo_04c := F_10dbc8.
Definition Do_04c := D_10dbc8.
Definition Fo_050 := F_10dbcc.
Definition Do_050 := D_10dbcc.
Definition Fo_054 := F_10dbd0.
Definition Do_054 := D_10dbd0.
Definition Fo_058 := F_10dbd4.
Definition Do_058 := D_10dbd4.
Definition Fo_05c := F_10dbd8.
Definition Do_05c := D_10dbd8.
Definition Fo_060 := F_10dbdc.
Definition Do_060 := D_10dbdc.
Definition Fo_064 := F_10dbe0.
Definition Do_064 := D_10dbe0.
Definition Fo_068 := F_10dbe4.
Definition Do_068 := D_10dbe4.
Definition Fo_06c := F_10dbe8.
Definition Do_06c := D_10dbe8.
Definition Fo_070 := F_10dbec.
Definition Do_070 := D_10dbec.
Definition Fo_074 := F_10dbf0.
Definition Do_074 := D_10dbf0.
Definition Fo_078 := F_10dbf4.
Definition Do_078 := D_10dbf4.
Definition Fo_07c := F_10dbf8.
Definition Do_07c := D_10dbf8.
Definition Fo_080 := F_10dbfc.
Definition Do_080 := D_10dbfc.
Definition Fo_084 := F_10dc00.
Definition Do_084 := D_10dc00.
Definition Fo_088 := F_10dc04.
Definition Do_088 := D_10dc04.
Definition Fo_08c := F_10dc08.
Definition Do_08c := D_10dc08.
Definition Fo_090 := F_10dc0c.
Definition Do_090 := D_10dc0c.
Definition Fo_094 := F_10dc10.
Definition Do_094 := D_10dc10.
Definition Fo_098 := F_10dc14.
Definition Do_098 := D_10dc14.
Definition Fo_09c := F_10dc18.
Definition Do_09c := D_10dc18.
Definition Fo_0a0 := F_10dc1c.
Definition Do_0a0 := D_10dc1c.
Definition Fo_0a4 := F_10dc20.
Definition Do_0a4 := D_10dc20.
Definition Fo_0a8 := F_10dc24.
Definition Do_0a8 := D_10dc24.
Definition Fo_0ac := F_10dc28.
Definition Do_0ac := D_10dc28.
Definition Fo_0b0 := F_10dc2c.
Definition Do_0b0 := D_10dc2c.
Definition Fo_0b4 := F_10dc30.
Definition Do_0b4 := D_10dc30.
Definition Fo_0b8 := F_10dc34.
Definition Do_0b8 := D_10dc34.
Definition Fo_0bc := F_10dc38.
Definition Do_0bc := D_10dc38.
Definition Fo_0c0 := F_10dc3c.
Definition Do_0c0 := D_10dc3c.
Definition Fo_0c4 := F_10dc40.
Definition Do_0c4 := D_10dc40.
Definition Fo_0c8 := F_10dc44.
Definition Do_0c8 := D_10dc44.
Definition Fo_0cc := F_10dc48.
Definition Do_0cc := D_10dc48.
Definition Fo_0d0 := F_10dc4c.
Definition Do_0d0 := D_10dc4c.
Definition Fo_0d4 := F_10dc50.
Definition Do_0d4 := D_10dc50.
Definition Fo_0d8 := F_10dc54.
Definition Do_0d8 := D_10dc54.
Definition Fo_0dc := F_10dc58.
Definition Do_0dc := D_10dc58.
Definition Fo_0e0 := F_10dc5c.
Definition Do_0e0 := D_10dc5c.
Definition Fo_0e4 := F_10dc60.
Definition Do_0e4 := D_10dc60.
Definition Fo_0e8 := F_10dc64.
Definition Do_0e8 := D_10dc64.
Definition Fo_0ec := F_10dc68.
Definition Do_0ec := D_10dc68.
Definition Fo_0f0 := F_10dc6c.
Definition Do_0f0 := D_10dc6c.
Definition Fo_0f4 := F_10dc70.
Definition Do_0f4 := D_10dc70.
