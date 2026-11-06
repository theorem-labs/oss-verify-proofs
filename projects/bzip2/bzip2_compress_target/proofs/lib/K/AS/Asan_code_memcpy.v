(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_b8c00 : bv 32 := 0x0035f693.
Lemma F_b8c00 : fetch_word Asan.M.loaded_segments (0xb8d84 : word) = Some W_b8c00.
Proof. vm_refl. Qed.
Lemma D_b8c00 : decode_any W_b8c00 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c04 : bv 32 := 0x10068863.
Lemma F_b8c04 : fetch_word Asan.M.loaded_segments (0xb8d88 : word) = Some W_b8c04.
Proof. vm_refl. Qed.
Lemma D_b8c04 : decode_any W_b8c04 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c08 : bv 32 := 0x02060e63.
Lemma F_b8c08 : fetch_word Asan.M.loaded_segments (0xb8d8c : word) = Some W_b8c08.
Proof. vm_refl. Qed.
Lemma D_b8c08 : decode_any W_b8c08 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c0c : bv 32 := 0x00158713.
Lemma F_b8c0c : fetch_word Asan.M.loaded_segments (0xb8d90 : word) = Some W_b8c0c.
Proof. vm_refl. Qed.
Lemma D_b8c0c : decode_any W_b8c0c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c10 : bv 32 := 0x00100793.
Lemma F_b8c10 : fetch_word Asan.M.loaded_segments (0xb8d94 : word) = Some W_b8c10.
Proof. vm_refl. Qed.
Lemma D_b8c10 : decode_any W_b8c10 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c14 : bv 32 := 0x00050693.
Lemma F_b8c14 : fetch_word Asan.M.loaded_segments (0xb8d98 : word) = Some W_b8c14.
Proof. vm_refl. Qed.
Lemma D_b8c14 : decode_any W_b8c14 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c18 : bv 32 := 0x0005c883.
Lemma F_b8c18 : fetch_word Asan.M.loaded_segments (0xb8d9c : word) = Some W_b8c18.
Proof. vm_refl. Qed.
Lemma D_b8c18 : decode_any W_b8c18 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c1c : bv 32 := 0x00060813.
Lemma F_b8c1c : fetch_word Asan.M.loaded_segments (0xb8da0 : word) = Some W_b8c1c.
Proof. vm_refl. Qed.
Lemma D_b8c1c : decode_any W_b8c1c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c20 : bv 32 := 0x00158593.
Lemma F_b8c20 : fetch_word Asan.M.loaded_segments (0xb8da4 : word) = Some W_b8c20.
Proof. vm_refl. Qed.
Lemma D_b8c20 : decode_any W_b8c20 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c24 : bv 32 := 0x00377293.
Lemma F_b8c24 : fetch_word Asan.M.loaded_segments (0xb8da8 : word) = Some W_b8c24.
Proof. vm_refl. Qed.
Lemma D_b8c24 : decode_any W_b8c24 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c28 : bv 32 := 0x01168023.
Lemma F_b8c28 : fetch_word Asan.M.loaded_segments (0xb8dac : word) = Some W_b8c28.
Proof. vm_refl. Qed.
Lemma D_b8c28 : decode_any W_b8c28 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c2c : bv 32 := 0x00168693.
Lemma F_b8c2c : fetch_word Asan.M.loaded_segments (0xb8db0 : word) = Some W_b8c2c.
Proof. vm_refl. Qed.
Lemma D_b8c2c : decode_any W_b8c2c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c30 : bv 32 := 0xfff60613.
Lemma F_b8c30 : fetch_word Asan.M.loaded_segments (0xb8db4 : word) = Some W_b8c30.
Proof. vm_refl. Qed.
Lemma D_b8c30 : decode_any W_b8c30 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c34 : bv 32 := 0x00028a63.
Lemma F_b8c34 : fetch_word Asan.M.loaded_segments (0xb8db8 : word) = Some W_b8c34.
Proof. vm_refl. Qed.
Lemma D_b8c34 : decode_any W_b8c34 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c38 : bv 32 := 0x00170713.
Lemma F_b8c38 : fetch_word Asan.M.loaded_segments (0xb8dbc : word) = Some W_b8c38.
Proof. vm_refl. Qed.
Lemma D_b8c38 : decode_any W_b8c38 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c3c : bv 32 := 0xfcf81ee3.
Lemma F_b8c3c : fetch_word Asan.M.loaded_segments (0xb8dc0 : word) = Some W_b8c3c.
Proof. vm_refl. Qed.
Lemma D_b8c3c : decode_any W_b8c3c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c40 : bv 32 := 0x0080006f.
Lemma F_b8c40 : fetch_word Asan.M.loaded_segments (0xb8dc4 : word) = Some W_b8c40.
Proof. vm_refl. Qed.
Lemma D_b8c40 : decode_any W_b8c40 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c44 : bv 32 := 0x00050693.
Lemma F_b8c44 : fetch_word Asan.M.loaded_segments (0xb8dc8 : word) = Some W_b8c44.
Proof. vm_refl. Qed.
Lemma D_b8c44 : decode_any W_b8c44 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c48 : bv 32 := 0x0036f793.
Lemma F_b8c48 : fetch_word Asan.M.loaded_segments (0xb8dcc : word) = Some W_b8c48.
Proof. vm_refl. Qed.
Lemma D_b8c48 : decode_any W_b8c48 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c4c : bv 32 := 0x0c078a63.
Lemma F_b8c4c : fetch_word Asan.M.loaded_segments (0xb8dd0 : word) = Some W_b8c4c.
Proof. vm_refl. Qed.
Lemma D_b8c4c : decode_any W_b8c4c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c50 : bv 32 := 0x02000713.
Lemma F_b8c50 : fetch_word Asan.M.loaded_segments (0xb8dd4 : word) = Some W_b8c50.
Proof. vm_refl. Qed.
Lemma D_b8c50 : decode_any W_b8c50 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c54 : bv 32 := 0x02e67063.
Lemma F_b8c54 : fetch_word Asan.M.loaded_segments (0xb8dd8 : word) = Some W_b8c54.
Proof. vm_refl. Qed.
Lemma D_b8c54 : decode_any W_b8c54 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c58 : bv 32 := 0x01000713.
Lemma F_b8c58 : fetch_word Asan.M.loaded_segments (0xb8ddc : word) = Some W_b8c58.
Proof. vm_refl. Qed.
Lemma D_b8c58 : decode_any W_b8c58 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c5c : bv 32 := 0x24e67863.
Lemma F_b8c5c : fetch_word Asan.M.loaded_segments (0xb8de0 : word) = Some W_b8c5c.
Proof. vm_refl. Qed.
Lemma D_b8c5c : decode_any W_b8c5c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c60 : bv 32 := 0x00867713.
Lemma F_b8c60 : fetch_word Asan.M.loaded_segments (0xb8de4 : word) = Some W_b8c60.
Proof. vm_refl. Qed.
Lemma D_b8c60 : decode_any W_b8c60 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c64 : bv 32 := 0x2c071e63.
Lemma F_b8c64 : fetch_word Asan.M.loaded_segments (0xb8de8 : word) = Some W_b8c64.
Proof. vm_refl. Qed.
Lemma D_b8c64 : decode_any W_b8c64 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c68 : bv 32 := 0x00467713.
Lemma F_b8c68 : fetch_word Asan.M.loaded_segments (0xb8dec : word) = Some W_b8c68.
Proof. vm_refl. Qed.
Lemma D_b8c68 : decode_any W_b8c68 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c6c : bv 32 := 0x32071463.
Lemma F_b8c6c : fetch_word Asan.M.loaded_segments (0xb8df0 : word) = Some W_b8c6c.
Proof. vm_refl. Qed.
Lemma D_b8c6c : decode_any W_b8c6c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c70 : bv 32 := 0x3500006f.
Lemma F_b8c70 : fetch_word Asan.M.loaded_segments (0xb8df4 : word) = Some W_b8c70.
Proof. vm_refl. Qed.
Lemma D_b8c70 : decode_any W_b8c70 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c74 : bv 32 := 0x0005a703.
Lemma F_b8c74 : fetch_word Asan.M.loaded_segments (0xb8df8 : word) = Some W_b8c74.
Proof. vm_refl. Qed.
Lemma D_b8c74 : decode_any W_b8c74 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c78 : bv 32 := 0x00300813.
Lemma F_b8c78 : fetch_word Asan.M.loaded_segments (0xb8dfc : word) = Some W_b8c78.
Proof. vm_refl. Qed.
Lemma D_b8c78 : decode_any W_b8c78 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c7c : bv 32 := 0x11078e63.
Lemma F_b8c7c : fetch_word Asan.M.loaded_segments (0xb8e00 : word) = Some W_b8c7c.
Proof. vm_refl. Qed.
Lemma D_b8c7c : decode_any W_b8c7c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c80 : bv 32 := 0x00200813.
Lemma F_b8c80 : fetch_word Asan.M.loaded_segments (0xb8e04 : word) = Some W_b8c80.
Proof. vm_refl. Qed.
Lemma D_b8c80 : decode_any W_b8c80 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c84 : bv 32 := 0x19079c63.
Lemma F_b8c84 : fetch_word Asan.M.loaded_segments (0xb8e08 : word) = Some W_b8c84.
Proof. vm_refl. Qed.
Lemma D_b8c84 : decode_any W_b8c84 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c88 : bv 32 := 0x00875793.
Lemma F_b8c88 : fetch_word Asan.M.loaded_segments (0xb8e0c : word) = Some W_b8c88.
Proof. vm_refl. Qed.
Lemma D_b8c88 : decode_any W_b8c88 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c8c : bv 32 := 0xffe60613.
Lemma F_b8c8c : fetch_word Asan.M.loaded_segments (0xb8e10 : word) = Some W_b8c8c.
Proof. vm_refl. Qed.
Lemma D_b8c8c : decode_any W_b8c8c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c90 : bv 32 := 0x00e68023.
Lemma F_b8c90 : fetch_word Asan.M.loaded_segments (0xb8e14 : word) = Some W_b8c90.
Proof. vm_refl. Qed.
Lemma D_b8c90 : decode_any W_b8c90 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c94 : bv 32 := 0x00f680a3.
Lemma F_b8c94 : fetch_word Asan.M.loaded_segments (0xb8e18 : word) = Some W_b8c94.
Proof. vm_refl. Qed.
Lemma D_b8c94 : decode_any W_b8c94 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c98 : bv 32 := 0x00268693.
Lemma F_b8c98 : fetch_word Asan.M.loaded_segments (0xb8e1c : word) = Some W_b8c98.
Proof. vm_refl. Qed.
Lemma D_b8c98 : decode_any W_b8c98 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8c9c : bv 32 := 0x01058593.
Lemma F_b8c9c : fetch_word Asan.M.loaded_segments (0xb8e20 : word) = Some W_b8c9c.
Proof. vm_refl. Qed.
Lemma D_b8c9c : decode_any W_b8c9c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ca0 : bv 32 := 0x01100793.
Lemma F_b8ca0 : fetch_word Asan.M.loaded_segments (0xb8e24 : word) = Some W_b8ca0.
Proof. vm_refl. Qed.
Lemma D_b8ca0 : decode_any W_b8ca0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ca4 : bv 32 := 0x0107581b.
Lemma F_b8ca4 : fetch_word Asan.M.loaded_segments (0xb8e28 : word) = Some W_b8ca4.
Proof. vm_refl. Qed.
Lemma D_b8ca4 : decode_any W_b8ca4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ca8 : bv 32 := 0xff45a883.
Lemma F_b8ca8 : fetch_word Asan.M.loaded_segments (0xb8e2c : word) = Some W_b8ca8.
Proof. vm_refl. Qed.
Lemma D_b8ca8 : decode_any W_b8ca8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cac : bv 32 := 0xff85a283.
Lemma F_b8cac : fetch_word Asan.M.loaded_segments (0xb8e30 : word) = Some W_b8cac.
Proof. vm_refl. Qed.
Lemma D_b8cac : decode_any W_b8cac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cb0 : bv 32 := 0xffc5a303.
Lemma F_b8cb0 : fetch_word Asan.M.loaded_segments (0xb8e34 : word) = Some W_b8cb0.
Proof. vm_refl. Qed.
Lemma D_b8cb0 : decode_any W_b8cb0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cb4 : bv 32 := 0x0005a703.
Lemma F_b8cb4 : fetch_word Asan.M.loaded_segments (0xb8e38 : word) = Some W_b8cb4.
Proof. vm_refl. Qed.
Lemma D_b8cb4 : decode_any W_b8cb4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cb8 : bv 32 := 0x01089393.
Lemma F_b8cb8 : fetch_word Asan.M.loaded_segments (0xb8e3c : word) = Some W_b8cb8.
Proof. vm_refl. Qed.
Lemma D_b8cb8 : decode_any W_b8cb8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cbc : bv 32 := 0x0108d89b.
Lemma F_b8cbc : fetch_word Asan.M.loaded_segments (0xb8e40 : word) = Some W_b8cbc.
Proof. vm_refl. Qed.
Lemma D_b8cbc : decode_any W_b8cbc = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cc0 : bv 32 := 0x0103e833.
Lemma F_b8cc0 : fetch_word Asan.M.loaded_segments (0xb8e44 : word) = Some W_b8cc0.
Proof. vm_refl. Qed.
Lemma D_b8cc0 : decode_any W_b8cc0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cc4 : bv 32 := 0x01029393.
Lemma F_b8cc4 : fetch_word Asan.M.loaded_segments (0xb8e48 : word) = Some W_b8cc4.
Proof. vm_refl. Qed.
Lemma D_b8cc4 : decode_any W_b8cc4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cc8 : bv 32 := 0x0102d29b.
Lemma F_b8cc8 : fetch_word Asan.M.loaded_segments (0xb8e4c : word) = Some W_b8cc8.
Proof. vm_refl. Qed.
Lemma D_b8cc8 : decode_any W_b8cc8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ccc : bv 32 := 0x0113e8b3.
Lemma F_b8ccc : fetch_word Asan.M.loaded_segments (0xb8e50 : word) = Some W_b8ccc.
Proof. vm_refl. Qed.
Lemma D_b8ccc : decode_any W_b8ccc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cd0 : bv 32 := 0x01031393.
Lemma F_b8cd0 : fetch_word Asan.M.loaded_segments (0xb8e54 : word) = Some W_b8cd0.
Proof. vm_refl. Qed.
Lemma D_b8cd0 : decode_any W_b8cd0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cd4 : bv 32 := 0x0103531b.
Lemma F_b8cd4 : fetch_word Asan.M.loaded_segments (0xb8e58 : word) = Some W_b8cd4.
Proof. vm_refl. Qed.
Lemma D_b8cd4 : decode_any W_b8cd4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cd8 : bv 32 := 0x0053e2b3.
Lemma F_b8cd8 : fetch_word Asan.M.loaded_segments (0xb8e5c : word) = Some W_b8cd8.
Proof. vm_refl. Qed.
Lemma D_b8cd8 : decode_any W_b8cd8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cdc : bv 32 := 0x01071393.
Lemma F_b8cdc : fetch_word Asan.M.loaded_segments (0xb8e60 : word) = Some W_b8cdc.
Proof. vm_refl. Qed.
Lemma D_b8cdc : decode_any W_b8cdc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ce0 : bv 32 := 0x0063e333.
Lemma F_b8ce0 : fetch_word Asan.M.loaded_segments (0xb8e64 : word) = Some W_b8ce0.
Proof. vm_refl. Qed.
Lemma D_b8ce0 : decode_any W_b8ce0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ce4 : bv 32 := 0xff060613.
Lemma F_b8ce4 : fetch_word Asan.M.loaded_segments (0xb8e68 : word) = Some W_b8ce4.
Proof. vm_refl. Qed.
Lemma D_b8ce4 : decode_any W_b8ce4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ce8 : bv 32 := 0x0106a023.
Lemma F_b8ce8 : fetch_word Asan.M.loaded_segments (0xb8e6c : word) = Some W_b8ce8.
Proof. vm_refl. Qed.
Lemma D_b8ce8 : decode_any W_b8ce8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cec : bv 32 := 0x0116a223.
Lemma F_b8cec : fetch_word Asan.M.loaded_segments (0xb8e70 : word) = Some W_b8cec.
Proof. vm_refl. Qed.
Lemma D_b8cec : decode_any W_b8cec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cf0 : bv 32 := 0x0056a423.
Lemma F_b8cf0 : fetch_word Asan.M.loaded_segments (0xb8e74 : word) = Some W_b8cf0.
Proof. vm_refl. Qed.
Lemma D_b8cf0 : decode_any W_b8cf0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cf4 : bv 32 := 0x0066a623.
Lemma F_b8cf4 : fetch_word Asan.M.loaded_segments (0xb8e78 : word) = Some W_b8cf4.
Proof. vm_refl. Qed.
Lemma D_b8cf4 : decode_any W_b8cf4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cf8 : bv 32 := 0x01068693.
Lemma F_b8cf8 : fetch_word Asan.M.loaded_segments (0xb8e7c : word) = Some W_b8cf8.
Proof. vm_refl. Qed.
Lemma D_b8cf8 : decode_any W_b8cf8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8cfc : bv 32 := 0x01058593.
Lemma F_b8cfc : fetch_word Asan.M.loaded_segments (0xb8e80 : word) = Some W_b8cfc.
Proof. vm_refl. Qed.
Lemma D_b8cfc : decode_any W_b8cfc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d00 : bv 32 := 0xfac7e2e3.
Lemma F_b8d00 : fetch_word Asan.M.loaded_segments (0xb8e84 : word) = Some W_b8d00.
Proof. vm_refl. Qed.
Lemma D_b8d00 : decode_any W_b8d00 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d04 : bv 32 := 0xff258593.
Lemma F_b8d04 : fetch_word Asan.M.loaded_segments (0xb8e88 : word) = Some W_b8d04.
Proof. vm_refl. Qed.
Lemma D_b8d04 : decode_any W_b8d04 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d08 : bv 32 := 0x01000713.
Lemma F_b8d08 : fetch_word Asan.M.loaded_segments (0xb8e8c : word) = Some W_b8d08.
Proof. vm_refl. Qed.
Lemma D_b8d08 : decode_any W_b8d08 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d0c : bv 32 := 0xf4e66ae3.
Lemma F_b8d0c : fetch_word Asan.M.loaded_segments (0xb8e90 : word) = Some W_b8d0c.
Proof. vm_refl. Qed.
Lemma D_b8d0c : decode_any W_b8d0c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d10 : bv 32 := 0x19c0006f.
Lemma F_b8d10 : fetch_word Asan.M.loaded_segments (0xb8e94 : word) = Some W_b8d10.
Proof. vm_refl. Qed.
Lemma D_b8d10 : decode_any W_b8d10 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d14 : bv 32 := 0x00050693.
Lemma F_b8d14 : fetch_word Asan.M.loaded_segments (0xb8e98 : word) = Some W_b8d14.
Proof. vm_refl. Qed.
Lemma D_b8d14 : decode_any W_b8d14 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d18 : bv 32 := 0x00357793.
Lemma F_b8d18 : fetch_word Asan.M.loaded_segments (0xb8e9c : word) = Some W_b8d18.
Proof. vm_refl. Qed.
Lemma D_b8d18 : decode_any W_b8d18 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d1c : bv 32 := 0xf2079ae3.
Lemma F_b8d1c : fetch_word Asan.M.loaded_segments (0xb8ea0 : word) = Some W_b8d1c.
Proof. vm_refl. Qed.
Lemma D_b8d1c : decode_any W_b8d1c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d20 : bv 32 := 0x01000713.
Lemma F_b8d20 : fetch_word Asan.M.loaded_segments (0xb8ea4 : word) = Some W_b8d20.
Proof. vm_refl. Qed.
Lemma D_b8d20 : decode_any W_b8d20 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d24 : bv 32 := 0x02e66c63.
Lemma F_b8d24 : fetch_word Asan.M.loaded_segments (0xb8ea8 : word) = Some W_b8d24.
Proof. vm_refl. Qed.
Lemma D_b8d24 : decode_any W_b8d24 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d28 : bv 32 := 0x00f00713.
Lemma F_b8d28 : fetch_word Asan.M.loaded_segments (0xb8eac : word) = Some W_b8d28.
Proof. vm_refl. Qed.
Lemma D_b8d28 : decode_any W_b8d28 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d2c : bv 32 := 0x0005a783.
Lemma F_b8d2c : fetch_word Asan.M.loaded_segments (0xb8eb0 : word) = Some W_b8d2c.
Proof. vm_refl. Qed.
Lemma D_b8d2c : decode_any W_b8d2c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d30 : bv 32 := 0x0045a803.
Lemma F_b8d30 : fetch_word Asan.M.loaded_segments (0xb8eb4 : word) = Some W_b8d30.
Proof. vm_refl. Qed.
Lemma D_b8d30 : decode_any W_b8d30 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d34 : bv 32 := 0x0085a883.
Lemma F_b8d34 : fetch_word Asan.M.loaded_segments (0xb8eb8 : word) = Some W_b8d34.
Proof. vm_refl. Qed.
Lemma D_b8d34 : decode_any W_b8d34 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d38 : bv 32 := 0x00c5a283.
Lemma F_b8d38 : fetch_word Asan.M.loaded_segments (0xb8ebc : word) = Some W_b8d38.
Proof. vm_refl. Qed.
Lemma D_b8d38 : decode_any W_b8d38 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d3c : bv 32 := 0x01058593.
Lemma F_b8d3c : fetch_word Asan.M.loaded_segments (0xb8ec0 : word) = Some W_b8d3c.
Proof. vm_refl. Qed.
Lemma D_b8d3c : decode_any W_b8d3c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d40 : bv 32 := 0xff060613.
Lemma F_b8d40 : fetch_word Asan.M.loaded_segments (0xb8ec4 : word) = Some W_b8d40.
Proof. vm_refl. Qed.
Lemma D_b8d40 : decode_any W_b8d40 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d44 : bv 32 := 0x00f6a023.
Lemma F_b8d44 : fetch_word Asan.M.loaded_segments (0xb8ec8 : word) = Some W_b8d44.
Proof. vm_refl. Qed.
Lemma D_b8d44 : decode_any W_b8d44 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d48 : bv 32 := 0x0106a223.
Lemma F_b8d48 : fetch_word Asan.M.loaded_segments (0xb8ecc : word) = Some W_b8d48.
Proof. vm_refl. Qed.
Lemma D_b8d48 : decode_any W_b8d48 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d4c : bv 32 := 0x0116a423.
Lemma F_b8d4c : fetch_word Asan.M.loaded_segments (0xb8ed0 : word) = Some W_b8d4c.
Proof. vm_refl. Qed.
Lemma D_b8d4c : decode_any W_b8d4c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d50 : bv 32 := 0x0056a623.
Lemma F_b8d50 : fetch_word Asan.M.loaded_segments (0xb8ed4 : word) = Some W_b8d50.
Proof. vm_refl. Qed.
Lemma D_b8d50 : decode_any W_b8d50 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d54 : bv 32 := 0x01068693.
Lemma F_b8d54 : fetch_word Asan.M.loaded_segments (0xb8ed8 : word) = Some W_b8d54.
Proof. vm_refl. Qed.
Lemma D_b8d54 : decode_any W_b8d54 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d58 : bv 32 := 0xfcc76ae3.
Lemma F_b8d58 : fetch_word Asan.M.loaded_segments (0xb8edc : word) = Some W_b8d58.
Proof. vm_refl. Qed.
Lemma D_b8d58 : decode_any W_b8d58 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d5c : bv 32 := 0x00800713.
Lemma F_b8d5c : fetch_word Asan.M.loaded_segments (0xb8ee0 : word) = Some W_b8d5c.
Proof. vm_refl. Qed.
Lemma D_b8d5c : decode_any W_b8d5c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d60 : bv 32 := 0x00e66e63.
Lemma F_b8d60 : fetch_word Asan.M.loaded_segments (0xb8ee4 : word) = Some W_b8d60.
Proof. vm_refl. Qed.
Lemma D_b8d60 : decode_any W_b8d60 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d64 : bv 32 := 0x0005a703.
Lemma F_b8d64 : fetch_word Asan.M.loaded_segments (0xb8ee8 : word) = Some W_b8d64.
Proof. vm_refl. Qed.
Lemma D_b8d64 : decode_any W_b8d64 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d68 : bv 32 := 0x0045a783.
Lemma F_b8d68 : fetch_word Asan.M.loaded_segments (0xb8eec : word) = Some W_b8d68.
Proof. vm_refl. Qed.
Lemma D_b8d68 : decode_any W_b8d68 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d6c : bv 32 := 0x00e6a023.
Lemma F_b8d6c : fetch_word Asan.M.loaded_segments (0xb8ef0 : word) = Some W_b8d6c.
Proof. vm_refl. Qed.
Lemma D_b8d6c : decode_any W_b8d6c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d70 : bv 32 := 0x00f6a223.
Lemma F_b8d70 : fetch_word Asan.M.loaded_segments (0xb8ef4 : word) = Some W_b8d70.
Proof. vm_refl. Qed.
Lemma D_b8d70 : decode_any W_b8d70 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d74 : bv 32 := 0x00868693.
Lemma F_b8d74 : fetch_word Asan.M.loaded_segments (0xb8ef8 : word) = Some W_b8d74.
Proof. vm_refl. Qed.
Lemma D_b8d74 : decode_any W_b8d74 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d78 : bv 32 := 0x00858593.
Lemma F_b8d78 : fetch_word Asan.M.loaded_segments (0xb8efc : word) = Some W_b8d78.
Proof. vm_refl. Qed.
Lemma D_b8d78 : decode_any W_b8d78 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d7c : bv 32 := 0x00467713.
Lemma F_b8d7c : fetch_word Asan.M.loaded_segments (0xb8f00 : word) = Some W_b8d7c.
Proof. vm_refl. Qed.
Lemma D_b8d7c : decode_any W_b8d7c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d80 : bv 32 := 0x24070063.
Lemma F_b8d80 : fetch_word Asan.M.loaded_segments (0xb8f04 : word) = Some W_b8d80.
Proof. vm_refl. Qed.
Lemma D_b8d80 : decode_any W_b8d80 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d84 : bv 32 := 0x0005a703.
Lemma F_b8d84 : fetch_word Asan.M.loaded_segments (0xb8f08 : word) = Some W_b8d84.
Proof. vm_refl. Qed.
Lemma D_b8d84 : decode_any W_b8d84 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d88 : bv 32 := 0x00458593.
Lemma F_b8d88 : fetch_word Asan.M.loaded_segments (0xb8f0c : word) = Some W_b8d88.
Proof. vm_refl. Qed.
Lemma D_b8d88 : decode_any W_b8d88 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d8c : bv 32 := 0x00e6a023.
Lemma F_b8d8c : fetch_word Asan.M.loaded_segments (0xb8f10 : word) = Some W_b8d8c.
Proof. vm_refl. Qed.
Lemma D_b8d8c : decode_any W_b8d8c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d90 : bv 32 := 0x00468693.
Lemma F_b8d90 : fetch_word Asan.M.loaded_segments (0xb8f14 : word) = Some W_b8d90.
Proof. vm_refl. Qed.
Lemma D_b8d90 : decode_any W_b8d90 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d94 : bv 32 := 0x22c0006f.
Lemma F_b8d94 : fetch_word Asan.M.loaded_segments (0xb8f18 : word) = Some W_b8d94.
Proof. vm_refl. Qed.
Lemma D_b8d94 : decode_any W_b8d94 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d98 : bv 32 := 0x00e68023.
Lemma F_b8d98 : fetch_word Asan.M.loaded_segments (0xb8f1c : word) = Some W_b8d98.
Proof. vm_refl. Qed.
Lemma D_b8d98 : decode_any W_b8d98 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8d9c : bv 32 := 0x00168693.
Lemma F_b8d9c : fetch_word Asan.M.loaded_segments (0xb8f20 : word) = Some W_b8d9c.
Proof. vm_refl. Qed.
Lemma D_b8d9c : decode_any W_b8d9c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8da0 : bv 32 := 0xfff60613.
Lemma F_b8da0 : fetch_word Asan.M.loaded_segments (0xb8f24 : word) = Some W_b8da0.
Proof. vm_refl. Qed.
Lemma D_b8da0 : decode_any W_b8da0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8da4 : bv 32 := 0x01058593.
Lemma F_b8da4 : fetch_word Asan.M.loaded_segments (0xb8f28 : word) = Some W_b8da4.
Proof. vm_refl. Qed.
Lemma D_b8da4 : decode_any W_b8da4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8da8 : bv 32 := 0x01200793.
Lemma F_b8da8 : fetch_word Asan.M.loaded_segments (0xb8f2c : word) = Some W_b8da8.
Proof. vm_refl. Qed.
Lemma D_b8da8 : decode_any W_b8da8 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dac : bv 32 := 0x0087581b.
Lemma F_b8dac : fetch_word Asan.M.loaded_segments (0xb8f30 : word) = Some W_b8dac.
Proof. vm_refl. Qed.
Lemma D_b8dac : decode_any W_b8dac = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8db0 : bv 32 := 0xff45a883.
Lemma F_b8db0 : fetch_word Asan.M.loaded_segments (0xb8f34 : word) = Some W_b8db0.
Proof. vm_refl. Qed.
Lemma D_b8db0 : decode_any W_b8db0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8db4 : bv 32 := 0xff85a283.
Lemma F_b8db4 : fetch_word Asan.M.loaded_segments (0xb8f38 : word) = Some W_b8db4.
Proof. vm_refl. Qed.
Lemma D_b8db4 : decode_any W_b8db4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8db8 : bv 32 := 0xffc5a303.
Lemma F_b8db8 : fetch_word Asan.M.loaded_segments (0xb8f3c : word) = Some W_b8db8.
Proof. vm_refl. Qed.
Lemma D_b8db8 : decode_any W_b8db8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dbc : bv 32 := 0x0005a703.
Lemma F_b8dbc : fetch_word Asan.M.loaded_segments (0xb8f40 : word) = Some W_b8dbc.
Proof. vm_refl. Qed.
Lemma D_b8dbc : decode_any W_b8dbc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dc0 : bv 32 := 0x01889393.
Lemma F_b8dc0 : fetch_word Asan.M.loaded_segments (0xb8f44 : word) = Some W_b8dc0.
Proof. vm_refl. Qed.
Lemma D_b8dc0 : decode_any W_b8dc0 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dc4 : bv 32 := 0x0088d89b.
Lemma F_b8dc4 : fetch_word Asan.M.loaded_segments (0xb8f48 : word) = Some W_b8dc4.
Proof. vm_refl. Qed.
Lemma D_b8dc4 : decode_any W_b8dc4 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dc8 : bv 32 := 0x0103e833.
Lemma F_b8dc8 : fetch_word Asan.M.loaded_segments (0xb8f4c : word) = Some W_b8dc8.
Proof. vm_refl. Qed.
Lemma D_b8dc8 : decode_any W_b8dc8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dcc : bv 32 := 0x01829393.
Lemma F_b8dcc : fetch_word Asan.M.loaded_segments (0xb8f50 : word) = Some W_b8dcc.
Proof. vm_refl. Qed.
Lemma D_b8dcc : decode_any W_b8dcc = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dd0 : bv 32 := 0x0082d29b.
Lemma F_b8dd0 : fetch_word Asan.M.loaded_segments (0xb8f54 : word) = Some W_b8dd0.
Proof. vm_refl. Qed.
Lemma D_b8dd0 : decode_any W_b8dd0 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dd4 : bv 32 := 0x0113e8b3.
Lemma F_b8dd4 : fetch_word Asan.M.loaded_segments (0xb8f58 : word) = Some W_b8dd4.
Proof. vm_refl. Qed.
Lemma D_b8dd4 : decode_any W_b8dd4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dd8 : bv 32 := 0x01831393.
Lemma F_b8dd8 : fetch_word Asan.M.loaded_segments (0xb8f5c : word) = Some W_b8dd8.
Proof. vm_refl. Qed.
Lemma D_b8dd8 : decode_any W_b8dd8 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ddc : bv 32 := 0x0083531b.
Lemma F_b8ddc : fetch_word Asan.M.loaded_segments (0xb8f60 : word) = Some W_b8ddc.
Proof. vm_refl. Qed.
Lemma D_b8ddc : decode_any W_b8ddc = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8de0 : bv 32 := 0x0053e2b3.
Lemma F_b8de0 : fetch_word Asan.M.loaded_segments (0xb8f64 : word) = Some W_b8de0.
Proof. vm_refl. Qed.
Lemma D_b8de0 : decode_any W_b8de0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8de4 : bv 32 := 0x01871393.
Lemma F_b8de4 : fetch_word Asan.M.loaded_segments (0xb8f68 : word) = Some W_b8de4.
Proof. vm_refl. Qed.
Lemma D_b8de4 : decode_any W_b8de4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8de8 : bv 32 := 0x0063e333.
Lemma F_b8de8 : fetch_word Asan.M.loaded_segments (0xb8f6c : word) = Some W_b8de8.
Proof. vm_refl. Qed.
Lemma D_b8de8 : decode_any W_b8de8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dec : bv 32 := 0xff060613.
Lemma F_b8dec : fetch_word Asan.M.loaded_segments (0xb8f70 : word) = Some W_b8dec.
Proof. vm_refl. Qed.
Lemma D_b8dec : decode_any W_b8dec = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8df0 : bv 32 := 0x0106a023.
Lemma F_b8df0 : fetch_word Asan.M.loaded_segments (0xb8f74 : word) = Some W_b8df0.
Proof. vm_refl. Qed.
Lemma D_b8df0 : decode_any W_b8df0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8df4 : bv 32 := 0x0116a223.
Lemma F_b8df4 : fetch_word Asan.M.loaded_segments (0xb8f78 : word) = Some W_b8df4.
Proof. vm_refl. Qed.
Lemma D_b8df4 : decode_any W_b8df4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8df8 : bv 32 := 0x0056a423.
Lemma F_b8df8 : fetch_word Asan.M.loaded_segments (0xb8f7c : word) = Some W_b8df8.
Proof. vm_refl. Qed.
Lemma D_b8df8 : decode_any W_b8df8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8dfc : bv 32 := 0x0066a623.
Lemma F_b8dfc : fetch_word Asan.M.loaded_segments (0xb8f80 : word) = Some W_b8dfc.
Proof. vm_refl. Qed.
Lemma D_b8dfc : decode_any W_b8dfc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e00 : bv 32 := 0x01068693.
Lemma F_b8e00 : fetch_word Asan.M.loaded_segments (0xb8f84 : word) = Some W_b8e00.
Proof. vm_refl. Qed.
Lemma D_b8e00 : decode_any W_b8e00 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e04 : bv 32 := 0x01058593.
Lemma F_b8e04 : fetch_word Asan.M.loaded_segments (0xb8f88 : word) = Some W_b8e04.
Proof. vm_refl. Qed.
Lemma D_b8e04 : decode_any W_b8e04 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e08 : bv 32 := 0xfac7e2e3.
Lemma F_b8e08 : fetch_word Asan.M.loaded_segments (0xb8f8c : word) = Some W_b8e08.
Proof. vm_refl. Qed.
Lemma D_b8e08 : decode_any W_b8e08 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e0c : bv 32 := 0xff158593.
Lemma F_b8e0c : fetch_word Asan.M.loaded_segments (0xb8f90 : word) = Some W_b8e0c.
Proof. vm_refl. Qed.
Lemma D_b8e0c : decode_any W_b8e0c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e10 : bv 32 := 0x01000713.
Lemma F_b8e10 : fetch_word Asan.M.loaded_segments (0xb8f94 : word) = Some W_b8e10.
Proof. vm_refl. Qed.
Lemma D_b8e10 : decode_any W_b8e10 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e14 : bv 32 := 0xe4e666e3.
Lemma F_b8e14 : fetch_word Asan.M.loaded_segments (0xb8f98 : word) = Some W_b8e14.
Proof. vm_refl. Qed.
Lemma D_b8e14 : decode_any W_b8e14 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e18 : bv 32 := 0x0940006f.
Lemma F_b8e18 : fetch_word Asan.M.loaded_segments (0xb8f9c : word) = Some W_b8e18.
Proof. vm_refl. Qed.
Lemma D_b8e18 : decode_any W_b8e18 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e1c : bv 32 := 0x00875793.
Lemma F_b8e1c : fetch_word Asan.M.loaded_segments (0xb8fa0 : word) = Some W_b8e1c.
Proof. vm_refl. Qed.
Lemma D_b8e1c : decode_any W_b8e1c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e20 : bv 32 := 0x01075813.
Lemma F_b8e20 : fetch_word Asan.M.loaded_segments (0xb8fa4 : word) = Some W_b8e20.
Proof. vm_refl. Qed.
Lemma D_b8e20 : decode_any W_b8e20 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e24 : bv 32 := 0xffd60613.
Lemma F_b8e24 : fetch_word Asan.M.loaded_segments (0xb8fa8 : word) = Some W_b8e24.
Proof. vm_refl. Qed.
Lemma D_b8e24 : decode_any W_b8e24 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e28 : bv 32 := 0x00e68023.
Lemma F_b8e28 : fetch_word Asan.M.loaded_segments (0xb8fac : word) = Some W_b8e28.
Proof. vm_refl. Qed.
Lemma D_b8e28 : decode_any W_b8e28 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e2c : bv 32 := 0x00f680a3.
Lemma F_b8e2c : fetch_word Asan.M.loaded_segments (0xb8fb0 : word) = Some W_b8e2c.
Proof. vm_refl. Qed.
Lemma D_b8e2c : decode_any W_b8e2c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e30 : bv 32 := 0x01068123.
Lemma F_b8e30 : fetch_word Asan.M.loaded_segments (0xb8fb4 : word) = Some W_b8e30.
Proof. vm_refl. Qed.
Lemma D_b8e30 : decode_any W_b8e30 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e34 : bv 32 := 0x00368693.
Lemma F_b8e34 : fetch_word Asan.M.loaded_segments (0xb8fb8 : word) = Some W_b8e34.
Proof. vm_refl. Qed.
Lemma D_b8e34 : decode_any W_b8e34 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e38 : bv 32 := 0x01058593.
Lemma F_b8e38 : fetch_word Asan.M.loaded_segments (0xb8fbc : word) = Some W_b8e38.
Proof. vm_refl. Qed.
Lemma D_b8e38 : decode_any W_b8e38 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e3c : bv 32 := 0x01000793.
Lemma F_b8e3c : fetch_word Asan.M.loaded_segments (0xb8fc0 : word) = Some W_b8e3c.
Proof. vm_refl. Qed.
Lemma D_b8e3c : decode_any W_b8e3c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e40 : bv 32 := 0x0187581b.
Lemma F_b8e40 : fetch_word Asan.M.loaded_segments (0xb8fc4 : word) = Some W_b8e40.
Proof. vm_refl. Qed.
Lemma D_b8e40 : decode_any W_b8e40 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e44 : bv 32 := 0xff45a883.
Lemma F_b8e44 : fetch_word Asan.M.loaded_segments (0xb8fc8 : word) = Some W_b8e44.
Proof. vm_refl. Qed.
Lemma D_b8e44 : decode_any W_b8e44 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e48 : bv 32 := 0xff85a283.
Lemma F_b8e48 : fetch_word Asan.M.loaded_segments (0xb8fcc : word) = Some W_b8e48.
Proof. vm_refl. Qed.
Lemma D_b8e48 : decode_any W_b8e48 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e4c : bv 32 := 0xffc5a303.
Lemma F_b8e4c : fetch_word Asan.M.loaded_segments (0xb8fd0 : word) = Some W_b8e4c.
Proof. vm_refl. Qed.
Lemma D_b8e4c : decode_any W_b8e4c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e50 : bv 32 := 0x0005a703.
Lemma F_b8e50 : fetch_word Asan.M.loaded_segments (0xb8fd4 : word) = Some W_b8e50.
Proof. vm_refl. Qed.
Lemma D_b8e50 : decode_any W_b8e50 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e54 : bv 32 := 0x00889393.
Lemma F_b8e54 : fetch_word Asan.M.loaded_segments (0xb8fd8 : word) = Some W_b8e54.
Proof. vm_refl. Qed.
Lemma D_b8e54 : decode_any W_b8e54 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e58 : bv 32 := 0x0188d89b.
Lemma F_b8e58 : fetch_word Asan.M.loaded_segments (0xb8fdc : word) = Some W_b8e58.
Proof. vm_refl. Qed.
Lemma D_b8e58 : decode_any W_b8e58 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e5c : bv 32 := 0x0103e833.
Lemma F_b8e5c : fetch_word Asan.M.loaded_segments (0xb8fe0 : word) = Some W_b8e5c.
Proof. vm_refl. Qed.
Lemma D_b8e5c : decode_any W_b8e5c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e60 : bv 32 := 0x00829393.
Lemma F_b8e60 : fetch_word Asan.M.loaded_segments (0xb8fe4 : word) = Some W_b8e60.
Proof. vm_refl. Qed.
Lemma D_b8e60 : decode_any W_b8e60 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e64 : bv 32 := 0x0182d29b.
Lemma F_b8e64 : fetch_word Asan.M.loaded_segments (0xb8fe8 : word) = Some W_b8e64.
Proof. vm_refl. Qed.
Lemma D_b8e64 : decode_any W_b8e64 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e68 : bv 32 := 0x0113e8b3.
Lemma F_b8e68 : fetch_word Asan.M.loaded_segments (0xb8fec : word) = Some W_b8e68.
Proof. vm_refl. Qed.
Lemma D_b8e68 : decode_any W_b8e68 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e6c : bv 32 := 0x00831393.
Lemma F_b8e6c : fetch_word Asan.M.loaded_segments (0xb8ff0 : word) = Some W_b8e6c.
Proof. vm_refl. Qed.
Lemma D_b8e6c : decode_any W_b8e6c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e70 : bv 32 := 0x0183531b.
Lemma F_b8e70 : fetch_word Asan.M.loaded_segments (0xb8ff4 : word) = Some W_b8e70.
Proof. vm_refl. Qed.
Lemma D_b8e70 : decode_any W_b8e70 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e74 : bv 32 := 0x0053e2b3.
Lemma F_b8e74 : fetch_word Asan.M.loaded_segments (0xb8ff8 : word) = Some W_b8e74.
Proof. vm_refl. Qed.
Lemma D_b8e74 : decode_any W_b8e74 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e78 : bv 32 := 0x00871393.
Lemma F_b8e78 : fetch_word Asan.M.loaded_segments (0xb8ffc : word) = Some W_b8e78.
Proof. vm_refl. Qed.
Lemma D_b8e78 : decode_any W_b8e78 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e7c : bv 32 := 0x0063e333.
Lemma F_b8e7c : fetch_word Asan.M.loaded_segments (0xb9000 : word) = Some W_b8e7c.
Proof. vm_refl. Qed.
Lemma D_b8e7c : decode_any W_b8e7c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e80 : bv 32 := 0xff060613.
Lemma F_b8e80 : fetch_word Asan.M.loaded_segments (0xb9004 : word) = Some W_b8e80.
Proof. vm_refl. Qed.
Lemma D_b8e80 : decode_any W_b8e80 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e84 : bv 32 := 0x0106a023.
Lemma F_b8e84 : fetch_word Asan.M.loaded_segments (0xb9008 : word) = Some W_b8e84.
Proof. vm_refl. Qed.
Lemma D_b8e84 : decode_any W_b8e84 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e88 : bv 32 := 0x0116a223.
Lemma F_b8e88 : fetch_word Asan.M.loaded_segments (0xb900c : word) = Some W_b8e88.
Proof. vm_refl. Qed.
Lemma D_b8e88 : decode_any W_b8e88 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e8c : bv 32 := 0x0056a423.
Lemma F_b8e8c : fetch_word Asan.M.loaded_segments (0xb9010 : word) = Some W_b8e8c.
Proof. vm_refl. Qed.
Lemma D_b8e8c : decode_any W_b8e8c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e90 : bv 32 := 0x0066a623.
Lemma F_b8e90 : fetch_word Asan.M.loaded_segments (0xb9014 : word) = Some W_b8e90.
Proof. vm_refl. Qed.
Lemma D_b8e90 : decode_any W_b8e90 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e94 : bv 32 := 0x01068693.
Lemma F_b8e94 : fetch_word Asan.M.loaded_segments (0xb9018 : word) = Some W_b8e94.
Proof. vm_refl. Qed.
Lemma D_b8e94 : decode_any W_b8e94 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e98 : bv 32 := 0x01058593.
Lemma F_b8e98 : fetch_word Asan.M.loaded_segments (0xb901c : word) = Some W_b8e98.
Proof. vm_refl. Qed.
Lemma D_b8e98 : decode_any W_b8e98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8e9c : bv 32 := 0xfac7e2e3.
Lemma F_b8e9c : fetch_word Asan.M.loaded_segments (0xb9020 : word) = Some W_b8e9c.
Proof. vm_refl. Qed.
Lemma D_b8e9c : decode_any W_b8e9c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ea0 : bv 32 := 0xff358593.
Lemma F_b8ea0 : fetch_word Asan.M.loaded_segments (0xb9024 : word) = Some W_b8ea0.
Proof. vm_refl. Qed.
Lemma D_b8ea0 : decode_any W_b8ea0 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ea4 : bv 32 := 0x01000713.
Lemma F_b8ea4 : fetch_word Asan.M.loaded_segments (0xb9028 : word) = Some W_b8ea4.
Proof. vm_refl. Qed.
Lemma D_b8ea4 : decode_any W_b8ea4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ea8 : bv 32 := 0xdae66ce3.
Lemma F_b8ea8 : fetch_word Asan.M.loaded_segments (0xb902c : word) = Some W_b8ea8.
Proof. vm_refl. Qed.
Lemma D_b8ea8 : decode_any W_b8ea8 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8eac : bv 32 := 0x0005c703.
Lemma F_b8eac : fetch_word Asan.M.loaded_segments (0xb9030 : word) = Some W_b8eac.
Proof. vm_refl. Qed.
Lemma D_b8eac : decode_any W_b8eac = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8eb0 : bv 32 := 0x0015c783.
Lemma F_b8eb0 : fetch_word Asan.M.loaded_segments (0xb9034 : word) = Some W_b8eb0.
Proof. vm_refl. Qed.
Lemma D_b8eb0 : decode_any W_b8eb0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8eb4 : bv 32 := 0x0025c803.
Lemma F_b8eb4 : fetch_word Asan.M.loaded_segments (0xb9038 : word) = Some W_b8eb4.
Proof. vm_refl. Qed.
Lemma D_b8eb4 : decode_any W_b8eb4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8eb8 : bv 32 := 0x0035c883.
Lemma F_b8eb8 : fetch_word Asan.M.loaded_segments (0xb903c : word) = Some W_b8eb8.
Proof. vm_refl. Qed.
Lemma D_b8eb8 : decode_any W_b8eb8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ebc : bv 32 := 0x0045c283.
Lemma F_b8ebc : fetch_word Asan.M.loaded_segments (0xb9040 : word) = Some W_b8ebc.
Proof. vm_refl. Qed.
Lemma D_b8ebc : decode_any W_b8ebc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ec0 : bv 32 := 0x0055c303.
Lemma F_b8ec0 : fetch_word Asan.M.loaded_segments (0xb9044 : word) = Some W_b8ec0.
Proof. vm_refl. Qed.
Lemma D_b8ec0 : decode_any W_b8ec0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ec4 : bv 32 := 0x0065c383.
Lemma F_b8ec4 : fetch_word Asan.M.loaded_segments (0xb9048 : word) = Some W_b8ec4.
Proof. vm_refl. Qed.
Lemma D_b8ec4 : decode_any W_b8ec4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ec8 : bv 32 := 0x0075ce03.
Lemma F_b8ec8 : fetch_word Asan.M.loaded_segments (0xb904c : word) = Some W_b8ec8.
Proof. vm_refl. Qed.
Lemma D_b8ec8 : decode_any W_b8ec8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ecc : bv 32 := 0x00e68023.
Lemma F_b8ecc : fetch_word Asan.M.loaded_segments (0xb9050 : word) = Some W_b8ecc.
Proof. vm_refl. Qed.
Lemma D_b8ecc : decode_any W_b8ecc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ed0 : bv 32 := 0x00f680a3.
Lemma F_b8ed0 : fetch_word Asan.M.loaded_segments (0xb9054 : word) = Some W_b8ed0.
Proof. vm_refl. Qed.
Lemma D_b8ed0 : decode_any W_b8ed0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ed4 : bv 32 := 0x01068123.
Lemma F_b8ed4 : fetch_word Asan.M.loaded_segments (0xb9058 : word) = Some W_b8ed4.
Proof. vm_refl. Qed.
Lemma D_b8ed4 : decode_any W_b8ed4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ed8 : bv 32 := 0x011681a3.
Lemma F_b8ed8 : fetch_word Asan.M.loaded_segments (0xb905c : word) = Some W_b8ed8.
Proof. vm_refl. Qed.
Lemma D_b8ed8 : decode_any W_b8ed8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8edc : bv 32 := 0x0085c703.
Lemma F_b8edc : fetch_word Asan.M.loaded_segments (0xb9060 : word) = Some W_b8edc.
Proof. vm_refl. Qed.
Lemma D_b8edc : decode_any W_b8edc = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ee0 : bv 32 := 0x0095c783.
Lemma F_b8ee0 : fetch_word Asan.M.loaded_segments (0xb9064 : word) = Some W_b8ee0.
Proof. vm_refl. Qed.
Lemma D_b8ee0 : decode_any W_b8ee0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ee4 : bv 32 := 0x00a5c803.
Lemma F_b8ee4 : fetch_word Asan.M.loaded_segments (0xb9068 : word) = Some W_b8ee4.
Proof. vm_refl. Qed.
Lemma D_b8ee4 : decode_any W_b8ee4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ee8 : bv 32 := 0x00b5c883.
Lemma F_b8ee8 : fetch_word Asan.M.loaded_segments (0xb906c : word) = Some W_b8ee8.
Proof. vm_refl. Qed.
Lemma D_b8ee8 : decode_any W_b8ee8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8eec : bv 32 := 0x00568223.
Lemma F_b8eec : fetch_word Asan.M.loaded_segments (0xb9070 : word) = Some W_b8eec.
Proof. vm_refl. Qed.
Lemma D_b8eec : decode_any W_b8eec = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ef0 : bv 32 := 0x006682a3.
Lemma F_b8ef0 : fetch_word Asan.M.loaded_segments (0xb9074 : word) = Some W_b8ef0.
Proof. vm_refl. Qed.
Lemma D_b8ef0 : decode_any W_b8ef0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ef4 : bv 32 := 0x00768323.
Lemma F_b8ef4 : fetch_word Asan.M.loaded_segments (0xb9078 : word) = Some W_b8ef4.
Proof. vm_refl. Qed.
Lemma D_b8ef4 : decode_any W_b8ef4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ef8 : bv 32 := 0x01c683a3.
Lemma F_b8ef8 : fetch_word Asan.M.loaded_segments (0xb907c : word) = Some W_b8ef8.
Proof. vm_refl. Qed.
Lemma D_b8ef8 : decode_any W_b8ef8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8efc : bv 32 := 0x00c5c283.
Lemma F_b8efc : fetch_word Asan.M.loaded_segments (0xb9080 : word) = Some W_b8efc.
Proof. vm_refl. Qed.
Lemma D_b8efc : decode_any W_b8efc = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f00 : bv 32 := 0x00d5c303.
Lemma F_b8f00 : fetch_word Asan.M.loaded_segments (0xb9084 : word) = Some W_b8f00.
Proof. vm_refl. Qed.
Lemma D_b8f00 : decode_any W_b8f00 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f04 : bv 32 := 0x00e5c383.
Lemma F_b8f04 : fetch_word Asan.M.loaded_segments (0xb9088 : word) = Some W_b8f04.
Proof. vm_refl. Qed.
Lemma D_b8f04 : decode_any W_b8f04 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f08 : bv 32 := 0x00f5ce03.
Lemma F_b8f08 : fetch_word Asan.M.loaded_segments (0xb908c : word) = Some W_b8f08.
Proof. vm_refl. Qed.
Lemma D_b8f08 : decode_any W_b8f08 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f0c : bv 32 := 0x01058593.
Lemma F_b8f0c : fetch_word Asan.M.loaded_segments (0xb9090 : word) = Some W_b8f0c.
Proof. vm_refl. Qed.
Lemma D_b8f0c : decode_any W_b8f0c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f10 : bv 32 := 0x00e68423.
Lemma F_b8f10 : fetch_word Asan.M.loaded_segments (0xb9094 : word) = Some W_b8f10.
Proof. vm_refl. Qed.
Lemma D_b8f10 : decode_any W_b8f10 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f14 : bv 32 := 0x00f684a3.
Lemma F_b8f14 : fetch_word Asan.M.loaded_segments (0xb9098 : word) = Some W_b8f14.
Proof. vm_refl. Qed.
Lemma D_b8f14 : decode_any W_b8f14 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f18 : bv 32 := 0x01068523.
Lemma F_b8f18 : fetch_word Asan.M.loaded_segments (0xb909c : word) = Some W_b8f18.
Proof. vm_refl. Qed.
Lemma D_b8f18 : decode_any W_b8f18 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f1c : bv 32 := 0x011685a3.
Lemma F_b8f1c : fetch_word Asan.M.loaded_segments (0xb90a0 : word) = Some W_b8f1c.
Proof. vm_refl. Qed.
Lemma D_b8f1c : decode_any W_b8f1c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f20 : bv 32 := 0x01068713.
Lemma F_b8f20 : fetch_word Asan.M.loaded_segments (0xb90a4 : word) = Some W_b8f20.
Proof. vm_refl. Qed.
Lemma D_b8f20 : decode_any W_b8f20 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f24 : bv 32 := 0x00568623.
Lemma F_b8f24 : fetch_word Asan.M.loaded_segments (0xb90a8 : word) = Some W_b8f24.
Proof. vm_refl. Qed.
Lemma D_b8f24 : decode_any W_b8f24 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f28 : bv 32 := 0x006686a3.
Lemma F_b8f28 : fetch_word Asan.M.loaded_segments (0xb90ac : word) = Some W_b8f28.
Proof. vm_refl. Qed.
Lemma D_b8f28 : decode_any W_b8f28 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f2c : bv 32 := 0x00768723.
Lemma F_b8f2c : fetch_word Asan.M.loaded_segments (0xb90b0 : word) = Some W_b8f2c.
Proof. vm_refl. Qed.
Lemma D_b8f2c : decode_any W_b8f2c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f30 : bv 32 := 0x01c687a3.
Lemma F_b8f30 : fetch_word Asan.M.loaded_segments (0xb90b4 : word) = Some W_b8f30.
Proof. vm_refl. Qed.
Lemma D_b8f30 : decode_any W_b8f30 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f34 : bv 32 := 0x00070693.
Lemma F_b8f34 : fetch_word Asan.M.loaded_segments (0xb90b8 : word) = Some W_b8f34.
Proof. vm_refl. Qed.
Lemma D_b8f34 : decode_any W_b8f34 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f38 : bv 32 := 0x00867713.
Lemma F_b8f38 : fetch_word Asan.M.loaded_segments (0xb90bc : word) = Some W_b8f38.
Proof. vm_refl. Qed.
Lemma D_b8f38 : decode_any W_b8f38 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f3c : bv 32 := 0xd20706e3.
Lemma F_b8f3c : fetch_word Asan.M.loaded_segments (0xb90c0 : word) = Some W_b8f3c.
Proof. vm_refl. Qed.
Lemma D_b8f3c : decode_any W_b8f3c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f40 : bv 32 := 0x0005c703.
Lemma F_b8f40 : fetch_word Asan.M.loaded_segments (0xb90c4 : word) = Some W_b8f40.
Proof. vm_refl. Qed.
Lemma D_b8f40 : decode_any W_b8f40 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f44 : bv 32 := 0x0015c783.
Lemma F_b8f44 : fetch_word Asan.M.loaded_segments (0xb90c8 : word) = Some W_b8f44.
Proof. vm_refl. Qed.
Lemma D_b8f44 : decode_any W_b8f44 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f48 : bv 32 := 0x0025c803.
Lemma F_b8f48 : fetch_word Asan.M.loaded_segments (0xb90cc : word) = Some W_b8f48.
Proof. vm_refl. Qed.
Lemma D_b8f48 : decode_any W_b8f48 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f4c : bv 32 := 0x0035c883.
Lemma F_b8f4c : fetch_word Asan.M.loaded_segments (0xb90d0 : word) = Some W_b8f4c.
Proof. vm_refl. Qed.
Lemma D_b8f4c : decode_any W_b8f4c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f50 : bv 32 := 0x0045c283.
Lemma F_b8f50 : fetch_word Asan.M.loaded_segments (0xb90d4 : word) = Some W_b8f50.
Proof. vm_refl. Qed.
Lemma D_b8f50 : decode_any W_b8f50 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f54 : bv 32 := 0x0055c303.
Lemma F_b8f54 : fetch_word Asan.M.loaded_segments (0xb90d8 : word) = Some W_b8f54.
Proof. vm_refl. Qed.
Lemma D_b8f54 : decode_any W_b8f54 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f58 : bv 32 := 0x0065c383.
Lemma F_b8f58 : fetch_word Asan.M.loaded_segments (0xb90dc : word) = Some W_b8f58.
Proof. vm_refl. Qed.
Lemma D_b8f58 : decode_any W_b8f58 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f5c : bv 32 := 0x0075ce03.
Lemma F_b8f5c : fetch_word Asan.M.loaded_segments (0xb90e0 : word) = Some W_b8f5c.
Proof. vm_refl. Qed.
Lemma D_b8f5c : decode_any W_b8f5c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f60 : bv 32 := 0x00858593.
Lemma F_b8f60 : fetch_word Asan.M.loaded_segments (0xb90e4 : word) = Some W_b8f60.
Proof. vm_refl. Qed.
Lemma D_b8f60 : decode_any W_b8f60 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f64 : bv 32 := 0x00e68023.
Lemma F_b8f64 : fetch_word Asan.M.loaded_segments (0xb90e8 : word) = Some W_b8f64.
Proof. vm_refl. Qed.
Lemma D_b8f64 : decode_any W_b8f64 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f68 : bv 32 := 0x00f680a3.
Lemma F_b8f68 : fetch_word Asan.M.loaded_segments (0xb90ec : word) = Some W_b8f68.
Proof. vm_refl. Qed.
Lemma D_b8f68 : decode_any W_b8f68 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f6c : bv 32 := 0x01068123.
Lemma F_b8f6c : fetch_word Asan.M.loaded_segments (0xb90f0 : word) = Some W_b8f6c.
Proof. vm_refl. Qed.
Lemma D_b8f6c : decode_any W_b8f6c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f70 : bv 32 := 0x011681a3.
Lemma F_b8f70 : fetch_word Asan.M.loaded_segments (0xb90f4 : word) = Some W_b8f70.
Proof. vm_refl. Qed.
Lemma D_b8f70 : decode_any W_b8f70 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f74 : bv 32 := 0x00868713.
Lemma F_b8f74 : fetch_word Asan.M.loaded_segments (0xb90f8 : word) = Some W_b8f74.
Proof. vm_refl. Qed.
Lemma D_b8f74 : decode_any W_b8f74 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f78 : bv 32 := 0x00568223.
Lemma F_b8f78 : fetch_word Asan.M.loaded_segments (0xb90fc : word) = Some W_b8f78.
Proof. vm_refl. Qed.
Lemma D_b8f78 : decode_any W_b8f78 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f7c : bv 32 := 0x006682a3.
Lemma F_b8f7c : fetch_word Asan.M.loaded_segments (0xb9100 : word) = Some W_b8f7c.
Proof. vm_refl. Qed.
Lemma D_b8f7c : decode_any W_b8f7c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f80 : bv 32 := 0x00768323.
Lemma F_b8f80 : fetch_word Asan.M.loaded_segments (0xb9104 : word) = Some W_b8f80.
Proof. vm_refl. Qed.
Lemma D_b8f80 : decode_any W_b8f80 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f84 : bv 32 := 0x01c683a3.
Lemma F_b8f84 : fetch_word Asan.M.loaded_segments (0xb9108 : word) = Some W_b8f84.
Proof. vm_refl. Qed.
Lemma D_b8f84 : decode_any W_b8f84 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f88 : bv 32 := 0x00070693.
Lemma F_b8f88 : fetch_word Asan.M.loaded_segments (0xb910c : word) = Some W_b8f88.
Proof. vm_refl. Qed.
Lemma D_b8f88 : decode_any W_b8f88 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f8c : bv 32 := 0x00467713.
Lemma F_b8f8c : fetch_word Asan.M.loaded_segments (0xb9110 : word) = Some W_b8f8c.
Proof. vm_refl. Qed.
Lemma D_b8f8c : decode_any W_b8f8c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f90 : bv 32 := 0x02070863.
Lemma F_b8f90 : fetch_word Asan.M.loaded_segments (0xb9114 : word) = Some W_b8f90.
Proof. vm_refl. Qed.
Lemma D_b8f90 : decode_any W_b8f90 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f94 : bv 32 := 0x0005c703.
Lemma F_b8f94 : fetch_word Asan.M.loaded_segments (0xb9118 : word) = Some W_b8f94.
Proof. vm_refl. Qed.
Lemma D_b8f94 : decode_any W_b8f94 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f98 : bv 32 := 0x0015c783.
Lemma F_b8f98 : fetch_word Asan.M.loaded_segments (0xb911c : word) = Some W_b8f98.
Proof. vm_refl. Qed.
Lemma D_b8f98 : decode_any W_b8f98 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8f9c : bv 32 := 0x0025c803.
Lemma F_b8f9c : fetch_word Asan.M.loaded_segments (0xb9120 : word) = Some W_b8f9c.
Proof. vm_refl. Qed.
Lemma D_b8f9c : decode_any W_b8f9c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fa0 : bv 32 := 0x0035c883.
Lemma F_b8fa0 : fetch_word Asan.M.loaded_segments (0xb9124 : word) = Some W_b8fa0.
Proof. vm_refl. Qed.
Lemma D_b8fa0 : decode_any W_b8fa0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fa4 : bv 32 := 0x00458593.
Lemma F_b8fa4 : fetch_word Asan.M.loaded_segments (0xb9128 : word) = Some W_b8fa4.
Proof. vm_refl. Qed.
Lemma D_b8fa4 : decode_any W_b8fa4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fa8 : bv 32 := 0x00468293.
Lemma F_b8fa8 : fetch_word Asan.M.loaded_segments (0xb912c : word) = Some W_b8fa8.
Proof. vm_refl. Qed.
Lemma D_b8fa8 : decode_any W_b8fa8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fac : bv 32 := 0x00e68023.
Lemma F_b8fac : fetch_word Asan.M.loaded_segments (0xb9130 : word) = Some W_b8fac.
Proof. vm_refl. Qed.
Lemma D_b8fac : decode_any W_b8fac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fb0 : bv 32 := 0x00f680a3.
Lemma F_b8fb0 : fetch_word Asan.M.loaded_segments (0xb9134 : word) = Some W_b8fb0.
Proof. vm_refl. Qed.
Lemma D_b8fb0 : decode_any W_b8fb0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fb4 : bv 32 := 0x01068123.
Lemma F_b8fb4 : fetch_word Asan.M.loaded_segments (0xb9138 : word) = Some W_b8fb4.
Proof. vm_refl. Qed.
Lemma D_b8fb4 : decode_any W_b8fb4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fb8 : bv 32 := 0x011681a3.
Lemma F_b8fb8 : fetch_word Asan.M.loaded_segments (0xb913c : word) = Some W_b8fb8.
Proof. vm_refl. Qed.
Lemma D_b8fb8 : decode_any W_b8fb8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fbc : bv 32 := 0x00028693.
Lemma F_b8fbc : fetch_word Asan.M.loaded_segments (0xb9140 : word) = Some W_b8fbc.
Proof. vm_refl. Qed.
Lemma D_b8fbc : decode_any W_b8fbc = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fc0 : bv 32 := 0x00267713.
Lemma F_b8fc0 : fetch_word Asan.M.loaded_segments (0xb9144 : word) = Some W_b8fc0.
Proof. vm_refl. Qed.
Lemma D_b8fc0 : decode_any W_b8fc0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fc4 : bv 32 := 0x00071863.
Lemma F_b8fc4 : fetch_word Asan.M.loaded_segments (0xb9148 : word) = Some W_b8fc4.
Proof. vm_refl. Qed.
Lemma D_b8fc4 : decode_any W_b8fc4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fc8 : bv 32 := 0x00167613.
Lemma F_b8fc8 : fetch_word Asan.M.loaded_segments (0xb914c : word) = Some W_b8fc8.
Proof. vm_refl. Qed.
Lemma D_b8fc8 : decode_any W_b8fc8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fcc : bv 32 := 0x02061663.
Lemma F_b8fcc : fetch_word Asan.M.loaded_segments (0xb9150 : word) = Some W_b8fcc.
Proof. vm_refl. Qed.
Lemma D_b8fcc : decode_any W_b8fcc = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fd0 : bv 32 := 0x00008067.
Lemma F_b8fd0 : fetch_word Asan.M.loaded_segments (0xb9154 : word) = Some W_b8fd0.
Proof. vm_refl. Qed.
Lemma D_b8fd0 : decode_any W_b8fd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fd4 : bv 32 := 0x0005c703.
Lemma F_b8fd4 : fetch_word Asan.M.loaded_segments (0xb9158 : word) = Some W_b8fd4.
Proof. vm_refl. Qed.
Lemma D_b8fd4 : decode_any W_b8fd4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fd8 : bv 32 := 0x0015c783.
Lemma F_b8fd8 : fetch_word Asan.M.loaded_segments (0xb915c : word) = Some W_b8fd8.
Proof. vm_refl. Qed.
Lemma D_b8fd8 : decode_any W_b8fd8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fdc : bv 32 := 0x00258593.
Lemma F_b8fdc : fetch_word Asan.M.loaded_segments (0xb9160 : word) = Some W_b8fdc.
Proof. vm_refl. Qed.
Lemma D_b8fdc : decode_any W_b8fdc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fe0 : bv 32 := 0x00268813.
Lemma F_b8fe0 : fetch_word Asan.M.loaded_segments (0xb9164 : word) = Some W_b8fe0.
Proof. vm_refl. Qed.
Lemma D_b8fe0 : decode_any W_b8fe0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fe4 : bv 32 := 0x00e68023.
Lemma F_b8fe4 : fetch_word Asan.M.loaded_segments (0xb9168 : word) = Some W_b8fe4.
Proof. vm_refl. Qed.
Lemma D_b8fe4 : decode_any W_b8fe4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fe8 : bv 32 := 0x00f680a3.
Lemma F_b8fe8 : fetch_word Asan.M.loaded_segments (0xb916c : word) = Some W_b8fe8.
Proof. vm_refl. Qed.
Lemma D_b8fe8 : decode_any W_b8fe8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8fec : bv 32 := 0x00080693.
Lemma F_b8fec : fetch_word Asan.M.loaded_segments (0xb9170 : word) = Some W_b8fec.
Proof. vm_refl. Qed.
Lemma D_b8fec : decode_any W_b8fec = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ff0 : bv 32 := 0x00167613.
Lemma F_b8ff0 : fetch_word Asan.M.loaded_segments (0xb9174 : word) = Some W_b8ff0.
Proof. vm_refl. Qed.
Lemma D_b8ff0 : decode_any W_b8ff0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ff4 : bv 32 := 0xfc060ee3.
Lemma F_b8ff4 : fetch_word Asan.M.loaded_segments (0xb9178 : word) = Some W_b8ff4.
Proof. vm_refl. Qed.
Lemma D_b8ff4 : decode_any W_b8ff4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ff8 : bv 32 := 0x0005c583.
Lemma F_b8ff8 : fetch_word Asan.M.loaded_segments (0xb917c : word) = Some W_b8ff8.
Proof. vm_refl. Qed.
Lemma D_b8ff8 : decode_any W_b8ff8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8ffc : bv 32 := 0x00b68023.
Lemma F_b8ffc : fetch_word Asan.M.loaded_segments (0xb9180 : word) = Some W_b8ffc.
Proof. vm_refl. Qed.
Lemma D_b8ffc : decode_any W_b8ffc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9000 : bv 32 := 0x00008067.
Lemma F_b9000 : fetch_word Asan.M.loaded_segments (0xb9184 : word) = Some W_b9000.
Proof. vm_refl. Qed.
Lemma D_b9000 : decode_any W_b9000 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
