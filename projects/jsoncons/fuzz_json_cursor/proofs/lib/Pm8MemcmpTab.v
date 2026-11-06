(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_144dc0 : bv 32 := 0xf5c2506f.
Lemma Fx_144dc0 : fetch_word Asan.M.loaded_segments (0x144e04 : word) = Some Wx_144dc0.
Proof. vm_refl. Qed.
Lemma Dx_144dc0 : decode_any Wx_144dc0 = Some (Jal 0 1202012, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144e90 : bv 32 := 0x02060063.
Lemma Fx_144e90 : fetch_word Asan.M.loaded_segments (0x144ed4 : word) = Some Wx_144e90.
Proof. vm_refl. Qed.
Lemma Dx_144e90 : decode_any Wx_144e90 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144e94 : bv 32 := 0x00054683.
Lemma Fx_144e94 : fetch_word Asan.M.loaded_segments (0x144ed8 : word) = Some Wx_144e94.
Proof. vm_refl. Qed.
Lemma Dx_144e94 : decode_any Wx_144e94 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144e98 : bv 32 := 0x0005c703.
Lemma Fx_144e98 : fetch_word Asan.M.loaded_segments (0x144edc : word) = Some Wx_144e98.
Proof. vm_refl. Qed.
Lemma Dx_144e98 : decode_any Wx_144e98 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144e9c : bv 32 := 0x00e69e63.
Lemma Fx_144e9c : fetch_word Asan.M.loaded_segments (0x144ee0 : word) = Some Wx_144e9c.
Proof. vm_refl. Qed.
Lemma Dx_144e9c : decode_any Wx_144e9c = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144ea0 : bv 32 := 0xfff60613.
Lemma Fx_144ea0 : fetch_word Asan.M.loaded_segments (0x144ee4 : word) = Some Wx_144ea0.
Proof. vm_refl. Qed.
Lemma Dx_144ea0 : decode_any Wx_144ea0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144ea4 : bv 32 := 0x00150513.
Lemma Fx_144ea4 : fetch_word Asan.M.loaded_segments (0x144ee8 : word) = Some Wx_144ea4.
Proof. vm_refl. Qed.
Lemma Dx_144ea4 : decode_any Wx_144ea4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144ea8 : bv 32 := 0x00158593.
Lemma Fx_144ea8 : fetch_word Asan.M.loaded_segments (0x144eec : word) = Some Wx_144ea8.
Proof. vm_refl. Qed.
Lemma Dx_144ea8 : decode_any Wx_144ea8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144eac : bv 32 := 0xfe0614e3.
Lemma Fx_144eac : fetch_word Asan.M.loaded_segments (0x144ef0 : word) = Some Wx_144eac.
Proof. vm_refl. Qed.
Lemma Dx_144eac : decode_any Wx_144eac = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144eb0 : bv 32 := 0x00000513.
Lemma Fx_144eb0 : fetch_word Asan.M.loaded_segments (0x144ef4 : word) = Some Wx_144eb0.
Proof. vm_refl. Qed.
Lemma Dx_144eb0 : decode_any Wx_144eb0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144eb4 : bv 32 := 0x00008067.
Lemma Fx_144eb4 : fetch_word Asan.M.loaded_segments (0x144ef8 : word) = Some Wx_144eb4.
Proof. vm_refl. Qed.
Lemma Dx_144eb4 : decode_any Wx_144eb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144eb8 : bv 32 := 0x40e68533.
Lemma Fx_144eb8 : fetch_word Asan.M.loaded_segments (0x144efc : word) = Some Wx_144eb8.
Proof. vm_refl. Qed.
Lemma Dx_144eb8 : decode_any Wx_144eb8 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_144ebc : bv 32 := 0x00008067.
Lemma Fx_144ebc : fetch_word Asan.M.loaded_segments (0x144f00 : word) = Some Wx_144ebc.
Proof. vm_refl. Qed.
Lemma Dx_144ebc : decode_any Wx_144ebc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a510 : bv 32 := 0x32d0106f.
Lemma Fx_6a510 : fetch_word Asan.M.loaded_segments (0x6a560 : word) = Some Wx_6a510.
Proof. vm_refl. Qed.
Lemma Dx_6a510 : decode_any Wx_6a510 = Some (Jal 0 6956, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a514 : bv 32 := 0x3e50106f.
Lemma Fx_6a514 : fetch_word Asan.M.loaded_segments (0x6a564 : word) = Some Wx_6a514.
Proof. vm_refl. Qed.
Lemma Dx_6a514 : decode_any Wx_6a514 = Some (Jal 0 7140, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7a4 : bv 32 := 0x00008067.
Lemma Fx_6b7a4 : fetch_word Asan.M.loaded_segments (0x6b7f4 : word) = Some Wx_6b7a4.
Proof. vm_refl. Qed.
Lemma Dx_6b7a4 : decode_any Wx_6b7a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7a8 : bv 32 := 0x81010113.
Lemma Fx_6b7a8 : fetch_word Asan.M.loaded_segments (0x6b7f8 : word) = Some Wx_6b7a8.
Proof. vm_refl. Qed.
Lemma Dx_6b7a8 : decode_any Wx_6b7a8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7ac : bv 32 := 0x7e113423.
Lemma Fx_6b7ac : fetch_word Asan.M.loaded_segments (0x6b7fc : word) = Some Wx_6b7ac.
Proof. vm_refl. Qed.
Lemma Dx_6b7ac : decode_any Wx_6b7ac = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7b0 : bv 32 := 0x7e813023.
Lemma Fx_6b7b0 : fetch_word Asan.M.loaded_segments (0x6b800 : word) = Some Wx_6b7b0.
Proof. vm_refl. Qed.
Lemma Dx_6b7b0 : decode_any Wx_6b7b0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7b4 : bv 32 := 0x7c913c23.
Lemma Fx_6b7b4 : fetch_word Asan.M.loaded_segments (0x6b804 : word) = Some Wx_6b7b4.
Proof. vm_refl. Qed.
Lemma Dx_6b7b4 : decode_any Wx_6b7b4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7b8 : bv 32 := 0x7d213823.
Lemma Fx_6b7b8 : fetch_word Asan.M.loaded_segments (0x6b808 : word) = Some Wx_6b7b8.
Proof. vm_refl. Qed.
Lemma Dx_6b7b8 : decode_any Wx_6b7b8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7bc : bv 32 := 0x7d313423.
Lemma Fx_6b7bc : fetch_word Asan.M.loaded_segments (0x6b80c : word) = Some Wx_6b7bc.
Proof. vm_refl. Qed.
Lemma Dx_6b7bc : decode_any Wx_6b7bc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7c0 : bv 32 := 0x7d413023.
Lemma Fx_6b7c0 : fetch_word Asan.M.loaded_segments (0x6b810 : word) = Some Wx_6b7c0.
Proof. vm_refl. Qed.
Lemma Dx_6b7c0 : decode_any Wx_6b7c0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7c4 : bv 32 := 0x7b513c23.
Lemma Fx_6b7c4 : fetch_word Asan.M.loaded_segments (0x6b814 : word) = Some Wx_6b7c4.
Proof. vm_refl. Qed.
Lemma Dx_6b7c4 : decode_any Wx_6b7c4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7c8 : bv 32 := 0x7b613823.
Lemma Fx_6b7c8 : fetch_word Asan.M.loaded_segments (0x6b818 : word) = Some Wx_6b7c8.
Proof. vm_refl. Qed.
Lemma Dx_6b7c8 : decode_any Wx_6b7c8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7cc : bv 32 := 0x7b713423.
Lemma Fx_6b7cc : fetch_word Asan.M.loaded_segments (0x6b81c : word) = Some Wx_6b7cc.
Proof. vm_refl. Qed.
Lemma Dx_6b7cc : decode_any Wx_6b7cc = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7d0 : bv 32 := 0x7b813023.
Lemma Fx_6b7d0 : fetch_word Asan.M.loaded_segments (0x6b820 : word) = Some Wx_6b7d0.
Proof. vm_refl. Qed.
Lemma Dx_6b7d0 : decode_any Wx_6b7d0 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7d4 : bv 32 := 0x79913c23.
Lemma Fx_6b7d4 : fetch_word Asan.M.loaded_segments (0x6b824 : word) = Some Wx_6b7d4.
Proof. vm_refl. Qed.
Lemma Dx_6b7d4 : decode_any Wx_6b7d4 = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7d8 : bv 32 := 0x79a13823.
Lemma Fx_6b7d8 : fetch_word Asan.M.loaded_segments (0x6b828 : word) = Some Wx_6b7d8.
Proof. vm_refl. Qed.
Lemma Dx_6b7d8 : decode_any Wx_6b7d8 = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7dc : bv 32 := 0x79b13423.
Lemma Fx_6b7dc : fetch_word Asan.M.loaded_segments (0x6b82c : word) = Some Wx_6b7dc.
Proof. vm_refl. Qed.
Lemma Dx_6b7dc : decode_any Wx_6b7dc = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7e0 : bv 32 := 0x7f010413.
Lemma Fx_6b7e0 : fetch_word Asan.M.loaded_segments (0x6b830 : word) = Some Wx_6b7e0.
Proof. vm_refl. Qed.
Lemma Dx_6b7e0 : decode_any Wx_6b7e0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7e4 : bv 32 := 0xf6010113.
Lemma Fx_6b7e4 : fetch_word Asan.M.loaded_segments (0x6b834 : word) = Some Wx_6b7e4.
Proof. vm_refl. Qed.
Lemma Dx_6b7e4 : decode_any Wx_6b7e4 = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7e8 : bv 32 := 0x00008993.
Lemma Fx_6b7e8 : fetch_word Asan.M.loaded_segments (0x6b838 : word) = Some Wx_6b7e8.
Proof. vm_refl. Qed.
Lemma Dx_6b7e8 : decode_any Wx_6b7e8 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7ec : bv 32 := 0x00070493.
Lemma Fx_6b7ec : fetch_word Asan.M.loaded_segments (0x6b83c : word) = Some Wx_6b7ec.
Proof. vm_refl. Qed.
Lemma Dx_6b7ec : decode_any Wx_6b7ec = Some (OpImm ALU_ADD 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7f0 : bv 32 := 0x00068913.
Lemma Fx_6b7f0 : fetch_word Asan.M.loaded_segments (0x6b840 : word) = Some Wx_6b7f0.
Proof. vm_refl. Qed.
Lemma Dx_6b7f0 : decode_any Wx_6b7f0 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7f4 : bv 32 := 0x00060a13.
Lemma Fx_6b7f4 : fetch_word Asan.M.loaded_segments (0x6b844 : word) = Some Wx_6b7f4.
Proof. vm_refl. Qed.
Lemma Dx_6b7f4 : decode_any Wx_6b7f4 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7f8 : bv 32 := 0x00058a93.
Lemma Fx_6b7f8 : fetch_word Asan.M.loaded_segments (0x6b848 : word) = Some Wx_6b7f8.
Proof. vm_refl. Qed.
Lemma Dx_6b7f8 : decode_any Wx_6b7f8 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b7fc : bv 32 := 0x000e8597.
Lemma Fx_6b7fc : fetch_word Asan.M.loaded_segments (0x6b84c : word) = Some Wx_6b7fc.
Proof. vm_refl. Qed.
Lemma Dx_6b7fc : decode_any Wx_6b7fc = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b800 : bv 32 := 0x8dc5bc03.
Lemma Fx_6b800 : fetch_word Asan.M.loaded_segments (0x6b850 : word) = Some Wx_6b800.
Proof. vm_refl. Qed.
Lemma Dx_6b800 : decode_any Wx_6b800 = Some (Load SZ8 true 24 11 2268, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b804 : bv 32 := 0x0fec4583.
Lemma Fx_6b804 : fetch_word Asan.M.loaded_segments (0x6b854 : word) = Some Wx_6b804.
Proof. vm_refl. Qed.
Lemma Dx_6b804 : decode_any Wx_6b804 = Some (Load SZ1 false 11 24 254, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b808 : bv 32 := 0x0a058863.
Lemma Fx_6b808 : fetch_word Asan.M.loaded_segments (0x6b858 : word) = Some Wx_6b808.
Proof. vm_refl. Qed.
Lemma Dx_6b808 : decode_any Wx_6b808 = Some (Branch BC_EQ 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b80c : bv 32 := 0x0ffc4583.
Lemma Fx_6b80c : fetch_word Asan.M.loaded_segments (0x6b85c : word) = Some Wx_6b80c.
Proof. vm_refl. Qed.
Lemma Dx_6b80c : decode_any Wx_6b80c = Some (Load SZ1 false 11 24 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b810 : bv 32 := 0x80040b93.
Lemma Fx_6b810 : fetch_word Asan.M.loaded_segments (0x6b860 : word) = Some Wx_6b810.
Proof. vm_refl. Qed.
Lemma Dx_6b810 : decode_any Wx_6b810 = Some (OpImm ALU_ADD 23 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b814 : bv 32 := 0xf80b8b93.
Lemma Fx_6b814 : fetch_word Asan.M.loaded_segments (0x6b864 : word) = Some Wx_6b814.
Proof. vm_refl. Qed.
Lemma Dx_6b814 : decode_any Wx_6b814 = Some (OpImm ALU_ADD 23 23 3968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b818 : bv 32 := 0x0a058c63.
Lemma Fx_6b818 : fetch_word Asan.M.loaded_segments (0x6b868 : word) = Some Wx_6b818.
Proof. vm_refl. Qed.
Lemma Dx_6b818 : decode_any Wx_6b818 = Some (Branch BC_EQ 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b81c : bv 32 := 0xfffa4593.
Lemma Fx_6b81c : fetch_word Asan.M.loaded_segments (0x6b86c : word) = Some Wx_6b81c.
Proof. vm_refl. Qed.
Lemma Dx_6b81c : decode_any Wx_6b81c = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b820 : bv 32 := 0x2095e063.
Lemma Fx_6b820 : fetch_word Asan.M.loaded_segments (0x6b870 : word) = Some Wx_6b820.
Proof. vm_refl. Qed.
Lemma Dx_6b820 : decode_any Wx_6b820 = Some (Branch BC_LTU 11 9 512, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b824 : bv 32 := 0xfbf48c93.
Lemma Fx_6b824 : fetch_word Asan.M.loaded_segments (0x6b874 : word) = Some Wx_6b824.
Proof. vm_refl. Qed.
Lemma Dx_6b824 : decode_any Wx_6b824 = Some (OpImm ALU_ADD 25 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b828 : bv 32 := 0xfbf00593.
Lemma Fx_6b828 : fetch_word Asan.M.loaded_segments (0x6b878 : word) = Some Wx_6b828.
Proof. vm_refl. Qed.
Lemma Dx_6b828 : decode_any Wx_6b828 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b82c : bv 32 := 0x2795f263.
Lemma Fx_6b82c : fetch_word Asan.M.loaded_segments (0x6b87c : word) = Some Wx_6b82c.
Proof. vm_refl. Qed.
Lemma Dx_6b82c : decode_any Wx_6b82c = Some (Branch BC_GEU 11 25 612, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b830 : bv 32 := 0x000e8597.
Lemma Fx_6b830 : fetch_word Asan.M.loaded_segments (0x6b880 : word) = Some Wx_6b830.
Proof. vm_refl. Qed.
Lemma Dx_6b830 : decode_any Wx_6b830 = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b834 : bv 32 := 0x8b85b583.
Lemma Fx_6b834 : fetch_word Asan.M.loaded_segments (0x6b884 : word) = Some Wx_6b834.
Proof. vm_refl. Qed.
Lemma Dx_6b834 : decode_any Wx_6b834 = Some (Load SZ8 true 11 11 2232, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b838 : bv 32 := 0x009a06b3.
Lemma Fx_6b838 : fetch_word Asan.M.loaded_segments (0x6b888 : word) = Some Wx_6b838.
Proof. vm_refl. Qed.
Lemma Dx_6b838 : decode_any Wx_6b838 = Some (Op ALU_ADD 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b83c : bv 32 := 0x0005b603.
Lemma Fx_6b83c : fetch_word Asan.M.loaded_segments (0x6b88c : word) = Some Wx_6b83c.
Proof. vm_refl. Qed.
Lemma Dx_6b83c : decode_any Wx_6b83c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b840 : bv 32 := 0x003a5593.
Lemma Fx_6b840 : fetch_word Asan.M.loaded_segments (0x6b890 : word) = Some Wx_6b840.
Proof. vm_refl. Qed.
Lemma Dx_6b840 : decode_any Wx_6b840 = Some (ShiftImm ALU_SRL 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b844 : bv 32 := 0xfff68693.
Lemma Fx_6b844 : fetch_word Asan.M.loaded_segments (0x6b894 : word) = Some Wx_6b844.
Proof. vm_refl. Qed.
Lemma Dx_6b844 : decode_any Wx_6b844 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b848 : bv 32 := 0x0036d713.
Lemma Fx_6b848 : fetch_word Asan.M.loaded_segments (0x6b898 : word) = Some Wx_6b848.
Proof. vm_refl. Qed.
Lemma Dx_6b848 : decode_any Wx_6b848 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b84c : bv 32 := 0x00b605b3.
Lemma Fx_6b84c : fetch_word Asan.M.loaded_segments (0x6b89c : word) = Some Wx_6b84c.
Proof. vm_refl. Qed.
Lemma Dx_6b84c : decode_any Wx_6b84c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b850 : bv 32 := 0x00e60633.
Lemma Fx_6b850 : fetch_word Asan.M.loaded_segments (0x6b8a0 : word) = Some Wx_6b850.
Proof. vm_refl. Qed.
Lemma Dx_6b850 : decode_any Wx_6b850 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b854 : bv 32 := 0xff85f713.
Lemma Fx_6b854 : fetch_word Asan.M.loaded_segments (0x6b8a4 : word) = Some Wx_6b854.
Proof. vm_refl. Qed.
Lemma Dx_6b854 : decode_any Wx_6b854 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b858 : bv 32 := 0xff867793.
Lemma Fx_6b858 : fetch_word Asan.M.loaded_segments (0x6b8a8 : word) = Some Wx_6b858.
Proof. vm_refl. Qed.
Lemma Dx_6b858 : decode_any Wx_6b858 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b85c : bv 32 := 0x00073703.
Lemma Fx_6b85c : fetch_word Asan.M.loaded_segments (0x6b8ac : word) = Some Wx_6b85c.
Proof. vm_refl. Qed.
Lemma Dx_6b85c : decode_any Wx_6b85c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b860 : bv 32 := 0x0007b783.
Lemma Fx_6b860 : fetch_word Asan.M.loaded_segments (0x6b8b0 : word) = Some Wx_6b860.
Proof. vm_refl. Qed.
Lemma Dx_6b860 : decode_any Wx_6b860 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b864 : bv 32 := 0x00e7e733.
Lemma Fx_6b864 : fetch_word Asan.M.loaded_segments (0x6b8b4 : word) = Some Wx_6b864.
Proof. vm_refl. Qed.
Lemma Dx_6b864 : decode_any Wx_6b864 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b868 : bv 32 := 0x3a071063.
Lemma Fx_6b868 : fetch_word Asan.M.loaded_segments (0x6b8b8 : word) = Some Wx_6b868.
Proof. vm_refl. Qed.
Lemma Dx_6b868 : decode_any Wx_6b868 = Some (Branch BC_NE 14 0 928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b86c : bv 32 := 0xfff94593.
Lemma Fx_6b86c : fetch_word Asan.M.loaded_segments (0x6b8bc : word) = Some Wx_6b86c.
Proof. vm_refl. Qed.
Lemma Dx_6b86c : decode_any Wx_6b86c = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b870 : bv 32 := 0x2295e463.
Lemma Fx_6b870 : fetch_word Asan.M.loaded_segments (0x6b8c0 : word) = Some Wx_6b870.
Proof. vm_refl. Qed.
Lemma Dx_6b870 : decode_any Wx_6b870 = Some (Branch BC_LTU 11 9 552, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b874 : bv 32 := 0xfbf00593.
Lemma Fx_6b874 : fetch_word Asan.M.loaded_segments (0x6b8c4 : word) = Some Wx_6b874.
Proof. vm_refl. Qed.
Lemma Dx_6b874 : decode_any Wx_6b874 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b878 : bv 32 := 0x2995f663.
Lemma Fx_6b878 : fetch_word Asan.M.loaded_segments (0x6b8c8 : word) = Some Wx_6b878.
Proof. vm_refl. Qed.
Lemma Dx_6b878 : decode_any Wx_6b878 = Some (Branch BC_GEU 11 25 652, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b87c : bv 32 := 0x000e8597.
Lemma Fx_6b87c : fetch_word Asan.M.loaded_segments (0x6b8cc : word) = Some Wx_6b87c.
Proof. vm_refl. Qed.
Lemma Dx_6b87c : decode_any Wx_6b87c = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b880 : bv 32 := 0x86c5b583.
Lemma Fx_6b880 : fetch_word Asan.M.loaded_segments (0x6b8d0 : word) = Some Wx_6b880.
Proof. vm_refl. Qed.
Lemma Dx_6b880 : decode_any Wx_6b880 = Some (Load SZ8 true 11 11 2156, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b884 : bv 32 := 0x009906b3.
Lemma Fx_6b884 : fetch_word Asan.M.loaded_segments (0x6b8d4 : word) = Some Wx_6b884.
Proof. vm_refl. Qed.
Lemma Dx_6b884 : decode_any Wx_6b884 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b888 : bv 32 := 0x0005b603.
Lemma Fx_6b888 : fetch_word Asan.M.loaded_segments (0x6b8d8 : word) = Some Wx_6b888.
Proof. vm_refl. Qed.
Lemma Dx_6b888 : decode_any Wx_6b888 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b88c : bv 32 := 0x00395593.
Lemma Fx_6b88c : fetch_word Asan.M.loaded_segments (0x6b8dc : word) = Some Wx_6b88c.
Proof. vm_refl. Qed.
Lemma Dx_6b88c : decode_any Wx_6b88c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b890 : bv 32 := 0xfff68693.
Lemma Fx_6b890 : fetch_word Asan.M.loaded_segments (0x6b8e0 : word) = Some Wx_6b890.
Proof. vm_refl. Qed.
Lemma Dx_6b890 : decode_any Wx_6b890 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b894 : bv 32 := 0x0036d713.
Lemma Fx_6b894 : fetch_word Asan.M.loaded_segments (0x6b8e4 : word) = Some Wx_6b894.
Proof. vm_refl. Qed.
Lemma Dx_6b894 : decode_any Wx_6b894 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b898 : bv 32 := 0x00b605b3.
Lemma Fx_6b898 : fetch_word Asan.M.loaded_segments (0x6b8e8 : word) = Some Wx_6b898.
Proof. vm_refl. Qed.
Lemma Dx_6b898 : decode_any Wx_6b898 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b89c : bv 32 := 0x00e60633.
Lemma Fx_6b89c : fetch_word Asan.M.loaded_segments (0x6b8ec : word) = Some Wx_6b89c.
Proof. vm_refl. Qed.
Lemma Dx_6b89c : decode_any Wx_6b89c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8a0 : bv 32 := 0xff85f713.
Lemma Fx_6b8a0 : fetch_word Asan.M.loaded_segments (0x6b8f0 : word) = Some Wx_6b8a0.
Proof. vm_refl. Qed.
Lemma Dx_6b8a0 : decode_any Wx_6b8a0 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8a4 : bv 32 := 0xff867793.
Lemma Fx_6b8a4 : fetch_word Asan.M.loaded_segments (0x6b8f4 : word) = Some Wx_6b8a4.
Proof. vm_refl. Qed.
Lemma Dx_6b8a4 : decode_any Wx_6b8a4 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8a8 : bv 32 := 0x00073703.
Lemma Fx_6b8a8 : fetch_word Asan.M.loaded_segments (0x6b8f8 : word) = Some Wx_6b8a8.
Proof. vm_refl. Qed.
Lemma Dx_6b8a8 : decode_any Wx_6b8a8 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8ac : bv 32 := 0x0007b783.
Lemma Fx_6b8ac : fetch_word Asan.M.loaded_segments (0x6b8fc : word) = Some Wx_6b8ac.
Proof. vm_refl. Qed.
Lemma Dx_6b8ac : decode_any Wx_6b8ac = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8b0 : bv 32 := 0x00e7e733.
Lemma Fx_6b8b0 : fetch_word Asan.M.loaded_segments (0x6b900 : word) = Some Wx_6b8b0.
Proof. vm_refl. Qed.
Lemma Dx_6b8b0 : decode_any Wx_6b8b0 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8b4 : bv 32 := 0x46071063.
Lemma Fx_6b8b4 : fetch_word Asan.M.loaded_segments (0x6b904 : word) = Some Wx_6b8b4.
Proof. vm_refl. Qed.
Lemma Dx_6b8b4 : decode_any Wx_6b8b4 = Some (Branch BC_NE 14 0 1120, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8b8 : bv 32 := 0x000a0513.
Lemma Fx_6b8b8 : fetch_word Asan.M.loaded_segments (0x6b908 : word) = Some Wx_6b8b8.
Proof. vm_refl. Qed.
Lemma Dx_6b8b8 : decode_any Wx_6b8b8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8bc : bv 32 := 0x00090593.
Lemma Fx_6b8bc : fetch_word Asan.M.loaded_segments (0x6b90c : word) = Some Wx_6b8bc.
Proof. vm_refl. Qed.
Lemma Dx_6b8bc : decode_any Wx_6b8bc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8c0 : bv 32 := 0x00048613.
Lemma Fx_6b8c0 : fetch_word Asan.M.loaded_segments (0x6b910 : word) = Some Wx_6b8c0.
Proof. vm_refl. Qed.
Lemma Dx_6b8c0 : decode_any Wx_6b8c0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8c4 : bv 32 := 0x000a80e7.
Lemma Fx_6b8c4 : fetch_word Asan.M.loaded_segments (0x6b914 : word) = Some Wx_6b8c4.
Proof. vm_refl. Qed.
Lemma Dx_6b8c4 : decode_any Wx_6b8c4 = Some (Jalr 1 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8c8 : bv 32 := 0x00050a93.
Lemma Fx_6b8c8 : fetch_word Asan.M.loaded_segments (0x6b918 : word) = Some Wx_6b8c8.
Proof. vm_refl. Qed.
Lemma Dx_6b8c8 : decode_any Wx_6b8c8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b8cc : bv 32 := 0x0e40006f.
Lemma Fx_6b8cc : fetch_word Asan.M.loaded_segments (0x6b91c : word) = Some Wx_6b8cc.
Proof. vm_refl. Qed.
Lemma Dx_6b8cc : decode_any Wx_6b8cc = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9b0 : bv 32 := 0x00098513.
Lemma Fx_6b9b0 : fetch_word Asan.M.loaded_segments (0x6ba00 : word) = Some Wx_6b9b0.
Proof. vm_refl. Qed.
Lemma Dx_6b9b0 : decode_any Wx_6b9b0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9b4 : bv 32 := 0x000a0593.
Lemma Fx_6b9b4 : fetch_word Asan.M.loaded_segments (0x6ba04 : word) = Some Wx_6b9b4.
Proof. vm_refl. Qed.
Lemma Dx_6b9b4 : decode_any Wx_6b9b4 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9b8 : bv 32 := 0x00090613.
Lemma Fx_6b9b8 : fetch_word Asan.M.loaded_segments (0x6ba08 : word) = Some Wx_6b9b8.
Proof. vm_refl. Qed.
Lemma Dx_6b9b8 : decode_any Wx_6b9b8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9bc : bv 32 := 0x00048693.
Lemma Fx_6b9bc : fetch_word Asan.M.loaded_segments (0x6ba0c : word) = Some Wx_6b9bc.
Proof. vm_refl. Qed.
Lemma Dx_6b9bc : decode_any Wx_6b9bc = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9c0 : bv 32 := 0x000a8713.
Lemma Fx_6b9c0 : fetch_word Asan.M.loaded_segments (0x6ba10 : word) = Some Wx_6b9c0.
Proof. vm_refl. Qed.
Lemma Dx_6b9c0 : decode_any Wx_6b9c0 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9c4 : bv 32 := 0xde1ff0ef.
Lemma Fx_6b9c4 : fetch_word Asan.M.loaded_segments (0x6ba14 : word) = Some Wx_6b9c4.
Proof. vm_refl. Qed.
Lemma Dx_6b9c4 : decode_any Wx_6b9c4 = Some (Jal 1 2096608, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9c8 : bv 32 := 0x000a8513.
Lemma Fx_6b9c8 : fetch_word Asan.M.loaded_segments (0x6ba18 : word) = Some Wx_6b9c8.
Proof. vm_refl. Qed.
Lemma Dx_6b9c8 : decode_any Wx_6b9c8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9cc : bv 32 := 0x0a010113.
Lemma Fx_6b9cc : fetch_word Asan.M.loaded_segments (0x6ba1c : word) = Some Wx_6b9cc.
Proof. vm_refl. Qed.
Lemma Dx_6b9cc : decode_any Wx_6b9cc = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9d0 : bv 32 := 0x7e813083.
Lemma Fx_6b9d0 : fetch_word Asan.M.loaded_segments (0x6ba20 : word) = Some Wx_6b9d0.
Proof. vm_refl. Qed.
Lemma Dx_6b9d0 : decode_any Wx_6b9d0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9d4 : bv 32 := 0x7e013403.
Lemma Fx_6b9d4 : fetch_word Asan.M.loaded_segments (0x6ba24 : word) = Some Wx_6b9d4.
Proof. vm_refl. Qed.
Lemma Dx_6b9d4 : decode_any Wx_6b9d4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9d8 : bv 32 := 0x7d813483.
Lemma Fx_6b9d8 : fetch_word Asan.M.loaded_segments (0x6ba28 : word) = Some Wx_6b9d8.
Proof. vm_refl. Qed.
Lemma Dx_6b9d8 : decode_any Wx_6b9d8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9dc : bv 32 := 0x7d013903.
Lemma Fx_6b9dc : fetch_word Asan.M.loaded_segments (0x6ba2c : word) = Some Wx_6b9dc.
Proof. vm_refl. Qed.
Lemma Dx_6b9dc : decode_any Wx_6b9dc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9e0 : bv 32 := 0x7c813983.
Lemma Fx_6b9e0 : fetch_word Asan.M.loaded_segments (0x6ba30 : word) = Some Wx_6b9e0.
Proof. vm_refl. Qed.
Lemma Dx_6b9e0 : decode_any Wx_6b9e0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9e4 : bv 32 := 0x7c013a03.
Lemma Fx_6b9e4 : fetch_word Asan.M.loaded_segments (0x6ba34 : word) = Some Wx_6b9e4.
Proof. vm_refl. Qed.
Lemma Dx_6b9e4 : decode_any Wx_6b9e4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9e8 : bv 32 := 0x7b813a83.
Lemma Fx_6b9e8 : fetch_word Asan.M.loaded_segments (0x6ba38 : word) = Some Wx_6b9e8.
Proof. vm_refl. Qed.
Lemma Dx_6b9e8 : decode_any Wx_6b9e8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9ec : bv 32 := 0x7b013b03.
Lemma Fx_6b9ec : fetch_word Asan.M.loaded_segments (0x6ba3c : word) = Some Wx_6b9ec.
Proof. vm_refl. Qed.
Lemma Dx_6b9ec : decode_any Wx_6b9ec = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9f0 : bv 32 := 0x7a813b83.
Lemma Fx_6b9f0 : fetch_word Asan.M.loaded_segments (0x6ba40 : word) = Some Wx_6b9f0.
Proof. vm_refl. Qed.
Lemma Dx_6b9f0 : decode_any Wx_6b9f0 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9f4 : bv 32 := 0x7a013c03.
Lemma Fx_6b9f4 : fetch_word Asan.M.loaded_segments (0x6ba44 : word) = Some Wx_6b9f4.
Proof. vm_refl. Qed.
Lemma Dx_6b9f4 : decode_any Wx_6b9f4 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9f8 : bv 32 := 0x79813c83.
Lemma Fx_6b9f8 : fetch_word Asan.M.loaded_segments (0x6ba48 : word) = Some Wx_6b9f8.
Proof. vm_refl. Qed.
Lemma Dx_6b9f8 : decode_any Wx_6b9f8 = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6b9fc : bv 32 := 0x79013d03.
Lemma Fx_6b9fc : fetch_word Asan.M.loaded_segments (0x6ba4c : word) = Some Wx_6b9fc.
Proof. vm_refl. Qed.
Lemma Dx_6b9fc : decode_any Wx_6b9fc = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6ba00 : bv 32 := 0x78813d83.
Lemma Fx_6ba00 : fetch_word Asan.M.loaded_segments (0x6ba50 : word) = Some Wx_6ba00.
Proof. vm_refl. Qed.
Lemma Dx_6ba00 : decode_any Wx_6ba00 = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6ba04 : bv 32 := 0x7f010113.
Lemma Fx_6ba04 : fetch_word Asan.M.loaded_segments (0x6ba54 : word) = Some Wx_6ba04.
Proof. vm_refl. Qed.
Lemma Dx_6ba04 : decode_any Wx_6ba04 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6ba08 : bv 32 := 0x00008067.
Lemma Fx_6ba08 : fetch_word Asan.M.loaded_segments (0x6ba58 : word) = Some Wx_6ba08.
Proof. vm_refl. Qed.
Lemma Dx_6ba08 : decode_any Wx_6ba08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6ba90 : bv 32 := 0x1a049663.
Lemma Fx_6ba90 : fetch_word Asan.M.loaded_segments (0x6bae0 : word) = Some Wx_6ba90.
Proof. vm_refl. Qed.
Lemma Dx_6ba90 : decode_any Wx_6ba90 = Some (Branch BC_NE 9 0 428, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6ba94 : bv 32 := 0xdd9ff06f.
Lemma Fx_6ba94 : fetch_word Asan.M.loaded_segments (0x6bae4 : word) = Some Wx_6ba94.
Proof. vm_refl. Qed.
Lemma Dx_6ba94 : decode_any Wx_6ba94 = Some (Jal 0 2096600, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb04 : bv 32 := 0x24049263.
Lemma Fx_6bb04 : fetch_word Asan.M.loaded_segments (0x6bb54 : word) = Some Wx_6bb04.
Proof. vm_refl. Qed.
Lemma Dx_6bb04 : decode_any Wx_6bb04 = Some (Branch BC_NE 9 0 580, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb08 : bv 32 := 0xdb1ff06f.
Lemma Fx_6bb08 : fetch_word Asan.M.loaded_segments (0x6bb58 : word) = Some Wx_6bb08.
Proof. vm_refl. Qed.
Lemma Dx_6bb08 : decode_any Wx_6bb08 = Some (Jal 0 2096560, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc08 : bv 32 := 0x00060703.
Lemma Fx_6bc08 : fetch_word Asan.M.loaded_segments (0x6bc58 : word) = Some Wx_6bc08.
Proof. vm_refl. Qed.
Lemma Dx_6bc08 : decode_any Wx_6bc08 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc0c : bv 32 := 0x0076f693.
Lemma Fx_6bc0c : fetch_word Asan.M.loaded_segments (0x6bc5c : word) = Some Wx_6bc0c.
Proof. vm_refl. Qed.
Lemma Dx_6bc0c : decode_any Wx_6bc0c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc10 : bv 32 := 0x00e037b3.
Lemma Fx_6bc10 : fetch_word Asan.M.loaded_segments (0x6bc60 : word) = Some Wx_6bc10.
Proof. vm_refl. Qed.
Lemma Dx_6bc10 : decode_any Wx_6bc10 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc14 : bv 32 := 0x00e6a6b3.
Lemma Fx_6bc14 : fetch_word Asan.M.loaded_segments (0x6bc64 : word) = Some Wx_6bc14.
Proof. vm_refl. Qed.
Lemma Dx_6bc14 : decode_any Wx_6bc14 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc18 : bv 32 := 0x0016c693.
Lemma Fx_6bc18 : fetch_word Asan.M.loaded_segments (0x6bc68 : word) = Some Wx_6bc18.
Proof. vm_refl. Qed.
Lemma Dx_6bc18 : decode_any Wx_6bc18 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc1c : bv 32 := 0x00d7f6b3.
Lemma Fx_6bc1c : fetch_word Asan.M.loaded_segments (0x6bc6c : word) = Some Wx_6bc1c.
Proof. vm_refl. Qed.
Lemma Dx_6bc1c : decode_any Wx_6bc1c = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc20 : bv 32 := 0x00c5fa63.
Lemma Fx_6bc20 : fetch_word Asan.M.loaded_segments (0x6bc70 : word) = Some Wx_6bc20.
Proof. vm_refl. Qed.
Lemma Dx_6bc20 : decode_any Wx_6bc20 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc24 : bv 32 := 0x0005c703.
Lemma Fx_6bc24 : fetch_word Asan.M.loaded_segments (0x6bc74 : word) = Some Wx_6bc24.
Proof. vm_refl. Qed.
Lemma Dx_6bc24 : decode_any Wx_6bc24 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc28 : bv 32 := 0x00158593.
Lemma Fx_6bc28 : fetch_word Asan.M.loaded_segments (0x6bc78 : word) = Some Wx_6bc28.
Proof. vm_refl. Qed.
Lemma Dx_6bc28 : decode_any Wx_6bc28 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc2c : bv 32 := 0x00d766b3.
Lemma Fx_6bc2c : fetch_word Asan.M.loaded_segments (0x6bc7c : word) = Some Wx_6bc2c.
Proof. vm_refl. Qed.
Lemma Dx_6bc2c : decode_any Wx_6bc2c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc30 : bv 32 := 0xfec59ae3.
Lemma Fx_6bc30 : fetch_word Asan.M.loaded_segments (0x6bc80 : word) = Some Wx_6bc30.
Proof. vm_refl. Qed.
Lemma Dx_6bc30 : decode_any Wx_6bc30 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc34 : bv 32 := 0x0ff6f593.
Lemma Fx_6bc34 : fetch_word Asan.M.loaded_segments (0x6bc84 : word) = Some Wx_6bc34.
Proof. vm_refl. Qed.
Lemma Dx_6bc34 : decode_any Wx_6bc34 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc38 : bv 32 := 0xc2058ae3.
Lemma Fx_6bc38 : fetch_word Asan.M.loaded_segments (0x6bc88 : word) = Some Wx_6bc38.
Proof. vm_refl. Qed.
Lemma Dx_6bc38 : decode_any Wx_6bc38 = Some (Branch BC_EQ 11 0 7220, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc3c : bv 32 := 0x00050d13.
Lemma Fx_6bc3c : fetch_word Asan.M.loaded_segments (0x6bc8c : word) = Some Wx_6bc3c.
Proof. vm_refl. Qed.
Lemma Dx_6bc3c : decode_any Wx_6bc3c = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc40 : bv 32 := 0x000a0513.
Lemma Fx_6bc40 : fetch_word Asan.M.loaded_segments (0x6bc90 : word) = Some Wx_6bc40.
Proof. vm_refl. Qed.
Lemma Dx_6bc40 : decode_any Wx_6bc40 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc44 : bv 32 := 0x00048593.
Lemma Fx_6bc44 : fetch_word Asan.M.loaded_segments (0x6bc94 : word) = Some Wx_6bc44.
Proof. vm_refl. Qed.
Lemma Dx_6bc44 : decode_any Wx_6bc44 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc48 : bv 32 := 0x209160ef.
Lemma Fx_6bc48 : fetch_word Asan.M.loaded_segments (0x6bc98 : word) = Some Wx_6bc48.
Proof. vm_refl. Qed.
Lemma Dx_6bc48 : decode_any Wx_6bc48 = Some (Jal 1 92680, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc4c : bv 32 := 0x00050b13.
Lemma Fx_6bc4c : fetch_word Asan.M.loaded_segments (0x6bc9c : word) = Some Wx_6bc4c.
Proof. vm_refl. Qed.
Lemma Dx_6bc4c : decode_any Wx_6bc4c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc50 : bv 32 := 0x000d0513.
Lemma Fx_6bc50 : fetch_word Asan.M.loaded_segments (0x6bca0 : word) = Some Wx_6bc50.
Proof. vm_refl. Qed.
Lemma Dx_6bc50 : decode_any Wx_6bc50 = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc54 : bv 32 := 0xc00b0ce3.
Lemma Fx_6bc54 : fetch_word Asan.M.loaded_segments (0x6bca4 : word) = Some Wx_6bc54.
Proof. vm_refl. Qed.
Lemma Dx_6bc54 : decode_any Wx_6bc54 = Some (Branch BC_EQ 22 0 7192, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd14 : bv 32 := 0x00060703.
Lemma Fx_6bd14 : fetch_word Asan.M.loaded_segments (0x6bd64 : word) = Some Wx_6bd14.
Proof. vm_refl. Qed.
Lemma Dx_6bd14 : decode_any Wx_6bd14 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd18 : bv 32 := 0x0076f693.
Lemma Fx_6bd18 : fetch_word Asan.M.loaded_segments (0x6bd68 : word) = Some Wx_6bd18.
Proof. vm_refl. Qed.
Lemma Dx_6bd18 : decode_any Wx_6bd18 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd1c : bv 32 := 0x00e037b3.
Lemma Fx_6bd1c : fetch_word Asan.M.loaded_segments (0x6bd6c : word) = Some Wx_6bd1c.
Proof. vm_refl. Qed.
Lemma Dx_6bd1c : decode_any Wx_6bd1c = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd20 : bv 32 := 0x00e6a6b3.
Lemma Fx_6bd20 : fetch_word Asan.M.loaded_segments (0x6bd70 : word) = Some Wx_6bd20.
Proof. vm_refl. Qed.
Lemma Dx_6bd20 : decode_any Wx_6bd20 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd24 : bv 32 := 0x0016c693.
Lemma Fx_6bd24 : fetch_word Asan.M.loaded_segments (0x6bd74 : word) = Some Wx_6bd24.
Proof. vm_refl. Qed.
Lemma Dx_6bd24 : decode_any Wx_6bd24 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd28 : bv 32 := 0x00d7f6b3.
Lemma Fx_6bd28 : fetch_word Asan.M.loaded_segments (0x6bd78 : word) = Some Wx_6bd28.
Proof. vm_refl. Qed.
Lemma Dx_6bd28 : decode_any Wx_6bd28 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd2c : bv 32 := 0x00c5fa63.
Lemma Fx_6bd2c : fetch_word Asan.M.loaded_segments (0x6bd7c : word) = Some Wx_6bd2c.
Proof. vm_refl. Qed.
Lemma Dx_6bd2c : decode_any Wx_6bd2c = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd30 : bv 32 := 0x0005c703.
Lemma Fx_6bd30 : fetch_word Asan.M.loaded_segments (0x6bd80 : word) = Some Wx_6bd30.
Proof. vm_refl. Qed.
Lemma Dx_6bd30 : decode_any Wx_6bd30 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd34 : bv 32 := 0x00158593.
Lemma Fx_6bd34 : fetch_word Asan.M.loaded_segments (0x6bd84 : word) = Some Wx_6bd34.
Proof. vm_refl. Qed.
Lemma Dx_6bd34 : decode_any Wx_6bd34 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd38 : bv 32 := 0x00d766b3.
Lemma Fx_6bd38 : fetch_word Asan.M.loaded_segments (0x6bd88 : word) = Some Wx_6bd38.
Proof. vm_refl. Qed.
Lemma Dx_6bd38 : decode_any Wx_6bd38 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd3c : bv 32 := 0xfec59ae3.
Lemma Fx_6bd3c : fetch_word Asan.M.loaded_segments (0x6bd8c : word) = Some Wx_6bd3c.
Proof. vm_refl. Qed.
Lemma Dx_6bd3c : decode_any Wx_6bd3c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd40 : bv 32 := 0x0ff6f593.
Lemma Fx_6bd40 : fetch_word Asan.M.loaded_segments (0x6bd90 : word) = Some Wx_6bd40.
Proof. vm_refl. Qed.
Lemma Dx_6bd40 : decode_any Wx_6bd40 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd44 : bv 32 := 0xb6058ae3.
Lemma Fx_6bd44 : fetch_word Asan.M.loaded_segments (0x6bd94 : word) = Some Wx_6bd44.
Proof. vm_refl. Qed.
Lemma Dx_6bd44 : decode_any Wx_6bd44 = Some (Branch BC_EQ 11 0 7028, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd48 : bv 32 := 0x00050c93.
Lemma Fx_6bd48 : fetch_word Asan.M.loaded_segments (0x6bd98 : word) = Some Wx_6bd48.
Proof. vm_refl. Qed.
Lemma Dx_6bd48 : decode_any Wx_6bd48 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd4c : bv 32 := 0x00090513.
Lemma Fx_6bd4c : fetch_word Asan.M.loaded_segments (0x6bd9c : word) = Some Wx_6bd4c.
Proof. vm_refl. Qed.
Lemma Dx_6bd4c : decode_any Wx_6bd4c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd50 : bv 32 := 0x00048593.
Lemma Fx_6bd50 : fetch_word Asan.M.loaded_segments (0x6bda0 : word) = Some Wx_6bd50.
Proof. vm_refl. Qed.
Lemma Dx_6bd50 : decode_any Wx_6bd50 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd54 : bv 32 := 0x0fd160ef.
Lemma Fx_6bd54 : fetch_word Asan.M.loaded_segments (0x6bda4 : word) = Some Wx_6bd54.
Proof. vm_refl. Qed.
Lemma Dx_6bd54 : decode_any Wx_6bd54 = Some (Jal 1 92412, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd58 : bv 32 := 0x00050b13.
Lemma Fx_6bd58 : fetch_word Asan.M.loaded_segments (0x6bda8 : word) = Some Wx_6bd58.
Proof. vm_refl. Qed.
Lemma Dx_6bd58 : decode_any Wx_6bd58 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd5c : bv 32 := 0xb4050ee3.
Lemma Fx_6bd5c : fetch_word Asan.M.loaded_segments (0x6bdac : word) = Some Wx_6bd5c.
Proof. vm_refl. Qed.
Lemma Dx_6bd5c : decode_any Wx_6bd5c = Some (Branch BC_EQ 10 0 7004, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c03c : bv 32 := 0xfd010113.
Lemma Fx_6c03c : fetch_word Asan.M.loaded_segments (0x6c08c : word) = Some Wx_6c03c.
Proof. vm_refl. Qed.
Lemma Dx_6c03c : decode_any Wx_6c03c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c040 : bv 32 := 0x02113423.
Lemma Fx_6c040 : fetch_word Asan.M.loaded_segments (0x6c090 : word) = Some Wx_6c040.
Proof. vm_refl. Qed.
Lemma Dx_6c040 : decode_any Wx_6c040 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c044 : bv 32 := 0x02813023.
Lemma Fx_6c044 : fetch_word Asan.M.loaded_segments (0x6c094 : word) = Some Wx_6c044.
Proof. vm_refl. Qed.
Lemma Dx_6c044 : decode_any Wx_6c044 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c048 : bv 32 := 0x00913c23.
Lemma Fx_6c048 : fetch_word Asan.M.loaded_segments (0x6c098 : word) = Some Wx_6c048.
Proof. vm_refl. Qed.
Lemma Dx_6c048 : decode_any Wx_6c048 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c04c : bv 32 := 0x01213823.
Lemma Fx_6c04c : fetch_word Asan.M.loaded_segments (0x6c09c : word) = Some Wx_6c04c.
Proof. vm_refl. Qed.
Lemma Dx_6c04c : decode_any Wx_6c04c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c050 : bv 32 := 0x00060413.
Lemma Fx_6c050 : fetch_word Asan.M.loaded_segments (0x6c0a0 : word) = Some Wx_6c050.
Proof. vm_refl. Qed.
Lemma Dx_6c050 : decode_any Wx_6c050 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c054 : bv 32 := 0x00058493.
Lemma Fx_6c054 : fetch_word Asan.M.loaded_segments (0x6c0a4 : word) = Some Wx_6c054.
Proof. vm_refl. Qed.
Lemma Dx_6c054 : decode_any Wx_6c054 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c058 : bv 32 := 0x00050913.
Lemma Fx_6c058 : fetch_word Asan.M.loaded_segments (0x6c0a8 : word) = Some Wx_6c058.
Proof. vm_refl. Qed.
Lemma Dx_6c058 : decode_any Wx_6c058 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c05c : bv 32 := 0x3081b0ef.
Lemma Fx_6c05c : fetch_word Asan.M.loaded_segments (0x6c0ac : word) = Some Wx_6c05c.
Proof. vm_refl. Qed.
Lemma Dx_6c05c : decode_any Wx_6c05c = Some (Jal 1 111368, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c060 : bv 32 := 0x04050863.
Lemma Fx_6c060 : fetch_word Asan.M.loaded_segments (0x6c0b0 : word) = Some Wx_6c060.
Proof. vm_refl. Qed.
Lemma Dx_6c060 : decode_any Wx_6c060 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c064 : bv 32 := 0xfffaf517.
Lemma Fx_6c064 : fetch_word Asan.M.loaded_segments (0x6c0b4 : word) = Some Wx_6c064.
Proof. vm_refl. Qed.
Lemma Dx_6c064 : decode_any Wx_6c064 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c068 : bv 32 := 0x21050513.
Lemma Fx_6c068 : fetch_word Asan.M.loaded_segments (0x6c0b8 : word) = Some Wx_6c068.
Proof. vm_refl. Qed.
Lemma Dx_6c068 : decode_any Wx_6c068 = Some (OpImm ALU_ADD 10 10 528, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c06c : bv 32 := 0x00a13423.
Lemma Fx_6c06c : fetch_word Asan.M.loaded_segments (0x6c0bc : word) = Some Wx_6c06c.
Proof. vm_refl. Qed.
Lemma Dx_6c06c : decode_any Wx_6c06c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c070 : bv 32 := 0x2041c0ef.
Lemma Fx_6c070 : fetch_word Asan.M.loaded_segments (0x6c0c0 : word) = Some Wx_6c070.
Proof. vm_refl. Qed.
Lemma Dx_6c070 : decode_any Wx_6c070 = Some (Jal 1 115204, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c074 : bv 32 := 0x000e9597.
Lemma Fx_6c074 : fetch_word Asan.M.loaded_segments (0x6c0c4 : word) = Some Wx_6c074.
Proof. vm_refl. Qed.
Lemma Dx_6c074 : decode_any Wx_6c074 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c078 : bv 32 := 0xec45b303.
Lemma Fx_6c078 : fetch_word Asan.M.loaded_segments (0x6c0c8 : word) = Some Wx_6c078.
Proof. vm_refl. Qed.
Lemma Dx_6c078 : decode_any Wx_6c078 = Some (Load SZ8 true 6 11 3780, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c07c : bv 32 := 0x04050c63.
Lemma Fx_6c07c : fetch_word Asan.M.loaded_segments (0x6c0cc : word) = Some Wx_6c07c.
Proof. vm_refl. Qed.
Lemma Dx_6c07c : decode_any Wx_6c07c = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c080 : bv 32 := 0x00810513.
Lemma Fx_6c080 : fetch_word Asan.M.loaded_segments (0x6c0d0 : word) = Some Wx_6c080.
Proof. vm_refl. Qed.
Lemma Dx_6c080 : decode_any Wx_6c080 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c084 : bv 32 := 0x00030593.
Lemma Fx_6c084 : fetch_word Asan.M.loaded_segments (0x6c0d4 : word) = Some Wx_6c084.
Proof. vm_refl. Qed.
Lemma Dx_6c084 : decode_any Wx_6c084 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c088 : bv 32 := 0x00090613.
Lemma Fx_6c088 : fetch_word Asan.M.loaded_segments (0x6c0d8 : word) = Some Wx_6c088.
Proof. vm_refl. Qed.
Lemma Dx_6c088 : decode_any Wx_6c088 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c08c : bv 32 := 0x00048693.
Lemma Fx_6c08c : fetch_word Asan.M.loaded_segments (0x6c0dc : word) = Some Wx_6c08c.
Proof. vm_refl. Qed.
Lemma Dx_6c08c : decode_any Wx_6c08c = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c090 : bv 32 := 0x00040713.
Lemma Fx_6c090 : fetch_word Asan.M.loaded_segments (0x6c0e0 : word) = Some Wx_6c090.
Proof. vm_refl. Qed.
Lemma Dx_6c090 : decode_any Wx_6c090 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c094 : bv 32 := 0xf14ff0ef.
Lemma Fx_6c094 : fetch_word Asan.M.loaded_segments (0x6c0e4 : word) = Some Wx_6c094.
Proof. vm_refl. Qed.
Lemma Dx_6c094 : decode_any Wx_6c094 = Some (Jal 1 2094868, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c098 : bv 32 := 0x02813083.
Lemma Fx_6c098 : fetch_word Asan.M.loaded_segments (0x6c0e8 : word) = Some Wx_6c098.
Proof. vm_refl. Qed.
Lemma Dx_6c098 : decode_any Wx_6c098 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c09c : bv 32 := 0x02013403.
Lemma Fx_6c09c : fetch_word Asan.M.loaded_segments (0x6c0ec : word) = Some Wx_6c09c.
Proof. vm_refl. Qed.
Lemma Dx_6c09c : decode_any Wx_6c09c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0a0 : bv 32 := 0x01813483.
Lemma Fx_6c0a0 : fetch_word Asan.M.loaded_segments (0x6c0f0 : word) = Some Wx_6c0a0.
Proof. vm_refl. Qed.
Lemma Dx_6c0a0 : decode_any Wx_6c0a0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0a4 : bv 32 := 0x01013903.
Lemma Fx_6c0a4 : fetch_word Asan.M.loaded_segments (0x6c0f4 : word) = Some Wx_6c0a4.
Proof. vm_refl. Qed.
Lemma Dx_6c0a4 : decode_any Wx_6c0a4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0a8 : bv 32 := 0x03010113.
Lemma Fx_6c0a8 : fetch_word Asan.M.loaded_segments (0x6c0f8 : word) = Some Wx_6c0a8.
Proof. vm_refl. Qed.
Lemma Dx_6c0a8 : decode_any Wx_6c0a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0ac : bv 32 := 0x00008067.
Lemma Fx_6c0ac : fetch_word Asan.M.loaded_segments (0x6c0fc : word) = Some Wx_6c0ac.
Proof. vm_refl. Qed.
Lemma Dx_6c0ac : decode_any Wx_6c0ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0f8 : bv 32 := 0xfd010113.
Lemma Fx_6c0f8 : fetch_word Asan.M.loaded_segments (0x6c148 : word) = Some Wx_6c0f8.
Proof. vm_refl. Qed.
Lemma Dx_6c0f8 : decode_any Wx_6c0f8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0fc : bv 32 := 0x02113423.
Lemma Fx_6c0fc : fetch_word Asan.M.loaded_segments (0x6c14c : word) = Some Wx_6c0fc.
Proof. vm_refl. Qed.
Lemma Dx_6c0fc : decode_any Wx_6c0fc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c100 : bv 32 := 0x02813023.
Lemma Fx_6c100 : fetch_word Asan.M.loaded_segments (0x6c150 : word) = Some Wx_6c100.
Proof. vm_refl. Qed.
Lemma Dx_6c100 : decode_any Wx_6c100 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c104 : bv 32 := 0x00913c23.
Lemma Fx_6c104 : fetch_word Asan.M.loaded_segments (0x6c154 : word) = Some Wx_6c104.
Proof. vm_refl. Qed.
Lemma Dx_6c104 : decode_any Wx_6c104 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c108 : bv 32 := 0x01213823.
Lemma Fx_6c108 : fetch_word Asan.M.loaded_segments (0x6c158 : word) = Some Wx_6c108.
Proof. vm_refl. Qed.
Lemma Dx_6c108 : decode_any Wx_6c108 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c10c : bv 32 := 0x00060413.
Lemma Fx_6c10c : fetch_word Asan.M.loaded_segments (0x6c15c : word) = Some Wx_6c10c.
Proof. vm_refl. Qed.
Lemma Dx_6c10c : decode_any Wx_6c10c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c110 : bv 32 := 0x00058493.
Lemma Fx_6c110 : fetch_word Asan.M.loaded_segments (0x6c160 : word) = Some Wx_6c110.
Proof. vm_refl. Qed.
Lemma Dx_6c110 : decode_any Wx_6c110 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c114 : bv 32 := 0x00050913.
Lemma Fx_6c114 : fetch_word Asan.M.loaded_segments (0x6c164 : word) = Some Wx_6c114.
Proof. vm_refl. Qed.
Lemma Dx_6c114 : decode_any Wx_6c114 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c118 : bv 32 := 0x24c1b0ef.
Lemma Fx_6c118 : fetch_word Asan.M.loaded_segments (0x6c168 : word) = Some Wx_6c118.
Proof. vm_refl. Qed.
Lemma Dx_6c118 : decode_any Wx_6c118 = Some (Jal 1 111180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c11c : bv 32 := 0x04050863.
Lemma Fx_6c11c : fetch_word Asan.M.loaded_segments (0x6c16c : word) = Some Wx_6c11c.
Proof. vm_refl. Qed.
Lemma Dx_6c11c : decode_any Wx_6c11c = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c120 : bv 32 := 0xfffaa517.
Lemma Fx_6c120 : fetch_word Asan.M.loaded_segments (0x6c170 : word) = Some Wx_6c120.
Proof. vm_refl. Qed.
Lemma Dx_6c120 : decode_any Wx_6c120 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c124 : bv 32 := 0xe2050513.
Lemma Fx_6c124 : fetch_word Asan.M.loaded_segments (0x6c174 : word) = Some Wx_6c124.
Proof. vm_refl. Qed.
Lemma Dx_6c124 : decode_any Wx_6c124 = Some (OpImm ALU_ADD 10 10 3616, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c128 : bv 32 := 0x00a13423.
Lemma Fx_6c128 : fetch_word Asan.M.loaded_segments (0x6c178 : word) = Some Wx_6c128.
Proof. vm_refl. Qed.
Lemma Dx_6c128 : decode_any Wx_6c128 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c12c : bv 32 := 0x1481c0ef.
Lemma Fx_6c12c : fetch_word Asan.M.loaded_segments (0x6c17c : word) = Some Wx_6c12c.
Proof. vm_refl. Qed.
Lemma Dx_6c12c : decode_any Wx_6c12c = Some (Jal 1 115016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c130 : bv 32 := 0x000e9597.
Lemma Fx_6c130 : fetch_word Asan.M.loaded_segments (0x6c180 : word) = Some Wx_6c130.
Proof. vm_refl. Qed.
Lemma Dx_6c130 : decode_any Wx_6c130 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c134 : bv 32 := 0xe105b303.
Lemma Fx_6c134 : fetch_word Asan.M.loaded_segments (0x6c184 : word) = Some Wx_6c134.
Proof. vm_refl. Qed.
Lemma Dx_6c134 : decode_any Wx_6c134 = Some (Load SZ8 true 6 11 3600, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c138 : bv 32 := 0x04050c63.
Lemma Fx_6c138 : fetch_word Asan.M.loaded_segments (0x6c188 : word) = Some Wx_6c138.
Proof. vm_refl. Qed.
Lemma Dx_6c138 : decode_any Wx_6c138 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c13c : bv 32 := 0x00810513.
Lemma Fx_6c13c : fetch_word Asan.M.loaded_segments (0x6c18c : word) = Some Wx_6c13c.
Proof. vm_refl. Qed.
Lemma Dx_6c13c : decode_any Wx_6c13c = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c140 : bv 32 := 0x00030593.
Lemma Fx_6c140 : fetch_word Asan.M.loaded_segments (0x6c190 : word) = Some Wx_6c140.
Proof. vm_refl. Qed.
Lemma Dx_6c140 : decode_any Wx_6c140 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c144 : bv 32 := 0x00090613.
Lemma Fx_6c144 : fetch_word Asan.M.loaded_segments (0x6c194 : word) = Some Wx_6c144.
Proof. vm_refl. Qed.
Lemma Dx_6c144 : decode_any Wx_6c144 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c148 : bv 32 := 0x00048693.
Lemma Fx_6c148 : fetch_word Asan.M.loaded_segments (0x6c198 : word) = Some Wx_6c148.
Proof. vm_refl. Qed.
Lemma Dx_6c148 : decode_any Wx_6c148 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c14c : bv 32 := 0x00040713.
Lemma Fx_6c14c : fetch_word Asan.M.loaded_segments (0x6c19c : word) = Some Wx_6c14c.
Proof. vm_refl. Qed.
Lemma Dx_6c14c : decode_any Wx_6c14c = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c150 : bv 32 := 0xe58ff0ef.
Lemma Fx_6c150 : fetch_word Asan.M.loaded_segments (0x6c1a0 : word) = Some Wx_6c150.
Proof. vm_refl. Qed.
Lemma Dx_6c150 : decode_any Wx_6c150 = Some (Jal 1 2094680, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c154 : bv 32 := 0x02813083.
Lemma Fx_6c154 : fetch_word Asan.M.loaded_segments (0x6c1a4 : word) = Some Wx_6c154.
Proof. vm_refl. Qed.
Lemma Dx_6c154 : decode_any Wx_6c154 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c158 : bv 32 := 0x02013403.
Lemma Fx_6c158 : fetch_word Asan.M.loaded_segments (0x6c1a8 : word) = Some Wx_6c158.
Proof. vm_refl. Qed.
Lemma Dx_6c158 : decode_any Wx_6c158 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c15c : bv 32 := 0x01813483.
Lemma Fx_6c15c : fetch_word Asan.M.loaded_segments (0x6c1ac : word) = Some Wx_6c15c.
Proof. vm_refl. Qed.
Lemma Dx_6c15c : decode_any Wx_6c15c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c160 : bv 32 := 0x01013903.
Lemma Fx_6c160 : fetch_word Asan.M.loaded_segments (0x6c1b0 : word) = Some Wx_6c160.
Proof. vm_refl. Qed.
Lemma Dx_6c160 : decode_any Wx_6c160 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c164 : bv 32 := 0x03010113.
Lemma Fx_6c164 : fetch_word Asan.M.loaded_segments (0x6c1b4 : word) = Some Wx_6c164.
Proof. vm_refl. Qed.
Lemma Dx_6c164 : decode_any Wx_6c164 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c168 : bv 32 := 0x00008067.
Lemma Fx_6c168 : fetch_word Asan.M.loaded_segments (0x6c1b8 : word) = Some Wx_6c168.
Proof. vm_refl. Qed.
Lemma Dx_6c168 : decode_any Wx_6c168 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87364 : bv 32 := 0x000d6517.
Lemma Fx_87364 : fetch_word Asan.M.loaded_segments (0x873b4 : word) = Some Wx_87364.
Proof. vm_refl. Qed.
Lemma Dx_87364 : decode_any Wx_87364 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87368 : bv 32 := 0x2e450503.
Lemma Fx_87368 : fetch_word Asan.M.loaded_segments (0x873b8 : word) = Some Wx_87368.
Proof. vm_refl. Qed.
Lemma Dx_87368 : decode_any Wx_87368 = Some (Load SZ1 true 10 10 740, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8736c : bv 32 := 0x0230000f.
Lemma Fx_8736c : fetch_word Asan.M.loaded_segments (0x873bc : word) = Some Wx_8736c.
Proof. vm_refl. Qed.
Lemma Dx_8736c : decode_any Wx_8736c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87370 : bv 32 := 0xfff50513.
Lemma Fx_87370 : fetch_word Asan.M.loaded_segments (0x873c0 : word) = Some Wx_87370.
Proof. vm_refl. Qed.
Lemma Dx_87370 : decode_any Wx_87370 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87374 : bv 32 := 0x00153513.
Lemma Fx_87374 : fetch_word Asan.M.loaded_segments (0x873c4 : word) = Some Wx_87374.
Proof. vm_refl. Qed.
Lemma Dx_87374 : decode_any Wx_87374 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87378 : bv 32 := 0x00008067.
Lemma Fx_87378 : fetch_word Asan.M.loaded_segments (0x873c8 : word) = Some Wx_87378.
Proof. vm_refl. Qed.
Lemma Dx_87378 : decode_any Wx_87378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

