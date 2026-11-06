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

Definition W_144dc4 : bv 32 := 0x0ff5f593.
Lemma F_144dc4 : fetch_word Asan.M.loaded_segments (0x144e08 : word) = Some W_144dc4.
Proof. vm_refl. Qed.
Lemma D_144dc4 : decode_any W_144dc4 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dc8 : bv 32 := 0x00757693.
Lemma F_144dc8 : fetch_word Asan.M.loaded_segments (0x144e0c : word) = Some W_144dc8.
Proof. vm_refl. Qed.
Lemma D_144dc8 : decode_any W_144dc8 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dcc : bv 32 := 0x00c03733.
Lemma F_144dcc : fetch_word Asan.M.loaded_segments (0x144e10 : word) = Some W_144dcc.
Proof. vm_refl. Qed.
Lemma D_144dcc : decode_any W_144dcc = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dd0 : bv 32 := 0x02068c63.
Lemma F_144dd0 : fetch_word Asan.M.loaded_segments (0x144e14 : word) = Some W_144dd0.
Proof. vm_refl. Qed.
Lemma D_144dd0 : decode_any W_144dd0 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dd4 : bv 32 := 0x02060a63.
Lemma F_144dd4 : fetch_word Asan.M.loaded_segments (0x144e18 : word) = Some W_144dd4.
Proof. vm_refl. Qed.
Lemma D_144dd4 : decode_any W_144dd4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dd8 : bv 32 := 0x00150793.
Lemma F_144dd8 : fetch_word Asan.M.loaded_segments (0x144e1c : word) = Some W_144dd8.
Proof. vm_refl. Qed.
Lemma D_144dd8 : decode_any W_144dd8 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ddc : bv 32 := 0x00100813.
Lemma F_144ddc : fetch_word Asan.M.loaded_segments (0x144e20 : word) = Some W_144ddc.
Proof. vm_refl. Qed.
Lemma D_144ddc : decode_any W_144ddc = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144de0 : bv 32 := 0x00054703.
Lemma F_144de0 : fetch_word Asan.M.loaded_segments (0x144e24 : word) = Some W_144de0.
Proof. vm_refl. Qed.
Lemma D_144de0 : decode_any W_144de0 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144de4 : bv 32 := 0x00060693.
Lemma F_144de4 : fetch_word Asan.M.loaded_segments (0x144e28 : word) = Some W_144de4.
Proof. vm_refl. Qed.
Lemma D_144de4 : decode_any W_144de4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144de8 : bv 32 := 0x06b70e63.
Lemma F_144de8 : fetch_word Asan.M.loaded_segments (0x144e2c : word) = Some W_144de8.
Proof. vm_refl. Qed.
Lemma D_144de8 : decode_any W_144de8 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dec : bv 32 := 0x00150513.
Lemma F_144dec : fetch_word Asan.M.loaded_segments (0x144e30 : word) = Some W_144dec.
Proof. vm_refl. Qed.
Lemma D_144dec : decode_any W_144dec = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144df0 : bv 32 := 0xfff68613.
Lemma F_144df0 : fetch_word Asan.M.loaded_segments (0x144e34 : word) = Some W_144df0.
Proof. vm_refl. Qed.
Lemma D_144df0 : decode_any W_144df0 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_144df4 : bv 32 := 0x0077f893.
Lemma F_144df4 : fetch_word Asan.M.loaded_segments (0x144e38 : word) = Some W_144df4.
Proof. vm_refl. Qed.
Lemma D_144df4 : decode_any W_144df4 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_144df8 : bv 32 := 0x00c03733.
Lemma F_144df8 : fetch_word Asan.M.loaded_segments (0x144e3c : word) = Some W_144df8.
Proof. vm_refl. Qed.
Lemma D_144df8 : decode_any W_144df8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_144dfc : bv 32 := 0x00088663.
Lemma F_144dfc : fetch_word Asan.M.loaded_segments (0x144e40 : word) = Some W_144dfc.
Proof. vm_refl. Qed.
Lemma D_144dfc : decode_any W_144dfc = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e00 : bv 32 := 0x00178793.
Lemma F_144e00 : fetch_word Asan.M.loaded_segments (0x144e44 : word) = Some W_144e00.
Proof. vm_refl. Qed.
Lemma D_144e00 : decode_any W_144e00 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e04 : bv 32 := 0xfd069ee3.
Lemma F_144e04 : fetch_word Asan.M.loaded_segments (0x144e48 : word) = Some W_144e04.
Proof. vm_refl. Qed.
Lemma D_144e04 : decode_any W_144e04 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e08 : bv 32 := 0x06070863.
Lemma F_144e08 : fetch_word Asan.M.loaded_segments (0x144e4c : word) = Some W_144e08.
Proof. vm_refl. Qed.
Lemma D_144e08 : decode_any W_144e08 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e0c : bv 32 := 0x00054683.
Lemma F_144e0c : fetch_word Asan.M.loaded_segments (0x144e50 : word) = Some W_144e0c.
Proof. vm_refl. Qed.
Lemma D_144e0c : decode_any W_144e0c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e10 : bv 32 := 0x04b68663.
Lemma F_144e10 : fetch_word Asan.M.loaded_segments (0x144e54 : word) = Some W_144e10.
Proof. vm_refl. Qed.
Lemma D_144e10 : decode_any W_144e10 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e14 : bv 32 := 0x00800693.
Lemma F_144e14 : fetch_word Asan.M.loaded_segments (0x144e58 : word) = Some W_144e14.
Proof. vm_refl. Qed.
Lemma D_144e14 : decode_any W_144e14 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e18 : bv 32 := 0x04d66263.
Lemma F_144e18 : fetch_word Asan.M.loaded_segments (0x144e5c : word) = Some W_144e18.
Proof. vm_refl. Qed.
Lemma D_144e18 : decode_any W_144e18 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e1c : bv 32 := 0xffecb697.
Lemma F_144e1c : fetch_word Asan.M.loaded_segments (0x144e60 : word) = Some W_144e1c.
Proof. vm_refl. Qed.
Lemma D_144e1c : decode_any W_144e1c = Some (Auipc 13 1048267, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e20 : bv 32 := 0x5786b683.
Lemma F_144e20 : fetch_word Asan.M.loaded_segments (0x144e64 : word) = Some W_144e20.
Proof. vm_refl. Qed.
Lemma D_144e20 : decode_any W_144e20 = Some (Load SZ8 true 13 13 1400, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e24 : bv 32 := 0xffecb717.
Lemma F_144e24 : fetch_word Asan.M.loaded_segments (0x144e68 : word) = Some W_144e24.
Proof. vm_refl. Qed.
Lemma D_144e24 : decode_any W_144e24 = Some (Auipc 14 1048267, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e28 : bv 32 := 0x55873703.
Lemma F_144e28 : fetch_word Asan.M.loaded_segments (0x144e6c : word) = Some W_144e28.
Proof. vm_refl. Qed.
Lemma D_144e28 : decode_any W_144e28 = Some (Load SZ8 true 14 14 1368, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e2c : bv 32 := 0x00168793.
Lemma F_144e2c : fetch_word Asan.M.loaded_segments (0x144e70 : word) = Some W_144e2c.
Proof. vm_refl. Qed.
Lemma D_144e2c : decode_any W_144e2c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e30 : bv 32 := 0x02f587b3.
Lemma F_144e30 : fetch_word Asan.M.loaded_segments (0x144e74 : word) = Some W_144e30.
Proof. vm_refl. Qed.
Lemma D_144e30 : decode_any W_144e30 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e34 : bv 32 := 0x00700813.
Lemma F_144e34 : fetch_word Asan.M.loaded_segments (0x144e78 : word) = Some W_144e34.
Proof. vm_refl. Qed.
Lemma D_144e34 : decode_any W_144e34 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e38 : bv 32 := 0x00053883.
Lemma F_144e38 : fetch_word Asan.M.loaded_segments (0x144e7c : word) = Some W_144e38.
Proof. vm_refl. Qed.
Lemma D_144e38 : decode_any W_144e38 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e3c : bv 32 := 0x00f8c8b3.
Lemma F_144e3c : fetch_word Asan.M.loaded_segments (0x144e80 : word) = Some W_144e3c.
Proof. vm_refl. Qed.
Lemma D_144e3c : decode_any W_144e3c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e40 : bv 32 := 0x411682b3.
Lemma F_144e40 : fetch_word Asan.M.loaded_segments (0x144e84 : word) = Some W_144e40.
Proof. vm_refl. Qed.
Lemma D_144e40 : decode_any W_144e40 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e44 : bv 32 := 0x0112e8b3.
Lemma F_144e44 : fetch_word Asan.M.loaded_segments (0x144e88 : word) = Some W_144e44.
Proof. vm_refl. Qed.
Lemma D_144e44 : decode_any W_144e44 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e48 : bv 32 := 0x00e8f8b3.
Lemma F_144e48 : fetch_word Asan.M.loaded_segments (0x144e8c : word) = Some W_144e48.
Proof. vm_refl. Qed.
Lemma D_144e48 : decode_any W_144e48 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e4c : bv 32 := 0x02e89a63.
Lemma F_144e4c : fetch_word Asan.M.loaded_segments (0x144e90 : word) = Some W_144e4c.
Proof. vm_refl. Qed.
Lemma D_144e4c : decode_any W_144e4c = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e50 : bv 32 := 0xff860613.
Lemma F_144e50 : fetch_word Asan.M.loaded_segments (0x144e94 : word) = Some W_144e50.
Proof. vm_refl. Qed.
Lemma D_144e50 : decode_any W_144e50 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e54 : bv 32 := 0x00850513.
Lemma F_144e54 : fetch_word Asan.M.loaded_segments (0x144e98 : word) = Some W_144e54.
Proof. vm_refl. Qed.
Lemma D_144e54 : decode_any W_144e54 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e58 : bv 32 := 0xfec860e3.
Lemma F_144e58 : fetch_word Asan.M.loaded_segments (0x144e9c : word) = Some W_144e58.
Proof. vm_refl. Qed.
Lemma D_144e58 : decode_any W_144e58 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e5c : bv 32 := 0x00060693.
Lemma F_144e5c : fetch_word Asan.M.loaded_segments (0x144ea0 : word) = Some W_144e5c.
Proof. vm_refl. Qed.
Lemma D_144e5c : decode_any W_144e5c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e60 : bv 32 := 0x00060c63.
Lemma F_144e60 : fetch_word Asan.M.loaded_segments (0x144ea4 : word) = Some W_144e60.
Proof. vm_refl. Qed.
Lemma D_144e60 : decode_any W_144e60 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e64 : bv 32 := 0x00054603.
Lemma F_144e64 : fetch_word Asan.M.loaded_segments (0x144ea8 : word) = Some W_144e64.
Proof. vm_refl. Qed.
Lemma D_144e64 : decode_any W_144e64 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e68 : bv 32 := 0x00b60a63.
Lemma F_144e68 : fetch_word Asan.M.loaded_segments (0x144eac : word) = Some W_144e68.
Proof. vm_refl. Qed.
Lemma D_144e68 : decode_any W_144e68 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e6c : bv 32 := 0xfff68693.
Lemma F_144e6c : fetch_word Asan.M.loaded_segments (0x144eb0 : word) = Some W_144e6c.
Proof. vm_refl. Qed.
Lemma D_144e6c : decode_any W_144e6c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e70 : bv 32 := 0x00150513.
Lemma F_144e70 : fetch_word Asan.M.loaded_segments (0x144eb4 : word) = Some W_144e70.
Proof. vm_refl. Qed.
Lemma D_144e70 : decode_any W_144e70 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e74 : bv 32 := 0xfe0698e3.
Lemma F_144e74 : fetch_word Asan.M.loaded_segments (0x144eb8 : word) = Some W_144e74.
Proof. vm_refl. Qed.
Lemma D_144e74 : decode_any W_144e74 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e7c : bv 32 := 0x00008067.
Lemma F_144e7c : fetch_word Asan.M.loaded_segments (0x144ec0 : word) = Some W_144e7c.
Proof. vm_refl. Qed.
Lemma D_144e7c : decode_any W_144e7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e80 : bv 32 := 0x00060693.
Lemma F_144e80 : fetch_word Asan.M.loaded_segments (0x144ec4 : word) = Some W_144e80.
Proof. vm_refl. Qed.
Lemma D_144e80 : decode_any W_144e80 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e84 : bv 32 := 0x00054603.
Lemma F_144e84 : fetch_word Asan.M.loaded_segments (0x144ec8 : word) = Some W_144e84.
Proof. vm_refl. Qed.
Lemma D_144e84 : decode_any W_144e84 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e88 : bv 32 := 0xfeb612e3.
Lemma F_144e88 : fetch_word Asan.M.loaded_segments (0x144ecc : word) = Some W_144e88.
Proof. vm_refl. Qed.
Lemma D_144e88 : decode_any W_144e88 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_144e8c : bv 32 := 0xff1ff06f.
Lemma F_144e8c : fetch_word Asan.M.loaded_segments (0x144ed0 : word) = Some W_144e8c.
Proof. vm_refl. Qed.
Lemma D_144e8c : decode_any W_144e8c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ec0 : bv 32 := 0x0035f693.
Lemma F_144ec0 : fetch_word Asan.M.loaded_segments (0x144f04 : word) = Some W_144ec0.
Proof. vm_refl. Qed.
Lemma D_144ec0 : decode_any W_144ec0 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ec4 : bv 32 := 0x10068863.
Lemma F_144ec4 : fetch_word Asan.M.loaded_segments (0x144f08 : word) = Some W_144ec4.
Proof. vm_refl. Qed.
Lemma D_144ec4 : decode_any W_144ec4 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ec8 : bv 32 := 0x02060e63.
Lemma F_144ec8 : fetch_word Asan.M.loaded_segments (0x144f0c : word) = Some W_144ec8.
Proof. vm_refl. Qed.
Lemma D_144ec8 : decode_any W_144ec8 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ecc : bv 32 := 0x00158713.
Lemma F_144ecc : fetch_word Asan.M.loaded_segments (0x144f10 : word) = Some W_144ecc.
Proof. vm_refl. Qed.
Lemma D_144ecc : decode_any W_144ecc = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ed0 : bv 32 := 0x00100793.
Lemma F_144ed0 : fetch_word Asan.M.loaded_segments (0x144f14 : word) = Some W_144ed0.
Proof. vm_refl. Qed.
Lemma D_144ed0 : decode_any W_144ed0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ed4 : bv 32 := 0x00050693.
Lemma F_144ed4 : fetch_word Asan.M.loaded_segments (0x144f18 : word) = Some W_144ed4.
Proof. vm_refl. Qed.
Lemma D_144ed4 : decode_any W_144ed4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ed8 : bv 32 := 0x0005c883.
Lemma F_144ed8 : fetch_word Asan.M.loaded_segments (0x144f1c : word) = Some W_144ed8.
Proof. vm_refl. Qed.
Lemma D_144ed8 : decode_any W_144ed8 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144edc : bv 32 := 0x00060813.
Lemma F_144edc : fetch_word Asan.M.loaded_segments (0x144f20 : word) = Some W_144edc.
Proof. vm_refl. Qed.
Lemma D_144edc : decode_any W_144edc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ee0 : bv 32 := 0x00158593.
Lemma F_144ee0 : fetch_word Asan.M.loaded_segments (0x144f24 : word) = Some W_144ee0.
Proof. vm_refl. Qed.
Lemma D_144ee0 : decode_any W_144ee0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ee4 : bv 32 := 0x00377293.
Lemma F_144ee4 : fetch_word Asan.M.loaded_segments (0x144f28 : word) = Some W_144ee4.
Proof. vm_refl. Qed.
Lemma D_144ee4 : decode_any W_144ee4 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ee8 : bv 32 := 0x01168023.
Lemma F_144ee8 : fetch_word Asan.M.loaded_segments (0x144f2c : word) = Some W_144ee8.
Proof. vm_refl. Qed.
Lemma D_144ee8 : decode_any W_144ee8 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144eec : bv 32 := 0x00168693.
Lemma F_144eec : fetch_word Asan.M.loaded_segments (0x144f30 : word) = Some W_144eec.
Proof. vm_refl. Qed.
Lemma D_144eec : decode_any W_144eec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ef0 : bv 32 := 0xfff60613.
Lemma F_144ef0 : fetch_word Asan.M.loaded_segments (0x144f34 : word) = Some W_144ef0.
Proof. vm_refl. Qed.
Lemma D_144ef0 : decode_any W_144ef0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ef4 : bv 32 := 0x00028a63.
Lemma F_144ef4 : fetch_word Asan.M.loaded_segments (0x144f38 : word) = Some W_144ef4.
Proof. vm_refl. Qed.
Lemma D_144ef4 : decode_any W_144ef4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ef8 : bv 32 := 0x00170713.
Lemma F_144ef8 : fetch_word Asan.M.loaded_segments (0x144f3c : word) = Some W_144ef8.
Proof. vm_refl. Qed.
Lemma D_144ef8 : decode_any W_144ef8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144efc : bv 32 := 0xfcf81ee3.
Lemma F_144efc : fetch_word Asan.M.loaded_segments (0x144f40 : word) = Some W_144efc.
Proof. vm_refl. Qed.
Lemma D_144efc : decode_any W_144efc = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f00 : bv 32 := 0x0080006f.
Lemma F_144f00 : fetch_word Asan.M.loaded_segments (0x144f44 : word) = Some W_144f00.
Proof. vm_refl. Qed.
Lemma D_144f00 : decode_any W_144f00 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f04 : bv 32 := 0x00050693.
Lemma F_144f04 : fetch_word Asan.M.loaded_segments (0x144f48 : word) = Some W_144f04.
Proof. vm_refl. Qed.
Lemma D_144f04 : decode_any W_144f04 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f08 : bv 32 := 0x0036f793.
Lemma F_144f08 : fetch_word Asan.M.loaded_segments (0x144f4c : word) = Some W_144f08.
Proof. vm_refl. Qed.
Lemma D_144f08 : decode_any W_144f08 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f0c : bv 32 := 0x0c078a63.
Lemma F_144f0c : fetch_word Asan.M.loaded_segments (0x144f50 : word) = Some W_144f0c.
Proof. vm_refl. Qed.
Lemma D_144f0c : decode_any W_144f0c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f10 : bv 32 := 0x02000713.
Lemma F_144f10 : fetch_word Asan.M.loaded_segments (0x144f54 : word) = Some W_144f10.
Proof. vm_refl. Qed.
Lemma D_144f10 : decode_any W_144f10 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f14 : bv 32 := 0x02e67063.
Lemma F_144f14 : fetch_word Asan.M.loaded_segments (0x144f58 : word) = Some W_144f14.
Proof. vm_refl. Qed.
Lemma D_144f14 : decode_any W_144f14 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f18 : bv 32 := 0x01000713.
Lemma F_144f18 : fetch_word Asan.M.loaded_segments (0x144f5c : word) = Some W_144f18.
Proof. vm_refl. Qed.
Lemma D_144f18 : decode_any W_144f18 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f1c : bv 32 := 0x24e67863.
Lemma F_144f1c : fetch_word Asan.M.loaded_segments (0x144f60 : word) = Some W_144f1c.
Proof. vm_refl. Qed.
Lemma D_144f1c : decode_any W_144f1c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f20 : bv 32 := 0x00867713.
Lemma F_144f20 : fetch_word Asan.M.loaded_segments (0x144f64 : word) = Some W_144f20.
Proof. vm_refl. Qed.
Lemma D_144f20 : decode_any W_144f20 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f24 : bv 32 := 0x2c071e63.
Lemma F_144f24 : fetch_word Asan.M.loaded_segments (0x144f68 : word) = Some W_144f24.
Proof. vm_refl. Qed.
Lemma D_144f24 : decode_any W_144f24 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f28 : bv 32 := 0x00467713.
Lemma F_144f28 : fetch_word Asan.M.loaded_segments (0x144f6c : word) = Some W_144f28.
Proof. vm_refl. Qed.
Lemma D_144f28 : decode_any W_144f28 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f2c : bv 32 := 0x32071463.
Lemma F_144f2c : fetch_word Asan.M.loaded_segments (0x144f70 : word) = Some W_144f2c.
Proof. vm_refl. Qed.
Lemma D_144f2c : decode_any W_144f2c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f30 : bv 32 := 0x3500006f.
Lemma F_144f30 : fetch_word Asan.M.loaded_segments (0x144f74 : word) = Some W_144f30.
Proof. vm_refl. Qed.
Lemma D_144f30 : decode_any W_144f30 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f34 : bv 32 := 0x0005a703.
Lemma F_144f34 : fetch_word Asan.M.loaded_segments (0x144f78 : word) = Some W_144f34.
Proof. vm_refl. Qed.
Lemma D_144f34 : decode_any W_144f34 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f38 : bv 32 := 0x00300813.
Lemma F_144f38 : fetch_word Asan.M.loaded_segments (0x144f7c : word) = Some W_144f38.
Proof. vm_refl. Qed.
Lemma D_144f38 : decode_any W_144f38 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f3c : bv 32 := 0x11078e63.
Lemma F_144f3c : fetch_word Asan.M.loaded_segments (0x144f80 : word) = Some W_144f3c.
Proof. vm_refl. Qed.
Lemma D_144f3c : decode_any W_144f3c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f40 : bv 32 := 0x00200813.
Lemma F_144f40 : fetch_word Asan.M.loaded_segments (0x144f84 : word) = Some W_144f40.
Proof. vm_refl. Qed.
Lemma D_144f40 : decode_any W_144f40 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f44 : bv 32 := 0x19079c63.
Lemma F_144f44 : fetch_word Asan.M.loaded_segments (0x144f88 : word) = Some W_144f44.
Proof. vm_refl. Qed.
Lemma D_144f44 : decode_any W_144f44 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f48 : bv 32 := 0x00875793.
Lemma F_144f48 : fetch_word Asan.M.loaded_segments (0x144f8c : word) = Some W_144f48.
Proof. vm_refl. Qed.
Lemma D_144f48 : decode_any W_144f48 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f4c : bv 32 := 0xffe60613.
Lemma F_144f4c : fetch_word Asan.M.loaded_segments (0x144f90 : word) = Some W_144f4c.
Proof. vm_refl. Qed.
Lemma D_144f4c : decode_any W_144f4c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f50 : bv 32 := 0x00e68023.
Lemma F_144f50 : fetch_word Asan.M.loaded_segments (0x144f94 : word) = Some W_144f50.
Proof. vm_refl. Qed.
Lemma D_144f50 : decode_any W_144f50 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f54 : bv 32 := 0x00f680a3.
Lemma F_144f54 : fetch_word Asan.M.loaded_segments (0x144f98 : word) = Some W_144f54.
Proof. vm_refl. Qed.
Lemma D_144f54 : decode_any W_144f54 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f58 : bv 32 := 0x00268693.
Lemma F_144f58 : fetch_word Asan.M.loaded_segments (0x144f9c : word) = Some W_144f58.
Proof. vm_refl. Qed.
Lemma D_144f58 : decode_any W_144f58 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f5c : bv 32 := 0x01058593.
Lemma F_144f5c : fetch_word Asan.M.loaded_segments (0x144fa0 : word) = Some W_144f5c.
Proof. vm_refl. Qed.
Lemma D_144f5c : decode_any W_144f5c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f60 : bv 32 := 0x01100793.
Lemma F_144f60 : fetch_word Asan.M.loaded_segments (0x144fa4 : word) = Some W_144f60.
Proof. vm_refl. Qed.
Lemma D_144f60 : decode_any W_144f60 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f64 : bv 32 := 0x0107581b.
Lemma F_144f64 : fetch_word Asan.M.loaded_segments (0x144fa8 : word) = Some W_144f64.
Proof. vm_refl. Qed.
Lemma D_144f64 : decode_any W_144f64 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f68 : bv 32 := 0xff45a883.
Lemma F_144f68 : fetch_word Asan.M.loaded_segments (0x144fac : word) = Some W_144f68.
Proof. vm_refl. Qed.
Lemma D_144f68 : decode_any W_144f68 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f6c : bv 32 := 0xff85a283.
Lemma F_144f6c : fetch_word Asan.M.loaded_segments (0x144fb0 : word) = Some W_144f6c.
Proof. vm_refl. Qed.
Lemma D_144f6c : decode_any W_144f6c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f70 : bv 32 := 0xffc5a303.
Lemma F_144f70 : fetch_word Asan.M.loaded_segments (0x144fb4 : word) = Some W_144f70.
Proof. vm_refl. Qed.
Lemma D_144f70 : decode_any W_144f70 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f74 : bv 32 := 0x0005a703.
Lemma F_144f74 : fetch_word Asan.M.loaded_segments (0x144fb8 : word) = Some W_144f74.
Proof. vm_refl. Qed.
Lemma D_144f74 : decode_any W_144f74 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f78 : bv 32 := 0x01089393.
Lemma F_144f78 : fetch_word Asan.M.loaded_segments (0x144fbc : word) = Some W_144f78.
Proof. vm_refl. Qed.
Lemma D_144f78 : decode_any W_144f78 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f7c : bv 32 := 0x0108d89b.
Lemma F_144f7c : fetch_word Asan.M.loaded_segments (0x144fc0 : word) = Some W_144f7c.
Proof. vm_refl. Qed.
Lemma D_144f7c : decode_any W_144f7c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f80 : bv 32 := 0x0103e833.
Lemma F_144f80 : fetch_word Asan.M.loaded_segments (0x144fc4 : word) = Some W_144f80.
Proof. vm_refl. Qed.
Lemma D_144f80 : decode_any W_144f80 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f84 : bv 32 := 0x01029393.
Lemma F_144f84 : fetch_word Asan.M.loaded_segments (0x144fc8 : word) = Some W_144f84.
Proof. vm_refl. Qed.
Lemma D_144f84 : decode_any W_144f84 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f88 : bv 32 := 0x0102d29b.
Lemma F_144f88 : fetch_word Asan.M.loaded_segments (0x144fcc : word) = Some W_144f88.
Proof. vm_refl. Qed.
Lemma D_144f88 : decode_any W_144f88 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f8c : bv 32 := 0x0113e8b3.
Lemma F_144f8c : fetch_word Asan.M.loaded_segments (0x144fd0 : word) = Some W_144f8c.
Proof. vm_refl. Qed.
Lemma D_144f8c : decode_any W_144f8c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f90 : bv 32 := 0x01031393.
Lemma F_144f90 : fetch_word Asan.M.loaded_segments (0x144fd4 : word) = Some W_144f90.
Proof. vm_refl. Qed.
Lemma D_144f90 : decode_any W_144f90 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f94 : bv 32 := 0x0103531b.
Lemma F_144f94 : fetch_word Asan.M.loaded_segments (0x144fd8 : word) = Some W_144f94.
Proof. vm_refl. Qed.
Lemma D_144f94 : decode_any W_144f94 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f98 : bv 32 := 0x0053e2b3.
Lemma F_144f98 : fetch_word Asan.M.loaded_segments (0x144fdc : word) = Some W_144f98.
Proof. vm_refl. Qed.
Lemma D_144f98 : decode_any W_144f98 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_144f9c : bv 32 := 0x01071393.
Lemma F_144f9c : fetch_word Asan.M.loaded_segments (0x144fe0 : word) = Some W_144f9c.
Proof. vm_refl. Qed.
Lemma D_144f9c : decode_any W_144f9c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fa0 : bv 32 := 0x0063e333.
Lemma F_144fa0 : fetch_word Asan.M.loaded_segments (0x144fe4 : word) = Some W_144fa0.
Proof. vm_refl. Qed.
Lemma D_144fa0 : decode_any W_144fa0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fa4 : bv 32 := 0xff060613.
Lemma F_144fa4 : fetch_word Asan.M.loaded_segments (0x144fe8 : word) = Some W_144fa4.
Proof. vm_refl. Qed.
Lemma D_144fa4 : decode_any W_144fa4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fa8 : bv 32 := 0x0106a023.
Lemma F_144fa8 : fetch_word Asan.M.loaded_segments (0x144fec : word) = Some W_144fa8.
Proof. vm_refl. Qed.
Lemma D_144fa8 : decode_any W_144fa8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fac : bv 32 := 0x0116a223.
Lemma F_144fac : fetch_word Asan.M.loaded_segments (0x144ff0 : word) = Some W_144fac.
Proof. vm_refl. Qed.
Lemma D_144fac : decode_any W_144fac = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fb0 : bv 32 := 0x0056a423.
Lemma F_144fb0 : fetch_word Asan.M.loaded_segments (0x144ff4 : word) = Some W_144fb0.
Proof. vm_refl. Qed.
Lemma D_144fb0 : decode_any W_144fb0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fb4 : bv 32 := 0x0066a623.
Lemma F_144fb4 : fetch_word Asan.M.loaded_segments (0x144ff8 : word) = Some W_144fb4.
Proof. vm_refl. Qed.
Lemma D_144fb4 : decode_any W_144fb4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fb8 : bv 32 := 0x01068693.
Lemma F_144fb8 : fetch_word Asan.M.loaded_segments (0x144ffc : word) = Some W_144fb8.
Proof. vm_refl. Qed.
Lemma D_144fb8 : decode_any W_144fb8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fbc : bv 32 := 0x01058593.
Lemma F_144fbc : fetch_word Asan.M.loaded_segments (0x145000 : word) = Some W_144fbc.
Proof. vm_refl. Qed.
Lemma D_144fbc : decode_any W_144fbc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fc0 : bv 32 := 0xfac7e2e3.
Lemma F_144fc0 : fetch_word Asan.M.loaded_segments (0x145004 : word) = Some W_144fc0.
Proof. vm_refl. Qed.
Lemma D_144fc0 : decode_any W_144fc0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fc4 : bv 32 := 0xff258593.
Lemma F_144fc4 : fetch_word Asan.M.loaded_segments (0x145008 : word) = Some W_144fc4.
Proof. vm_refl. Qed.
Lemma D_144fc4 : decode_any W_144fc4 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fc8 : bv 32 := 0x01000713.
Lemma F_144fc8 : fetch_word Asan.M.loaded_segments (0x14500c : word) = Some W_144fc8.
Proof. vm_refl. Qed.
Lemma D_144fc8 : decode_any W_144fc8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fcc : bv 32 := 0xf4e66ae3.
Lemma F_144fcc : fetch_word Asan.M.loaded_segments (0x145010 : word) = Some W_144fcc.
Proof. vm_refl. Qed.
Lemma D_144fcc : decode_any W_144fcc = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fd0 : bv 32 := 0x19c0006f.
Lemma F_144fd0 : fetch_word Asan.M.loaded_segments (0x145014 : word) = Some W_144fd0.
Proof. vm_refl. Qed.
Lemma D_144fd0 : decode_any W_144fd0 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fd4 : bv 32 := 0x00050693.
Lemma F_144fd4 : fetch_word Asan.M.loaded_segments (0x145018 : word) = Some W_144fd4.
Proof. vm_refl. Qed.
Lemma D_144fd4 : decode_any W_144fd4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fd8 : bv 32 := 0x00357793.
Lemma F_144fd8 : fetch_word Asan.M.loaded_segments (0x14501c : word) = Some W_144fd8.
Proof. vm_refl. Qed.
Lemma D_144fd8 : decode_any W_144fd8 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fdc : bv 32 := 0xf2079ae3.
Lemma F_144fdc : fetch_word Asan.M.loaded_segments (0x145020 : word) = Some W_144fdc.
Proof. vm_refl. Qed.
Lemma D_144fdc : decode_any W_144fdc = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fe0 : bv 32 := 0x01000713.
Lemma F_144fe0 : fetch_word Asan.M.loaded_segments (0x145024 : word) = Some W_144fe0.
Proof. vm_refl. Qed.
Lemma D_144fe0 : decode_any W_144fe0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fe4 : bv 32 := 0x02e66c63.
Lemma F_144fe4 : fetch_word Asan.M.loaded_segments (0x145028 : word) = Some W_144fe4.
Proof. vm_refl. Qed.
Lemma D_144fe4 : decode_any W_144fe4 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fe8 : bv 32 := 0x00f00713.
Lemma F_144fe8 : fetch_word Asan.M.loaded_segments (0x14502c : word) = Some W_144fe8.
Proof. vm_refl. Qed.
Lemma D_144fe8 : decode_any W_144fe8 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_144fec : bv 32 := 0x0005a783.
Lemma F_144fec : fetch_word Asan.M.loaded_segments (0x145030 : word) = Some W_144fec.
Proof. vm_refl. Qed.
Lemma D_144fec : decode_any W_144fec = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ff0 : bv 32 := 0x0045a803.
Lemma F_144ff0 : fetch_word Asan.M.loaded_segments (0x145034 : word) = Some W_144ff0.
Proof. vm_refl. Qed.
Lemma D_144ff0 : decode_any W_144ff0 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ff4 : bv 32 := 0x0085a883.
Lemma F_144ff4 : fetch_word Asan.M.loaded_segments (0x145038 : word) = Some W_144ff4.
Proof. vm_refl. Qed.
Lemma D_144ff4 : decode_any W_144ff4 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ff8 : bv 32 := 0x00c5a283.
Lemma F_144ff8 : fetch_word Asan.M.loaded_segments (0x14503c : word) = Some W_144ff8.
Proof. vm_refl. Qed.
Lemma D_144ff8 : decode_any W_144ff8 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_144ffc : bv 32 := 0x01058593.
Lemma F_144ffc : fetch_word Asan.M.loaded_segments (0x145040 : word) = Some W_144ffc.
Proof. vm_refl. Qed.
Lemma D_144ffc : decode_any W_144ffc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

