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

Definition W_7f028 : bv 32 := 0x22061663.
Lemma F_7f028 : fetch_word Asan.M.loaded_segments (0x7f078 : word) = Some W_7f028.
Proof. vm_refl. Qed.
Lemma D_7f028 : decode_any W_7f028 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f02c : bv 32 := 0xee9ff06f.
Lemma F_7f02c : fetch_word Asan.M.loaded_segments (0x7f07c : word) = Some W_7f02c.
Proof. vm_refl. Qed.
Lemma D_7f02c : decode_any W_7f02c = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f174 : bv 32 := 0x02061e63.
Lemma F_7f174 : fetch_word Asan.M.loaded_segments (0x7f1c4 : word) = Some W_7f174.
Proof. vm_refl. Qed.
Lemma D_7f174 : decode_any W_7f174 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f178 : bv 32 := 0xd55ff06f.
Lemma F_7f178 : fetch_word Asan.M.loaded_segments (0x7f1c8 : word) = Some W_7f178.
Proof. vm_refl. Qed.
Lemma D_7f178 : decode_any W_7f178 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f17c : bv 32 := 0x00070783.
Lemma F_7f17c : fetch_word Asan.M.loaded_segments (0x7f1cc : word) = Some W_7f17c.
Proof. vm_refl. Qed.
Lemma D_7f17c : decode_any W_7f17c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f180 : bv 32 := 0x007af813.
Lemma F_7f180 : fetch_word Asan.M.loaded_segments (0x7f1d0 : word) = Some W_7f180.
Proof. vm_refl. Qed.
Lemma D_7f180 : decode_any W_7f180 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f184 : bv 32 := 0x00f038b3.
Lemma F_7f184 : fetch_word Asan.M.loaded_segments (0x7f1d4 : word) = Some W_7f184.
Proof. vm_refl. Qed.
Lemma D_7f184 : decode_any W_7f184 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f188 : bv 32 := 0x00f827b3.
Lemma F_7f188 : fetch_word Asan.M.loaded_segments (0x7f1d8 : word) = Some W_7f188.
Proof. vm_refl. Qed.
Lemma D_7f188 : decode_any W_7f188 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f18c : bv 32 := 0x0017c793.
Lemma F_7f18c : fetch_word Asan.M.loaded_segments (0x7f1dc : word) = Some W_7f18c.
Proof. vm_refl. Qed.
Lemma D_7f18c : decode_any W_7f18c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f190 : bv 32 := 0x00f8f7b3.
Lemma F_7f190 : fetch_word Asan.M.loaded_segments (0x7f1e0 : word) = Some W_7f190.
Proof. vm_refl. Qed.
Lemma D_7f190 : decode_any W_7f190 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f194 : bv 32 := 0x00e6fa63.
Lemma F_7f194 : fetch_word Asan.M.loaded_segments (0x7f1e4 : word) = Some W_7f194.
Proof. vm_refl. Qed.
Lemma D_7f194 : decode_any W_7f194 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f198 : bv 32 := 0x0006c803.
Lemma F_7f198 : fetch_word Asan.M.loaded_segments (0x7f1e8 : word) = Some W_7f198.
Proof. vm_refl. Qed.
Lemma D_7f198 : decode_any W_7f198 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f19c : bv 32 := 0x00168693.
Lemma F_7f19c : fetch_word Asan.M.loaded_segments (0x7f1ec : word) = Some W_7f19c.
Proof. vm_refl. Qed.
Lemma D_7f19c : decode_any W_7f19c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a0 : bv 32 := 0x00f867b3.
Lemma F_7f1a0 : fetch_word Asan.M.loaded_segments (0x7f1f0 : word) = Some W_7f1a0.
Proof. vm_refl. Qed.
Lemma D_7f1a0 : decode_any W_7f1a0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a4 : bv 32 := 0xfee69ae3.
Lemma F_7f1a4 : fetch_word Asan.M.loaded_segments (0x7f1f4 : word) = Some W_7f1a4.
Proof. vm_refl. Qed.
Lemma D_7f1a4 : decode_any W_7f1a4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a8 : bv 32 := 0x0ff7f693.
Lemma F_7f1a8 : fetch_word Asan.M.loaded_segments (0x7f1f8 : word) = Some W_7f1a8.
Proof. vm_refl. Qed.
Lemma D_7f1a8 : decode_any W_7f1a8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ac : bv 32 := 0xd20680e3.
Lemma F_7f1ac : fetch_word Asan.M.loaded_segments (0x7f1fc : word) = Some W_7f1ac.
Proof. vm_refl. Qed.
Lemma D_7f1ac : decode_any W_7f1ac = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b0 : bv 32 := 0x00050a93.
Lemma F_7f1b0 : fetch_word Asan.M.loaded_segments (0x7f200 : word) = Some W_7f1b0.
Proof. vm_refl. Qed.
Lemma D_7f1b0 : decode_any W_7f1b0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b4 : bv 32 := 0x00058513.
Lemma F_7f1b4 : fetch_word Asan.M.loaded_segments (0x7f204 : word) = Some W_7f1b4.
Proof. vm_refl. Qed.
Lemma D_7f1b4 : decode_any W_7f1b4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b8 : bv 32 := 0x00058b93.
Lemma F_7f1b8 : fetch_word Asan.M.loaded_segments (0x7f208 : word) = Some W_7f1b8.
Proof. vm_refl. Qed.
Lemma D_7f1b8 : decode_any W_7f1b8 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1bc : bv 32 := 0x00060593.
Lemma F_7f1bc : fetch_word Asan.M.loaded_segments (0x7f20c : word) = Some W_7f1bc.
Proof. vm_refl. Qed.
Lemma D_7f1bc : decode_any W_7f1bc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c0 : bv 32 := 0x00060493.
Lemma F_7f1c0 : fetch_word Asan.M.loaded_segments (0x7f210 : word) = Some W_7f1c0.
Proof. vm_refl. Qed.
Lemma D_7f1c0 : decode_any W_7f1c0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c4 : bv 32 := 0x48c030ef.
Lemma F_7f1c4 : fetch_word Asan.M.loaded_segments (0x7f214 : word) = Some W_7f1c4.
Proof. vm_refl. Qed.
Lemma D_7f1c4 : decode_any W_7f1c4 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c8 : bv 32 := 0x000b8593.
Lemma F_7f1c8 : fetch_word Asan.M.loaded_segments (0x7f218 : word) = Some W_7f1c8.
Proof. vm_refl. Qed.
Lemma D_7f1c8 : decode_any W_7f1c8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1cc : bv 32 := 0x00048613.
Lemma F_7f1cc : fetch_word Asan.M.loaded_segments (0x7f21c : word) = Some W_7f1cc.
Proof. vm_refl. Qed.
Lemma D_7f1cc : decode_any W_7f1cc = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d0 : bv 32 := 0x00050913.
Lemma F_7f1d0 : fetch_word Asan.M.loaded_segments (0x7f220 : word) = Some W_7f1d0.
Proof. vm_refl. Qed.
Lemma D_7f1d0 : decode_any W_7f1d0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d4 : bv 32 := 0x000a8513.
Lemma F_7f1d4 : fetch_word Asan.M.loaded_segments (0x7f224 : word) = Some W_7f1d4.
Proof. vm_refl. Qed.
Lemma D_7f1d4 : decode_any W_7f1d4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d8 : bv 32 := 0xce090ae3.
Lemma F_7f1d8 : fetch_word Asan.M.loaded_segments (0x7f228 : word) = Some W_7f1d8.
Proof. vm_refl. Qed.
Lemma D_7f1d8 : decode_any W_7f1d8 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f220 : bv 32 := 0x00070783.
Lemma F_7f220 : fetch_word Asan.M.loaded_segments (0x7f270 : word) = Some W_7f220.
Proof. vm_refl. Qed.
Lemma D_7f220 : decode_any W_7f220 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f224 : bv 32 := 0x0079f813.
Lemma F_7f224 : fetch_word Asan.M.loaded_segments (0x7f274 : word) = Some W_7f224.
Proof. vm_refl. Qed.
Lemma D_7f224 : decode_any W_7f224 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f228 : bv 32 := 0x00f038b3.
Lemma F_7f228 : fetch_word Asan.M.loaded_segments (0x7f278 : word) = Some W_7f228.
Proof. vm_refl. Qed.
Lemma D_7f228 : decode_any W_7f228 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f22c : bv 32 := 0x00f827b3.
Lemma F_7f22c : fetch_word Asan.M.loaded_segments (0x7f27c : word) = Some W_7f22c.
Proof. vm_refl. Qed.
Lemma D_7f22c : decode_any W_7f22c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f230 : bv 32 := 0x0017c793.
Lemma F_7f230 : fetch_word Asan.M.loaded_segments (0x7f280 : word) = Some W_7f230.
Proof. vm_refl. Qed.
Lemma D_7f230 : decode_any W_7f230 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f234 : bv 32 := 0x00f8f7b3.
Lemma F_7f234 : fetch_word Asan.M.loaded_segments (0x7f284 : word) = Some W_7f234.
Proof. vm_refl. Qed.
Lemma D_7f234 : decode_any W_7f234 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f238 : bv 32 := 0x00e6fa63.
Lemma F_7f238 : fetch_word Asan.M.loaded_segments (0x7f288 : word) = Some W_7f238.
Proof. vm_refl. Qed.
Lemma D_7f238 : decode_any W_7f238 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f23c : bv 32 := 0x0006c803.
Lemma F_7f23c : fetch_word Asan.M.loaded_segments (0x7f28c : word) = Some W_7f23c.
Proof. vm_refl. Qed.
Lemma D_7f23c : decode_any W_7f23c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f240 : bv 32 := 0x00168693.
Lemma F_7f240 : fetch_word Asan.M.loaded_segments (0x7f290 : word) = Some W_7f240.
Proof. vm_refl. Qed.
Lemma D_7f240 : decode_any W_7f240 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f244 : bv 32 := 0x00f867b3.
Lemma F_7f244 : fetch_word Asan.M.loaded_segments (0x7f294 : word) = Some W_7f244.
Proof. vm_refl. Qed.
Lemma D_7f244 : decode_any W_7f244 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f248 : bv 32 := 0xfee69ae3.
Lemma F_7f248 : fetch_word Asan.M.loaded_segments (0x7f298 : word) = Some W_7f248.
Proof. vm_refl. Qed.
Lemma D_7f248 : decode_any W_7f248 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f24c : bv 32 := 0x0ff7f693.
Lemma F_7f24c : fetch_word Asan.M.loaded_segments (0x7f29c : word) = Some W_7f24c.
Proof. vm_refl. Qed.
Lemma D_7f24c : decode_any W_7f24c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f250 : bv 32 := 0xcc0682e3.
Lemma F_7f250 : fetch_word Asan.M.loaded_segments (0x7f2a0 : word) = Some W_7f250.
Proof. vm_refl. Qed.
Lemma D_7f250 : decode_any W_7f250 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f254 : bv 32 := 0x00050493.
Lemma F_7f254 : fetch_word Asan.M.loaded_segments (0x7f2a4 : word) = Some W_7f254.
Proof. vm_refl. Qed.
Lemma D_7f254 : decode_any W_7f254 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f258 : bv 32 := 0x00058a93.
Lemma F_7f258 : fetch_word Asan.M.loaded_segments (0x7f2a8 : word) = Some W_7f258.
Proof. vm_refl. Qed.
Lemma D_7f258 : decode_any W_7f258 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f25c : bv 32 := 0x00060593.
Lemma F_7f25c : fetch_word Asan.M.loaded_segments (0x7f2ac : word) = Some W_7f25c.
Proof. vm_refl. Qed.
Lemma D_7f25c : decode_any W_7f25c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f260 : bv 32 := 0x00060913.
Lemma F_7f260 : fetch_word Asan.M.loaded_segments (0x7f2b0 : word) = Some W_7f260.
Proof. vm_refl. Qed.
Lemma D_7f260 : decode_any W_7f260 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f264 : bv 32 := 0x3ec030ef.
Lemma F_7f264 : fetch_word Asan.M.loaded_segments (0x7f2b4 : word) = Some W_7f264.
Proof. vm_refl. Qed.
Lemma D_7f264 : decode_any W_7f264 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f268 : bv 32 := 0x000a8593.
Lemma F_7f268 : fetch_word Asan.M.loaded_segments (0x7f2b8 : word) = Some W_7f268.
Proof. vm_refl. Qed.
Lemma D_7f268 : decode_any W_7f268 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f26c : bv 32 := 0x00090613.
Lemma F_7f26c : fetch_word Asan.M.loaded_segments (0x7f2bc : word) = Some W_7f26c.
Proof. vm_refl. Qed.
Lemma D_7f26c : decode_any W_7f26c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f270 : bv 32 := 0x00050993.
Lemma F_7f270 : fetch_word Asan.M.loaded_segments (0x7f2c0 : word) = Some W_7f270.
Proof. vm_refl. Qed.
Lemma D_7f270 : decode_any W_7f270 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f274 : bv 32 := 0x00048513.
Lemma F_7f274 : fetch_word Asan.M.loaded_segments (0x7f2c4 : word) = Some W_7f274.
Proof. vm_refl. Qed.
Lemma D_7f274 : decode_any W_7f274 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f278 : bv 32 := 0xc8098ee3.
Lemma F_7f278 : fetch_word Asan.M.loaded_segments (0x7f2c8 : word) = Some W_7f278.
Proof. vm_refl. Qed.
Lemma D_7f278 : decode_any W_7f278 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c0 : bv 32 := 0x81010113.
Lemma F_7f2c0 : fetch_word Asan.M.loaded_segments (0x7f310 : word) = Some W_7f2c0.
Proof. vm_refl. Qed.
Lemma D_7f2c0 : decode_any W_7f2c0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c4 : bv 32 := 0x7e113423.
Lemma F_7f2c4 : fetch_word Asan.M.loaded_segments (0x7f314 : word) = Some W_7f2c4.
Proof. vm_refl. Qed.
Lemma D_7f2c4 : decode_any W_7f2c4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c8 : bv 32 := 0x7e813023.
Lemma F_7f2c8 : fetch_word Asan.M.loaded_segments (0x7f318 : word) = Some W_7f2c8.
Proof. vm_refl. Qed.
Lemma D_7f2c8 : decode_any W_7f2c8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2cc : bv 32 := 0x7c913c23.
Lemma F_7f2cc : fetch_word Asan.M.loaded_segments (0x7f31c : word) = Some W_7f2cc.
Proof. vm_refl. Qed.
Lemma D_7f2cc : decode_any W_7f2cc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d0 : bv 32 := 0x7d213823.
Lemma F_7f2d0 : fetch_word Asan.M.loaded_segments (0x7f320 : word) = Some W_7f2d0.
Proof. vm_refl. Qed.
Lemma D_7f2d0 : decode_any W_7f2d0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d4 : bv 32 := 0x7d313423.
Lemma F_7f2d4 : fetch_word Asan.M.loaded_segments (0x7f324 : word) = Some W_7f2d4.
Proof. vm_refl. Qed.
Lemma D_7f2d4 : decode_any W_7f2d4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d8 : bv 32 := 0x7d413023.
Lemma F_7f2d8 : fetch_word Asan.M.loaded_segments (0x7f328 : word) = Some W_7f2d8.
Proof. vm_refl. Qed.
Lemma D_7f2d8 : decode_any W_7f2d8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2dc : bv 32 := 0x7b513c23.
Lemma F_7f2dc : fetch_word Asan.M.loaded_segments (0x7f32c : word) = Some W_7f2dc.
Proof. vm_refl. Qed.
Lemma D_7f2dc : decode_any W_7f2dc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e0 : bv 32 := 0x7f010413.
Lemma F_7f2e0 : fetch_word Asan.M.loaded_segments (0x7f330 : word) = Some W_7f2e0.
Proof. vm_refl. Qed.
Lemma D_7f2e0 : decode_any W_7f2e0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e4 : bv 32 := 0xfa010113.
Lemma F_7f2e4 : fetch_word Asan.M.loaded_segments (0x7f334 : word) = Some W_7f2e4.
Proof. vm_refl. Qed.
Lemma D_7f2e4 : decode_any W_7f2e4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e8 : bv 32 := 0x000d5697.
Lemma F_7f2e8 : fetch_word Asan.M.loaded_segments (0x7f338 : word) = Some W_7f2e8.
Proof. vm_refl. Qed.
Lemma D_7f2e8 : decode_any W_7f2e8 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ec : bv 32 := 0x9686b683.
Lemma F_7f2ec : fetch_word Asan.M.loaded_segments (0x7f33c : word) = Some W_7f2ec.
Proof. vm_refl. Qed.
Lemma D_7f2ec : decode_any W_7f2ec = Some (Load SZ8 true 13 13 2408, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f0 : bv 32 := 0x0006c683.
Lemma F_7f2f0 : fetch_word Asan.M.loaded_segments (0x7f340 : word) = Some W_7f2f0.
Proof. vm_refl. Qed.
Lemma D_7f2f0 : decode_any W_7f2f0 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f4 : bv 32 := 0x08068863.
Lemma F_7f2f4 : fetch_word Asan.M.loaded_segments (0x7f344 : word) = Some W_7f2f4.
Proof. vm_refl. Qed.
Lemma D_7f2f4 : decode_any W_7f2f4 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f8 : bv 32 := 0xfff54693.
Lemma F_7f2f8 : fetch_word Asan.M.loaded_segments (0x7f348 : word) = Some W_7f2f8.
Proof. vm_refl. Qed.
Lemma D_7f2f8 : decode_any W_7f2f8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2fc : bv 32 := 0x80040a13.
Lemma F_7f2fc : fetch_word Asan.M.loaded_segments (0x7f34c : word) = Some W_7f2fc.
Proof. vm_refl. Qed.
Lemma D_7f2fc : decode_any W_7f2fc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f300 : bv 32 := 0xfb0a0a13.
Lemma F_7f300 : fetch_word Asan.M.loaded_segments (0x7f350 : word) = Some W_7f300.
Proof. vm_refl. Qed.
Lemma D_7f300 : decode_any W_7f300 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f304 : bv 32 := 0x0cc6e663.
Lemma F_7f304 : fetch_word Asan.M.loaded_segments (0x7f354 : word) = Some W_7f304.
Proof. vm_refl. Qed.
Lemma D_7f304 : decode_any W_7f304 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f308 : bv 32 := 0xfbf60693.
Lemma F_7f308 : fetch_word Asan.M.loaded_segments (0x7f358 : word) = Some W_7f308.
Proof. vm_refl. Qed.
Lemma D_7f308 : decode_any W_7f308 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f30c : bv 32 := 0xfbf00713.
Lemma F_7f30c : fetch_word Asan.M.loaded_segments (0x7f35c : word) = Some W_7f30c.
Proof. vm_refl. Qed.
Lemma D_7f30c : decode_any W_7f30c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f310 : bv 32 := 0x14d77463.
Lemma F_7f310 : fetch_word Asan.M.loaded_segments (0x7f360 : word) = Some W_7f310.
Proof. vm_refl. Qed.
Lemma D_7f310 : decode_any W_7f310 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f314 : bv 32 := 0x000d4697.
Lemma F_7f314 : fetch_word Asan.M.loaded_segments (0x7f364 : word) = Some W_7f314.
Proof. vm_refl. Qed.
Lemma D_7f314 : decode_any W_7f314 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f318 : bv 32 := 0xdd46b683.
Lemma F_7f318 : fetch_word Asan.M.loaded_segments (0x7f368 : word) = Some W_7f318.
Proof. vm_refl. Qed.
Lemma D_7f318 : decode_any W_7f318 = Some (Load SZ8 true 13 13 3540, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f31c : bv 32 := 0x00c507b3.
Lemma F_7f31c : fetch_word Asan.M.loaded_segments (0x7f36c : word) = Some W_7f31c.
Proof. vm_refl. Qed.
Lemma D_7f31c : decode_any W_7f31c = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f320 : bv 32 := 0x0006b703.
Lemma F_7f320 : fetch_word Asan.M.loaded_segments (0x7f370 : word) = Some W_7f320.
Proof. vm_refl. Qed.
Lemma D_7f320 : decode_any W_7f320 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f324 : bv 32 := 0x00355693.
Lemma F_7f324 : fetch_word Asan.M.loaded_segments (0x7f374 : word) = Some W_7f324.
Proof. vm_refl. Qed.
Lemma D_7f324 : decode_any W_7f324 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f328 : bv 32 := 0xfff78793.
Lemma F_7f328 : fetch_word Asan.M.loaded_segments (0x7f378 : word) = Some W_7f328.
Proof. vm_refl. Qed.
Lemma D_7f328 : decode_any W_7f328 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f32c : bv 32 := 0x0037d813.
Lemma F_7f32c : fetch_word Asan.M.loaded_segments (0x7f37c : word) = Some W_7f32c.
Proof. vm_refl. Qed.
Lemma D_7f32c : decode_any W_7f32c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f330 : bv 32 := 0x00d706b3.
Lemma F_7f330 : fetch_word Asan.M.loaded_segments (0x7f380 : word) = Some W_7f330.
Proof. vm_refl. Qed.
Lemma D_7f330 : decode_any W_7f330 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f334 : bv 32 := 0x01070733.
Lemma F_7f334 : fetch_word Asan.M.loaded_segments (0x7f384 : word) = Some W_7f334.
Proof. vm_refl. Qed.
Lemma D_7f334 : decode_any W_7f334 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f338 : bv 32 := 0xff86f813.
Lemma F_7f338 : fetch_word Asan.M.loaded_segments (0x7f388 : word) = Some W_7f338.
Proof. vm_refl. Qed.
Lemma D_7f338 : decode_any W_7f338 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f33c : bv 32 := 0xff877893.
Lemma F_7f33c : fetch_word Asan.M.loaded_segments (0x7f38c : word) = Some W_7f33c.
Proof. vm_refl. Qed.
Lemma D_7f33c : decode_any W_7f33c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f340 : bv 32 := 0x00083803.
Lemma F_7f340 : fetch_word Asan.M.loaded_segments (0x7f390 : word) = Some W_7f340.
Proof. vm_refl. Qed.
Lemma D_7f340 : decode_any W_7f340 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f344 : bv 32 := 0x0008b883.
Lemma F_7f344 : fetch_word Asan.M.loaded_segments (0x7f394 : word) = Some W_7f344.
Proof. vm_refl. Qed.
Lemma D_7f344 : decode_any W_7f344 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f348 : bv 32 := 0x0108e833.
Lemma F_7f348 : fetch_word Asan.M.loaded_segments (0x7f398 : word) = Some W_7f348.
Proof. vm_refl. Qed.
Lemma D_7f348 : decode_any W_7f348 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f34c : bv 32 := 0x10081a63.
Lemma F_7f34c : fetch_word Asan.M.loaded_segments (0x7f39c : word) = Some W_7f34c.
Proof. vm_refl. Qed.
Lemma D_7f34c : decode_any W_7f34c = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f350 : bv 32 := 0x000d6697.
Lemma F_7f350 : fetch_word Asan.M.loaded_segments (0x7f3a0 : word) = Some W_7f350.
Proof. vm_refl. Qed.
Lemma D_7f350 : decode_any W_7f350 = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f354 : bv 32 := 0xdc06b683.
Lemma F_7f354 : fetch_word Asan.M.loaded_segments (0x7f3a4 : word) = Some W_7f354.
Proof. vm_refl. Qed.
Lemma D_7f354 : decode_any W_7f354 = Some (Load SZ8 true 13 13 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f358 : bv 32 := 0x000680e7.
Lemma F_7f358 : fetch_word Asan.M.loaded_segments (0x7f3a8 : word) = Some W_7f358.
Proof. vm_refl. Qed.
Lemma D_7f358 : decode_any W_7f358 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f35c : bv 32 := 0x06010113.
Lemma F_7f35c : fetch_word Asan.M.loaded_segments (0x7f3ac : word) = Some W_7f35c.
Proof. vm_refl. Qed.
Lemma D_7f35c : decode_any W_7f35c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f360 : bv 32 := 0x7e813083.
Lemma F_7f360 : fetch_word Asan.M.loaded_segments (0x7f3b0 : word) = Some W_7f360.
Proof. vm_refl. Qed.
Lemma D_7f360 : decode_any W_7f360 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f364 : bv 32 := 0x7e013403.
Lemma F_7f364 : fetch_word Asan.M.loaded_segments (0x7f3b4 : word) = Some W_7f364.
Proof. vm_refl. Qed.
Lemma D_7f364 : decode_any W_7f364 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f368 : bv 32 := 0x7d813483.
Lemma F_7f368 : fetch_word Asan.M.loaded_segments (0x7f3b8 : word) = Some W_7f368.
Proof. vm_refl. Qed.
Lemma D_7f368 : decode_any W_7f368 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f36c : bv 32 := 0x7d013903.
Lemma F_7f36c : fetch_word Asan.M.loaded_segments (0x7f3bc : word) = Some W_7f36c.
Proof. vm_refl. Qed.
Lemma D_7f36c : decode_any W_7f36c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f370 : bv 32 := 0x7c813983.
Lemma F_7f370 : fetch_word Asan.M.loaded_segments (0x7f3c0 : word) = Some W_7f370.
Proof. vm_refl. Qed.
Lemma D_7f370 : decode_any W_7f370 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f374 : bv 32 := 0x7c013a03.
Lemma F_7f374 : fetch_word Asan.M.loaded_segments (0x7f3c4 : word) = Some W_7f374.
Proof. vm_refl. Qed.
Lemma D_7f374 : decode_any W_7f374 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f378 : bv 32 := 0x7b813a83.
Lemma F_7f378 : fetch_word Asan.M.loaded_segments (0x7f3c8 : word) = Some W_7f378.
Proof. vm_refl. Qed.
Lemma D_7f378 : decode_any W_7f378 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f37c : bv 32 := 0x7f010113.
Lemma F_7f37c : fetch_word Asan.M.loaded_segments (0x7f3cc : word) = Some W_7f37c.
Proof. vm_refl. Qed.
Lemma D_7f37c : decode_any W_7f37c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f380 : bv 32 := 0x00008067.
Lemma F_7f380 : fetch_word Asan.M.loaded_segments (0x7f3d0 : word) = Some W_7f380.
Proof. vm_refl. Qed.
Lemma D_7f380 : decode_any W_7f380 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f458 : bv 32 := 0x02061e63.
Lemma F_7f458 : fetch_word Asan.M.loaded_segments (0x7f4a8 : word) = Some W_7f458.
Proof. vm_refl. Qed.
Lemma D_7f458 : decode_any W_7f458 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f45c : bv 32 := 0xef5ff06f.
Lemma F_7f45c : fetch_word Asan.M.loaded_segments (0x7f4ac : word) = Some W_7f45c.
Proof. vm_refl. Qed.
Lemma D_7f45c : decode_any W_7f45c = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f460 : bv 32 := 0x00070803.
Lemma F_7f460 : fetch_word Asan.M.loaded_segments (0x7f4b0 : word) = Some W_7f460.
Proof. vm_refl. Qed.
Lemma D_7f460 : decode_any W_7f460 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f464 : bv 32 := 0x0077f793.
Lemma F_7f464 : fetch_word Asan.M.loaded_segments (0x7f4b4 : word) = Some W_7f464.
Proof. vm_refl. Qed.
Lemma D_7f464 : decode_any W_7f464 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f468 : bv 32 := 0x010038b3.
Lemma F_7f468 : fetch_word Asan.M.loaded_segments (0x7f4b8 : word) = Some W_7f468.
Proof. vm_refl. Qed.
Lemma D_7f468 : decode_any W_7f468 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f46c : bv 32 := 0x0107a7b3.
Lemma F_7f46c : fetch_word Asan.M.loaded_segments (0x7f4bc : word) = Some W_7f46c.
Proof. vm_refl. Qed.
Lemma D_7f46c : decode_any W_7f46c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f470 : bv 32 := 0x0017c793.
Lemma F_7f470 : fetch_word Asan.M.loaded_segments (0x7f4c0 : word) = Some W_7f470.
Proof. vm_refl. Qed.
Lemma D_7f470 : decode_any W_7f470 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f474 : bv 32 := 0x00f8f7b3.
Lemma F_7f474 : fetch_word Asan.M.loaded_segments (0x7f4c4 : word) = Some W_7f474.
Proof. vm_refl. Qed.
Lemma D_7f474 : decode_any W_7f474 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f478 : bv 32 := 0x00e6fa63.
Lemma F_7f478 : fetch_word Asan.M.loaded_segments (0x7f4c8 : word) = Some W_7f478.
Proof. vm_refl. Qed.
Lemma D_7f478 : decode_any W_7f478 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f47c : bv 32 := 0x0006c803.
Lemma F_7f47c : fetch_word Asan.M.loaded_segments (0x7f4cc : word) = Some W_7f47c.
Proof. vm_refl. Qed.
Lemma D_7f47c : decode_any W_7f47c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f480 : bv 32 := 0x00168693.
Lemma F_7f480 : fetch_word Asan.M.loaded_segments (0x7f4d0 : word) = Some W_7f480.
Proof. vm_refl. Qed.
Lemma D_7f480 : decode_any W_7f480 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f484 : bv 32 := 0x00f867b3.
Lemma F_7f484 : fetch_word Asan.M.loaded_segments (0x7f4d4 : word) = Some W_7f484.
Proof. vm_refl. Qed.
Lemma D_7f484 : decode_any W_7f484 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f488 : bv 32 := 0xfee69ae3.
Lemma F_7f488 : fetch_word Asan.M.loaded_segments (0x7f4d8 : word) = Some W_7f488.
Proof. vm_refl. Qed.
Lemma D_7f488 : decode_any W_7f488 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f48c : bv 32 := 0x0ff7f693.
Lemma F_7f48c : fetch_word Asan.M.loaded_segments (0x7f4dc : word) = Some W_7f48c.
Proof. vm_refl. Qed.
Lemma D_7f48c : decode_any W_7f48c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f490 : bv 32 := 0xec0680e3.
Lemma F_7f490 : fetch_word Asan.M.loaded_segments (0x7f4e0 : word) = Some W_7f490.
Proof. vm_refl. Qed.
Lemma D_7f490 : decode_any W_7f490 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f494 : bv 32 := 0x00050493.
Lemma F_7f494 : fetch_word Asan.M.loaded_segments (0x7f4e4 : word) = Some W_7f494.
Proof. vm_refl. Qed.
Lemma D_7f494 : decode_any W_7f494 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f498 : bv 32 := 0x00058a93.
Lemma F_7f498 : fetch_word Asan.M.loaded_segments (0x7f4e8 : word) = Some W_7f498.
Proof. vm_refl. Qed.
Lemma D_7f498 : decode_any W_7f498 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f49c : bv 32 := 0x00060593.
Lemma F_7f49c : fetch_word Asan.M.loaded_segments (0x7f4ec : word) = Some W_7f49c.
Proof. vm_refl. Qed.
Lemma D_7f49c : decode_any W_7f49c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a0 : bv 32 := 0x00060913.
Lemma F_7f4a0 : fetch_word Asan.M.loaded_segments (0x7f4f0 : word) = Some W_7f4a0.
Proof. vm_refl. Qed.
Lemma D_7f4a0 : decode_any W_7f4a0 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a4 : bv 32 := 0x1ac030ef.
Lemma F_7f4a4 : fetch_word Asan.M.loaded_segments (0x7f4f4 : word) = Some W_7f4a4.
Proof. vm_refl. Qed.
Lemma D_7f4a4 : decode_any W_7f4a4 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a8 : bv 32 := 0x000a8593.
Lemma F_7f4a8 : fetch_word Asan.M.loaded_segments (0x7f4f8 : word) = Some W_7f4a8.
Proof. vm_refl. Qed.
Lemma D_7f4a8 : decode_any W_7f4a8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4ac : bv 32 := 0x00090613.
Lemma F_7f4ac : fetch_word Asan.M.loaded_segments (0x7f4fc : word) = Some W_7f4ac.
Proof. vm_refl. Qed.
Lemma D_7f4ac : decode_any W_7f4ac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b0 : bv 32 := 0x00050993.
Lemma F_7f4b0 : fetch_word Asan.M.loaded_segments (0x7f500 : word) = Some W_7f4b0.
Proof. vm_refl. Qed.
Lemma D_7f4b0 : decode_any W_7f4b0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b4 : bv 32 := 0x00048513.
Lemma F_7f4b4 : fetch_word Asan.M.loaded_segments (0x7f504 : word) = Some W_7f4b4.
Proof. vm_refl. Qed.
Lemma D_7f4b4 : decode_any W_7f4b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b8 : bv 32 := 0xe8098ce3.
Lemma F_7f4b8 : fetch_word Asan.M.loaded_segments (0x7f508 : word) = Some W_7f4b8.
Proof. vm_refl. Qed.
Lemma D_7f4b8 : decode_any W_7f4b8 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f500 : bv 32 := 0x81010113.
Lemma F_7f500 : fetch_word Asan.M.loaded_segments (0x7f550 : word) = Some W_7f500.
Proof. vm_refl. Qed.
Lemma D_7f500 : decode_any W_7f500 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f504 : bv 32 := 0x7e113423.
Lemma F_7f504 : fetch_word Asan.M.loaded_segments (0x7f554 : word) = Some W_7f504.
Proof. vm_refl. Qed.
Lemma D_7f504 : decode_any W_7f504 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f508 : bv 32 := 0x7e813023.
Lemma F_7f508 : fetch_word Asan.M.loaded_segments (0x7f558 : word) = Some W_7f508.
Proof. vm_refl. Qed.
Lemma D_7f508 : decode_any W_7f508 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f50c : bv 32 := 0x7c913c23.
Lemma F_7f50c : fetch_word Asan.M.loaded_segments (0x7f55c : word) = Some W_7f50c.
Proof. vm_refl. Qed.
Lemma D_7f50c : decode_any W_7f50c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f510 : bv 32 := 0x7d213823.
Lemma F_7f510 : fetch_word Asan.M.loaded_segments (0x7f560 : word) = Some W_7f510.
Proof. vm_refl. Qed.
Lemma D_7f510 : decode_any W_7f510 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f514 : bv 32 := 0x7d313423.
Lemma F_7f514 : fetch_word Asan.M.loaded_segments (0x7f564 : word) = Some W_7f514.
Proof. vm_refl. Qed.
Lemma D_7f514 : decode_any W_7f514 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f518 : bv 32 := 0x7d413023.
Lemma F_7f518 : fetch_word Asan.M.loaded_segments (0x7f568 : word) = Some W_7f518.
Proof. vm_refl. Qed.
Lemma D_7f518 : decode_any W_7f518 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f51c : bv 32 := 0x7b513c23.
Lemma F_7f51c : fetch_word Asan.M.loaded_segments (0x7f56c : word) = Some W_7f51c.
Proof. vm_refl. Qed.
Lemma D_7f51c : decode_any W_7f51c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f520 : bv 32 := 0x7b613823.
Lemma F_7f520 : fetch_word Asan.M.loaded_segments (0x7f570 : word) = Some W_7f520.
Proof. vm_refl. Qed.
Lemma D_7f520 : decode_any W_7f520 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f524 : bv 32 := 0x7f010413.
Lemma F_7f524 : fetch_word Asan.M.loaded_segments (0x7f574 : word) = Some W_7f524.
Proof. vm_refl. Qed.
Lemma D_7f524 : decode_any W_7f524 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f528 : bv 32 := 0xf9010113.
Lemma F_7f528 : fetch_word Asan.M.loaded_segments (0x7f578 : word) = Some W_7f528.
Proof. vm_refl. Qed.
Lemma D_7f528 : decode_any W_7f528 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f52c : bv 32 := 0x000d4697.
Lemma F_7f52c : fetch_word Asan.M.loaded_segments (0x7f57c : word) = Some W_7f52c.
Proof. vm_refl. Qed.
Lemma D_7f52c : decode_any W_7f52c = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f530 : bv 32 := 0x7246b683.
Lemma F_7f530 : fetch_word Asan.M.loaded_segments (0x7f580 : word) = Some W_7f530.
Proof. vm_refl. Qed.
Lemma D_7f530 : decode_any W_7f530 = Some (Load SZ8 true 13 13 1828, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f534 : bv 32 := 0x0006c683.
Lemma F_7f534 : fetch_word Asan.M.loaded_segments (0x7f584 : word) = Some W_7f534.
Proof. vm_refl. Qed.
Lemma D_7f534 : decode_any W_7f534 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f538 : bv 32 := 0x0a068463.
Lemma F_7f538 : fetch_word Asan.M.loaded_segments (0x7f588 : word) = Some W_7f538.
Proof. vm_refl. Qed.
Lemma D_7f538 : decode_any W_7f538 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f53c : bv 32 := 0xfff5c693.
Lemma F_7f53c : fetch_word Asan.M.loaded_segments (0x7f58c : word) = Some W_7f53c.
Proof. vm_refl. Qed.
Lemma D_7f53c : decode_any W_7f53c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f540 : bv 32 := 0x80040a13.
Lemma F_7f540 : fetch_word Asan.M.loaded_segments (0x7f590 : word) = Some W_7f540.
Proof. vm_refl. Qed.
Lemma D_7f540 : decode_any W_7f540 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f544 : bv 32 := 0xfa8a0a13.
Lemma F_7f544 : fetch_word Asan.M.loaded_segments (0x7f594 : word) = Some W_7f544.
Proof. vm_refl. Qed.
Lemma D_7f544 : decode_any W_7f544 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f548 : bv 32 := 0x0cc6e463.
Lemma F_7f548 : fetch_word Asan.M.loaded_segments (0x7f598 : word) = Some W_7f548.
Proof. vm_refl. Qed.
Lemma D_7f548 : decode_any W_7f548 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f54c : bv 32 := 0xfbf60993.
Lemma F_7f54c : fetch_word Asan.M.loaded_segments (0x7f59c : word) = Some W_7f54c.
Proof. vm_refl. Qed.
Lemma D_7f54c : decode_any W_7f54c = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f550 : bv 32 := 0xfbf00693.
Lemma F_7f550 : fetch_word Asan.M.loaded_segments (0x7f5a0 : word) = Some W_7f550.
Proof. vm_refl. Qed.
Lemma D_7f550 : decode_any W_7f550 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f554 : bv 32 := 0x1536f263.
Lemma F_7f554 : fetch_word Asan.M.loaded_segments (0x7f5a4 : word) = Some W_7f554.
Proof. vm_refl. Qed.
Lemma D_7f554 : decode_any W_7f554 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f558 : bv 32 := 0x000d4697.
Lemma F_7f558 : fetch_word Asan.M.loaded_segments (0x7f5a8 : word) = Some W_7f558.
Proof. vm_refl. Qed.
Lemma D_7f558 : decode_any W_7f558 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f55c : bv 32 := 0xb906b683.
Lemma F_7f55c : fetch_word Asan.M.loaded_segments (0x7f5ac : word) = Some W_7f55c.
Proof. vm_refl. Qed.
Lemma D_7f55c : decode_any W_7f55c = Some (Load SZ8 true 13 13 2960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f560 : bv 32 := 0x00c587b3.
Lemma F_7f560 : fetch_word Asan.M.loaded_segments (0x7f5b0 : word) = Some W_7f560.
Proof. vm_refl. Qed.
Lemma D_7f560 : decode_any W_7f560 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f564 : bv 32 := 0x0006b703.
Lemma F_7f564 : fetch_word Asan.M.loaded_segments (0x7f5b4 : word) = Some W_7f564.
Proof. vm_refl. Qed.
Lemma D_7f564 : decode_any W_7f564 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f568 : bv 32 := 0x0035d693.
Lemma F_7f568 : fetch_word Asan.M.loaded_segments (0x7f5b8 : word) = Some W_7f568.
Proof. vm_refl. Qed.
Lemma D_7f568 : decode_any W_7f568 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f56c : bv 32 := 0xfff78793.
Lemma F_7f56c : fetch_word Asan.M.loaded_segments (0x7f5bc : word) = Some W_7f56c.
Proof. vm_refl. Qed.
Lemma D_7f56c : decode_any W_7f56c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f570 : bv 32 := 0x0037d813.
Lemma F_7f570 : fetch_word Asan.M.loaded_segments (0x7f5c0 : word) = Some W_7f570.
Proof. vm_refl. Qed.
Lemma D_7f570 : decode_any W_7f570 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f574 : bv 32 := 0x00d706b3.
Lemma F_7f574 : fetch_word Asan.M.loaded_segments (0x7f5c4 : word) = Some W_7f574.
Proof. vm_refl. Qed.
Lemma D_7f574 : decode_any W_7f574 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f578 : bv 32 := 0x01070733.
Lemma F_7f578 : fetch_word Asan.M.loaded_segments (0x7f5c8 : word) = Some W_7f578.
Proof. vm_refl. Qed.
Lemma D_7f578 : decode_any W_7f578 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f57c : bv 32 := 0xff86f813.
Lemma F_7f57c : fetch_word Asan.M.loaded_segments (0x7f5cc : word) = Some W_7f57c.
Proof. vm_refl. Qed.
Lemma D_7f57c : decode_any W_7f57c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f580 : bv 32 := 0xff877893.
Lemma F_7f580 : fetch_word Asan.M.loaded_segments (0x7f5d0 : word) = Some W_7f580.
Proof. vm_refl. Qed.
Lemma D_7f580 : decode_any W_7f580 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f584 : bv 32 := 0x00083803.
Lemma F_7f584 : fetch_word Asan.M.loaded_segments (0x7f5d4 : word) = Some W_7f584.
Proof. vm_refl. Qed.
Lemma D_7f584 : decode_any W_7f584 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f588 : bv 32 := 0x0008b883.
Lemma F_7f588 : fetch_word Asan.M.loaded_segments (0x7f5d8 : word) = Some W_7f588.
Proof. vm_refl. Qed.
Lemma D_7f588 : decode_any W_7f588 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f58c : bv 32 := 0x0108e833.
Lemma F_7f58c : fetch_word Asan.M.loaded_segments (0x7f5dc : word) = Some W_7f58c.
Proof. vm_refl. Qed.
Lemma D_7f58c : decode_any W_7f58c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f590 : bv 32 := 0x18081e63.
Lemma F_7f590 : fetch_word Asan.M.loaded_segments (0x7f5e0 : word) = Some W_7f590.
Proof. vm_refl. Qed.
Lemma D_7f590 : decode_any W_7f590 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f594 : bv 32 := 0xfff54693.
Lemma F_7f594 : fetch_word Asan.M.loaded_segments (0x7f5e4 : word) = Some W_7f594.
Proof. vm_refl. Qed.
Lemma D_7f594 : decode_any W_7f594 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f598 : bv 32 := 0x10c6e463.
Lemma F_7f598 : fetch_word Asan.M.loaded_segments (0x7f5e8 : word) = Some W_7f598.
Proof. vm_refl. Qed.
Lemma D_7f598 : decode_any W_7f598 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f59c : bv 32 := 0xfbf00693.
Lemma F_7f59c : fetch_word Asan.M.loaded_segments (0x7f5ec : word) = Some W_7f59c.
Proof. vm_refl. Qed.
Lemma D_7f59c : decode_any W_7f59c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a0 : bv 32 := 0x1936f263.
Lemma F_7f5a0 : fetch_word Asan.M.loaded_segments (0x7f5f0 : word) = Some W_7f5a0.
Proof. vm_refl. Qed.
Lemma D_7f5a0 : decode_any W_7f5a0 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a4 : bv 32 := 0x000d4697.
Lemma F_7f5a4 : fetch_word Asan.M.loaded_segments (0x7f5f4 : word) = Some W_7f5a4.
Proof. vm_refl. Qed.
Lemma D_7f5a4 : decode_any W_7f5a4 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a8 : bv 32 := 0xb446b683.
Lemma F_7f5a8 : fetch_word Asan.M.loaded_segments (0x7f5f8 : word) = Some W_7f5a8.
Proof. vm_refl. Qed.
Lemma D_7f5a8 : decode_any W_7f5a8 = Some (Load SZ8 true 13 13 2884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ac : bv 32 := 0x00c507b3.
Lemma F_7f5ac : fetch_word Asan.M.loaded_segments (0x7f5fc : word) = Some W_7f5ac.
Proof. vm_refl. Qed.
Lemma D_7f5ac : decode_any W_7f5ac = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b0 : bv 32 := 0x0006b703.
Lemma F_7f5b0 : fetch_word Asan.M.loaded_segments (0x7f600 : word) = Some W_7f5b0.
Proof. vm_refl. Qed.
Lemma D_7f5b0 : decode_any W_7f5b0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b4 : bv 32 := 0x00355693.
Lemma F_7f5b4 : fetch_word Asan.M.loaded_segments (0x7f604 : word) = Some W_7f5b4.
Proof. vm_refl. Qed.
Lemma D_7f5b4 : decode_any W_7f5b4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b8 : bv 32 := 0xfff78793.
Lemma F_7f5b8 : fetch_word Asan.M.loaded_segments (0x7f608 : word) = Some W_7f5b8.
Proof. vm_refl. Qed.
Lemma D_7f5b8 : decode_any W_7f5b8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5bc : bv 32 := 0x0037d813.
Lemma F_7f5bc : fetch_word Asan.M.loaded_segments (0x7f60c : word) = Some W_7f5bc.
Proof. vm_refl. Qed.
Lemma D_7f5bc : decode_any W_7f5bc = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c0 : bv 32 := 0x00d706b3.
Lemma F_7f5c0 : fetch_word Asan.M.loaded_segments (0x7f610 : word) = Some W_7f5c0.
Proof. vm_refl. Qed.
Lemma D_7f5c0 : decode_any W_7f5c0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c4 : bv 32 := 0x01070733.
Lemma F_7f5c4 : fetch_word Asan.M.loaded_segments (0x7f614 : word) = Some W_7f5c4.
Proof. vm_refl. Qed.
Lemma D_7f5c4 : decode_any W_7f5c4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c8 : bv 32 := 0xff86f813.
Lemma F_7f5c8 : fetch_word Asan.M.loaded_segments (0x7f618 : word) = Some W_7f5c8.
Proof. vm_refl. Qed.
Lemma D_7f5c8 : decode_any W_7f5c8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5cc : bv 32 := 0xff877893.
Lemma F_7f5cc : fetch_word Asan.M.loaded_segments (0x7f61c : word) = Some W_7f5cc.
Proof. vm_refl. Qed.
Lemma D_7f5cc : decode_any W_7f5cc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d0 : bv 32 := 0x00083803.
Lemma F_7f5d0 : fetch_word Asan.M.loaded_segments (0x7f620 : word) = Some W_7f5d0.
Proof. vm_refl. Qed.
Lemma D_7f5d0 : decode_any W_7f5d0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d4 : bv 32 := 0x0008b883.
Lemma F_7f5d4 : fetch_word Asan.M.loaded_segments (0x7f624 : word) = Some W_7f5d4.
Proof. vm_refl. Qed.
Lemma D_7f5d4 : decode_any W_7f5d4 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d8 : bv 32 := 0x0108e833.
Lemma F_7f5d8 : fetch_word Asan.M.loaded_segments (0x7f628 : word) = Some W_7f5d8.
Proof. vm_refl. Qed.
Lemma D_7f5d8 : decode_any W_7f5d8 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5dc : bv 32 := 0x1e081a63.
Lemma F_7f5dc : fetch_word Asan.M.loaded_segments (0x7f62c : word) = Some W_7f5dc.
Proof. vm_refl. Qed.
Lemma D_7f5dc : decode_any W_7f5dc = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e0 : bv 32 := 0x7b9120ef.
Lemma F_7f5e0 : fetch_word Asan.M.loaded_segments (0x7f630 : word) = Some W_7f5e0.
Proof. vm_refl. Qed.
Lemma D_7f5e0 : decode_any W_7f5e0 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e4 : bv 32 := 0x07010113.
Lemma F_7f5e4 : fetch_word Asan.M.loaded_segments (0x7f634 : word) = Some W_7f5e4.
Proof. vm_refl. Qed.
Lemma D_7f5e4 : decode_any W_7f5e4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e8 : bv 32 := 0x7e813083.
Lemma F_7f5e8 : fetch_word Asan.M.loaded_segments (0x7f638 : word) = Some W_7f5e8.
Proof. vm_refl. Qed.
Lemma D_7f5e8 : decode_any W_7f5e8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ec : bv 32 := 0x7e013403.
Lemma F_7f5ec : fetch_word Asan.M.loaded_segments (0x7f63c : word) = Some W_7f5ec.
Proof. vm_refl. Qed.
Lemma D_7f5ec : decode_any W_7f5ec = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f0 : bv 32 := 0x7d813483.
Lemma F_7f5f0 : fetch_word Asan.M.loaded_segments (0x7f640 : word) = Some W_7f5f0.
Proof. vm_refl. Qed.
Lemma D_7f5f0 : decode_any W_7f5f0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f4 : bv 32 := 0x7d013903.
Lemma F_7f5f4 : fetch_word Asan.M.loaded_segments (0x7f644 : word) = Some W_7f5f4.
Proof. vm_refl. Qed.
Lemma D_7f5f4 : decode_any W_7f5f4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f8 : bv 32 := 0x7c813983.
Lemma F_7f5f8 : fetch_word Asan.M.loaded_segments (0x7f648 : word) = Some W_7f5f8.
Proof. vm_refl. Qed.
Lemma D_7f5f8 : decode_any W_7f5f8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5fc : bv 32 := 0x7c013a03.
Lemma F_7f5fc : fetch_word Asan.M.loaded_segments (0x7f64c : word) = Some W_7f5fc.
Proof. vm_refl. Qed.
Lemma D_7f5fc : decode_any W_7f5fc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f600 : bv 32 := 0x7b813a83.
Lemma F_7f600 : fetch_word Asan.M.loaded_segments (0x7f650 : word) = Some W_7f600.
Proof. vm_refl. Qed.
Lemma D_7f600 : decode_any W_7f600 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f604 : bv 32 := 0x7b013b03.
Lemma F_7f604 : fetch_word Asan.M.loaded_segments (0x7f654 : word) = Some W_7f604.
Proof. vm_refl. Qed.
Lemma D_7f604 : decode_any W_7f604 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f608 : bv 32 := 0x7f010113.
Lemma F_7f608 : fetch_word Asan.M.loaded_segments (0x7f658 : word) = Some W_7f608.
Proof. vm_refl. Qed.
Lemma D_7f608 : decode_any W_7f608 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f60c : bv 32 := 0x00008067.
Lemma F_7f60c : fetch_word Asan.M.loaded_segments (0x7f65c : word) = Some W_7f60c.
Proof. vm_refl. Qed.
Lemma D_7f60c : decode_any W_7f60c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f698 : bv 32 := 0x0c061463.
Lemma F_7f698 : fetch_word Asan.M.loaded_segments (0x7f6e8 : word) = Some W_7f698.
Proof. vm_refl. Qed.
Lemma D_7f698 : decode_any W_7f698 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f69c : bv 32 := 0xef9ff06f.
Lemma F_7f69c : fetch_word Asan.M.loaded_segments (0x7f6ec : word) = Some W_7f69c.
Proof. vm_refl. Qed.
Lemma D_7f69c : decode_any W_7f69c = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f724 : bv 32 := 0x0e061063.
Lemma F_7f724 : fetch_word Asan.M.loaded_segments (0x7f774 : word) = Some W_7f724.
Proof. vm_refl. Qed.
Lemma D_7f724 : decode_any W_7f724 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f728 : bv 32 := 0xeb9ff06f.
Lemma F_7f728 : fetch_word Asan.M.loaded_segments (0x7f778 : word) = Some W_7f728.
Proof. vm_refl. Qed.
Lemma D_7f728 : decode_any W_7f728 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f72c : bv 32 := 0x00070803.
Lemma F_7f72c : fetch_word Asan.M.loaded_segments (0x7f77c : word) = Some W_7f72c.
Proof. vm_refl. Qed.
Lemma D_7f72c : decode_any W_7f72c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f730 : bv 32 := 0x0077f793.
Lemma F_7f730 : fetch_word Asan.M.loaded_segments (0x7f780 : word) = Some W_7f730.
Proof. vm_refl. Qed.
Lemma D_7f730 : decode_any W_7f730 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f734 : bv 32 := 0x010038b3.
Lemma F_7f734 : fetch_word Asan.M.loaded_segments (0x7f784 : word) = Some W_7f734.
Proof. vm_refl. Qed.
Lemma D_7f734 : decode_any W_7f734 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f738 : bv 32 := 0x0107a7b3.
Lemma F_7f738 : fetch_word Asan.M.loaded_segments (0x7f788 : word) = Some W_7f738.
Proof. vm_refl. Qed.
Lemma D_7f738 : decode_any W_7f738 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f73c : bv 32 := 0x0017c793.
Lemma F_7f73c : fetch_word Asan.M.loaded_segments (0x7f78c : word) = Some W_7f73c.
Proof. vm_refl. Qed.
Lemma D_7f73c : decode_any W_7f73c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f740 : bv 32 := 0x00f8f7b3.
Lemma F_7f740 : fetch_word Asan.M.loaded_segments (0x7f790 : word) = Some W_7f740.
Proof. vm_refl. Qed.
Lemma D_7f740 : decode_any W_7f740 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f744 : bv 32 := 0x00e6fa63.
Lemma F_7f744 : fetch_word Asan.M.loaded_segments (0x7f794 : word) = Some W_7f744.
Proof. vm_refl. Qed.
Lemma D_7f744 : decode_any W_7f744 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f748 : bv 32 := 0x0006c803.
Lemma F_7f748 : fetch_word Asan.M.loaded_segments (0x7f798 : word) = Some W_7f748.
Proof. vm_refl. Qed.
Lemma D_7f748 : decode_any W_7f748 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f74c : bv 32 := 0x00168693.
Lemma F_7f74c : fetch_word Asan.M.loaded_segments (0x7f79c : word) = Some W_7f74c.
Proof. vm_refl. Qed.
Lemma D_7f74c : decode_any W_7f74c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f750 : bv 32 := 0x00f867b3.
Lemma F_7f750 : fetch_word Asan.M.loaded_segments (0x7f7a0 : word) = Some W_7f750.
Proof. vm_refl. Qed.
Lemma D_7f750 : decode_any W_7f750 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f754 : bv 32 := 0xfee69ae3.
Lemma F_7f754 : fetch_word Asan.M.loaded_segments (0x7f7a4 : word) = Some W_7f754.
Proof. vm_refl. Qed.
Lemma D_7f754 : decode_any W_7f754 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f758 : bv 32 := 0x0ff7f693.
Lemma F_7f758 : fetch_word Asan.M.loaded_segments (0x7f7a8 : word) = Some W_7f758.
Proof. vm_refl. Qed.
Lemma D_7f758 : decode_any W_7f758 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f75c : bv 32 := 0xe2068ce3.
Lemma F_7f75c : fetch_word Asan.M.loaded_segments (0x7f7ac : word) = Some W_7f75c.
Proof. vm_refl. Qed.
Lemma D_7f75c : decode_any W_7f75c = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f760 : bv 32 := 0x00050a93.
Lemma F_7f760 : fetch_word Asan.M.loaded_segments (0x7f7b0 : word) = Some W_7f760.
Proof. vm_refl. Qed.
Lemma D_7f760 : decode_any W_7f760 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f764 : bv 32 := 0x00058513.
Lemma F_7f764 : fetch_word Asan.M.loaded_segments (0x7f7b4 : word) = Some W_7f764.
Proof. vm_refl. Qed.
Lemma D_7f764 : decode_any W_7f764 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f768 : bv 32 := 0x00058b13.
Lemma F_7f768 : fetch_word Asan.M.loaded_segments (0x7f7b8 : word) = Some W_7f768.
Proof. vm_refl. Qed.
Lemma D_7f768 : decode_any W_7f768 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f76c : bv 32 := 0x00060593.
Lemma F_7f76c : fetch_word Asan.M.loaded_segments (0x7f7bc : word) = Some W_7f76c.
Proof. vm_refl. Qed.
Lemma D_7f76c : decode_any W_7f76c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f770 : bv 32 := 0x00060493.
Lemma F_7f770 : fetch_word Asan.M.loaded_segments (0x7f7c0 : word) = Some W_7f770.
Proof. vm_refl. Qed.
Lemma D_7f770 : decode_any W_7f770 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f774 : bv 32 := 0x6dd020ef.
Lemma F_7f774 : fetch_word Asan.M.loaded_segments (0x7f7c4 : word) = Some W_7f774.
Proof. vm_refl. Qed.
Lemma D_7f774 : decode_any W_7f774 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f778 : bv 32 := 0x000b0593.
Lemma F_7f778 : fetch_word Asan.M.loaded_segments (0x7f7c8 : word) = Some W_7f778.
Proof. vm_refl. Qed.
Lemma D_7f778 : decode_any W_7f778 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f77c : bv 32 := 0x00048613.
Lemma F_7f77c : fetch_word Asan.M.loaded_segments (0x7f7cc : word) = Some W_7f77c.
Proof. vm_refl. Qed.
Lemma D_7f77c : decode_any W_7f77c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f780 : bv 32 := 0x00050913.
Lemma F_7f780 : fetch_word Asan.M.loaded_segments (0x7f7d0 : word) = Some W_7f780.
Proof. vm_refl. Qed.
Lemma D_7f780 : decode_any W_7f780 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f784 : bv 32 := 0x000a8513.
Lemma F_7f784 : fetch_word Asan.M.loaded_segments (0x7f7d4 : word) = Some W_7f784.
Proof. vm_refl. Qed.
Lemma D_7f784 : decode_any W_7f784 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f788 : bv 32 := 0xe00906e3.
Lemma F_7f788 : fetch_word Asan.M.loaded_segments (0x7f7d8 : word) = Some W_7f788.
Proof. vm_refl. Qed.
Lemma D_7f788 : decode_any W_7f788 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d0 : bv 32 := 0x00070803.
Lemma F_7f7d0 : fetch_word Asan.M.loaded_segments (0x7f820 : word) = Some W_7f7d0.
Proof. vm_refl. Qed.
Lemma D_7f7d0 : decode_any W_7f7d0 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d4 : bv 32 := 0x0077f793.
Lemma F_7f7d4 : fetch_word Asan.M.loaded_segments (0x7f824 : word) = Some W_7f7d4.
Proof. vm_refl. Qed.
Lemma D_7f7d4 : decode_any W_7f7d4 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d8 : bv 32 := 0x010038b3.
Lemma F_7f7d8 : fetch_word Asan.M.loaded_segments (0x7f828 : word) = Some W_7f7d8.
Proof. vm_refl. Qed.
Lemma D_7f7d8 : decode_any W_7f7d8 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7dc : bv 32 := 0x0107a7b3.
Lemma F_7f7dc : fetch_word Asan.M.loaded_segments (0x7f82c : word) = Some W_7f7dc.
Proof. vm_refl. Qed.
Lemma D_7f7dc : decode_any W_7f7dc = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e0 : bv 32 := 0x0017c793.
Lemma F_7f7e0 : fetch_word Asan.M.loaded_segments (0x7f830 : word) = Some W_7f7e0.
Proof. vm_refl. Qed.
Lemma D_7f7e0 : decode_any W_7f7e0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e4 : bv 32 := 0x00f8f7b3.
Lemma F_7f7e4 : fetch_word Asan.M.loaded_segments (0x7f834 : word) = Some W_7f7e4.
Proof. vm_refl. Qed.
Lemma D_7f7e4 : decode_any W_7f7e4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e8 : bv 32 := 0x00e6fa63.
Lemma F_7f7e8 : fetch_word Asan.M.loaded_segments (0x7f838 : word) = Some W_7f7e8.
Proof. vm_refl. Qed.
Lemma D_7f7e8 : decode_any W_7f7e8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7ec : bv 32 := 0x0006c803.
Lemma F_7f7ec : fetch_word Asan.M.loaded_segments (0x7f83c : word) = Some W_7f7ec.
Proof. vm_refl. Qed.
Lemma D_7f7ec : decode_any W_7f7ec = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f0 : bv 32 := 0x00168693.
Lemma F_7f7f0 : fetch_word Asan.M.loaded_segments (0x7f840 : word) = Some W_7f7f0.
Proof. vm_refl. Qed.
Lemma D_7f7f0 : decode_any W_7f7f0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f4 : bv 32 := 0x00f867b3.
Lemma F_7f7f4 : fetch_word Asan.M.loaded_segments (0x7f844 : word) = Some W_7f7f4.
Proof. vm_refl. Qed.
Lemma D_7f7f4 : decode_any W_7f7f4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f8 : bv 32 := 0xfee69ae3.
Lemma F_7f7f8 : fetch_word Asan.M.loaded_segments (0x7f848 : word) = Some W_7f7f8.
Proof. vm_refl. Qed.
Lemma D_7f7f8 : decode_any W_7f7f8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7fc : bv 32 := 0x0ff7f693.
Lemma F_7f7fc : fetch_word Asan.M.loaded_segments (0x7f84c : word) = Some W_7f7fc.
Proof. vm_refl. Qed.
Lemma D_7f7fc : decode_any W_7f7fc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f800 : bv 32 := 0xde0680e3.
Lemma F_7f800 : fetch_word Asan.M.loaded_segments (0x7f850 : word) = Some W_7f800.
Proof. vm_refl. Qed.
Lemma D_7f800 : decode_any W_7f800 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f804 : bv 32 := 0x00050493.
Lemma F_7f804 : fetch_word Asan.M.loaded_segments (0x7f854 : word) = Some W_7f804.
Proof. vm_refl. Qed.
Lemma D_7f804 : decode_any W_7f804 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f808 : bv 32 := 0x00058a93.
Lemma F_7f808 : fetch_word Asan.M.loaded_segments (0x7f858 : word) = Some W_7f808.
Proof. vm_refl. Qed.
Lemma D_7f808 : decode_any W_7f808 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f80c : bv 32 := 0x00060593.
Lemma F_7f80c : fetch_word Asan.M.loaded_segments (0x7f85c : word) = Some W_7f80c.
Proof. vm_refl. Qed.
Lemma D_7f80c : decode_any W_7f80c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f810 : bv 32 := 0x00060913.
Lemma F_7f810 : fetch_word Asan.M.loaded_segments (0x7f860 : word) = Some W_7f810.
Proof. vm_refl. Qed.
Lemma D_7f810 : decode_any W_7f810 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f814 : bv 32 := 0x63d020ef.
Lemma F_7f814 : fetch_word Asan.M.loaded_segments (0x7f864 : word) = Some W_7f814.
Proof. vm_refl. Qed.
Lemma D_7f814 : decode_any W_7f814 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f818 : bv 32 := 0x000a8593.
Lemma F_7f818 : fetch_word Asan.M.loaded_segments (0x7f868 : word) = Some W_7f818.
Proof. vm_refl. Qed.
Lemma D_7f818 : decode_any W_7f818 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f81c : bv 32 := 0x00090613.
Lemma F_7f81c : fetch_word Asan.M.loaded_segments (0x7f86c : word) = Some W_7f81c.
Proof. vm_refl. Qed.
Lemma D_7f81c : decode_any W_7f81c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f820 : bv 32 := 0x00050993.
Lemma F_7f820 : fetch_word Asan.M.loaded_segments (0x7f870 : word) = Some W_7f820.
Proof. vm_refl. Qed.
Lemma D_7f820 : decode_any W_7f820 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f824 : bv 32 := 0x00048513.
Lemma F_7f824 : fetch_word Asan.M.loaded_segments (0x7f874 : word) = Some W_7f824.
Proof. vm_refl. Qed.
Lemma D_7f824 : decode_any W_7f824 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f828 : bv 32 := 0xda098ce3.
Lemma F_7f828 : fetch_word Asan.M.loaded_segments (0x7f878 : word) = Some W_7f828.
Proof. vm_refl. Qed.
Lemma D_7f828 : decode_any W_7f828 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb60 : bv 32 := 0x81010113.
Lemma F_7fb60 : fetch_word Asan.M.loaded_segments (0x7fbb0 : word) = Some W_7fb60.
Proof. vm_refl. Qed.
Lemma D_7fb60 : decode_any W_7fb60 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb64 : bv 32 := 0x7e113423.
Lemma F_7fb64 : fetch_word Asan.M.loaded_segments (0x7fbb4 : word) = Some W_7fb64.
Proof. vm_refl. Qed.
Lemma D_7fb64 : decode_any W_7fb64 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb68 : bv 32 := 0x7e813023.
Lemma F_7fb68 : fetch_word Asan.M.loaded_segments (0x7fbb8 : word) = Some W_7fb68.
Proof. vm_refl. Qed.
Lemma D_7fb68 : decode_any W_7fb68 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb6c : bv 32 := 0x7c913c23.
Lemma F_7fb6c : fetch_word Asan.M.loaded_segments (0x7fbbc : word) = Some W_7fb6c.
Proof. vm_refl. Qed.
Lemma D_7fb6c : decode_any W_7fb6c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb70 : bv 32 := 0x7d213823.
Lemma F_7fb70 : fetch_word Asan.M.loaded_segments (0x7fbc0 : word) = Some W_7fb70.
Proof. vm_refl. Qed.
Lemma D_7fb70 : decode_any W_7fb70 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb74 : bv 32 := 0x7d313423.
Lemma F_7fb74 : fetch_word Asan.M.loaded_segments (0x7fbc4 : word) = Some W_7fb74.
Proof. vm_refl. Qed.
Lemma D_7fb74 : decode_any W_7fb74 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb78 : bv 32 := 0x7d413023.
Lemma F_7fb78 : fetch_word Asan.M.loaded_segments (0x7fbc8 : word) = Some W_7fb78.
Proof. vm_refl. Qed.
Lemma D_7fb78 : decode_any W_7fb78 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb7c : bv 32 := 0x7b513c23.
Lemma F_7fb7c : fetch_word Asan.M.loaded_segments (0x7fbcc : word) = Some W_7fb7c.
Proof. vm_refl. Qed.
Lemma D_7fb7c : decode_any W_7fb7c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb80 : bv 32 := 0x7b613823.
Lemma F_7fb80 : fetch_word Asan.M.loaded_segments (0x7fbd0 : word) = Some W_7fb80.
Proof. vm_refl. Qed.
Lemma D_7fb80 : decode_any W_7fb80 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb84 : bv 32 := 0x7b713423.
Lemma F_7fb84 : fetch_word Asan.M.loaded_segments (0x7fbd4 : word) = Some W_7fb84.
Proof. vm_refl. Qed.
Lemma D_7fb84 : decode_any W_7fb84 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb88 : bv 32 := 0x7f010413.
Lemma F_7fb88 : fetch_word Asan.M.loaded_segments (0x7fbd8 : word) = Some W_7fb88.
Proof. vm_refl. Qed.
Lemma D_7fb88 : decode_any W_7fb88 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb8c : bv 32 := 0xf9010113.
Lemma F_7fb8c : fetch_word Asan.M.loaded_segments (0x7fbdc : word) = Some W_7fb8c.
Proof. vm_refl. Qed.
Lemma D_7fb8c : decode_any W_7fb8c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb90 : bv 32 := 0x000d4697.
Lemma F_7fb90 : fetch_word Asan.M.loaded_segments (0x7fbe0 : word) = Some W_7fb90.
Proof. vm_refl. Qed.
Lemma D_7fb90 : decode_any W_7fb90 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb94 : bv 32 := 0x0c06b683.
Lemma F_7fb94 : fetch_word Asan.M.loaded_segments (0x7fbe4 : word) = Some W_7fb94.
Proof. vm_refl. Qed.
Lemma D_7fb94 : decode_any W_7fb94 = Some (Load SZ8 true 13 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb98 : bv 32 := 0x0006c683.
Lemma F_7fb98 : fetch_word Asan.M.loaded_segments (0x7fbe8 : word) = Some W_7fb98.
Proof. vm_refl. Qed.
Lemma D_7fb98 : decode_any W_7fb98 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb9c : bv 32 := 0x0a068463.
Lemma F_7fb9c : fetch_word Asan.M.loaded_segments (0x7fbec : word) = Some W_7fb9c.
Proof. vm_refl. Qed.
Lemma D_7fb9c : decode_any W_7fb9c = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba0 : bv 32 := 0xfff5c693.
Lemma F_7fba0 : fetch_word Asan.M.loaded_segments (0x7fbf0 : word) = Some W_7fba0.
Proof. vm_refl. Qed.
Lemma D_7fba0 : decode_any W_7fba0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba4 : bv 32 := 0x80040a93.
Lemma F_7fba4 : fetch_word Asan.M.loaded_segments (0x7fbf4 : word) = Some W_7fba4.
Proof. vm_refl. Qed.
Lemma D_7fba4 : decode_any W_7fba4 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba8 : bv 32 := 0xfa0a8a93.
Lemma F_7fba8 : fetch_word Asan.M.loaded_segments (0x7fbf8 : word) = Some W_7fba8.
Proof. vm_refl. Qed.
Lemma D_7fba8 : decode_any W_7fba8 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbac : bv 32 := 0x0cc6e663.
Lemma F_7fbac : fetch_word Asan.M.loaded_segments (0x7fbfc : word) = Some W_7fbac.
Proof. vm_refl. Qed.
Lemma D_7fbac : decode_any W_7fbac = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb0 : bv 32 := 0xfbf60a13.
Lemma F_7fbb0 : fetch_word Asan.M.loaded_segments (0x7fc00 : word) = Some W_7fbb0.
Proof. vm_refl. Qed.
Lemma D_7fbb0 : decode_any W_7fbb0 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb4 : bv 32 := 0xfbf00693.
Lemma F_7fbb4 : fetch_word Asan.M.loaded_segments (0x7fc04 : word) = Some W_7fbb4.
Proof. vm_refl. Qed.
Lemma D_7fbb4 : decode_any W_7fbb4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb8 : bv 32 := 0x1546f463.
Lemma F_7fbb8 : fetch_word Asan.M.loaded_segments (0x7fc08 : word) = Some W_7fbb8.
Proof. vm_refl. Qed.
Lemma D_7fbb8 : decode_any W_7fbb8 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbbc : bv 32 := 0x000d3697.
Lemma F_7fbbc : fetch_word Asan.M.loaded_segments (0x7fc0c : word) = Some W_7fbbc.
Proof. vm_refl. Qed.
Lemma D_7fbbc : decode_any W_7fbbc = Some (Auipc 13 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc0 : bv 32 := 0x52c6b683.
Lemma F_7fbc0 : fetch_word Asan.M.loaded_segments (0x7fc10 : word) = Some W_7fbc0.
Proof. vm_refl. Qed.
Lemma D_7fbc0 : decode_any W_7fbc0 = Some (Load SZ8 true 13 13 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc4 : bv 32 := 0x00c587b3.
Lemma F_7fbc4 : fetch_word Asan.M.loaded_segments (0x7fc14 : word) = Some W_7fbc4.
Proof. vm_refl. Qed.
Lemma D_7fbc4 : decode_any W_7fbc4 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc8 : bv 32 := 0x0006b703.
Lemma F_7fbc8 : fetch_word Asan.M.loaded_segments (0x7fc18 : word) = Some W_7fbc8.
Proof. vm_refl. Qed.
Lemma D_7fbc8 : decode_any W_7fbc8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbcc : bv 32 := 0x0035d693.
Lemma F_7fbcc : fetch_word Asan.M.loaded_segments (0x7fc1c : word) = Some W_7fbcc.
Proof. vm_refl. Qed.
Lemma D_7fbcc : decode_any W_7fbcc = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd0 : bv 32 := 0xfff78793.
Lemma F_7fbd0 : fetch_word Asan.M.loaded_segments (0x7fc20 : word) = Some W_7fbd0.
Proof. vm_refl. Qed.
Lemma D_7fbd0 : decode_any W_7fbd0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd4 : bv 32 := 0x0037d813.
Lemma F_7fbd4 : fetch_word Asan.M.loaded_segments (0x7fc24 : word) = Some W_7fbd4.
Proof. vm_refl. Qed.
Lemma D_7fbd4 : decode_any W_7fbd4 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd8 : bv 32 := 0x00d706b3.
Lemma F_7fbd8 : fetch_word Asan.M.loaded_segments (0x7fc28 : word) = Some W_7fbd8.
Proof. vm_refl. Qed.
Lemma D_7fbd8 : decode_any W_7fbd8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbdc : bv 32 := 0x01070733.
Lemma F_7fbdc : fetch_word Asan.M.loaded_segments (0x7fc2c : word) = Some W_7fbdc.
Proof. vm_refl. Qed.
Lemma D_7fbdc : decode_any W_7fbdc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe0 : bv 32 := 0xff86f813.
Lemma F_7fbe0 : fetch_word Asan.M.loaded_segments (0x7fc30 : word) = Some W_7fbe0.
Proof. vm_refl. Qed.
Lemma D_7fbe0 : decode_any W_7fbe0 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe4 : bv 32 := 0xff877893.
Lemma F_7fbe4 : fetch_word Asan.M.loaded_segments (0x7fc34 : word) = Some W_7fbe4.
Proof. vm_refl. Qed.
Lemma D_7fbe4 : decode_any W_7fbe4 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe8 : bv 32 := 0x00083803.
Lemma F_7fbe8 : fetch_word Asan.M.loaded_segments (0x7fc38 : word) = Some W_7fbe8.
Proof. vm_refl. Qed.
Lemma D_7fbe8 : decode_any W_7fbe8 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbec : bv 32 := 0x0008b883.
Lemma F_7fbec : fetch_word Asan.M.loaded_segments (0x7fc3c : word) = Some W_7fbec.
Proof. vm_refl. Qed.
Lemma D_7fbec : decode_any W_7fbec = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf0 : bv 32 := 0x0108e833.
Lemma F_7fbf0 : fetch_word Asan.M.loaded_segments (0x7fc40 : word) = Some W_7fbf0.
Proof. vm_refl. Qed.
Lemma D_7fbf0 : decode_any W_7fbf0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf4 : bv 32 := 0x1a081063.
Lemma F_7fbf4 : fetch_word Asan.M.loaded_segments (0x7fc44 : word) = Some W_7fbf4.
Proof. vm_refl. Qed.
Lemma D_7fbf4 : decode_any W_7fbf4 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf8 : bv 32 := 0xfff54693.
Lemma F_7fbf8 : fetch_word Asan.M.loaded_segments (0x7fc48 : word) = Some W_7fbf8.
Proof. vm_refl. Qed.
Lemma D_7fbf8 : decode_any W_7fbf8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbfc : bv 32 := 0x10c6e663.
Lemma F_7fbfc : fetch_word Asan.M.loaded_segments (0x7fc4c : word) = Some W_7fbfc.
Proof. vm_refl. Qed.
Lemma D_7fbfc : decode_any W_7fbfc = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc00 : bv 32 := 0xfbf00693.
Lemma F_7fc00 : fetch_word Asan.M.loaded_segments (0x7fc50 : word) = Some W_7fc00.
Proof. vm_refl. Qed.
Lemma D_7fc00 : decode_any W_7fc00 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc04 : bv 32 := 0x1946f463.
Lemma F_7fc04 : fetch_word Asan.M.loaded_segments (0x7fc54 : word) = Some W_7fc04.
Proof. vm_refl. Qed.
Lemma D_7fc04 : decode_any W_7fc04 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc08 : bv 32 := 0x000d3697.
Lemma F_7fc08 : fetch_word Asan.M.loaded_segments (0x7fc58 : word) = Some W_7fc08.
Proof. vm_refl. Qed.
Lemma D_7fc08 : decode_any W_7fc08 = Some (Auipc 13 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc0c : bv 32 := 0x4e06b683.
Lemma F_7fc0c : fetch_word Asan.M.loaded_segments (0x7fc5c : word) = Some W_7fc0c.
Proof. vm_refl. Qed.
Lemma D_7fc0c : decode_any W_7fc0c = Some (Load SZ8 true 13 13 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc10 : bv 32 := 0x00c507b3.
Lemma F_7fc10 : fetch_word Asan.M.loaded_segments (0x7fc60 : word) = Some W_7fc10.
Proof. vm_refl. Qed.
Lemma D_7fc10 : decode_any W_7fc10 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc14 : bv 32 := 0x0006b703.
Lemma F_7fc14 : fetch_word Asan.M.loaded_segments (0x7fc64 : word) = Some W_7fc14.
Proof. vm_refl. Qed.
Lemma D_7fc14 : decode_any W_7fc14 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc18 : bv 32 := 0x00355693.
Lemma F_7fc18 : fetch_word Asan.M.loaded_segments (0x7fc68 : word) = Some W_7fc18.
Proof. vm_refl. Qed.
Lemma D_7fc18 : decode_any W_7fc18 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc1c : bv 32 := 0xfff78793.
Lemma F_7fc1c : fetch_word Asan.M.loaded_segments (0x7fc6c : word) = Some W_7fc1c.
Proof. vm_refl. Qed.
Lemma D_7fc1c : decode_any W_7fc1c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc20 : bv 32 := 0x0037d813.
Lemma F_7fc20 : fetch_word Asan.M.loaded_segments (0x7fc70 : word) = Some W_7fc20.
Proof. vm_refl. Qed.
Lemma D_7fc20 : decode_any W_7fc20 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc24 : bv 32 := 0x00d706b3.
Lemma F_7fc24 : fetch_word Asan.M.loaded_segments (0x7fc74 : word) = Some W_7fc24.
Proof. vm_refl. Qed.
Lemma D_7fc24 : decode_any W_7fc24 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc28 : bv 32 := 0x01070733.
Lemma F_7fc28 : fetch_word Asan.M.loaded_segments (0x7fc78 : word) = Some W_7fc28.
Proof. vm_refl. Qed.
Lemma D_7fc28 : decode_any W_7fc28 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc2c : bv 32 := 0xff86f813.
Lemma F_7fc2c : fetch_word Asan.M.loaded_segments (0x7fc7c : word) = Some W_7fc2c.
Proof. vm_refl. Qed.
Lemma D_7fc2c : decode_any W_7fc2c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc30 : bv 32 := 0xff877893.
Lemma F_7fc30 : fetch_word Asan.M.loaded_segments (0x7fc80 : word) = Some W_7fc30.
Proof. vm_refl. Qed.
Lemma D_7fc30 : decode_any W_7fc30 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc34 : bv 32 := 0x00083803.
Lemma F_7fc34 : fetch_word Asan.M.loaded_segments (0x7fc84 : word) = Some W_7fc34.
Proof. vm_refl. Qed.
Lemma D_7fc34 : decode_any W_7fc34 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc38 : bv 32 := 0x0008b883.
Lemma F_7fc38 : fetch_word Asan.M.loaded_segments (0x7fc88 : word) = Some W_7fc38.
Proof. vm_refl. Qed.
Lemma D_7fc38 : decode_any W_7fc38 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc3c : bv 32 := 0x0108e833.
Lemma F_7fc3c : fetch_word Asan.M.loaded_segments (0x7fc8c : word) = Some W_7fc3c.
Proof. vm_refl. Qed.
Lemma D_7fc3c : decode_any W_7fc3c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc40 : bv 32 := 0x24081a63.
Lemma F_7fc40 : fetch_word Asan.M.loaded_segments (0x7fc90 : word) = Some W_7fc40.
Proof. vm_refl. Qed.
Lemma D_7fc40 : decode_any W_7fc40 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc44 : bv 32 := 0x155120ef.
Lemma F_7fc44 : fetch_word Asan.M.loaded_segments (0x7fc94 : word) = Some W_7fc44.
Proof. vm_refl. Qed.
Lemma D_7fc44 : decode_any W_7fc44 = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc48 : bv 32 := 0x07010113.
Lemma F_7fc48 : fetch_word Asan.M.loaded_segments (0x7fc98 : word) = Some W_7fc48.
Proof. vm_refl. Qed.
Lemma D_7fc48 : decode_any W_7fc48 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc4c : bv 32 := 0x7e813083.
Lemma F_7fc4c : fetch_word Asan.M.loaded_segments (0x7fc9c : word) = Some W_7fc4c.
Proof. vm_refl. Qed.
Lemma D_7fc4c : decode_any W_7fc4c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc50 : bv 32 := 0x7e013403.
Lemma F_7fc50 : fetch_word Asan.M.loaded_segments (0x7fca0 : word) = Some W_7fc50.
Proof. vm_refl. Qed.
Lemma D_7fc50 : decode_any W_7fc50 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc54 : bv 32 := 0x7d813483.
Lemma F_7fc54 : fetch_word Asan.M.loaded_segments (0x7fca4 : word) = Some W_7fc54.
Proof. vm_refl. Qed.
Lemma D_7fc54 : decode_any W_7fc54 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc58 : bv 32 := 0x7d013903.
Lemma F_7fc58 : fetch_word Asan.M.loaded_segments (0x7fca8 : word) = Some W_7fc58.
Proof. vm_refl. Qed.
Lemma D_7fc58 : decode_any W_7fc58 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc5c : bv 32 := 0x7c813983.
Lemma F_7fc5c : fetch_word Asan.M.loaded_segments (0x7fcac : word) = Some W_7fc5c.
Proof. vm_refl. Qed.
Lemma D_7fc5c : decode_any W_7fc5c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc60 : bv 32 := 0x7c013a03.
Lemma F_7fc60 : fetch_word Asan.M.loaded_segments (0x7fcb0 : word) = Some W_7fc60.
Proof. vm_refl. Qed.
Lemma D_7fc60 : decode_any W_7fc60 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc64 : bv 32 := 0x7b813a83.
Lemma F_7fc64 : fetch_word Asan.M.loaded_segments (0x7fcb4 : word) = Some W_7fc64.
Proof. vm_refl. Qed.
Lemma D_7fc64 : decode_any W_7fc64 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc68 : bv 32 := 0x7b013b03.
Lemma F_7fc68 : fetch_word Asan.M.loaded_segments (0x7fcb8 : word) = Some W_7fc68.
Proof. vm_refl. Qed.
Lemma D_7fc68 : decode_any W_7fc68 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc6c : bv 32 := 0x7a813b83.
Lemma F_7fc6c : fetch_word Asan.M.loaded_segments (0x7fcbc : word) = Some W_7fc6c.
Proof. vm_refl. Qed.
Lemma D_7fc6c : decode_any W_7fc6c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc70 : bv 32 := 0x7f010113.
Lemma F_7fc70 : fetch_word Asan.M.loaded_segments (0x7fcc0 : word) = Some W_7fc70.
Proof. vm_refl. Qed.
Lemma D_7fc70 : decode_any W_7fc70 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc74 : bv 32 := 0x00008067.
Lemma F_7fc74 : fetch_word Asan.M.loaded_segments (0x7fcc4 : word) = Some W_7fc74.
Proof. vm_refl. Qed.
Lemma D_7fc74 : decode_any W_7fc74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd00 : bv 32 := 0x0c061463.
Lemma F_7fd00 : fetch_word Asan.M.loaded_segments (0x7fd50 : word) = Some W_7fd00.
Proof. vm_refl. Qed.
Lemma D_7fd00 : decode_any W_7fd00 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd04 : bv 32 := 0xef5ff06f.
Lemma F_7fd04 : fetch_word Asan.M.loaded_segments (0x7fd54 : word) = Some W_7fd04.
Proof. vm_refl. Qed.
Lemma D_7fd04 : decode_any W_7fd04 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd8c : bv 32 := 0x12061e63.
Lemma F_7fd8c : fetch_word Asan.M.loaded_segments (0x7fddc : word) = Some W_7fd8c.
Proof. vm_refl. Qed.
Lemma D_7fd8c : decode_any W_7fd8c = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd90 : bv 32 := 0xeb5ff06f.
Lemma F_7fd90 : fetch_word Asan.M.loaded_segments (0x7fde0 : word) = Some W_7fd90.
Proof. vm_refl. Qed.
Lemma D_7fd90 : decode_any W_7fd90 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd94 : bv 32 := 0x00070803.
Lemma F_7fd94 : fetch_word Asan.M.loaded_segments (0x7fde4 : word) = Some W_7fd94.
Proof. vm_refl. Qed.
Lemma D_7fd94 : decode_any W_7fd94 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd98 : bv 32 := 0x0077f793.
Lemma F_7fd98 : fetch_word Asan.M.loaded_segments (0x7fde8 : word) = Some W_7fd98.
Proof. vm_refl. Qed.
Lemma D_7fd98 : decode_any W_7fd98 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd9c : bv 32 := 0x010038b3.
Lemma F_7fd9c : fetch_word Asan.M.loaded_segments (0x7fdec : word) = Some W_7fd9c.
Proof. vm_refl. Qed.
Lemma D_7fd9c : decode_any W_7fd9c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda0 : bv 32 := 0x0107a7b3.
Lemma F_7fda0 : fetch_word Asan.M.loaded_segments (0x7fdf0 : word) = Some W_7fda0.
Proof. vm_refl. Qed.
Lemma D_7fda0 : decode_any W_7fda0 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda4 : bv 32 := 0x0017c793.
Lemma F_7fda4 : fetch_word Asan.M.loaded_segments (0x7fdf4 : word) = Some W_7fda4.
Proof. vm_refl. Qed.
Lemma D_7fda4 : decode_any W_7fda4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda8 : bv 32 := 0x00f8f7b3.
Lemma F_7fda8 : fetch_word Asan.M.loaded_segments (0x7fdf8 : word) = Some W_7fda8.
Proof. vm_refl. Qed.
Lemma D_7fda8 : decode_any W_7fda8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdac : bv 32 := 0x00e6fa63.
Lemma F_7fdac : fetch_word Asan.M.loaded_segments (0x7fdfc : word) = Some W_7fdac.
Proof. vm_refl. Qed.
Lemma D_7fdac : decode_any W_7fdac = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb0 : bv 32 := 0x0006c803.
Lemma F_7fdb0 : fetch_word Asan.M.loaded_segments (0x7fe00 : word) = Some W_7fdb0.
Proof. vm_refl. Qed.
Lemma D_7fdb0 : decode_any W_7fdb0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb4 : bv 32 := 0x00168693.
Lemma F_7fdb4 : fetch_word Asan.M.loaded_segments (0x7fe04 : word) = Some W_7fdb4.
Proof. vm_refl. Qed.
Lemma D_7fdb4 : decode_any W_7fdb4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb8 : bv 32 := 0x00f867b3.
Lemma F_7fdb8 : fetch_word Asan.M.loaded_segments (0x7fe08 : word) = Some W_7fdb8.
Proof. vm_refl. Qed.
Lemma D_7fdb8 : decode_any W_7fdb8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdbc : bv 32 := 0xfee69ae3.
Lemma F_7fdbc : fetch_word Asan.M.loaded_segments (0x7fe0c : word) = Some W_7fdbc.
Proof. vm_refl. Qed.
Lemma D_7fdbc : decode_any W_7fdbc = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc0 : bv 32 := 0x0ff7f693.
Lemma F_7fdc0 : fetch_word Asan.M.loaded_segments (0x7fe10 : word) = Some W_7fdc0.
Proof. vm_refl. Qed.
Lemma D_7fdc0 : decode_any W_7fdc0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc4 : bv 32 := 0xe2068ae3.
Lemma F_7fdc4 : fetch_word Asan.M.loaded_segments (0x7fe14 : word) = Some W_7fdc4.
Proof. vm_refl. Qed.
Lemma D_7fdc4 : decode_any W_7fdc4 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc8 : bv 32 := 0x00050b13.
Lemma F_7fdc8 : fetch_word Asan.M.loaded_segments (0x7fe18 : word) = Some W_7fdc8.
Proof. vm_refl. Qed.
Lemma D_7fdc8 : decode_any W_7fdc8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdcc : bv 32 := 0x00058513.
Lemma F_7fdcc : fetch_word Asan.M.loaded_segments (0x7fe1c : word) = Some W_7fdcc.
Proof. vm_refl. Qed.
Lemma D_7fdcc : decode_any W_7fdcc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd0 : bv 32 := 0x00058b93.
Lemma F_7fdd0 : fetch_word Asan.M.loaded_segments (0x7fe20 : word) = Some W_7fdd0.
Proof. vm_refl. Qed.
Lemma D_7fdd0 : decode_any W_7fdd0 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd4 : bv 32 := 0x00060593.
Lemma F_7fdd4 : fetch_word Asan.M.loaded_segments (0x7fe24 : word) = Some W_7fdd4.
Proof. vm_refl. Qed.
Lemma D_7fdd4 : decode_any W_7fdd4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd8 : bv 32 := 0x00060493.
Lemma F_7fdd8 : fetch_word Asan.M.loaded_segments (0x7fe28 : word) = Some W_7fdd8.
Proof. vm_refl. Qed.
Lemma D_7fdd8 : decode_any W_7fdd8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fddc : bv 32 := 0x075020ef.
Lemma F_7fddc : fetch_word Asan.M.loaded_segments (0x7fe2c : word) = Some W_7fddc.
Proof. vm_refl. Qed.
Lemma D_7fddc : decode_any W_7fddc = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde0 : bv 32 := 0x000b8593.
Lemma F_7fde0 : fetch_word Asan.M.loaded_segments (0x7fe30 : word) = Some W_7fde0.
Proof. vm_refl. Qed.
Lemma D_7fde0 : decode_any W_7fde0 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde4 : bv 32 := 0x00048613.
Lemma F_7fde4 : fetch_word Asan.M.loaded_segments (0x7fe34 : word) = Some W_7fde4.
Proof. vm_refl. Qed.
Lemma D_7fde4 : decode_any W_7fde4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde8 : bv 32 := 0x00050913.
Lemma F_7fde8 : fetch_word Asan.M.loaded_segments (0x7fe38 : word) = Some W_7fde8.
Proof. vm_refl. Qed.
Lemma D_7fde8 : decode_any W_7fde8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdec : bv 32 := 0x000b0513.
Lemma F_7fdec : fetch_word Asan.M.loaded_segments (0x7fe3c : word) = Some W_7fdec.
Proof. vm_refl. Qed.
Lemma D_7fdec : decode_any W_7fdec = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf0 : bv 32 := 0xe00904e3.
Lemma F_7fdf0 : fetch_word Asan.M.loaded_segments (0x7fe40 : word) = Some W_7fdf0.
Proof. vm_refl. Qed.
Lemma D_7fdf0 : decode_any W_7fdf0 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe94 : bv 32 := 0x00070803.
Lemma F_7fe94 : fetch_word Asan.M.loaded_segments (0x7fee4 : word) = Some W_7fe94.
Proof. vm_refl. Qed.
Lemma D_7fe94 : decode_any W_7fe94 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe98 : bv 32 := 0x0077f793.
Lemma F_7fe98 : fetch_word Asan.M.loaded_segments (0x7fee8 : word) = Some W_7fe98.
Proof. vm_refl. Qed.
Lemma D_7fe98 : decode_any W_7fe98 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe9c : bv 32 := 0x010038b3.
Lemma F_7fe9c : fetch_word Asan.M.loaded_segments (0x7feec : word) = Some W_7fe9c.
Proof. vm_refl. Qed.
Lemma D_7fe9c : decode_any W_7fe9c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea0 : bv 32 := 0x0107a7b3.
Lemma F_7fea0 : fetch_word Asan.M.loaded_segments (0x7fef0 : word) = Some W_7fea0.
Proof. vm_refl. Qed.
Lemma D_7fea0 : decode_any W_7fea0 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea4 : bv 32 := 0x0017c793.
Lemma F_7fea4 : fetch_word Asan.M.loaded_segments (0x7fef4 : word) = Some W_7fea4.
Proof. vm_refl. Qed.
Lemma D_7fea4 : decode_any W_7fea4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fea8 : bv 32 := 0x00f8f7b3.
Lemma F_7fea8 : fetch_word Asan.M.loaded_segments (0x7fef8 : word) = Some W_7fea8.
Proof. vm_refl. Qed.
Lemma D_7fea8 : decode_any W_7fea8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feac : bv 32 := 0x00e6fa63.
Lemma F_7feac : fetch_word Asan.M.loaded_segments (0x7fefc : word) = Some W_7feac.
Proof. vm_refl. Qed.
Lemma D_7feac : decode_any W_7feac = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb0 : bv 32 := 0x0006c803.
Lemma F_7feb0 : fetch_word Asan.M.loaded_segments (0x7ff00 : word) = Some W_7feb0.
Proof. vm_refl. Qed.
Lemma D_7feb0 : decode_any W_7feb0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb4 : bv 32 := 0x00168693.
Lemma F_7feb4 : fetch_word Asan.M.loaded_segments (0x7ff04 : word) = Some W_7feb4.
Proof. vm_refl. Qed.
Lemma D_7feb4 : decode_any W_7feb4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb8 : bv 32 := 0x00f867b3.
Lemma F_7feb8 : fetch_word Asan.M.loaded_segments (0x7ff08 : word) = Some W_7feb8.
Proof. vm_refl. Qed.
Lemma D_7feb8 : decode_any W_7feb8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7febc : bv 32 := 0xfee69ae3.
Lemma F_7febc : fetch_word Asan.M.loaded_segments (0x7ff0c : word) = Some W_7febc.
Proof. vm_refl. Qed.
Lemma D_7febc : decode_any W_7febc = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec0 : bv 32 := 0x0ff7f693.
Lemma F_7fec0 : fetch_word Asan.M.loaded_segments (0x7ff10 : word) = Some W_7fec0.
Proof. vm_refl. Qed.
Lemma D_7fec0 : decode_any W_7fec0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec4 : bv 32 := 0xd80680e3.
Lemma F_7fec4 : fetch_word Asan.M.loaded_segments (0x7ff14 : word) = Some W_7fec4.
Proof. vm_refl. Qed.
Lemma D_7fec4 : decode_any W_7fec4 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec8 : bv 32 := 0x00050493.
Lemma F_7fec8 : fetch_word Asan.M.loaded_segments (0x7ff18 : word) = Some W_7fec8.
Proof. vm_refl. Qed.
Lemma D_7fec8 : decode_any W_7fec8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fecc : bv 32 := 0x00058b13.
Lemma F_7fecc : fetch_word Asan.M.loaded_segments (0x7ff1c : word) = Some W_7fecc.
Proof. vm_refl. Qed.
Lemma D_7fecc : decode_any W_7fecc = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed0 : bv 32 := 0x00060593.
Lemma F_7fed0 : fetch_word Asan.M.loaded_segments (0x7ff20 : word) = Some W_7fed0.
Proof. vm_refl. Qed.
Lemma D_7fed0 : decode_any W_7fed0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed4 : bv 32 := 0x00060913.
Lemma F_7fed4 : fetch_word Asan.M.loaded_segments (0x7ff24 : word) = Some W_7fed4.
Proof. vm_refl. Qed.
Lemma D_7fed4 : decode_any W_7fed4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed8 : bv 32 := 0x778020ef.
Lemma F_7fed8 : fetch_word Asan.M.loaded_segments (0x7ff28 : word) = Some W_7fed8.
Proof. vm_refl. Qed.
Lemma D_7fed8 : decode_any W_7fed8 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fedc : bv 32 := 0x000b0593.
Lemma F_7fedc : fetch_word Asan.M.loaded_segments (0x7ff2c : word) = Some W_7fedc.
Proof. vm_refl. Qed.
Lemma D_7fedc : decode_any W_7fedc = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee0 : bv 32 := 0x00090613.
Lemma F_7fee0 : fetch_word Asan.M.loaded_segments (0x7ff30 : word) = Some W_7fee0.
Proof. vm_refl. Qed.
Lemma D_7fee0 : decode_any W_7fee0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee4 : bv 32 := 0x00050993.
Lemma F_7fee4 : fetch_word Asan.M.loaded_segments (0x7ff34 : word) = Some W_7fee4.
Proof. vm_refl. Qed.
Lemma D_7fee4 : decode_any W_7fee4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee8 : bv 32 := 0x00048513.
Lemma F_7fee8 : fetch_word Asan.M.loaded_segments (0x7ff38 : word) = Some W_7fee8.
Proof. vm_refl. Qed.
Lemma D_7fee8 : decode_any W_7fee8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feec : bv 32 := 0xd4098ce3.
Lemma F_7feec : fetch_word Asan.M.loaded_segments (0x7ff3c : word) = Some W_7feec.
Proof. vm_refl. Qed.
Lemma D_7feec : decode_any W_7feec = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

