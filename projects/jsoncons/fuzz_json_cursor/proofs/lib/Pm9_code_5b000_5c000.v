(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5b4a0 : bv 32 := 0xfd010113.
Lemma F_5b4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b4e8 : word) = Some W_5b4a0.
Proof. vm_refl. Qed.
Lemma D_5b4a0 : decode_any W_5b4a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4a4 : bv 32 := 0x02113423.
Lemma F_5b4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b4ec : word) = Some W_5b4a4.
Proof. vm_refl. Qed.
Lemma D_5b4a4 : decode_any W_5b4a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4a8 : bv 32 := 0x02813023.
Lemma F_5b4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b4f0 : word) = Some W_5b4a8.
Proof. vm_refl. Qed.
Lemma D_5b4a8 : decode_any W_5b4a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4ac : bv 32 := 0x00913c23.
Lemma F_5b4ac : fetch_word AsanUbsan.M.loaded_segments (0x5b4f4 : word) = Some W_5b4ac.
Proof. vm_refl. Qed.
Lemma D_5b4ac : decode_any W_5b4ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b0 : bv 32 := 0x01213823.
Lemma F_5b4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b4f8 : word) = Some W_5b4b0.
Proof. vm_refl. Qed.
Lemma D_5b4b0 : decode_any W_5b4b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b4 : bv 32 := 0x01313423.
Lemma F_5b4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b4fc : word) = Some W_5b4b4.
Proof. vm_refl. Qed.
Lemma D_5b4b4 : decode_any W_5b4b4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b8 : bv 32 := 0x09850713.
Lemma F_5b4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b500 : word) = Some W_5b4b8.
Proof. vm_refl. Qed.
Lemma D_5b4b8 : decode_any W_5b4b8 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4bc : bv 32 := 0x0ff00793.
Lemma F_5b4bc : fetch_word AsanUbsan.M.loaded_segments (0x5b504 : word) = Some W_5b4bc.
Proof. vm_refl. Qed.
Lemma D_5b4bc : decode_any W_5b4bc = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c0 : bv 32 := 0xffc77813.
Lemma F_5b4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b508 : word) = Some W_5b4c0.
Proof. vm_refl. Qed.
Lemma D_5b4c0 : decode_any W_5b4c0 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c4 : bv 32 := 0x00100893.
Lemma F_5b4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b50c : word) = Some W_5b4c4.
Proof. vm_refl. Qed.
Lemma D_5b4c4 : decode_any W_5b4c4 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c8 : bv 32 := 0x140822af.
Lemma F_5b4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b510 : word) = Some W_5b4c8.
Proof. vm_refl. Qed.
Lemma D_5b4c8 : decode_any W_5b4c8 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4cc : bv 32 := 0x00088313.
Lemma F_5b4cc : fetch_word AsanUbsan.M.loaded_segments (0x5b514 : word) = Some W_5b4cc.
Proof. vm_refl. Qed.
Lemma D_5b4cc : decode_any W_5b4cc = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d0 : bv 32 := 0x0062c333.
Lemma F_5b4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b518 : word) = Some W_5b4d0.
Proof. vm_refl. Qed.
Lemma D_5b4d0 : decode_any W_5b4d0 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d4 : bv 32 := 0x00f37333.
Lemma F_5b4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b51c : word) = Some W_5b4d4.
Proof. vm_refl. Qed.
Lemma D_5b4d4 : decode_any W_5b4d4 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d8 : bv 32 := 0x0062c333.
Lemma F_5b4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b520 : word) = Some W_5b4d8.
Proof. vm_refl. Qed.
Lemma D_5b4d8 : decode_any W_5b4d8 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4dc : bv 32 := 0x1868232f.
Lemma F_5b4dc : fetch_word AsanUbsan.M.loaded_segments (0x5b524 : word) = Some W_5b4dc.
Proof. vm_refl. Qed.
Lemma D_5b4dc : decode_any W_5b4dc = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e0 : bv 32 := 0xfe0314e3.
Lemma F_5b4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b528 : word) = Some W_5b4e0.
Proof. vm_refl. Qed.
Lemma D_5b4e0 : decode_any W_5b4e0 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e4 : bv 32 := 0x0ff2f793.
Lemma F_5b4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b52c : word) = Some W_5b4e4.
Proof. vm_refl. Qed.
Lemma D_5b4e4 : decode_any W_5b4e4 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e8 : bv 32 := 0x10079663.
Lemma F_5b4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b530 : word) = Some W_5b4e8.
Proof. vm_refl. Qed.
Lemma D_5b4e8 : decode_any W_5b4e8 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4ec : bv 32 := 0x0a050713.
Lemma F_5b4ec : fetch_word AsanUbsan.M.loaded_segments (0x5b534 : word) = Some W_5b4ec.
Proof. vm_refl. Qed.
Lemma D_5b4ec : decode_any W_5b4ec = Some (OpImm ALU_ADD 14 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f0 : bv 32 := 0x12b70a63.
Lemma F_5b4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b538 : word) = Some W_5b4f0.
Proof. vm_refl. Qed.
Lemma D_5b4f0 : decode_any W_5b4f0 = Some (Branch BC_EQ 14 11 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f4 : bv 32 := 0x0005b783.
Lemma F_5b4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5b53c : word) = Some W_5b4f4.
Proof. vm_refl. Qed.
Lemma D_5b4f4 : decode_any W_5b4f4 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f8 : bv 32 := 0x04078863.
Lemma F_5b4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5b540 : word) = Some W_5b4f8.
Proof. vm_refl. Qed.
Lemma D_5b4f8 : decode_any W_5b4f8 = Some (Branch BC_EQ 15 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4fc : bv 32 := 0x00073803.
Lemma F_5b4fc : fetch_word AsanUbsan.M.loaded_segments (0x5b544 : word) = Some W_5b4fc.
Proof. vm_refl. Qed.
Lemma D_5b4fc : decode_any W_5b4fc = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b500 : bv 32 := 0x02080263.
Lemma F_5b500 : fetch_word AsanUbsan.M.loaded_segments (0x5b548 : word) = Some W_5b500.
Proof. vm_refl. Qed.
Lemma D_5b500 : decode_any W_5b500 = Some (Branch BC_EQ 16 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b504 : bv 32 := 0x0b053703.
Lemma F_5b504 : fetch_word AsanUbsan.M.loaded_segments (0x5b54c : word) = Some W_5b504.
Proof. vm_refl. Qed.
Lemma D_5b504 : decode_any W_5b504 = Some (Load SZ8 true 14 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b508 : bv 32 := 0x0085b883.
Lemma F_5b508 : fetch_word AsanUbsan.M.loaded_segments (0x5b550 : word) = Some W_5b508.
Proof. vm_refl. Qed.
Lemma D_5b508 : decode_any W_5b508 = Some (Load SZ8 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b50c : bv 32 := 0x0105b283.
Lemma F_5b50c : fetch_word AsanUbsan.M.loaded_segments (0x5b554 : word) = Some W_5b50c.
Proof. vm_refl. Qed.
Lemma D_5b50c : decode_any W_5b50c = Some (Load SZ8 true 5 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b510 : bv 32 := 0x00f807b3.
Lemma F_5b510 : fetch_word AsanUbsan.M.loaded_segments (0x5b558 : word) = Some W_5b510.
Proof. vm_refl. Qed.
Lemma D_5b510 : decode_any W_5b510 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b514 : bv 32 := 0x01173023.
Lemma F_5b514 : fetch_word AsanUbsan.M.loaded_segments (0x5b55c : word) = Some W_5b514.
Proof. vm_refl. Qed.
Lemma D_5b514 : decode_any W_5b514 = Some (Store SZ8 14 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b518 : bv 32 := 0x0af53023.
Lemma F_5b518 : fetch_word AsanUbsan.M.loaded_segments (0x5b560 : word) = Some W_5b518.
Proof. vm_refl. Qed.
Lemma D_5b518 : decode_any W_5b518 = Some (Store SZ8 10 15 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b51c : bv 32 := 0x0a553823.
Lemma F_5b51c : fetch_word AsanUbsan.M.loaded_segments (0x5b564 : word) = Some W_5b51c.
Proof. vm_refl. Qed.
Lemma D_5b51c : decode_any W_5b51c = Some (Store SZ8 10 5 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b520 : bv 32 := 0x01c0006f.
Lemma F_5b520 : fetch_word AsanUbsan.M.loaded_segments (0x5b568 : word) = Some W_5b520.
Proof. vm_refl. Qed.
Lemma D_5b520 : decode_any W_5b520 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b524 : bv 32 := 0x0105b783.
Lemma F_5b524 : fetch_word AsanUbsan.M.loaded_segments (0x5b56c : word) = Some W_5b524.
Proof. vm_refl. Qed.
Lemma D_5b524 : decode_any W_5b524 = Some (Load SZ8 true 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b528 : bv 32 := 0x00f73823.
Lemma F_5b528 : fetch_word AsanUbsan.M.loaded_segments (0x5b570 : word) = Some W_5b528.
Proof. vm_refl. Qed.
Lemma D_5b528 : decode_any W_5b528 = Some (Store SZ8 14 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b52c : bv 32 := 0x0085b783.
Lemma F_5b52c : fetch_word AsanUbsan.M.loaded_segments (0x5b574 : word) = Some W_5b52c.
Proof. vm_refl. Qed.
Lemma D_5b52c : decode_any W_5b52c = Some (Load SZ8 true 15 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b530 : bv 32 := 0x00f73423.
Lemma F_5b530 : fetch_word AsanUbsan.M.loaded_segments (0x5b578 : word) = Some W_5b530.
Proof. vm_refl. Qed.
Lemma D_5b530 : decode_any W_5b530 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b534 : bv 32 := 0x0005b783.
Lemma F_5b534 : fetch_word AsanUbsan.M.loaded_segments (0x5b57c : word) = Some W_5b534.
Proof. vm_refl. Qed.
Lemma D_5b534 : decode_any W_5b534 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b538 : bv 32 := 0x00f73023.
Lemma F_5b538 : fetch_word AsanUbsan.M.loaded_segments (0x5b580 : word) = Some W_5b538.
Proof. vm_refl. Qed.
Lemma D_5b538 : decode_any W_5b538 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b53c : bv 32 := 0x0005b023.
Lemma F_5b53c : fetch_word AsanUbsan.M.loaded_segments (0x5b584 : word) = Some W_5b53c.
Proof. vm_refl. Qed.
Lemma D_5b53c : decode_any W_5b53c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b540 : bv 32 := 0x0005b423.
Lemma F_5b540 : fetch_word AsanUbsan.M.loaded_segments (0x5b588 : word) = Some W_5b540.
Proof. vm_refl. Qed.
Lemma D_5b540 : decode_any W_5b540 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b544 : bv 32 := 0x0005b823.
Lemma F_5b544 : fetch_word AsanUbsan.M.loaded_segments (0x5b58c : word) = Some W_5b544.
Proof. vm_refl. Qed.
Lemma D_5b544 : decode_any W_5b544 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b548 : bv 32 := 0x0185b703.
Lemma F_5b548 : fetch_word AsanUbsan.M.loaded_segments (0x5b590 : word) = Some W_5b548.
Proof. vm_refl. Qed.
Lemma D_5b548 : decode_any W_5b548 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b54c : bv 32 := 0x0b853783.
Lemma F_5b54c : fetch_word AsanUbsan.M.loaded_segments (0x5b594 : word) = Some W_5b54c.
Proof. vm_refl. Qed.
Lemma D_5b54c : decode_any W_5b54c = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b550 : bv 32 := 0x00e78733.
Lemma F_5b550 : fetch_word AsanUbsan.M.loaded_segments (0x5b598 : word) = Some W_5b550.
Proof. vm_refl. Qed.
Lemma D_5b550 : decode_any W_5b550 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b554 : bv 32 := 0x0ae53c23.
Lemma F_5b554 : fetch_word AsanUbsan.M.loaded_segments (0x5b59c : word) = Some W_5b554.
Proof. vm_refl. Qed.
Lemma D_5b554 : decode_any W_5b554 = Some (Store SZ8 10 14 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b558 : bv 32 := 0x0005bc23.
Lemma F_5b558 : fetch_word AsanUbsan.M.loaded_segments (0x5b5a0 : word) = Some W_5b558.
Proof. vm_refl. Qed.
Lemma D_5b558 : decode_any W_5b558 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b55c : bv 32 := 0x0310000f.
Lemma F_5b55c : fetch_word AsanUbsan.M.loaded_segments (0x5b5a4 : word) = Some W_5b55c.
Proof. vm_refl. Qed.
Lemma D_5b55c : decode_any W_5b55c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b560 : bv 32 := 0x08050c23.
Lemma F_5b560 : fetch_word AsanUbsan.M.loaded_segments (0x5b5a8 : word) = Some W_5b560.
Proof. vm_refl. Qed.
Lemma D_5b560 : decode_any W_5b560 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b564 : bv 32 := 0x0b853583.
Lemma F_5b564 : fetch_word AsanUbsan.M.loaded_segments (0x5b5ac : word) = Some W_5b564.
Proof. vm_refl. Qed.
Lemma D_5b564 : decode_any W_5b564 = Some (Load SZ8 true 11 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b568 : bv 32 := 0x04053703.
Lemma F_5b568 : fetch_word AsanUbsan.M.loaded_segments (0x5b5b0 : word) = Some W_5b568.
Proof. vm_refl. Qed.
Lemma D_5b568 : decode_any W_5b568 = Some (Load SZ8 true 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b56c : bv 32 := 0x04b77663.
Lemma F_5b56c : fetch_word AsanUbsan.M.loaded_segments (0x5b5b4 : word) = Some W_5b56c.
Proof. vm_refl. Qed.
Lemma D_5b56c : decode_any W_5b56c = Some (Branch BC_GEU 14 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b570 : bv 32 := 0x09950593.
Lemma F_5b570 : fetch_word AsanUbsan.M.loaded_segments (0x5b5b8 : word) = Some W_5b570.
Proof. vm_refl. Qed.
Lemma D_5b570 : decode_any W_5b570 = Some (OpImm ALU_ADD 11 10 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b574 : bv 32 := 0x0ff00713.
Lemma F_5b574 : fetch_word AsanUbsan.M.loaded_segments (0x5b5bc : word) = Some W_5b574.
Proof. vm_refl. Qed.
Lemma D_5b574 : decode_any W_5b574 = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b578 : bv 32 := 0x00100793.
Lemma F_5b578 : fetch_word AsanUbsan.M.loaded_segments (0x5b5c0 : word) = Some W_5b578.
Proof. vm_refl. Qed.
Lemma D_5b578 : decode_any W_5b578 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b57c : bv 32 := 0xffc5f813.
Lemma F_5b57c : fetch_word AsanUbsan.M.loaded_segments (0x5b5c4 : word) = Some W_5b57c.
Proof. vm_refl. Qed.
Lemma D_5b57c : decode_any W_5b57c = Some (OpImm ALU_AND 16 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b580 : bv 32 := 0x0035f593.
Lemma F_5b580 : fetch_word AsanUbsan.M.loaded_segments (0x5b5c8 : word) = Some W_5b580.
Proof. vm_refl. Qed.
Lemma D_5b580 : decode_any W_5b580 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b584 : bv 32 := 0x00359593.
Lemma F_5b584 : fetch_word AsanUbsan.M.loaded_segments (0x5b5cc : word) = Some W_5b584.
Proof. vm_refl. Qed.
Lemma D_5b584 : decode_any W_5b584 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b588 : bv 32 := 0x00b7173b.
Lemma F_5b588 : fetch_word AsanUbsan.M.loaded_segments (0x5b5d0 : word) = Some W_5b588.
Proof. vm_refl. Qed.
Lemma D_5b588 : decode_any W_5b588 = Some (Op32 ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b58c : bv 32 := 0x00b797bb.
Lemma F_5b58c : fetch_word AsanUbsan.M.loaded_segments (0x5b5d4 : word) = Some W_5b58c.
Proof. vm_refl. Qed.
Lemma D_5b58c : decode_any W_5b58c = Some (Op32 ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b590 : bv 32 := 0x140828af.
Lemma F_5b590 : fetch_word AsanUbsan.M.loaded_segments (0x5b5d8 : word) = Some W_5b590.
Proof. vm_refl. Qed.
Lemma D_5b590 : decode_any W_5b590 = Some (Lr AW true false 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b594 : bv 32 := 0x00078293.
Lemma F_5b594 : fetch_word AsanUbsan.M.loaded_segments (0x5b5dc : word) = Some W_5b594.
Proof. vm_refl. Qed.
Lemma D_5b594 : decode_any W_5b594 = Some (OpImm ALU_ADD 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b598 : bv 32 := 0x0058c2b3.
Lemma F_5b598 : fetch_word AsanUbsan.M.loaded_segments (0x5b5e0 : word) = Some W_5b598.
Proof. vm_refl. Qed.
Lemma D_5b598 : decode_any W_5b598 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b59c : bv 32 := 0x00e2f2b3.
Lemma F_5b59c : fetch_word AsanUbsan.M.loaded_segments (0x5b5e4 : word) = Some W_5b59c.
Proof. vm_refl. Qed.
Lemma D_5b59c : decode_any W_5b59c = Some (Op ALU_AND 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a0 : bv 32 := 0x0058c2b3.
Lemma F_5b5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b5e8 : word) = Some W_5b5a0.
Proof. vm_refl. Qed.
Lemma D_5b5a0 : decode_any W_5b5a0 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a4 : bv 32 := 0x185822af.
Lemma F_5b5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b5ec : word) = Some W_5b5a4.
Proof. vm_refl. Qed.
Lemma D_5b5a4 : decode_any W_5b5a4 = Some (Sc AW false false 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a8 : bv 32 := 0xfe0294e3.
Lemma F_5b5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b5f0 : word) = Some W_5b5a8.
Proof. vm_refl. Qed.
Lemma D_5b5a8 : decode_any W_5b5a8 = Some (Branch BC_NE 5 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5ac : bv 32 := 0x00b8d5bb.
Lemma F_5b5ac : fetch_word AsanUbsan.M.loaded_segments (0x5b5f4 : word) = Some W_5b5ac.
Proof. vm_refl. Qed.
Lemma D_5b5ac : decode_any W_5b5ac = Some (Op32 ALU_SRL 11 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b0 : bv 32 := 0x0ff5f593.
Lemma F_5b5b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b5f8 : word) = Some W_5b5b0.
Proof. vm_refl. Qed.
Lemma D_5b5b0 : decode_any W_5b5b0 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b4 : bv 32 := 0x02058063.
Lemma F_5b5b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b5fc : word) = Some W_5b5b4.
Proof. vm_refl. Qed.
Lemma D_5b5b4 : decode_any W_5b5b4 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b8 : bv 32 := 0x02813083.
Lemma F_5b5b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b600 : word) = Some W_5b5b8.
Proof. vm_refl. Qed.
Lemma D_5b5b8 : decode_any W_5b5b8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5bc : bv 32 := 0x02013403.
Lemma F_5b5bc : fetch_word AsanUbsan.M.loaded_segments (0x5b604 : word) = Some W_5b5bc.
Proof. vm_refl. Qed.
Lemma D_5b5bc : decode_any W_5b5bc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c0 : bv 32 := 0x01813483.
Lemma F_5b5c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b608 : word) = Some W_5b5c0.
Proof. vm_refl. Qed.
Lemma D_5b5c0 : decode_any W_5b5c0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c4 : bv 32 := 0x01013903.
Lemma F_5b5c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b60c : word) = Some W_5b5c4.
Proof. vm_refl. Qed.
Lemma D_5b5c4 : decode_any W_5b5c4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c8 : bv 32 := 0x00813983.
Lemma F_5b5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b610 : word) = Some W_5b5c8.
Proof. vm_refl. Qed.
Lemma D_5b5c8 : decode_any W_5b5c8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5cc : bv 32 := 0x03010113.
Lemma F_5b5cc : fetch_word AsanUbsan.M.loaded_segments (0x5b614 : word) = Some W_5b5cc.
Proof. vm_refl. Qed.
Lemma D_5b5cc : decode_any W_5b5cc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d0 : bv 32 := 0x00008067.
Lemma F_5b5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b618 : word) = Some W_5b5d0.
Proof. vm_refl. Qed.
Lemma D_5b5d0 : decode_any W_5b5d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d4 : bv 32 := 0x04853583.
Lemma F_5b5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5b61c : word) = Some W_5b5d4.
Proof. vm_refl. Qed.
Lemma D_5b5d4 : decode_any W_5b5d4 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d8 : bv 32 := 0x02813083.
Lemma F_5b5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5b620 : word) = Some W_5b5d8.
Proof. vm_refl. Qed.
Lemma D_5b5d8 : decode_any W_5b5d8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5dc : bv 32 := 0x02013403.
Lemma F_5b5dc : fetch_word AsanUbsan.M.loaded_segments (0x5b624 : word) = Some W_5b5dc.
Proof. vm_refl. Qed.
Lemma D_5b5dc : decode_any W_5b5dc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e0 : bv 32 := 0x01813483.
Lemma F_5b5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5b628 : word) = Some W_5b5e0.
Proof. vm_refl. Qed.
Lemma D_5b5e0 : decode_any W_5b5e0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e4 : bv 32 := 0x01013903.
Lemma F_5b5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5b62c : word) = Some W_5b5e4.
Proof. vm_refl. Qed.
Lemma D_5b5e4 : decode_any W_5b5e4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e8 : bv 32 := 0x00813983.
Lemma F_5b5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5b630 : word) = Some W_5b5e8.
Proof. vm_refl. Qed.
Lemma D_5b5e8 : decode_any W_5b5e8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5ec : bv 32 := 0x03010113.
Lemma F_5b5ec : fetch_word AsanUbsan.M.loaded_segments (0x5b634 : word) = Some W_5b5ec.
Proof. vm_refl. Qed.
Lemma D_5b5ec : decode_any W_5b5ec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f0 : bv 32 := 0x0540006f.
Lemma F_5b5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5b638 : word) = Some W_5b5f0.
Proof. vm_refl. Qed.
Lemma D_5b5f0 : decode_any W_5b5f0 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b644 : bv 32 := 0xfb010113.
Lemma F_5b644 : fetch_word AsanUbsan.M.loaded_segments (0x5b68c : word) = Some W_5b644.
Proof. vm_refl. Qed.
Lemma D_5b644 : decode_any W_5b644 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b648 : bv 32 := 0x04113423.
Lemma F_5b648 : fetch_word AsanUbsan.M.loaded_segments (0x5b690 : word) = Some W_5b648.
Proof. vm_refl. Qed.
Lemma D_5b648 : decode_any W_5b648 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b64c : bv 32 := 0x04813023.
Lemma F_5b64c : fetch_word AsanUbsan.M.loaded_segments (0x5b694 : word) = Some W_5b64c.
Proof. vm_refl. Qed.
Lemma D_5b64c : decode_any W_5b64c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b650 : bv 32 := 0x02913c23.
Lemma F_5b650 : fetch_word AsanUbsan.M.loaded_segments (0x5b698 : word) = Some W_5b650.
Proof. vm_refl. Qed.
Lemma D_5b650 : decode_any W_5b650 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b654 : bv 32 := 0x03213823.
Lemma F_5b654 : fetch_word AsanUbsan.M.loaded_segments (0x5b69c : word) = Some W_5b654.
Proof. vm_refl. Qed.
Lemma D_5b654 : decode_any W_5b654 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b658 : bv 32 := 0x03313423.
Lemma F_5b658 : fetch_word AsanUbsan.M.loaded_segments (0x5b6a0 : word) = Some W_5b658.
Proof. vm_refl. Qed.
Lemma D_5b658 : decode_any W_5b658 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b65c : bv 32 := 0x03413023.
Lemma F_5b65c : fetch_word AsanUbsan.M.loaded_segments (0x5b6a4 : word) = Some W_5b65c.
Proof. vm_refl. Qed.
Lemma D_5b65c : decode_any W_5b65c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b660 : bv 32 := 0x00013023.
Lemma F_5b660 : fetch_word AsanUbsan.M.loaded_segments (0x5b6a8 : word) = Some W_5b660.
Proof. vm_refl. Qed.
Lemma D_5b660 : decode_any W_5b660 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b664 : bv 32 := 0x00013423.
Lemma F_5b664 : fetch_word AsanUbsan.M.loaded_segments (0x5b6ac : word) = Some W_5b664.
Proof. vm_refl. Qed.
Lemma D_5b664 : decode_any W_5b664 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b668 : bv 32 := 0x00013823.
Lemma F_5b668 : fetch_word AsanUbsan.M.loaded_segments (0x5b6b0 : word) = Some W_5b668.
Proof. vm_refl. Qed.
Lemma D_5b668 : decode_any W_5b668 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b66c : bv 32 := 0x00013c23.
Lemma F_5b66c : fetch_word AsanUbsan.M.loaded_segments (0x5b6b4 : word) = Some W_5b66c.
Proof. vm_refl. Qed.
Lemma D_5b66c : decode_any W_5b66c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b670 : bv 32 := 0x09850713.
Lemma F_5b670 : fetch_word AsanUbsan.M.loaded_segments (0x5b6b8 : word) = Some W_5b670.
Proof. vm_refl. Qed.
Lemma D_5b670 : decode_any W_5b670 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b674 : bv 32 := 0x0ff00793.
Lemma F_5b674 : fetch_word AsanUbsan.M.loaded_segments (0x5b6bc : word) = Some W_5b674.
Proof. vm_refl. Qed.
Lemma D_5b674 : decode_any W_5b674 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b678 : bv 32 := 0xffc77813.
Lemma F_5b678 : fetch_word AsanUbsan.M.loaded_segments (0x5b6c0 : word) = Some W_5b678.
Proof. vm_refl. Qed.
Lemma D_5b678 : decode_any W_5b678 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b67c : bv 32 := 0x00100893.
Lemma F_5b67c : fetch_word AsanUbsan.M.loaded_segments (0x5b6c4 : word) = Some W_5b67c.
Proof. vm_refl. Qed.
Lemma D_5b67c : decode_any W_5b67c = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b680 : bv 32 := 0x140822af.
Lemma F_5b680 : fetch_word AsanUbsan.M.loaded_segments (0x5b6c8 : word) = Some W_5b680.
Proof. vm_refl. Qed.
Lemma D_5b680 : decode_any W_5b680 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b684 : bv 32 := 0x00088313.
Lemma F_5b684 : fetch_word AsanUbsan.M.loaded_segments (0x5b6cc : word) = Some W_5b684.
Proof. vm_refl. Qed.
Lemma D_5b684 : decode_any W_5b684 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b688 : bv 32 := 0x0062c333.
Lemma F_5b688 : fetch_word AsanUbsan.M.loaded_segments (0x5b6d0 : word) = Some W_5b688.
Proof. vm_refl. Qed.
Lemma D_5b688 : decode_any W_5b688 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b68c : bv 32 := 0x00f37333.
Lemma F_5b68c : fetch_word AsanUbsan.M.loaded_segments (0x5b6d4 : word) = Some W_5b68c.
Proof. vm_refl. Qed.
Lemma D_5b68c : decode_any W_5b68c = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b690 : bv 32 := 0x0062c333.
Lemma F_5b690 : fetch_word AsanUbsan.M.loaded_segments (0x5b6d8 : word) = Some W_5b690.
Proof. vm_refl. Qed.
Lemma D_5b690 : decode_any W_5b690 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b694 : bv 32 := 0x1868232f.
Lemma F_5b694 : fetch_word AsanUbsan.M.loaded_segments (0x5b6dc : word) = Some W_5b694.
Proof. vm_refl. Qed.
Lemma D_5b694 : decode_any W_5b694 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b698 : bv 32 := 0xfe0314e3.
Lemma F_5b698 : fetch_word AsanUbsan.M.loaded_segments (0x5b6e0 : word) = Some W_5b698.
Proof. vm_refl. Qed.
Lemma D_5b698 : decode_any W_5b698 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b69c : bv 32 := 0x0ff2f793.
Lemma F_5b69c : fetch_word AsanUbsan.M.loaded_segments (0x5b6e4 : word) = Some W_5b69c.
Proof. vm_refl. Qed.
Lemma D_5b69c : decode_any W_5b69c = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a0 : bv 32 := 0x12079a63.
Lemma F_5b6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b6e8 : word) = Some W_5b6a0.
Proof. vm_refl. Qed.
Lemma D_5b6a0 : decode_any W_5b6a0 = Some (Branch BC_NE 15 0 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a4 : bv 32 := 0x0b853783.
Lemma F_5b6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b6ec : word) = Some W_5b6a4.
Proof. vm_refl. Qed.
Lemma D_5b6a4 : decode_any W_5b6a4 = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a8 : bv 32 := 0x0a053803.
Lemma F_5b6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b6f0 : word) = Some W_5b6a8.
Proof. vm_refl. Qed.
Lemma D_5b6a8 : decode_any W_5b6a8 = Some (Load SZ8 true 16 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6ac : bv 32 := 0x00d81713.
Lemma F_5b6ac : fetch_word AsanUbsan.M.loaded_segments (0x5b6f4 : word) = Some W_5b6ac.
Proof. vm_refl. Qed.
Lemma D_5b6ac : decode_any W_5b6ac = Some (ShiftImm ALU_SLL 14 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b0 : bv 32 := 0x14e7ee63.
Lemma F_5b6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b6f8 : word) = Some W_5b6b0.
Proof. vm_refl. Qed.
Lemma D_5b6b0 : decode_any W_5b6b0 = Some (Branch BC_LTU 15 14 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b4 : bv 32 := 0x04f77663.
Lemma F_5b6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b6fc : word) = Some W_5b6b4.
Proof. vm_refl. Qed.
Lemma D_5b6b4 : decode_any W_5b6b4 = Some (Branch BC_GEU 14 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b8 : bv 32 := 0x00190737.
Lemma F_5b6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b700 : word) = Some W_5b6b8.
Proof. vm_refl. Qed.
Lemma D_5b6b8 : decode_any W_5b6b8 = Some (Lui 14 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6bc : bv 32 := 0x06400893.
Lemma F_5b6bc : fetch_word AsanUbsan.M.loaded_segments (0x5b704 : word) = Some W_5b6bc.
Proof. vm_refl. Qed.
Lemma D_5b6bc : decode_any W_5b6bc = Some (OpImm ALU_ADD 17 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c0 : bv 32 := 0x02e80733.
Lemma F_5b6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b708 : word) = Some W_5b6c0.
Proof. vm_refl. Qed.
Lemma D_5b6c0 : decode_any W_5b6c0 = Some (Mul M_MUL 14 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c4 : bv 32 := 0x031787b3.
Lemma F_5b6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b70c : word) = Some W_5b6c4.
Proof. vm_refl. Qed.
Lemma D_5b6c4 : decode_any W_5b6c4 = Some (Mul M_MUL 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c8 : bv 32 := 0x02e7fc63.
Lemma F_5b6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b710 : word) = Some W_5b6c8.
Proof. vm_refl. Qed.
Lemma D_5b6c8 : decode_any W_5b6c8 = Some (Branch BC_GEU 15 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b700 : bv 32 := 0x00013703.
Lemma F_5b700 : fetch_word AsanUbsan.M.loaded_segments (0x5b748 : word) = Some W_5b700.
Proof. vm_refl. Qed.
Lemma D_5b700 : decode_any W_5b700 = Some (Load SZ8 true 14 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b704 : bv 32 := 0x01013783.
Lemma F_5b704 : fetch_word AsanUbsan.M.loaded_segments (0x5b74c : word) = Some W_5b704.
Proof. vm_refl. Qed.
Lemma D_5b704 : decode_any W_5b704 = Some (Load SZ8 true 15 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b708 : bv 32 := 0x0b853883.
Lemma F_5b708 : fetch_word AsanUbsan.M.loaded_segments (0x5b750 : word) = Some W_5b708.
Proof. vm_refl. Qed.
Lemma D_5b708 : decode_any W_5b708 = Some (Load SZ8 true 17 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b70c : bv 32 := 0x0915f863.
Lemma F_5b70c : fetch_word AsanUbsan.M.loaded_segments (0x5b754 : word) = Some W_5b70c.
Proof. vm_refl. Qed.
Lemma D_5b70c : decode_any W_5b70c = Some (Branch BC_GEU 11 17 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b710 : bv 32 := 0x0a853283.
Lemma F_5b710 : fetch_word AsanUbsan.M.loaded_segments (0x5b758 : word) = Some W_5b710.
Proof. vm_refl. Qed.
Lemma D_5b710 : decode_any W_5b710 = Some (Load SZ8 true 5 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b714 : bv 32 := 0x02c0006f.
Lemma F_5b714 : fetch_word AsanUbsan.M.loaded_segments (0x5b75c : word) = Some W_5b714.
Proof. vm_refl. Qed.
Lemma D_5b714 : decode_any W_5b714 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b718 : bv 32 := 0x0067b023.
Lemma F_5b718 : fetch_word AsanUbsan.M.loaded_segments (0x5b760 : word) = Some W_5b718.
Proof. vm_refl. Qed.
Lemma D_5b718 : decode_any W_5b718 = Some (Store SZ8 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b71c : bv 32 := 0x00833783.
Lemma F_5b71c : fetch_word AsanUbsan.M.loaded_segments (0x5b764 : word) = Some W_5b71c.
Proof. vm_refl. Qed.
Lemma D_5b71c : decode_any W_5b71c = Some (Load SZ8 true 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b720 : bv 32 := 0x01813283.
Lemma F_5b720 : fetch_word AsanUbsan.M.loaded_segments (0x5b768 : word) = Some W_5b720.
Proof. vm_refl. Qed.
Lemma D_5b720 : decode_any W_5b720 = Some (Load SZ8 true 5 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b724 : bv 32 := 0x00f287b3.
Lemma F_5b724 : fetch_word AsanUbsan.M.loaded_segments (0x5b76c : word) = Some W_5b724.
Proof. vm_refl. Qed.
Lemma D_5b724 : decode_any W_5b724 = Some (Op ALU_ADD 15 5 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b728 : bv 32 := 0x00f13c23.
Lemma F_5b728 : fetch_word AsanUbsan.M.loaded_segments (0x5b770 : word) = Some W_5b728.
Proof. vm_refl. Qed.
Lemma D_5b728 : decode_any W_5b728 = Some (Store SZ8 2 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b72c : bv 32 := 0x0b853383.
Lemma F_5b72c : fetch_word AsanUbsan.M.loaded_segments (0x5b774 : word) = Some W_5b72c.
Proof. vm_refl. Qed.
Lemma D_5b72c : decode_any W_5b72c = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b730 : bv 32 := 0x00170713.
Lemma F_5b730 : fetch_word AsanUbsan.M.loaded_segments (0x5b778 : word) = Some W_5b730.
Proof. vm_refl. Qed.
Lemma D_5b730 : decode_any W_5b730 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b734 : bv 32 := 0x00088293.
Lemma F_5b734 : fetch_word AsanUbsan.M.loaded_segments (0x5b77c : word) = Some W_5b734.
Proof. vm_refl. Qed.
Lemma D_5b734 : decode_any W_5b734 = Some (OpImm ALU_ADD 5 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b738 : bv 32 := 0x00030793.
Lemma F_5b738 : fetch_word AsanUbsan.M.loaded_segments (0x5b780 : word) = Some W_5b738.
Proof. vm_refl. Qed.
Lemma D_5b738 : decode_any W_5b738 = Some (OpImm ALU_ADD 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b73c : bv 32 := 0x0475fc63.
Lemma F_5b73c : fetch_word AsanUbsan.M.loaded_segments (0x5b784 : word) = Some W_5b73c.
Proof. vm_refl. Qed.
Lemma D_5b73c : decode_any W_5b73c = Some (Branch BC_GEU 11 7 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b740 : bv 32 := 0x02080e63.
Lemma F_5b740 : fetch_word AsanUbsan.M.loaded_segments (0x5b788 : word) = Some W_5b740.
Proof. vm_refl. Qed.
Lemma D_5b740 : decode_any W_5b740 = Some (Branch BC_EQ 16 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b744 : bv 32 := 0x0002b883.
Lemma F_5b744 : fetch_word AsanUbsan.M.loaded_segments (0x5b78c : word) = Some W_5b744.
Proof. vm_refl. Qed.
Lemma D_5b744 : decode_any W_5b744 = Some (Load SZ8 true 17 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b748 : bv 32 := 0x0b153423.
Lemma F_5b748 : fetch_word AsanUbsan.M.loaded_segments (0x5b790 : word) = Some W_5b748.
Proof. vm_refl. Qed.
Lemma D_5b748 : decode_any W_5b748 = Some (Store SZ8 10 17 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b74c : bv 32 := 0x00089463.
Lemma F_5b74c : fetch_word AsanUbsan.M.loaded_segments (0x5b794 : word) = Some W_5b74c.
Proof. vm_refl. Qed.
Lemma D_5b74c : decode_any W_5b74c = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b750 : bv 32 := 0x0a053823.
Lemma F_5b750 : fetch_word AsanUbsan.M.loaded_segments (0x5b798 : word) = Some W_5b750.
Proof. vm_refl. Qed.
Lemma D_5b750 : decode_any W_5b750 = Some (Store SZ8 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b754 : bv 32 := 0xfff80813.
Lemma F_5b754 : fetch_word AsanUbsan.M.loaded_segments (0x5b79c : word) = Some W_5b754.
Proof. vm_refl. Qed.
Lemma D_5b754 : decode_any W_5b754 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b758 : bv 32 := 0x0b053023.
Lemma F_5b758 : fetch_word AsanUbsan.M.loaded_segments (0x5b7a0 : word) = Some W_5b758.
Proof. vm_refl. Qed.
Lemma D_5b758 : decode_any W_5b758 = Some (Store SZ8 10 16 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b75c : bv 32 := 0x0082b303.
Lemma F_5b75c : fetch_word AsanUbsan.M.loaded_segments (0x5b7a4 : word) = Some W_5b75c.
Proof. vm_refl. Qed.
Lemma D_5b75c : decode_any W_5b75c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b760 : bv 32 := 0x0b853383.
Lemma F_5b760 : fetch_word AsanUbsan.M.loaded_segments (0x5b7a8 : word) = Some W_5b760.
Proof. vm_refl. Qed.
Lemma D_5b760 : decode_any W_5b760 = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b764 : bv 32 := 0x40638333.
Lemma F_5b764 : fetch_word AsanUbsan.M.loaded_segments (0x5b7ac : word) = Some W_5b764.
Proof. vm_refl. Qed.
Lemma D_5b764 : decode_any W_5b764 = Some (Op ALU_SUB 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b768 : bv 32 := 0x0a653c23.
Lemma F_5b768 : fetch_word AsanUbsan.M.loaded_segments (0x5b7b0 : word) = Some W_5b768.
Proof. vm_refl. Qed.
Lemma D_5b768 : decode_any W_5b768 = Some (Store SZ8 10 6 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b76c : bv 32 := 0x00028313.
Lemma F_5b76c : fetch_word AsanUbsan.M.loaded_segments (0x5b7b4 : word) = Some W_5b76c.
Proof. vm_refl. Qed.
Lemma D_5b76c : decode_any W_5b76c = Some (OpImm ALU_ADD 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b770 : bv 32 := 0x0002b023.
Lemma F_5b770 : fetch_word AsanUbsan.M.loaded_segments (0x5b7b8 : word) = Some W_5b770.
Proof. vm_refl. Qed.
Lemma D_5b770 : decode_any W_5b770 = Some (Store SZ8 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b774 : bv 32 := 0xfa0712e3.
Lemma F_5b774 : fetch_word AsanUbsan.M.loaded_segments (0x5b7bc : word) = Some W_5b774.
Proof. vm_refl. Qed.
Lemma D_5b774 : decode_any W_5b774 = Some (Branch BC_NE 14 0 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b778 : bv 32 := 0x0140006f.
Lemma F_5b778 : fetch_word AsanUbsan.M.loaded_segments (0x5b7c0 : word) = Some W_5b778.
Proof. vm_refl. Qed.
Lemma D_5b778 : decode_any W_5b778 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b78c : bv 32 := 0x00613423.
Lemma F_5b78c : fetch_word AsanUbsan.M.loaded_segments (0x5b7d4 : word) = Some W_5b78c.
Proof. vm_refl. Qed.
Lemma D_5b78c : decode_any W_5b78c = Some (Store SZ8 2 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b790 : bv 32 := 0xf8dff06f.
Lemma F_5b790 : fetch_word AsanUbsan.M.loaded_segments (0x5b7d8 : word) = Some W_5b790.
Proof. vm_refl. Qed.
Lemma D_5b790 : decode_any W_5b790 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b794 : bv 32 := 0x00e13023.
Lemma F_5b794 : fetch_word AsanUbsan.M.loaded_segments (0x5b7dc : word) = Some W_5b794.
Proof. vm_refl. Qed.
Lemma D_5b794 : decode_any W_5b794 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b798 : bv 32 := 0x00613823.
Lemma F_5b798 : fetch_word AsanUbsan.M.loaded_segments (0x5b7e0 : word) = Some W_5b798.
Proof. vm_refl. Qed.
Lemma D_5b798 : decode_any W_5b798 = Some (Store SZ8 2 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b79c : bv 32 := 0x0310000f.
Lemma F_5b79c : fetch_word AsanUbsan.M.loaded_segments (0x5b7e4 : word) = Some W_5b79c.
Proof. vm_refl. Qed.
Lemma D_5b79c : decode_any W_5b79c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a0 : bv 32 := 0x08050c23.
Lemma F_5b7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5b7e8 : word) = Some W_5b7a0.
Proof. vm_refl. Qed.
Lemma D_5b7a0 : decode_any W_5b7a0 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a4 : bv 32 := 0x0310000f.
Lemma F_5b7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5b7ec : word) = Some W_5b7a4.
Proof. vm_refl. Qed.
Lemma D_5b7a4 : decode_any W_5b7a4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a8 : bv 32 := 0x08050ca3.
Lemma F_5b7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5b7f0 : word) = Some W_5b7a8.
Proof. vm_refl. Qed.
Lemma D_5b7a8 : decode_any W_5b7a8 = Some (Store SZ1 10 0 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7ac : bv 32 := 0x00010593.
Lemma F_5b7ac : fetch_word AsanUbsan.M.loaded_segments (0x5b7f4 : word) = Some W_5b7ac.
Proof. vm_refl. Qed.
Lemma D_5b7ac : decode_any W_5b7ac = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b0 : bv 32 := 0x1fc000ef.
Lemma F_5b7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b7f8 : word) = Some W_5b7b0.
Proof. vm_refl. Qed.
Lemma D_5b7b0 : decode_any W_5b7b0 = Some (Jal 1 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b4 : bv 32 := 0x04813083.
Lemma F_5b7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b7fc : word) = Some W_5b7b4.
Proof. vm_refl. Qed.
Lemma D_5b7b4 : decode_any W_5b7b4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b8 : bv 32 := 0x04013403.
Lemma F_5b7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5b800 : word) = Some W_5b7b8.
Proof. vm_refl. Qed.
Lemma D_5b7b8 : decode_any W_5b7b8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7bc : bv 32 := 0x03813483.
Lemma F_5b7bc : fetch_word AsanUbsan.M.loaded_segments (0x5b804 : word) = Some W_5b7bc.
Proof. vm_refl. Qed.
Lemma D_5b7bc : decode_any W_5b7bc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c0 : bv 32 := 0x03013903.
Lemma F_5b7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5b808 : word) = Some W_5b7c0.
Proof. vm_refl. Qed.
Lemma D_5b7c0 : decode_any W_5b7c0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c4 : bv 32 := 0x02813983.
Lemma F_5b7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5b80c : word) = Some W_5b7c4.
Proof. vm_refl. Qed.
Lemma D_5b7c4 : decode_any W_5b7c4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c8 : bv 32 := 0x02013a03.
Lemma F_5b7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5b810 : word) = Some W_5b7c8.
Proof. vm_refl. Qed.
Lemma D_5b7c8 : decode_any W_5b7c8 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7cc : bv 32 := 0x05010113.
Lemma F_5b7cc : fetch_word AsanUbsan.M.loaded_segments (0x5b814 : word) = Some W_5b7cc.
Proof. vm_refl. Qed.
Lemma D_5b7cc : decode_any W_5b7cc = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7d0 : bv 32 := 0x00008067.
Lemma F_5b7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5b818 : word) = Some W_5b7d0.
Proof. vm_refl. Qed.
Lemma D_5b7d0 : decode_any W_5b7d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9ac : bv 32 := 0xf9010113.
Lemma F_5b9ac : fetch_word AsanUbsan.M.loaded_segments (0x5b9f4 : word) = Some W_5b9ac.
Proof. vm_refl. Qed.
Lemma D_5b9ac : decode_any W_5b9ac = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b0 : bv 32 := 0x06113423.
Lemma F_5b9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5b9f8 : word) = Some W_5b9b0.
Proof. vm_refl. Qed.
Lemma D_5b9b0 : decode_any W_5b9b0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b4 : bv 32 := 0x06813023.
Lemma F_5b9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5b9fc : word) = Some W_5b9b4.
Proof. vm_refl. Qed.
Lemma D_5b9b4 : decode_any W_5b9b4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b8 : bv 32 := 0x04913c23.
Lemma F_5b9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5ba00 : word) = Some W_5b9b8.
Proof. vm_refl. Qed.
Lemma D_5b9b8 : decode_any W_5b9b8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9bc : bv 32 := 0x05213823.
Lemma F_5b9bc : fetch_word AsanUbsan.M.loaded_segments (0x5ba04 : word) = Some W_5b9bc.
Proof. vm_refl. Qed.
Lemma D_5b9bc : decode_any W_5b9bc = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c0 : bv 32 := 0x05313423.
Lemma F_5b9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5ba08 : word) = Some W_5b9c0.
Proof. vm_refl. Qed.
Lemma D_5b9c0 : decode_any W_5b9c0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c4 : bv 32 := 0x05413023.
Lemma F_5b9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5ba0c : word) = Some W_5b9c4.
Proof. vm_refl. Qed.
Lemma D_5b9c4 : decode_any W_5b9c4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c8 : bv 32 := 0x03513c23.
Lemma F_5b9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5ba10 : word) = Some W_5b9c8.
Proof. vm_refl. Qed.
Lemma D_5b9c8 : decode_any W_5b9c8 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9cc : bv 32 := 0x03613823.
Lemma F_5b9cc : fetch_word AsanUbsan.M.loaded_segments (0x5ba14 : word) = Some W_5b9cc.
Proof. vm_refl. Qed.
Lemma D_5b9cc : decode_any W_5b9cc = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d0 : bv 32 := 0x03713423.
Lemma F_5b9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5ba18 : word) = Some W_5b9d0.
Proof. vm_refl. Qed.
Lemma D_5b9d0 : decode_any W_5b9d0 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d4 : bv 32 := 0x03813023.
Lemma F_5b9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5ba1c : word) = Some W_5b9d4.
Proof. vm_refl. Qed.
Lemma D_5b9d4 : decode_any W_5b9d4 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d8 : bv 32 := 0x01913c23.
Lemma F_5b9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5ba20 : word) = Some W_5b9d8.
Proof. vm_refl. Qed.
Lemma D_5b9d8 : decode_any W_5b9d8 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9dc : bv 32 := 0x0005b503.
Lemma F_5b9dc : fetch_word AsanUbsan.M.loaded_segments (0x5ba24 : word) = Some W_5b9dc.
Proof. vm_refl. Qed.
Lemma D_5b9dc : decode_any W_5b9dc = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e0 : bv 32 := 0x00c13423.
Lemma F_5b9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5ba28 : word) = Some W_5b9e0.
Proof. vm_refl. Qed.
Lemma D_5b9e0 : decode_any W_5b9e0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e4 : bv 32 := 0x00d13823.
Lemma F_5b9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5ba2c : word) = Some W_5b9e4.
Proof. vm_refl. Qed.
Lemma D_5b9e4 : decode_any W_5b9e4 = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e8 : bv 32 := 0x0c050463.
Lemma F_5b9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5ba30 : word) = Some W_5b9e8.
Proof. vm_refl. Qed.
Lemma D_5b9e8 : decode_any W_5b9e8 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9ec : bv 32 := 0x00058413.
Lemma F_5b9ec : fetch_word AsanUbsan.M.loaded_segments (0x5ba34 : word) = Some W_5b9ec.
Proof. vm_refl. Qed.
Lemma D_5b9ec : decode_any W_5b9ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f0 : bv 32 := 0x000ff597.
Lemma F_5b9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5ba38 : word) = Some W_5b9f0.
Proof. vm_refl. Qed.
Lemma D_5b9f0 : decode_any W_5b9f0 = Some (Auipc 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f4 : bv 32 := 0x00100a93.
Lemma F_5b9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5ba3c : word) = Some W_5b9f4.
Proof. vm_refl. Qed.
Lemma D_5b9f4 : decode_any W_5b9f4 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f8 : bv 32 := 0xc6058493.
Lemma F_5b9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5ba40 : word) = Some W_5b9f8.
Proof. vm_refl. Qed.
Lemma D_5b9f8 : decode_any W_5b9f8 = Some (OpImm ALU_ADD 9 11 3168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9fc : bv 32 := 0x025a9a93.
Lemma F_5b9fc : fetch_word AsanUbsan.M.loaded_segments (0x5ba44 : word) = Some W_5b9fc.
Proof. vm_refl. Qed.
Lemma D_5b9fc : decode_any W_5b9fc = Some (ShiftImm ALU_SLL 21 21 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba00 : bv 32 := 0x04048913.
Lemma F_5ba00 : fetch_word AsanUbsan.M.loaded_segments (0x5ba48 : word) = Some W_5ba00.
Proof. vm_refl. Qed.
Lemma D_5ba00 : decode_any W_5ba00 = Some (OpImm ALU_ADD 18 9 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba04 : bv 32 := 0x2b048993.
Lemma F_5ba04 : fetch_word AsanUbsan.M.loaded_segments (0x5ba4c : word) = Some W_5ba04.
Proof. vm_refl. Qed.
Lemma D_5ba04 : decode_any W_5ba04 = Some (OpImm ALU_ADD 19 9 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba08 : bv 32 := 0x01c0006f.
Lemma F_5ba08 : fetch_word AsanUbsan.M.loaded_segments (0x5ba50 : word) = Some W_5ba08.
Proof. vm_refl. Qed.
Lemma D_5ba08 : decode_any W_5ba08 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba24 : bv 32 := 0x00843a03.
Lemma F_5ba24 : fetch_word AsanUbsan.M.loaded_segments (0x5ba6c : word) = Some W_5ba24.
Proof. vm_refl. Qed.
Lemma D_5ba24 : decode_any W_5ba24 = Some (Load SZ8 true 20 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba28 : bv 32 := 0x000a3583.
Lemma F_5ba28 : fetch_word AsanUbsan.M.loaded_segments (0x5ba70 : word) = Some W_5ba28.
Proof. vm_refl. Qed.
Lemma D_5ba28 : decode_any W_5ba28 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba2c : bv 32 := 0x00b43423.
Lemma F_5ba2c : fetch_word AsanUbsan.M.loaded_segments (0x5ba74 : word) = Some W_5ba2c.
Proof. vm_refl. Qed.
Lemma D_5ba2c : decode_any W_5ba2c = Some (Store SZ8 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba30 : bv 32 := 0x00059463.
Lemma F_5ba30 : fetch_word AsanUbsan.M.loaded_segments (0x5ba78 : word) = Some W_5ba30.
Proof. vm_refl. Qed.
Lemma D_5ba30 : decode_any W_5ba30 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba34 : bv 32 := 0x00043823.
Lemma F_5ba34 : fetch_word AsanUbsan.M.loaded_segments (0x5ba7c : word) = Some W_5ba34.
Proof. vm_refl. Qed.
Lemma D_5ba34 : decode_any W_5ba34 = Some (Store SZ8 8 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba38 : bv 32 := 0xfff50513.
Lemma F_5ba38 : fetch_word AsanUbsan.M.loaded_segments (0x5ba80 : word) = Some W_5ba38.
Proof. vm_refl. Qed.
Lemma D_5ba38 : decode_any W_5ba38 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba3c : bv 32 := 0x00a43023.
Lemma F_5ba3c : fetch_word AsanUbsan.M.loaded_segments (0x5ba84 : word) = Some W_5ba3c.
Proof. vm_refl. Qed.
Lemma D_5ba3c : decode_any W_5ba3c = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba40 : bv 32 := 0x008a3503.
Lemma F_5ba40 : fetch_word AsanUbsan.M.loaded_segments (0x5ba88 : word) = Some W_5ba40.
Proof. vm_refl. Qed.
Lemma D_5ba40 : decode_any W_5ba40 = Some (Load SZ8 true 10 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba44 : bv 32 := 0x01843583.
Lemma F_5ba44 : fetch_word AsanUbsan.M.loaded_segments (0x5ba8c : word) = Some W_5ba44.
Proof. vm_refl. Qed.
Lemma D_5ba44 : decode_any W_5ba44 = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba48 : bv 32 := 0x40a585b3.
Lemma F_5ba48 : fetch_word AsanUbsan.M.loaded_segments (0x5ba90 : word) = Some W_5ba48.
Proof. vm_refl. Qed.
Lemma D_5ba48 : decode_any W_5ba48 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba4c : bv 32 := 0x00b43c23.
Lemma F_5ba4c : fetch_word AsanUbsan.M.loaded_segments (0x5ba94 : word) = Some W_5ba4c.
Proof. vm_refl. Qed.
Lemma D_5ba4c : decode_any W_5ba4c = Some (Store SZ8 8 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba50 : bv 32 := 0x010a3b03.
Lemma F_5ba50 : fetch_word AsanUbsan.M.loaded_segments (0x5ba98 : word) = Some W_5ba50.
Proof. vm_refl. Qed.
Lemma D_5ba50 : decode_any W_5ba50 = Some (Load SZ8 true 22 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba54 : bv 32 := 0x020b0463.
Lemma F_5ba54 : fetch_word AsanUbsan.M.loaded_segments (0x5ba9c : word) = Some W_5ba54.
Proof. vm_refl. Qed.
Lemma D_5ba54 : decode_any W_5ba54 = Some (Branch BC_EQ 22 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba58 : bv 32 := 0x098a0b93.
Lemma F_5ba58 : fetch_word AsanUbsan.M.loaded_segments (0x5baa0 : word) = Some W_5ba58.
Proof. vm_refl. Qed.
Lemma D_5ba58 : decode_any W_5ba58 = Some (OpImm ALU_ADD 23 20 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba5c : bv 32 := 0x010b0c13.
Lemma F_5ba5c : fetch_word AsanUbsan.M.loaded_segments (0x5baa4 : word) = Some W_5ba5c.
Proof. vm_refl. Qed.
Lemma D_5ba5c : decode_any W_5ba5c = Some (OpImm ALU_ADD 24 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba60 : bv 32 := 0x01000c93.
Lemma F_5ba60 : fetch_word AsanUbsan.M.loaded_segments (0x5baa8 : word) = Some W_5ba60.
Proof. vm_refl. Qed.
Lemma D_5ba60 : decode_any W_5ba60 = Some (OpImm ALU_ADD 25 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba64 : bv 32 := 0xf80bb583.
Lemma F_5ba64 : fetch_word AsanUbsan.M.loaded_segments (0x5baac : word) = Some W_5ba64.
Proof. vm_refl. Qed.
Lemma D_5ba64 : decode_any W_5ba64 = Some (Load SZ8 true 11 23 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba68 : bv 32 := 0x00810513.
Lemma F_5ba68 : fetch_word AsanUbsan.M.loaded_segments (0x5bab0 : word) = Some W_5ba68.
Proof. vm_refl. Qed.
Lemma D_5ba68 : decode_any W_5ba68 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba6c : bv 32 := 0x078000ef.
Lemma F_5ba6c : fetch_word AsanUbsan.M.loaded_segments (0x5bab4 : word) = Some W_5ba6c.
Proof. vm_refl. Qed.
Lemma D_5ba6c : decode_any W_5ba6c = Some (Jal 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba70 : bv 32 := 0x001c8c93.
Lemma F_5ba70 : fetch_word AsanUbsan.M.loaded_segments (0x5bab8 : word) = Some W_5ba70.
Proof. vm_refl. Qed.
Lemma D_5ba70 : decode_any W_5ba70 = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba74 : bv 32 := 0x008b8b93.
Lemma F_5ba74 : fetch_word AsanUbsan.M.loaded_segments (0x5babc : word) = Some W_5ba74.
Proof. vm_refl. Qed.
Lemma D_5ba74 : decode_any W_5ba74 = Some (OpImm ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba78 : bv 32 := 0xff8c96e3.
Lemma F_5ba78 : fetch_word AsanUbsan.M.loaded_segments (0x5bac0 : word) = Some W_5ba78.
Proof. vm_refl. Qed.
Lemma D_5ba78 : decode_any W_5ba78 = Some (Branch BC_NE 25 24 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba7c : bv 32 := 0x0204b583.
Lemma F_5ba7c : fetch_word AsanUbsan.M.loaded_segments (0x5bac4 : word) = Some W_5ba7c.
Proof. vm_refl. Qed.
Lemma D_5ba7c : decode_any W_5ba7c = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba80 : bv 32 := 0xf8ba66e3.
Lemma F_5ba80 : fetch_word AsanUbsan.M.loaded_segments (0x5bac8 : word) = Some W_5ba80.
Proof. vm_refl. Qed.
Lemma D_5ba80 : decode_any W_5ba80 = Some (Branch BC_LTU 20 11 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba84 : bv 32 := 0x01558533.
Lemma F_5ba84 : fetch_word AsanUbsan.M.loaded_segments (0x5bacc : word) = Some W_5ba84.
Proof. vm_refl. Qed.
Lemma D_5ba84 : decode_any W_5ba84 = Some (Op ALU_ADD 10 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba88 : bv 32 := 0xf8aa72e3.
Lemma F_5ba88 : fetch_word AsanUbsan.M.loaded_segments (0x5bad0 : word) = Some W_5ba88.
Proof. vm_refl. Qed.
Lemma D_5ba88 : decode_any W_5ba88 = Some (Branch BC_GEU 20 10 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba8c : bv 32 := 0x00813503.
Lemma F_5ba8c : fetch_word AsanUbsan.M.loaded_segments (0x5bad4 : word) = Some W_5ba8c.
Proof. vm_refl. Qed.
Lemma D_5ba8c : decode_any W_5ba8c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba90 : bv 32 := 0x40ba05b3.
Lemma F_5ba90 : fetch_word AsanUbsan.M.loaded_segments (0x5bad8 : word) = Some W_5ba90.
Proof. vm_refl. Qed.
Lemma D_5ba90 : decode_any W_5ba90 = Some (Op ALU_SUB 11 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba94 : bv 32 := 0x01b59593.
Lemma F_5ba94 : fetch_word AsanUbsan.M.loaded_segments (0x5badc : word) = Some W_5ba94.
Proof. vm_refl. Qed.
Lemma D_5ba94 : decode_any W_5ba94 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba98 : bv 32 := 0x03b5d613.
Lemma F_5ba98 : fetch_word AsanUbsan.M.loaded_segments (0x5bae0 : word) = Some W_5ba98.
Proof. vm_refl. Qed.
Lemma D_5ba98 : decode_any W_5ba98 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba9c : bv 32 := 0x00048593.
Lemma F_5ba9c : fetch_word AsanUbsan.M.loaded_segments (0x5bae4 : word) = Some W_5ba9c.
Proof. vm_refl. Qed.
Lemma D_5ba9c : decode_any W_5ba9c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa0 : bv 32 := 0x000a0693.
Lemma F_5baa0 : fetch_word AsanUbsan.M.loaded_segments (0x5bae8 : word) = Some W_5baa0.
Proof. vm_refl. Qed.
Lemma D_5baa0 : decode_any W_5baa0 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa4 : bv 32 := 0x444000ef.
Lemma F_5baa4 : fetch_word AsanUbsan.M.loaded_segments (0x5baec : word) = Some W_5baa4.
Proof. vm_refl. Qed.
Lemma D_5baa4 : decode_any W_5baa4 = Some (Jal 1 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa8 : bv 32 := 0x00043503.
Lemma F_5baa8 : fetch_word AsanUbsan.M.loaded_segments (0x5baf0 : word) = Some W_5baa8.
Proof. vm_refl. Qed.
Lemma D_5baa8 : decode_any W_5baa8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baac : bv 32 := 0xf6051ce3.
Lemma F_5baac : fetch_word AsanUbsan.M.loaded_segments (0x5baf4 : word) = Some W_5baac.
Proof. vm_refl. Qed.
Lemma D_5baac : decode_any W_5baac = Some (Branch BC_NE 10 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab0 : bv 32 := 0x06813083.
Lemma F_5bab0 : fetch_word AsanUbsan.M.loaded_segments (0x5baf8 : word) = Some W_5bab0.
Proof. vm_refl. Qed.
Lemma D_5bab0 : decode_any W_5bab0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab4 : bv 32 := 0x06013403.
Lemma F_5bab4 : fetch_word AsanUbsan.M.loaded_segments (0x5bafc : word) = Some W_5bab4.
Proof. vm_refl. Qed.
Lemma D_5bab4 : decode_any W_5bab4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab8 : bv 32 := 0x05813483.
Lemma F_5bab8 : fetch_word AsanUbsan.M.loaded_segments (0x5bb00 : word) = Some W_5bab8.
Proof. vm_refl. Qed.
Lemma D_5bab8 : decode_any W_5bab8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5babc : bv 32 := 0x05013903.
Lemma F_5babc : fetch_word AsanUbsan.M.loaded_segments (0x5bb04 : word) = Some W_5babc.
Proof. vm_refl. Qed.
Lemma D_5babc : decode_any W_5babc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac0 : bv 32 := 0x04813983.
Lemma F_5bac0 : fetch_word AsanUbsan.M.loaded_segments (0x5bb08 : word) = Some W_5bac0.
Proof. vm_refl. Qed.
Lemma D_5bac0 : decode_any W_5bac0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac4 : bv 32 := 0x04013a03.
Lemma F_5bac4 : fetch_word AsanUbsan.M.loaded_segments (0x5bb0c : word) = Some W_5bac4.
Proof. vm_refl. Qed.
Lemma D_5bac4 : decode_any W_5bac4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac8 : bv 32 := 0x03813a83.
Lemma F_5bac8 : fetch_word AsanUbsan.M.loaded_segments (0x5bb10 : word) = Some W_5bac8.
Proof. vm_refl. Qed.
Lemma D_5bac8 : decode_any W_5bac8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bacc : bv 32 := 0x03013b03.
Lemma F_5bacc : fetch_word AsanUbsan.M.loaded_segments (0x5bb14 : word) = Some W_5bacc.
Proof. vm_refl. Qed.
Lemma D_5bacc : decode_any W_5bacc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad0 : bv 32 := 0x02813b83.
Lemma F_5bad0 : fetch_word AsanUbsan.M.loaded_segments (0x5bb18 : word) = Some W_5bad0.
Proof. vm_refl. Qed.
Lemma D_5bad0 : decode_any W_5bad0 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad4 : bv 32 := 0x02013c03.
Lemma F_5bad4 : fetch_word AsanUbsan.M.loaded_segments (0x5bb1c : word) = Some W_5bad4.
Proof. vm_refl. Qed.
Lemma D_5bad4 : decode_any W_5bad4 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad8 : bv 32 := 0x01813c83.
Lemma F_5bad8 : fetch_word AsanUbsan.M.loaded_segments (0x5bb20 : word) = Some W_5bad8.
Proof. vm_refl. Qed.
Lemma D_5bad8 : decode_any W_5bad8 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5badc : bv 32 := 0x07010113.
Lemma F_5badc : fetch_word AsanUbsan.M.loaded_segments (0x5bb24 : word) = Some W_5badc.
Proof. vm_refl. Qed.
Lemma D_5badc : decode_any W_5badc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae0 : bv 32 := 0x00008067.
Lemma F_5bae0 : fetch_word AsanUbsan.M.loaded_segments (0x5bb28 : word) = Some W_5bae0.
Proof. vm_refl. Qed.
Lemma D_5bae0 : decode_any W_5bae0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae4 : bv 32 := 0xfd010113.
Lemma F_5bae4 : fetch_word AsanUbsan.M.loaded_segments (0x5bb2c : word) = Some W_5bae4.
Proof. vm_refl. Qed.
Lemma D_5bae4 : decode_any W_5bae4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae8 : bv 32 := 0x02113423.
Lemma F_5bae8 : fetch_word AsanUbsan.M.loaded_segments (0x5bb30 : word) = Some W_5bae8.
Proof. vm_refl. Qed.
Lemma D_5bae8 : decode_any W_5bae8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baec : bv 32 := 0x02813023.
Lemma F_5baec : fetch_word AsanUbsan.M.loaded_segments (0x5bb34 : word) = Some W_5baec.
Proof. vm_refl. Qed.
Lemma D_5baec : decode_any W_5baec = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf0 : bv 32 := 0x00913c23.
Lemma F_5baf0 : fetch_word AsanUbsan.M.loaded_segments (0x5bb38 : word) = Some W_5baf0.
Proof. vm_refl. Qed.
Lemma D_5baf0 : decode_any W_5baf0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf4 : bv 32 := 0x01213823.
Lemma F_5baf4 : fetch_word AsanUbsan.M.loaded_segments (0x5bb3c : word) = Some W_5baf4.
Proof. vm_refl. Qed.
Lemma D_5baf4 : decode_any W_5baf4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf8 : bv 32 := 0x01313423.
Lemma F_5baf8 : fetch_word AsanUbsan.M.loaded_segments (0x5bb40 : word) = Some W_5baf8.
Proof. vm_refl. Qed.
Lemma D_5baf8 : decode_any W_5baf8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bafc : bv 32 := 0x01413023.
Lemma F_5bafc : fetch_word AsanUbsan.M.loaded_segments (0x5bb44 : word) = Some W_5bafc.
Proof. vm_refl. Qed.
Lemma D_5bafc : decode_any W_5bafc = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb00 : bv 32 := 0x00058493.
Lemma F_5bb00 : fetch_word AsanUbsan.M.loaded_segments (0x5bb48 : word) = Some W_5bb00.
Proof. vm_refl. Qed.
Lemma D_5bb00 : decode_any W_5bb00 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb04 : bv 32 := 0x00050413.
Lemma F_5bb04 : fetch_word AsanUbsan.M.loaded_segments (0x5bb4c : word) = Some W_5bb04.
Proof. vm_refl. Qed.
Lemma D_5bb04 : decode_any W_5bb04 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb08 : bv 32 := 0x000ff517.
Lemma F_5bb08 : fetch_word AsanUbsan.M.loaded_segments (0x5bb50 : word) = Some W_5bb08.
Proof. vm_refl. Qed.
Lemma D_5bb08 : decode_any W_5bb08 = Some (Auipc 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb0c : bv 32 := 0xb4850993.
Lemma F_5bb0c : fetch_word AsanUbsan.M.loaded_segments (0x5bb54 : word) = Some W_5bb0c.
Proof. vm_refl. Qed.
Lemma D_5bb0c : decode_any W_5bb0c = Some (OpImm ALU_ADD 19 10 2888, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb10 : bv 32 := 0x0209b503.
Lemma F_5bb10 : fetch_word AsanUbsan.M.loaded_segments (0x5bb58 : word) = Some W_5bb10.
Proof. vm_refl. Qed.
Lemma D_5bb10 : decode_any W_5bb10 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb14 : bv 32 := 0x00100a13.
Lemma F_5bb14 : fetch_word AsanUbsan.M.loaded_segments (0x5bb5c : word) = Some W_5bb14.
Proof. vm_refl. Qed.
Lemma D_5bb14 : decode_any W_5bb14 = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb18 : bv 32 := 0x025a1a13.
Lemma F_5bb18 : fetch_word AsanUbsan.M.loaded_segments (0x5bb60 : word) = Some W_5bb18.
Proof. vm_refl. Qed.
Lemma D_5bb18 : decode_any W_5bb18 = Some (ShiftImm ALU_SLL 20 20 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb1c : bv 32 := 0x02a5ea63.
Lemma F_5bb1c : fetch_word AsanUbsan.M.loaded_segments (0x5bb64 : word) = Some W_5bb1c.
Proof. vm_refl. Qed.
Lemma D_5bb1c : decode_any W_5bb1c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb20 : bv 32 := 0x014505b3.
Lemma F_5bb20 : fetch_word AsanUbsan.M.loaded_segments (0x5bb68 : word) = Some W_5bb20.
Proof. vm_refl. Qed.
Lemma D_5bb20 : decode_any W_5bb20 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb24 : bv 32 := 0x02b4f663.
Lemma F_5bb24 : fetch_word AsanUbsan.M.loaded_segments (0x5bb6c : word) = Some W_5bb24.
Proof. vm_refl. Qed.
Lemma D_5bb24 : decode_any W_5bb24 = Some (Branch BC_GEU 9 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb28 : bv 32 := 0x40a48733.
Lemma F_5bb28 : fetch_word AsanUbsan.M.loaded_segments (0x5bb70 : word) = Some W_5bb28.
Proof. vm_refl. Qed.
Lemma D_5bb28 : decode_any W_5bb28 = Some (Op ALU_SUB 14 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb2c : bv 32 := 0x02075693.
Lemma F_5bb2c : fetch_word AsanUbsan.M.loaded_segments (0x5bb74 : word) = Some W_5bb2c.
Proof. vm_refl. Qed.
Lemma D_5bb2c : decode_any W_5bb2c = Some (ShiftImm ALU_SRL 13 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb30 : bv 32 := 0x01f6f613.
Lemma F_5bb30 : fetch_word AsanUbsan.M.loaded_segments (0x5bb78 : word) = Some W_5bb30.
Proof. vm_refl. Qed.
Lemma D_5bb30 : decode_any W_5bb30 = Some (OpImm ALU_AND 12 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb34 : bv 32 := 0x01f00793.
Lemma F_5bb34 : fetch_word AsanUbsan.M.loaded_segments (0x5bb7c : word) = Some W_5bb34.
Proof. vm_refl. Qed.
Lemma D_5bb34 : decode_any W_5bb34 = Some (OpImm ALU_ADD 15 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb38 : bv 32 := 0x1ef60663.
Lemma F_5bb38 : fetch_word AsanUbsan.M.loaded_segments (0x5bb80 : word) = Some W_5bb38.
Proof. vm_refl. Qed.
Lemma D_5bb38 : decode_any W_5bb38 = Some (Branch BC_EQ 12 15 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb3c : bv 32 := 0x01100793.
Lemma F_5bb3c : fetch_word AsanUbsan.M.loaded_segments (0x5bb84 : word) = Some W_5bb3c.
Proof. vm_refl. Qed.
Lemma D_5bb3c : decode_any W_5bb3c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb40 : bv 32 := 0x02f67863.
Lemma F_5bb40 : fetch_word AsanUbsan.M.loaded_segments (0x5bb88 : word) = Some W_5bb40.
Proof. vm_refl. Qed.
Lemma D_5bb40 : decode_any W_5bb40 = Some (Branch BC_GEU 12 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb44 : bv 32 := 0x1c060a63.
Lemma F_5bb44 : fetch_word AsanUbsan.M.loaded_segments (0x5bb8c : word) = Some W_5bb44.
Proof. vm_refl. Qed.
Lemma D_5bb44 : decode_any W_5bb44 = Some (Branch BC_EQ 12 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb48 : bv 32 := 0x00561793.
Lemma F_5bb48 : fetch_word AsanUbsan.M.loaded_segments (0x5bb90 : word) = Some W_5bb48.
Proof. vm_refl. Qed.
Lemma D_5bb48 : decode_any W_5bb48 = Some (ShiftImm ALU_SLL 15 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb4c : bv 32 := 0x0480006f.
Lemma F_5bb4c : fetch_word AsanUbsan.M.loaded_segments (0x5bb94 : word) = Some W_5bb4c.
Proof. vm_refl. Qed.
Lemma D_5bb4c : decode_any W_5bb4c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb50 : bv 32 := 0x04098513.
Lemma F_5bb50 : fetch_word AsanUbsan.M.loaded_segments (0x5bb98 : word) = Some W_5bb50.
Proof. vm_refl. Qed.
Lemma D_5bb50 : decode_any W_5bb50 = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb54 : bv 32 := 0x00048593.
Lemma F_5bb54 : fetch_word AsanUbsan.M.loaded_segments (0x5bb9c : word) = Some W_5bb54.
Proof. vm_refl. Qed.
Lemma D_5bb54 : decode_any W_5bb54 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb58 : bv 32 := 0x210000ef.
Lemma F_5bb58 : fetch_word AsanUbsan.M.loaded_segments (0x5bba0 : word) = Some W_5bb58.
Proof. vm_refl. Qed.
Lemma D_5bb58 : decode_any W_5bb58 = Some (Jal 1 528, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb5c : bv 32 := 0x00050913.
Lemma F_5bb5c : fetch_word AsanUbsan.M.loaded_segments (0x5bba4 : word) = Some W_5bb5c.
Proof. vm_refl. Qed.
Lemma D_5bb5c : decode_any W_5bb5c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb60 : bv 32 := 0x0209b503.
Lemma F_5bb60 : fetch_word AsanUbsan.M.loaded_segments (0x5bba8 : word) = Some W_5bb60.
Proof. vm_refl. Qed.
Lemma D_5bb60 : decode_any W_5bb60 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb64 : bv 32 := 0x014505b3.
Lemma F_5bb64 : fetch_word AsanUbsan.M.loaded_segments (0x5bbac : word) = Some W_5bb64.
Proof. vm_refl. Qed.
Lemma D_5bb64 : decode_any W_5bb64 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb68 : bv 32 := 0x06a97663.
Lemma F_5bb68 : fetch_word AsanUbsan.M.loaded_segments (0x5bbb0 : word) = Some W_5bb68.
Proof. vm_refl. Qed.
Lemma D_5bb68 : decode_any W_5bb68 = Some (Branch BC_GEU 18 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb6c : bv 32 := 0x0e40006f.
Lemma F_5bb6c : fetch_word AsanUbsan.M.loaded_segments (0x5bbb4 : word) = Some W_5bb6c.
Proof. vm_refl. Qed.
Lemma D_5bb6c : decode_any W_5bb6c = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb70 : bv 32 := 0xff060793.
Lemma F_5bb70 : fetch_word AsanUbsan.M.loaded_segments (0x5bbb8 : word) = Some W_5bb70.
Proof. vm_refl. Qed.
Lemma D_5bb70 : decode_any W_5bb70 = Some (OpImm ALU_ADD 15 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb74 : bv 32 := 0x20000813.
Lemma F_5bb74 : fetch_word AsanUbsan.M.loaded_segments (0x5bbbc : word) = Some W_5bb74.
Proof. vm_refl. Qed.
Lemma D_5bb74 : decode_any W_5bb74 = Some (OpImm ALU_ADD 16 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb78 : bv 32 := 0x03f69893.
Lemma F_5bb78 : fetch_word AsanUbsan.M.loaded_segments (0x5bbc0 : word) = Some W_5bb78.
Proof. vm_refl. Qed.
Lemma D_5bb78 : decode_any W_5bb78 = Some (ShiftImm ALU_SLL 17 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb7c : bv 32 := 0x0017d793.
Lemma F_5bb7c : fetch_word AsanUbsan.M.loaded_segments (0x5bbc4 : word) = Some W_5bb7c.
Proof. vm_refl. Qed.
Lemma D_5bb7c : decode_any W_5bb7c = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb80 : bv 32 := 0x00f817b3.
Lemma F_5bb80 : fetch_word AsanUbsan.M.loaded_segments (0x5bbc8 : word) = Some W_5bb80.
Proof. vm_refl. Qed.
Lemma D_5bb80 : decode_any W_5bb80 = Some (Op ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb84 : bv 32 := 0x0017d813.
Lemma F_5bb84 : fetch_word AsanUbsan.M.loaded_segments (0x5bbcc : word) = Some W_5bb84.
Proof. vm_refl. Qed.
Lemma D_5bb84 : decode_any W_5bb84 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb88 : bv 32 := 0x43f8d893.
Lemma F_5bb88 : fetch_word AsanUbsan.M.loaded_segments (0x5bbd0 : word) = Some W_5bb88.
Proof. vm_refl. Qed.
Lemma D_5bb88 : decode_any W_5bb88 = Some (ShiftImm ALU_SRA 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb8c : bv 32 := 0x0108f833.
Lemma F_5bb8c : fetch_word AsanUbsan.M.loaded_segments (0x5bbd4 : word) = Some W_5bb8c.
Proof. vm_refl. Qed.
Lemma D_5bb8c : decode_any W_5bb8c = Some (Op ALU_AND 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb90 : bv 32 := 0x00f807b3.
Lemma F_5bb90 : fetch_word AsanUbsan.M.loaded_segments (0x5bbd8 : word) = Some W_5bb90.
Proof. vm_refl. Qed.
Lemma D_5bb90 : decode_any W_5bb90 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb94 : bv 32 := 0x02f7573b.
Lemma F_5bb94 : fetch_word AsanUbsan.M.loaded_segments (0x5bbdc : word) = Some W_5bb94.
Proof. vm_refl. Qed.
Lemma D_5bb94 : decode_any W_5bb94 = Some (Mul32 M_DIVU 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb98 : bv 32 := 0x02069693.
Lemma F_5bb98 : fetch_word AsanUbsan.M.loaded_segments (0x5bbe0 : word) = Some W_5bb98.
Proof. vm_refl. Qed.
Lemma D_5bb98 : decode_any W_5bb98 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb9c : bv 32 := 0x0309b803.
Lemma F_5bb9c : fetch_word AsanUbsan.M.loaded_segments (0x5bbe4 : word) = Some W_5bb9c.
Proof. vm_refl. Qed.
Lemma D_5bb9c : decode_any W_5bb9c = Some (Load SZ8 true 16 19 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba0 : bv 32 := 0x00761613.
Lemma F_5bba0 : fetch_word AsanUbsan.M.loaded_segments (0x5bbe8 : word) = Some W_5bba0.
Proof. vm_refl. Qed.
Lemma D_5bba0 : decode_any W_5bba0 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba4 : bv 32 := 0x02071713.
Lemma F_5bba4 : fetch_word AsanUbsan.M.loaded_segments (0x5bbec : word) = Some W_5bba4.
Proof. vm_refl. Qed.
Lemma D_5bba4 : decode_any W_5bba4 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba8 : bv 32 := 0x00a686b3.
Lemma F_5bba8 : fetch_word AsanUbsan.M.loaded_segments (0x5bbf0 : word) = Some W_5bba8.
Proof. vm_refl. Qed.
Lemma D_5bba8 : decode_any W_5bba8 = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbac : bv 32 := 0x00c80633.
Lemma F_5bbac : fetch_word AsanUbsan.M.loaded_segments (0x5bbf4 : word) = Some W_5bbac.
Proof. vm_refl. Qed.
Lemma D_5bbac : decode_any W_5bbac = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb0 : bv 32 := 0x03063603.
Lemma F_5bbb0 : fetch_word AsanUbsan.M.loaded_segments (0x5bbf8 : word) = Some W_5bbb0.
Proof. vm_refl. Qed.
Lemma D_5bbb0 : decode_any W_5bbb0 = Some (Load SZ8 true 12 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb4 : bv 32 := 0x02075713.
Lemma F_5bbb4 : fetch_word AsanUbsan.M.loaded_segments (0x5bbfc : word) = Some W_5bbb4.
Proof. vm_refl. Qed.
Lemma D_5bbb4 : decode_any W_5bbb4 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb8 : bv 32 := 0x02e78733.
Lemma F_5bbb8 : fetch_word AsanUbsan.M.loaded_segments (0x5bc00 : word) = Some W_5bbb8.
Proof. vm_refl. Qed.
Lemma D_5bbb8 : decode_any W_5bbb8 = Some (Mul M_MUL 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbbc : bv 32 := 0x00f707b3.
Lemma F_5bbbc : fetch_word AsanUbsan.M.loaded_segments (0x5bc04 : word) = Some W_5bbbc.
Proof. vm_refl. Qed.
Lemma D_5bbbc : decode_any W_5bbbc = Some (Op ALU_ADD 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbc0 : bv 32 := 0x00f63633.
Lemma F_5bbc0 : fetch_word AsanUbsan.M.loaded_segments (0x5bc08 : word) = Some W_5bbc0.
Proof. vm_refl. Qed.
Lemma D_5bbc0 : decode_any W_5bbc0 = Some (Op ALU_SLTU 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbc4 : bv 32 := 0x00e686b3.
Lemma F_5bbc4 : fetch_word AsanUbsan.M.loaded_segments (0x5bc0c : word) = Some W_5bbc4.
Proof. vm_refl. Qed.
Lemma D_5bbc4 : decode_any W_5bbc4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbc8 : bv 32 := 0xfff60613.
Lemma F_5bbc8 : fetch_word AsanUbsan.M.loaded_segments (0x5bc10 : word) = Some W_5bbc8.
Proof. vm_refl. Qed.
Lemma D_5bbc8 : decode_any W_5bbc8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbcc : bv 32 := 0x00d67933.
Lemma F_5bbcc : fetch_word AsanUbsan.M.loaded_segments (0x5bc14 : word) = Some W_5bbcc.
Proof. vm_refl. Qed.
Lemma D_5bbcc : decode_any W_5bbcc = Some (Op ALU_AND 18 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbd0 : bv 32 := 0x08a96063.
Lemma F_5bbd0 : fetch_word AsanUbsan.M.loaded_segments (0x5bc18 : word) = Some W_5bbd0.
Proof. vm_refl. Qed.
Lemma D_5bbd0 : decode_any W_5bbd0 = Some (Branch BC_LTU 18 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbd4 : bv 32 := 0x06b97e63.
Lemma F_5bbd4 : fetch_word AsanUbsan.M.loaded_segments (0x5bc1c : word) = Some W_5bbd4.
Proof. vm_refl. Qed.
Lemma D_5bbd4 : decode_any W_5bbd4 = Some (Branch BC_GEU 18 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbd8 : bv 32 := 0x00990e63.
Lemma F_5bbd8 : fetch_word AsanUbsan.M.loaded_segments (0x5bc20 : word) = Some W_5bbd8.
Proof. vm_refl. Qed.
Lemma D_5bbd8 : decode_any W_5bbd8 = Some (Branch BC_EQ 18 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbdc : bv 32 := 0xfffb4517.
Lemma F_5bbdc : fetch_word AsanUbsan.M.loaded_segments (0x5bc24 : word) = Some W_5bbdc.
Proof. vm_refl. Qed.
Lemma D_5bbdc : decode_any W_5bbdc = Some (Auipc 10 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbe0 : bv 32 := 0x76453703.
Lemma F_5bbe0 : fetch_word AsanUbsan.M.loaded_segments (0x5bc28 : word) = Some W_5bbe0.
Proof. vm_refl. Qed.
Lemma D_5bbe0 : decode_any W_5bbe0 = Some (Load SZ8 true 14 10 1892, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbe4 : bv 32 := 0x160936af.
Lemma F_5bbe4 : fetch_word AsanUbsan.M.loaded_segments (0x5bc2c : word) = Some W_5bbe4.
Proof. vm_refl. Qed.
Lemma D_5bbe4 : decode_any W_5bbe4 = Some (Lr AD true true 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbe8 : bv 32 := 0x16e69463.
Lemma F_5bbe8 : fetch_word AsanUbsan.M.loaded_segments (0x5bc30 : word) = Some W_5bbe8.
Proof. vm_refl. Qed.
Lemma D_5bbe8 : decode_any W_5bbe8 = Some (Branch BC_NE 13 14 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbec : bv 32 := 0x1a09352f.
Lemma F_5bbec : fetch_word AsanUbsan.M.loaded_segments (0x5bc34 : word) = Some W_5bbec.
Proof. vm_refl. Qed.
Lemma D_5bbec : decode_any W_5bbec = Some (Sc AD false true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbf0 : bv 32 := 0xfe051ae3.
Lemma F_5bbf0 : fetch_word AsanUbsan.M.loaded_segments (0x5bc38 : word) = Some W_5bbf0.
Proof. vm_refl. Qed.
Lemma D_5bbf0 : decode_any W_5bbf0 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbf4 : bv 32 := 0xffc4f613.
Lemma F_5bbf4 : fetch_word AsanUbsan.M.loaded_segments (0x5bc3c : word) = Some W_5bbf4.
Proof. vm_refl. Qed.
Lemma D_5bbf4 : decode_any W_5bbf4 = Some (OpImm ALU_AND 12 9 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbf8 : bv 32 := 0x00349513.
Lemma F_5bbf8 : fetch_word AsanUbsan.M.loaded_segments (0x5bc40 : word) = Some W_5bbf8.
Proof. vm_refl. Qed.
Lemma D_5bbf8 : decode_any W_5bbf8 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbfc : bv 32 := 0x0ff00593.
Lemma F_5bbfc : fetch_word AsanUbsan.M.loaded_segments (0x5bc44 : word) = Some W_5bbfc.
Proof. vm_refl. Qed.
Lemma D_5bbfc : decode_any W_5bbfc = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc00 : bv 32 := 0x00300693.
Lemma F_5bc00 : fetch_word AsanUbsan.M.loaded_segments (0x5bc48 : word) = Some W_5bc00.
Proof. vm_refl. Qed.
Lemma D_5bc00 : decode_any W_5bc00 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc04 : bv 32 := 0x00a5973b.
Lemma F_5bc04 : fetch_word AsanUbsan.M.loaded_segments (0x5bc4c : word) = Some W_5bc04.
Proof. vm_refl. Qed.
Lemma D_5bc04 : decode_any W_5bc04 = Some (Op32 ALU_SLL 14 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc08 : bv 32 := 0x00a696bb.
Lemma F_5bc08 : fetch_word AsanUbsan.M.loaded_segments (0x5bc50 : word) = Some W_5bc08.
Proof. vm_refl. Qed.
Lemma D_5bc08 : decode_any W_5bc08 = Some (Op32 ALU_SLL 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc0c : bv 32 := 0x160625af.
Lemma F_5bc0c : fetch_word AsanUbsan.M.loaded_segments (0x5bc54 : word) = Some W_5bc0c.
Proof. vm_refl. Qed.
Lemma D_5bc0c : decode_any W_5bc0c = Some (Lr AW true true 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc10 : bv 32 := 0x00e5f7b3.
Lemma F_5bc10 : fetch_word AsanUbsan.M.loaded_segments (0x5bc58 : word) = Some W_5bc10.
Proof. vm_refl. Qed.
Lemma D_5bc10 : decode_any W_5bc10 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc14 : bv 32 := 0x10d79c63.
Lemma F_5bc14 : fetch_word AsanUbsan.M.loaded_segments (0x5bc5c : word) = Some W_5bc14.
Proof. vm_refl. Qed.
Lemma D_5bc14 : decode_any W_5bc14 = Some (Branch BC_NE 15 13 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc18 : bv 32 := 0x0005c7b3.
Lemma F_5bc18 : fetch_word AsanUbsan.M.loaded_segments (0x5bc60 : word) = Some W_5bc18.
Proof. vm_refl. Qed.
Lemma D_5bc18 : decode_any W_5bc18 = Some (Op ALU_XOR 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc1c : bv 32 := 0x00e7f7b3.
Lemma F_5bc1c : fetch_word AsanUbsan.M.loaded_segments (0x5bc64 : word) = Some W_5bc1c.
Proof. vm_refl. Qed.
Lemma D_5bc1c : decode_any W_5bc1c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc20 : bv 32 := 0x00f5c7b3.
Lemma F_5bc20 : fetch_word AsanUbsan.M.loaded_segments (0x5bc68 : word) = Some W_5bc20.
Proof. vm_refl. Qed.
Lemma D_5bc20 : decode_any W_5bc20 = Some (Op ALU_XOR 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc24 : bv 32 := 0x1af627af.
Lemma F_5bc24 : fetch_word AsanUbsan.M.loaded_segments (0x5bc6c : word) = Some W_5bc24.
Proof. vm_refl. Qed.
Lemma D_5bc24 : decode_any W_5bc24 = Some (Sc AW false true 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc28 : bv 32 := 0xfe0792e3.
Lemma F_5bc28 : fetch_word AsanUbsan.M.loaded_segments (0x5bc70 : word) = Some W_5bc28.
Proof. vm_refl. Qed.
Lemma D_5bc28 : decode_any W_5bc28 = Some (Branch BC_NE 15 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc2c : bv 32 := 0x0024d583.
Lemma F_5bc2c : fetch_word AsanUbsan.M.loaded_segments (0x5bc74 : word) = Some W_5bc2c.
Proof. vm_refl. Qed.
Lemma D_5bc2c : decode_any W_5bc2c = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc30 : bv 32 := 0x0044e603.
Lemma F_5bc30 : fetch_word AsanUbsan.M.loaded_segments (0x5bc78 : word) = Some W_5bc30.
Proof. vm_refl. Qed.
Lemma D_5bc30 : decode_any W_5bc30 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc34 : bv 32 := 0x01048513.
Lemma F_5bc34 : fetch_word AsanUbsan.M.loaded_segments (0x5bc7c : word) = Some W_5bc34.
Proof. vm_refl. Qed.
Lemma D_5bc34 : decode_any W_5bc34 = Some (OpImm ALU_ADD 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc38 : bv 32 := 0x02059593.
Lemma F_5bc38 : fetch_word AsanUbsan.M.loaded_segments (0x5bc80 : word) = Some W_5bc38.
Proof. vm_refl. Qed.
Lemma D_5bc38 : decode_any W_5bc38 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc3c : bv 32 := 0x00c5e5b3.
Lemma F_5bc3c : fetch_word AsanUbsan.M.loaded_segments (0x5bc84 : word) = Some W_5bc3c.
Proof. vm_refl. Qed.
Lemma D_5bc3c : decode_any W_5bc3c = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc40 : bv 32 := 0x00758593.
Lemma F_5bc40 : fetch_word AsanUbsan.M.loaded_segments (0x5bc88 : word) = Some W_5bc40.
Proof. vm_refl. Qed.
Lemma D_5bc40 : decode_any W_5bc40 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc44 : bv 32 := 0xff85f593.
Lemma F_5bc44 : fetch_word AsanUbsan.M.loaded_segments (0x5bc8c : word) = Some W_5bc44.
Proof. vm_refl. Qed.
Lemma D_5bc44 : decode_any W_5bc44 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc48 : bv 32 := 0x0fa00613.
Lemma F_5bc48 : fetch_word AsanUbsan.M.loaded_segments (0x5bc90 : word) = Some W_5bc48.
Proof. vm_refl. Qed.
Lemma D_5bc48 : decode_any W_5bc48 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc4c : bv 32 := 0x444260ef.
Lemma F_5bc4c : fetch_word AsanUbsan.M.loaded_segments (0x5bc94 : word) = Some W_5bc4c.
Proof. vm_refl. Qed.
Lemma D_5bc4c : decode_any W_5bc4c = Some (Jal 1 156740, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc50 : bv 32 := 0x3b82e0ef.
Lemma F_5bc50 : fetch_word AsanUbsan.M.loaded_segments (0x5bc98 : word) = Some W_5bc50.
Proof. vm_refl. Qed.
Lemma D_5bc50 : decode_any W_5bc50 = Some (Jal 1 189368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc54 : bv 32 := 0x0024d583.
Lemma F_5bc54 : fetch_word AsanUbsan.M.loaded_segments (0x5bc9c : word) = Some W_5bc54.
Proof. vm_refl. Qed.
Lemma D_5bc54 : decode_any W_5bc54 = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc58 : bv 32 := 0x0044e603.
Lemma F_5bc58 : fetch_word AsanUbsan.M.loaded_segments (0x5bca0 : word) = Some W_5bc58.
Proof. vm_refl. Qed.
Lemma D_5bc58 : decode_any W_5bc58 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc5c : bv 32 := 0x03053683.
Lemma F_5bc5c : fetch_word AsanUbsan.M.loaded_segments (0x5bca4 : word) = Some W_5bc5c.
Proof. vm_refl. Qed.
Lemma D_5bc5c : decode_any W_5bc5c = Some (Load SZ8 true 13 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc60 : bv 32 := 0x02853703.
Lemma F_5bc60 : fetch_word AsanUbsan.M.loaded_segments (0x5bca8 : word) = Some W_5bc60.
Proof. vm_refl. Qed.
Lemma D_5bc60 : decode_any W_5bc60 = Some (Load SZ8 true 14 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc64 : bv 32 := 0x02059593.
Lemma F_5bc64 : fetch_word AsanUbsan.M.loaded_segments (0x5bcac : word) = Some W_5bc64.
Proof. vm_refl. Qed.
Lemma D_5bc64 : decode_any W_5bc64 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc68 : bv 32 := 0x00c5e5b3.
Lemma F_5bc68 : fetch_word AsanUbsan.M.loaded_segments (0x5bcb0 : word) = Some W_5bc68.
Proof. vm_refl. Qed.
Lemma D_5bc68 : decode_any W_5bc68 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc6c : bv 32 := 0x00d585b3.
Lemma F_5bc6c : fetch_word AsanUbsan.M.loaded_segments (0x5bcb4 : word) = Some W_5bc6c.
Proof. vm_refl. Qed.
Lemma D_5bc6c : decode_any W_5bc6c = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc70 : bv 32 := 0x00170713.
Lemma F_5bc70 : fetch_word AsanUbsan.M.loaded_segments (0x5bcb8 : word) = Some W_5bc70.
Proof. vm_refl. Qed.
Lemma D_5bc70 : decode_any W_5bc70 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc74 : bv 32 := 0x02e53423.
Lemma F_5bc74 : fetch_word AsanUbsan.M.loaded_segments (0x5bcbc : word) = Some W_5bc74.
Proof. vm_refl. Qed.
Lemma D_5bc74 : decode_any W_5bc74 = Some (Store SZ8 10 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc78 : bv 32 := 0x02b53823.
Lemma F_5bc78 : fetch_word AsanUbsan.M.loaded_segments (0x5bcc0 : word) = Some W_5bc78.
Proof. vm_refl. Qed.
Lemma D_5bc78 : decode_any W_5bc78 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc7c : bv 32 := 0x04090863.
Lemma F_5bc7c : fetch_word AsanUbsan.M.loaded_segments (0x5bcc4 : word) = Some W_5bc7c.
Proof. vm_refl. Qed.
Lemma D_5bc7c : decode_any W_5bc7c = Some (Branch BC_EQ 18 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc80 : bv 32 := 0x0209b583.
Lemma F_5bc80 : fetch_word AsanUbsan.M.loaded_segments (0x5bcc8 : word) = Some W_5bc80.
Proof. vm_refl. Qed.
Lemma D_5bc80 : decode_any W_5bc80 = Some (Load SZ8 true 11 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc84 : bv 32 := 0x06b96463.
Lemma F_5bc84 : fetch_word AsanUbsan.M.loaded_segments (0x5bccc : word) = Some W_5bc84.
Proof. vm_refl. Qed.
Lemma D_5bc84 : decode_any W_5bc84 = Some (Branch BC_LTU 18 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc88 : bv 32 := 0x01458a33.
Lemma F_5bc88 : fetch_word AsanUbsan.M.loaded_segments (0x5bcd0 : word) = Some W_5bc88.
Proof. vm_refl. Qed.
Lemma D_5bc88 : decode_any W_5bc88 = Some (Op ALU_ADD 20 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc8c : bv 32 := 0x07497063.
Lemma F_5bc8c : fetch_word AsanUbsan.M.loaded_segments (0x5bcd4 : word) = Some W_5bc8c.
Proof. vm_refl. Qed.
Lemma D_5bc8c : decode_any W_5bc8c = Some (Branch BC_GEU 18 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc90 : bv 32 := 0x00043503.
Lemma F_5bc90 : fetch_word AsanUbsan.M.loaded_segments (0x5bcd8 : word) = Some W_5bc90.
Proof. vm_refl. Qed.
Lemma D_5bc90 : decode_any W_5bc90 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc94 : bv 32 := 0x40b905b3.
Lemma F_5bc94 : fetch_word AsanUbsan.M.loaded_segments (0x5bcdc : word) = Some W_5bc94.
Proof. vm_refl. Qed.
Lemma D_5bc94 : decode_any W_5bc94 = Some (Op ALU_SUB 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc98 : bv 32 := 0x01b59593.
Lemma F_5bc98 : fetch_word AsanUbsan.M.loaded_segments (0x5bce0 : word) = Some W_5bc98.
Proof. vm_refl. Qed.
Lemma D_5bc98 : decode_any W_5bc98 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc9c : bv 32 := 0x03b5d613.
Lemma F_5bc9c : fetch_word AsanUbsan.M.loaded_segments (0x5bce4 : word) = Some W_5bc9c.
Proof. vm_refl. Qed.
Lemma D_5bc9c : decode_any W_5bc9c = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bca0 : bv 32 := 0x000ff597.
Lemma F_5bca0 : fetch_word AsanUbsan.M.loaded_segments (0x5bce8 : word) = Some W_5bca0.
Proof. vm_refl. Qed.
Lemma D_5bca0 : decode_any W_5bca0 = Some (Auipc 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bca4 : bv 32 := 0x9b058593.
Lemma F_5bca4 : fetch_word AsanUbsan.M.loaded_segments (0x5bcec : word) = Some W_5bca4.
Proof. vm_refl. Qed.
Lemma D_5bca4 : decode_any W_5bca4 = Some (OpImm ALU_ADD 11 11 2480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bca8 : bv 32 := 0x00090693.
Lemma F_5bca8 : fetch_word AsanUbsan.M.loaded_segments (0x5bcf0 : word) = Some W_5bca8.
Proof. vm_refl. Qed.
Lemma D_5bca8 : decode_any W_5bca8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcac : bv 32 := 0x02813083.
Lemma F_5bcac : fetch_word AsanUbsan.M.loaded_segments (0x5bcf4 : word) = Some W_5bcac.
Proof. vm_refl. Qed.
Lemma D_5bcac : decode_any W_5bcac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb0 : bv 32 := 0x02013403.
Lemma F_5bcb0 : fetch_word AsanUbsan.M.loaded_segments (0x5bcf8 : word) = Some W_5bcb0.
Proof. vm_refl. Qed.
Lemma D_5bcb0 : decode_any W_5bcb0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb4 : bv 32 := 0x01813483.
Lemma F_5bcb4 : fetch_word AsanUbsan.M.loaded_segments (0x5bcfc : word) = Some W_5bcb4.
Proof. vm_refl. Qed.
Lemma D_5bcb4 : decode_any W_5bcb4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb8 : bv 32 := 0x01013903.
Lemma F_5bcb8 : fetch_word AsanUbsan.M.loaded_segments (0x5bd00 : word) = Some W_5bcb8.
Proof. vm_refl. Qed.
Lemma D_5bcb8 : decode_any W_5bcb8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcbc : bv 32 := 0x00813983.
Lemma F_5bcbc : fetch_word AsanUbsan.M.loaded_segments (0x5bd04 : word) = Some W_5bcbc.
Proof. vm_refl. Qed.
Lemma D_5bcbc : decode_any W_5bcbc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc0 : bv 32 := 0x00013a03.
Lemma F_5bcc0 : fetch_word AsanUbsan.M.loaded_segments (0x5bd08 : word) = Some W_5bcc0.
Proof. vm_refl. Qed.
Lemma D_5bcc0 : decode_any W_5bcc0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc4 : bv 32 := 0x03010113.
Lemma F_5bcc4 : fetch_word AsanUbsan.M.loaded_segments (0x5bd0c : word) = Some W_5bcc4.
Proof. vm_refl. Qed.
Lemma D_5bcc4 : decode_any W_5bcc4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc8 : bv 32 := 0x2200006f.
Lemma F_5bcc8 : fetch_word AsanUbsan.M.loaded_segments (0x5bd10 : word) = Some W_5bcc8.
Proof. vm_refl. Qed.
Lemma D_5bcc8 : decode_any W_5bcc8 = Some (Jal 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcec : bv 32 := 0x04098513.
Lemma F_5bcec : fetch_word AsanUbsan.M.loaded_segments (0x5bd34 : word) = Some W_5bcec.
Proof. vm_refl. Qed.
Lemma D_5bcec : decode_any W_5bcec = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf0 : bv 32 := 0x2b098593.
Lemma F_5bcf0 : fetch_word AsanUbsan.M.loaded_segments (0x5bd38 : word) = Some W_5bcf0.
Proof. vm_refl. Qed.
Lemma D_5bcf0 : decode_any W_5bcf0 = Some (OpImm ALU_ADD 11 19 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf4 : bv 32 := 0x00090613.
Lemma F_5bcf4 : fetch_word AsanUbsan.M.loaded_segments (0x5bd3c : word) = Some W_5bcf4.
Proof. vm_refl. Qed.
Lemma D_5bcf4 : decode_any W_5bcf4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf8 : bv 32 := 0x02813083.
Lemma F_5bcf8 : fetch_word AsanUbsan.M.loaded_segments (0x5bd40 : word) = Some W_5bcf8.
Proof. vm_refl. Qed.
Lemma D_5bcf8 : decode_any W_5bcf8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcfc : bv 32 := 0x02013403.
Lemma F_5bcfc : fetch_word AsanUbsan.M.loaded_segments (0x5bd44 : word) = Some W_5bcfc.
Proof. vm_refl. Qed.
Lemma D_5bcfc : decode_any W_5bcfc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd00 : bv 32 := 0x01813483.
Lemma F_5bd00 : fetch_word AsanUbsan.M.loaded_segments (0x5bd48 : word) = Some W_5bd00.
Proof. vm_refl. Qed.
Lemma D_5bd00 : decode_any W_5bd00 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd04 : bv 32 := 0x01013903.
Lemma F_5bd04 : fetch_word AsanUbsan.M.loaded_segments (0x5bd4c : word) = Some W_5bd04.
Proof. vm_refl. Qed.
Lemma D_5bd04 : decode_any W_5bd04 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd08 : bv 32 := 0x00813983.
Lemma F_5bd08 : fetch_word AsanUbsan.M.loaded_segments (0x5bd50 : word) = Some W_5bd08.
Proof. vm_refl. Qed.
Lemma D_5bd08 : decode_any W_5bd08 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd0c : bv 32 := 0x00013a03.
Lemma F_5bd0c : fetch_word AsanUbsan.M.loaded_segments (0x5bd54 : word) = Some W_5bd0c.
Proof. vm_refl. Qed.
Lemma D_5bd0c : decode_any W_5bd0c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd10 : bv 32 := 0x03010113.
Lemma F_5bd10 : fetch_word AsanUbsan.M.loaded_segments (0x5bd58 : word) = Some W_5bd10.
Proof. vm_refl. Qed.
Lemma D_5bd10 : decode_any W_5bd10 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd14 : bv 32 := 0x39c0006f.
Lemma F_5bd14 : fetch_word AsanUbsan.M.loaded_segments (0x5bd5c : word) = Some W_5bd14.
Proof. vm_refl. Qed.
Lemma D_5bd14 : decode_any W_5bd14 = Some (Jal 0 924, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd68 : bv 32 := 0xfe010113.
Lemma F_5bd68 : fetch_word AsanUbsan.M.loaded_segments (0x5bdb0 : word) = Some W_5bd68.
Proof. vm_refl. Qed.
Lemma D_5bd68 : decode_any W_5bd68 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd6c : bv 32 := 0x00113c23.
Lemma F_5bd6c : fetch_word AsanUbsan.M.loaded_segments (0x5bdb4 : word) = Some W_5bd6c.
Proof. vm_refl. Qed.
Lemma D_5bd6c : decode_any W_5bd6c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd70 : bv 32 := 0x00813823.
Lemma F_5bd70 : fetch_word AsanUbsan.M.loaded_segments (0x5bdb8 : word) = Some W_5bd70.
Proof. vm_refl. Qed.
Lemma D_5bd70 : decode_any W_5bd70 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd74 : bv 32 := 0x00913423.
Lemma F_5bd74 : fetch_word AsanUbsan.M.loaded_segments (0x5bdbc : word) = Some W_5bd74.
Proof. vm_refl. Qed.
Lemma D_5bd74 : decode_any W_5bd74 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd78 : bv 32 := 0x01213023.
Lemma F_5bd78 : fetch_word AsanUbsan.M.loaded_segments (0x5bdc0 : word) = Some W_5bd78.
Proof. vm_refl. Qed.
Lemma D_5bd78 : decode_any W_5bd78 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd7c : bv 32 := 0x26850413.
Lemma F_5bd7c : fetch_word AsanUbsan.M.loaded_segments (0x5bdc4 : word) = Some W_5bd7c.
Proof. vm_refl. Qed.
Lemma D_5bd7c : decode_any W_5bd7c = Some (OpImm ALU_ADD 8 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd80 : bv 32 := 0x0ff00613.
Lemma F_5bd80 : fetch_word AsanUbsan.M.loaded_segments (0x5bdc8 : word) = Some W_5bd80.
Proof. vm_refl. Qed.
Lemma D_5bd80 : decode_any W_5bd80 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd84 : bv 32 := 0xffc47693.
Lemma F_5bd84 : fetch_word AsanUbsan.M.loaded_segments (0x5bdcc : word) = Some W_5bd84.
Proof. vm_refl. Qed.
Lemma D_5bd84 : decode_any W_5bd84 = Some (OpImm ALU_AND 13 8 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd88 : bv 32 := 0x00100713.
Lemma F_5bd88 : fetch_word AsanUbsan.M.loaded_segments (0x5bdd0 : word) = Some W_5bd88.
Proof. vm_refl. Qed.
Lemma D_5bd88 : decode_any W_5bd88 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd8c : bv 32 := 0x1406a7af.
Lemma F_5bd8c : fetch_word AsanUbsan.M.loaded_segments (0x5bdd4 : word) = Some W_5bd8c.
Proof. vm_refl. Qed.
Lemma D_5bd8c : decode_any W_5bd8c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd90 : bv 32 := 0x00070813.
Lemma F_5bd90 : fetch_word AsanUbsan.M.loaded_segments (0x5bdd8 : word) = Some W_5bd90.
Proof. vm_refl. Qed.
Lemma D_5bd90 : decode_any W_5bd90 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd94 : bv 32 := 0x0107c833.
Lemma F_5bd94 : fetch_word AsanUbsan.M.loaded_segments (0x5bddc : word) = Some W_5bd94.
Proof. vm_refl. Qed.
Lemma D_5bd94 : decode_any W_5bd94 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd98 : bv 32 := 0x00c87833.
Lemma F_5bd98 : fetch_word AsanUbsan.M.loaded_segments (0x5bde0 : word) = Some W_5bd98.
Proof. vm_refl. Qed.
Lemma D_5bd98 : decode_any W_5bd98 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd9c : bv 32 := 0x0107c833.
Lemma F_5bd9c : fetch_word AsanUbsan.M.loaded_segments (0x5bde4 : word) = Some W_5bd9c.
Proof. vm_refl. Qed.
Lemma D_5bd9c : decode_any W_5bd9c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda0 : bv 32 := 0x1906a82f.
Lemma F_5bda0 : fetch_word AsanUbsan.M.loaded_segments (0x5bde8 : word) = Some W_5bda0.
Proof. vm_refl. Qed.
Lemma D_5bda0 : decode_any W_5bda0 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda4 : bv 32 := 0xfe0814e3.
Lemma F_5bda4 : fetch_word AsanUbsan.M.loaded_segments (0x5bdec : word) = Some W_5bda4.
Proof. vm_refl. Qed.
Lemma D_5bda4 : decode_any W_5bda4 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda8 : bv 32 := 0x0ff7f613.
Lemma F_5bda8 : fetch_word AsanUbsan.M.loaded_segments (0x5bdf0 : word) = Some W_5bda8.
Proof. vm_refl. Qed.
Lemma D_5bda8 : decode_any W_5bda8 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdac : bv 32 := 0x08061663.
Lemma F_5bdac : fetch_word AsanUbsan.M.loaded_segments (0x5bdf4 : word) = Some W_5bdac.
Proof. vm_refl. Qed.
Lemma D_5bdac : decode_any W_5bdac = Some (Branch BC_NE 12 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb0 : bv 32 := 0x03853703.
Lemma F_5bdb0 : fetch_word AsanUbsan.M.loaded_segments (0x5bdf8 : word) = Some W_5bdb0.
Proof. vm_refl. Qed.
Lemma D_5bdb0 : decode_any W_5bdb0 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb4 : bv 32 := 0x0a070263.
Lemma F_5bdb4 : fetch_word AsanUbsan.M.loaded_segments (0x5bdfc : word) = Some W_5bdb4.
Proof. vm_refl. Qed.
Lemma D_5bdb4 : decode_any W_5bdb4 = Some (Branch BC_EQ 14 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb8 : bv 32 := 0x00000693.
Lemma F_5bdb8 : fetch_word AsanUbsan.M.loaded_segments (0x5be00 : word) = Some W_5bdb8.
Proof. vm_refl. Qed.
Lemma D_5bdb8 : decode_any W_5bdb8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdbc : bv 32 := 0x00853603.
Lemma F_5bdbc : fetch_word AsanUbsan.M.loaded_segments (0x5be04 : word) = Some W_5bdbc.
Proof. vm_refl. Qed.
Lemma D_5bdbc : decode_any W_5bdbc = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc0 : bv 32 := 0x00371713.
Lemma F_5bdc0 : fetch_word AsanUbsan.M.loaded_segments (0x5be08 : word) = Some W_5bdc0.
Proof. vm_refl. Qed.
Lemma D_5bdc0 : decode_any W_5bdc0 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc4 : bv 32 := 0x00e60733.
Lemma F_5bdc4 : fetch_word AsanUbsan.M.loaded_segments (0x5be0c : word) = Some W_5bdc4.
Proof. vm_refl. Qed.
Lemma D_5bdc4 : decode_any W_5bdc4 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc8 : bv 32 := 0x00c0006f.
Lemma F_5bdc8 : fetch_word AsanUbsan.M.loaded_segments (0x5be10 : word) = Some W_5bdc8.
Proof. vm_refl. Qed.
Lemma D_5bdc8 : decode_any W_5bdc8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdcc : bv 32 := 0x00860613.
Lemma F_5bdcc : fetch_word AsanUbsan.M.loaded_segments (0x5be14 : word) = Some W_5bdcc.
Proof. vm_refl. Qed.
Lemma D_5bdcc : decode_any W_5bdcc = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd0 : bv 32 := 0x02e60863.
Lemma F_5bdd0 : fetch_word AsanUbsan.M.loaded_segments (0x5be18 : word) = Some W_5bdd0.
Proof. vm_refl. Qed.
Lemma D_5bdd0 : decode_any W_5bdd0 = Some (Branch BC_EQ 12 14 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd4 : bv 32 := 0x00063783.
Lemma F_5bdd4 : fetch_word AsanUbsan.M.loaded_segments (0x5be1c : word) = Some W_5bdd4.
Proof. vm_refl. Qed.
Lemma D_5bdd4 : decode_any W_5bdd4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd8 : bv 32 := 0x40f588b3.
Lemma F_5bdd8 : fetch_word AsanUbsan.M.loaded_segments (0x5be20 : word) = Some W_5bdd8.
Proof. vm_refl. Qed.
Lemma D_5bdd8 : decode_any W_5bdd8 = Some (Op ALU_SUB 17 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bddc : bv 32 := 0x40d582b3.
Lemma F_5bddc : fetch_word AsanUbsan.M.loaded_segments (0x5be24 : word) = Some W_5bddc.
Proof. vm_refl. Qed.
Lemma D_5bddc : decode_any W_5bddc = Some (Op ALU_SUB 5 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde0 : bv 32 := 0x00078813.
Lemma F_5bde0 : fetch_word AsanUbsan.M.loaded_segments (0x5be28 : word) = Some W_5bde0.
Proof. vm_refl. Qed.
Lemma D_5bde0 : decode_any W_5bde0 = Some (OpImm ALU_ADD 16 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde4 : bv 32 := 0x0058e863.
Lemma F_5bde4 : fetch_word AsanUbsan.M.loaded_segments (0x5be2c : word) = Some W_5bde4.
Proof. vm_refl. Qed.
Lemma D_5bde4 : decode_any W_5bde4 = Some (Branch BC_LTU 17 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde8 : bv 32 := 0x00068813.
Lemma F_5bde8 : fetch_word AsanUbsan.M.loaded_segments (0x5be30 : word) = Some W_5bde8.
Proof. vm_refl. Qed.
Lemma D_5bde8 : decode_any W_5bde8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdec : bv 32 := 0xfef5e0e3.
Lemma F_5bdec : fetch_word AsanUbsan.M.loaded_segments (0x5be34 : word) = Some W_5bdec.
Proof. vm_refl. Qed.
Lemma D_5bdec : decode_any W_5bdec = Some (Branch BC_LTU 11 15 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf0 : bv 32 := 0x0080006f.
Lemma F_5bdf0 : fetch_word AsanUbsan.M.loaded_segments (0x5be38 : word) = Some W_5bdf0.
Proof. vm_refl. Qed.
Lemma D_5bdf0 : decode_any W_5bdf0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf4 : bv 32 := 0xfcf5ece3.
Lemma F_5bdf4 : fetch_word AsanUbsan.M.loaded_segments (0x5be3c : word) = Some W_5bdf4.
Proof. vm_refl. Qed.
Lemma D_5bdf4 : decode_any W_5bdf4 = Some (Branch BC_LTU 11 15 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf8 : bv 32 := 0x00080693.
Lemma F_5bdf8 : fetch_word AsanUbsan.M.loaded_segments (0x5be40 : word) = Some W_5bdf8.
Proof. vm_refl. Qed.
Lemma D_5bdf8 : decode_any W_5bdf8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdfc : bv 32 := 0xfd1ff06f.
Lemma F_5bdfc : fetch_word AsanUbsan.M.loaded_segments (0x5be44 : word) = Some W_5bdfc.
Proof. vm_refl. Qed.
Lemma D_5bdfc : decode_any W_5bdfc = Some (Jal 0 2097104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be00 : bv 32 := 0x04068c63.
Lemma F_5be00 : fetch_word AsanUbsan.M.loaded_segments (0x5be48 : word) = Some W_5be00.
Proof. vm_refl. Qed.
Lemma D_5be00 : decode_any W_5be00 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be04 : bv 32 := 0x0006b703.
Lemma F_5be04 : fetch_word AsanUbsan.M.loaded_segments (0x5be4c : word) = Some W_5be04.
Proof. vm_refl. Qed.
Lemma D_5be04 : decode_any W_5be04 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be08 : bv 32 := 0x06e6ea63.
Lemma F_5be08 : fetch_word AsanUbsan.M.loaded_segments (0x5be50 : word) = Some W_5be08.
Proof. vm_refl. Qed.
Lemma D_5be08 : decode_any W_5be08 = Some (Branch BC_LTU 13 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be0c : bv 32 := 0x0086b603.
Lemma F_5be0c : fetch_word AsanUbsan.M.loaded_segments (0x5be54 : word) = Some W_5be0c.
Proof. vm_refl. Qed.
Lemma D_5be0c : decode_any W_5be0c = Some (Load SZ8 true 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be10 : bv 32 := 0x00e60733.
Lemma F_5be10 : fetch_word AsanUbsan.M.loaded_segments (0x5be58 : word) = Some W_5be10.
Proof. vm_refl. Qed.
Lemma D_5be10 : decode_any W_5be10 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be14 : bv 32 := 0x08e6f063.
Lemma F_5be14 : fetch_word AsanUbsan.M.loaded_segments (0x5be5c : word) = Some W_5be14.
Proof. vm_refl. Qed.
Lemma D_5be14 : decode_any W_5be14 = Some (Branch BC_GEU 13 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be18 : bv 32 := 0x08d5ea63.
Lemma F_5be18 : fetch_word AsanUbsan.M.loaded_segments (0x5be60 : word) = Some W_5be18.
Proof. vm_refl. Qed.
Lemma D_5be18 : decode_any W_5be18 = Some (Branch BC_LTU 11 13 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be1c : bv 32 := 0x02e5fe63.
Lemma F_5be1c : fetch_word AsanUbsan.M.loaded_segments (0x5be64 : word) = Some W_5be1c.
Proof. vm_refl. Qed.
Lemma D_5be1c : decode_any W_5be1c = Some (Branch BC_GEU 11 14 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be20 : bv 32 := 0x00053503.
Lemma F_5be20 : fetch_word AsanUbsan.M.loaded_segments (0x5be68 : word) = Some W_5be20.
Proof. vm_refl. Qed.
Lemma D_5be20 : decode_any W_5be20 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be24 : bv 32 := 0xfff50593.
Lemma F_5be24 : fetch_word AsanUbsan.M.loaded_segments (0x5be6c : word) = Some W_5be24.
Proof. vm_refl. Qed.
Lemma D_5be24 : decode_any W_5be24 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be28 : bv 32 := 0x00d5f5b3.
Lemma F_5be28 : fetch_word AsanUbsan.M.loaded_segments (0x5be70 : word) = Some W_5be28.
Proof. vm_refl. Qed.
Lemma D_5be28 : decode_any W_5be28 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be2c : bv 32 := 0x08059e63.
Lemma F_5be2c : fetch_word AsanUbsan.M.loaded_segments (0x5be74 : word) = Some W_5be2c.
Proof. vm_refl. Qed.
Lemma D_5be2c : decode_any W_5be2c = Some (Branch BC_NE 11 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be30 : bv 32 := 0x00d50533.
Lemma F_5be30 : fetch_word AsanUbsan.M.loaded_segments (0x5be78 : word) = Some W_5be30.
Proof. vm_refl. Qed.
Lemma D_5be30 : decode_any W_5be30 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be34 : bv 32 := 0x0280006f.
Lemma F_5be34 : fetch_word AsanUbsan.M.loaded_segments (0x5be7c : word) = Some W_5be34.
Proof. vm_refl. Qed.
Lemma D_5be34 : decode_any W_5be34 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be5c : bv 32 := 0x0310000f.
Lemma F_5be5c : fetch_word AsanUbsan.M.loaded_segments (0x5bea4 : word) = Some W_5be5c.
Proof. vm_refl. Qed.
Lemma D_5be5c : decode_any W_5be5c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be60 : bv 32 := 0x00040023.
Lemma F_5be60 : fetch_word AsanUbsan.M.loaded_segments (0x5bea8 : word) = Some W_5be60.
Proof. vm_refl. Qed.
Lemma D_5be60 : decode_any W_5be60 = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be64 : bv 32 := 0x01813083.
Lemma F_5be64 : fetch_word AsanUbsan.M.loaded_segments (0x5beac : word) = Some W_5be64.
Proof. vm_refl. Qed.
Lemma D_5be64 : decode_any W_5be64 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be68 : bv 32 := 0x01013403.
Lemma F_5be68 : fetch_word AsanUbsan.M.loaded_segments (0x5beb0 : word) = Some W_5be68.
Proof. vm_refl. Qed.
Lemma D_5be68 : decode_any W_5be68 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be6c : bv 32 := 0x00813483.
Lemma F_5be6c : fetch_word AsanUbsan.M.loaded_segments (0x5beb4 : word) = Some W_5be6c.
Proof. vm_refl. Qed.
Lemma D_5be6c : decode_any W_5be6c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be70 : bv 32 := 0x00013903.
Lemma F_5be70 : fetch_word AsanUbsan.M.loaded_segments (0x5beb8 : word) = Some W_5be70.
Proof. vm_refl. Qed.
Lemma D_5be70 : decode_any W_5be70 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be74 : bv 32 := 0x02010113.
Lemma F_5be74 : fetch_word AsanUbsan.M.loaded_segments (0x5bebc : word) = Some W_5be74.
Proof. vm_refl. Qed.
Lemma D_5be74 : decode_any W_5be74 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be78 : bv 32 := 0x00008067.
Lemma F_5be78 : fetch_word AsanUbsan.M.loaded_segments (0x5bec0 : word) = Some W_5be78.
Proof. vm_refl. Qed.
Lemma D_5be78 : decode_any W_5be78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bee8 : bv 32 := 0xfd010113.
Lemma F_5bee8 : fetch_word AsanUbsan.M.loaded_segments (0x5bf30 : word) = Some W_5bee8.
Proof. vm_refl. Qed.
Lemma D_5bee8 : decode_any W_5bee8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5beec : bv 32 := 0x02113423.
Lemma F_5beec : fetch_word AsanUbsan.M.loaded_segments (0x5bf34 : word) = Some W_5beec.
Proof. vm_refl. Qed.
Lemma D_5beec : decode_any W_5beec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef0 : bv 32 := 0x02813023.
Lemma F_5bef0 : fetch_word AsanUbsan.M.loaded_segments (0x5bf38 : word) = Some W_5bef0.
Proof. vm_refl. Qed.
Lemma D_5bef0 : decode_any W_5bef0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef4 : bv 32 := 0x00913c23.
Lemma F_5bef4 : fetch_word AsanUbsan.M.loaded_segments (0x5bf3c : word) = Some W_5bef4.
Proof. vm_refl. Qed.
Lemma D_5bef4 : decode_any W_5bef4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef8 : bv 32 := 0x01213823.
Lemma F_5bef8 : fetch_word AsanUbsan.M.loaded_segments (0x5bf40 : word) = Some W_5bef8.
Proof. vm_refl. Qed.
Lemma D_5bef8 : decode_any W_5bef8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5befc : bv 32 := 0x01313423.
Lemma F_5befc : fetch_word AsanUbsan.M.loaded_segments (0x5bf44 : word) = Some W_5befc.
Proof. vm_refl. Qed.
Lemma D_5befc : decode_any W_5befc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf00 : bv 32 := 0x01413023.
Lemma F_5bf00 : fetch_word AsanUbsan.M.loaded_segments (0x5bf48 : word) = Some W_5bf00.
Proof. vm_refl. Qed.
Lemma D_5bf00 : decode_any W_5bf00 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf04 : bv 32 := 0x08060463.
Lemma F_5bf04 : fetch_word AsanUbsan.M.loaded_segments (0x5bf4c : word) = Some W_5bf04.
Proof. vm_refl. Qed.
Lemma D_5bf04 : decode_any W_5bf04 = Some (Branch BC_EQ 12 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf08 : bv 32 := 0x02000713.
Lemma F_5bf08 : fetch_word AsanUbsan.M.loaded_segments (0x5bf50 : word) = Some W_5bf08.
Proof. vm_refl. Qed.
Lemma D_5bf08 : decode_any W_5bf08 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf0c : bv 32 := 0x0ae67063.
Lemma F_5bf0c : fetch_word AsanUbsan.M.loaded_segments (0x5bf54 : word) = Some W_5bf0c.
Proof. vm_refl. Qed.
Lemma D_5bf0c : decode_any W_5bf0c = Some (Branch BC_GEU 12 14 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf10 : bv 32 := 0x05000713.
Lemma F_5bf10 : fetch_word AsanUbsan.M.loaded_segments (0x5bf58 : word) = Some W_5bf10.
Proof. vm_refl. Qed.
Lemma D_5bf10 : decode_any W_5bf10 = Some (OpImm ALU_ADD 14 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf14 : bv 32 := 0x02e60433.
Lemma F_5bf14 : fetch_word AsanUbsan.M.loaded_segments (0x5bf5c : word) = Some W_5bf14.
Proof. vm_refl. Qed.
Lemma D_5bf14 : decode_any W_5bf14 = Some (Mul M_MUL 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf18 : bv 32 := 0x00850433.
Lemma F_5bf18 : fetch_word AsanUbsan.M.loaded_segments (0x5bf60 : word) = Some W_5bf18.
Proof. vm_refl. Qed.
Lemma D_5bf18 : decode_any W_5bf18 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf1c : bv 32 := 0x00442783.
Lemma F_5bf1c : fetch_word AsanUbsan.M.loaded_segments (0x5bf64 : word) = Some W_5bf1c.
Proof. vm_refl. Qed.
Lemma D_5bf1c : decode_any W_5bf1c = Some (Load SZ4 true 15 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf20 : bv 32 := 0x0a078863.
Lemma F_5bf20 : fetch_word AsanUbsan.M.loaded_segments (0x5bf68 : word) = Some W_5bf20.
Proof. vm_refl. Qed.
Lemma D_5bf20 : decode_any W_5bf20 = Some (Branch BC_EQ 15 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf24 : bv 32 := 0x00042703.
Lemma F_5bf24 : fetch_word AsanUbsan.M.loaded_segments (0x5bf6c : word) = Some W_5bf24.
Proof. vm_refl. Qed.
Lemma D_5bf24 : decode_any W_5bf24 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf28 : bv 32 := 0x14f70863.
Lemma F_5bf28 : fetch_word AsanUbsan.M.loaded_segments (0x5bf70 : word) = Some W_5bf28.
Proof. vm_refl. Qed.
Lemma D_5bf28 : decode_any W_5bf28 = Some (Branch BC_EQ 14 15 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf2c : bv 32 := 0x0205b583.
Lemma F_5bf2c : fetch_word AsanUbsan.M.loaded_segments (0x5bf74 : word) = Some W_5bf2c.
Proof. vm_refl. Qed.
Lemma D_5bf2c : decode_any W_5bf2c = Some (Load SZ8 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf30 : bv 32 := 0x02061613.
Lemma F_5bf30 : fetch_word AsanUbsan.M.loaded_segments (0x5bf78 : word) = Some W_5bf30.
Proof. vm_refl. Qed.
Lemma D_5bf30 : decode_any W_5bf30 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf34 : bv 32 := 0x40c686b3.
Lemma F_5bf34 : fetch_word AsanUbsan.M.loaded_segments (0x5bf7c : word) = Some W_5bf34.
Proof. vm_refl. Qed.
Lemma D_5bf34 : decode_any W_5bf34 = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf38 : bv 32 := 0x02071613.
Lemma F_5bf38 : fetch_word AsanUbsan.M.loaded_segments (0x5bf80 : word) = Some W_5bf38.
Proof. vm_refl. Qed.
Lemma D_5bf38 : decode_any W_5bf38 = Some (ShiftImm ALU_SLL 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf3c : bv 32 := 0x00170713.
Lemma F_5bf3c : fetch_word AsanUbsan.M.loaded_segments (0x5bf84 : word) = Some W_5bf3c.
Proof. vm_refl. Qed.
Lemma D_5bf3c : decode_any W_5bf3c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf40 : bv 32 := 0x40b686b3.
Lemma F_5bf40 : fetch_word AsanUbsan.M.loaded_segments (0x5bf88 : word) = Some W_5bf40.
Proof. vm_refl. Qed.
Lemma D_5bf40 : decode_any W_5bf40 = Some (Op ALU_SUB 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf44 : bv 32 := 0x00843583.
Lemma F_5bf44 : fetch_word AsanUbsan.M.loaded_segments (0x5bf8c : word) = Some W_5bf44.
Proof. vm_refl. Qed.
Lemma D_5bf44 : decode_any W_5bf44 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf48 : bv 32 := 0x7ff50513.
Lemma F_5bf48 : fetch_word AsanUbsan.M.loaded_segments (0x5bf90 : word) = Some W_5bf48.
Proof. vm_refl. Qed.
Lemma D_5bf48 : decode_any W_5bf48 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf4c : bv 32 := 0x01e65613.
Lemma F_5bf4c : fetch_word AsanUbsan.M.loaded_segments (0x5bf94 : word) = Some W_5bf4c.
Proof. vm_refl. Qed.
Lemma D_5bf4c : decode_any W_5bf4c = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf50 : bv 32 := 0x21150513.
Lemma F_5bf50 : fetch_word AsanUbsan.M.loaded_segments (0x5bf98 : word) = Some W_5bf50.
Proof. vm_refl. Qed.
Lemma D_5bf50 : decode_any W_5bf50 = Some (OpImm ALU_ADD 10 10 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf54 : bv 32 := 0x00c40633.
Lemma F_5bf54 : fetch_word AsanUbsan.M.loaded_segments (0x5bf9c : word) = Some W_5bf54.
Proof. vm_refl. Qed.
Lemma D_5bf54 : decode_any W_5bf54 = Some (Op ALU_ADD 12 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf58 : bv 32 := 0x0046d693.
Lemma F_5bf58 : fetch_word AsanUbsan.M.loaded_segments (0x5bfa0 : word) = Some W_5bf58.
Proof. vm_refl. Qed.
Lemma D_5bf58 : decode_any W_5bf58 = Some (ShiftImm ALU_SRL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf5c : bv 32 := 0x00e42023.
Lemma F_5bf5c : fetch_word AsanUbsan.M.loaded_segments (0x5bfa4 : word) = Some W_5bf5c.
Proof. vm_refl. Qed.
Lemma D_5bf5c : decode_any W_5bf5c = Some (Store SZ4 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf60 : bv 32 := 0x00d62823.
Lemma F_5bf60 : fetch_word AsanUbsan.M.loaded_segments (0x5bfa8 : word) = Some W_5bf60.
Proof. vm_refl. Qed.
Lemma D_5bf60 : decode_any W_5bf60 = Some (Store SZ4 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf64 : bv 32 := 0x40b005b3.
Lemma F_5bf64 : fetch_word AsanUbsan.M.loaded_segments (0x5bfac : word) = Some W_5bf64.
Proof. vm_refl. Qed.
Lemma D_5bf64 : decode_any W_5bf64 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf68 : bv 32 := 0x00b5302f.
Lemma F_5bf68 : fetch_word AsanUbsan.M.loaded_segments (0x5bfb0 : word) = Some W_5bf68.
Proof. vm_refl. Qed.
Lemma D_5bf68 : decode_any W_5bf68 = Some (Amo AMO_ADD AD false false 0 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf6c : bv 32 := 0x02813083.
Lemma F_5bf6c : fetch_word AsanUbsan.M.loaded_segments (0x5bfb4 : word) = Some W_5bf6c.
Proof. vm_refl. Qed.
Lemma D_5bf6c : decode_any W_5bf6c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf70 : bv 32 := 0x02013403.
Lemma F_5bf70 : fetch_word AsanUbsan.M.loaded_segments (0x5bfb8 : word) = Some W_5bf70.
Proof. vm_refl. Qed.
Lemma D_5bf70 : decode_any W_5bf70 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf74 : bv 32 := 0x01813483.
Lemma F_5bf74 : fetch_word AsanUbsan.M.loaded_segments (0x5bfbc : word) = Some W_5bf74.
Proof. vm_refl. Qed.
Lemma D_5bf74 : decode_any W_5bf74 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf78 : bv 32 := 0x01013903.
Lemma F_5bf78 : fetch_word AsanUbsan.M.loaded_segments (0x5bfc0 : word) = Some W_5bf78.
Proof. vm_refl. Qed.
Lemma D_5bf78 : decode_any W_5bf78 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf7c : bv 32 := 0x00813983.
Lemma F_5bf7c : fetch_word AsanUbsan.M.loaded_segments (0x5bfc4 : word) = Some W_5bf7c.
Proof. vm_refl. Qed.
Lemma D_5bf7c : decode_any W_5bf7c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf80 : bv 32 := 0x00013a03.
Lemma F_5bf80 : fetch_word AsanUbsan.M.loaded_segments (0x5bfc8 : word) = Some W_5bf80.
Proof. vm_refl. Qed.
Lemma D_5bf80 : decode_any W_5bf80 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf84 : bv 32 := 0x03010113.
Lemma F_5bf84 : fetch_word AsanUbsan.M.loaded_segments (0x5bfcc : word) = Some W_5bf84.
Proof. vm_refl. Qed.
Lemma D_5bf84 : decode_any W_5bf84 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf88 : bv 32 := 0x00008067.
Lemma F_5bf88 : fetch_word AsanUbsan.M.loaded_segments (0x5bfd0 : word) = Some W_5bf88.
Proof. vm_refl. Qed.
Lemma D_5bf88 : decode_any W_5bf88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

