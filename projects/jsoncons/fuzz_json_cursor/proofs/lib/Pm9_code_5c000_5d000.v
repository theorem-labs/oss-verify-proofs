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

Definition W_5c078 : bv 32 := 0x00050493.
Lemma F_5c078 : fetch_word AsanUbsan.M.loaded_segments (0x5c0c0 : word) = Some W_5c078.
Proof. vm_refl. Qed.
Lemma D_5c078 : decode_any W_5c078 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c07c : bv 32 := 0x00058913.
Lemma F_5c07c : fetch_word AsanUbsan.M.loaded_segments (0x5c0c4 : word) = Some W_5c07c.
Proof. vm_refl. Qed.
Lemma D_5c07c : decode_any W_5c07c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c080 : bv 32 := 0x00040593.
Lemma F_5c080 : fetch_word AsanUbsan.M.loaded_segments (0x5c0c8 : word) = Some W_5c080.
Proof. vm_refl. Qed.
Lemma D_5c080 : decode_any W_5c080 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c084 : bv 32 := 0x00060993.
Lemma F_5c084 : fetch_word AsanUbsan.M.loaded_segments (0x5c0cc : word) = Some W_5c084.
Proof. vm_refl. Qed.
Lemma D_5c084 : decode_any W_5c084 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c088 : bv 32 := 0x00090613.
Lemma F_5c088 : fetch_word AsanUbsan.M.loaded_segments (0x5c0d0 : word) = Some W_5c088.
Proof. vm_refl. Qed.
Lemma D_5c088 : decode_any W_5c088 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c08c : bv 32 := 0x00068a13.
Lemma F_5c08c : fetch_word AsanUbsan.M.loaded_segments (0x5c0d4 : word) = Some W_5c08c.
Proof. vm_refl. Qed.
Lemma D_5c08c : decode_any W_5c08c = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c090 : bv 32 := 0x00098693.
Lemma F_5c090 : fetch_word AsanUbsan.M.loaded_segments (0x5c0d8 : word) = Some W_5c090.
Proof. vm_refl. Qed.
Lemma D_5c090 : decode_any W_5c090 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c094 : bv 32 := 0x1e8000ef.
Lemma F_5c094 : fetch_word AsanUbsan.M.loaded_segments (0x5c0dc : word) = Some W_5c094.
Proof. vm_refl. Qed.
Lemma D_5c094 : decode_any W_5c094 = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c098 : bv 32 := 0x00090593.
Lemma F_5c098 : fetch_word AsanUbsan.M.loaded_segments (0x5c0e0 : word) = Some W_5c098.
Proof. vm_refl. Qed.
Lemma D_5c098 : decode_any W_5c098 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c09c : bv 32 := 0x000a0693.
Lemma F_5c09c : fetch_word AsanUbsan.M.loaded_segments (0x5c0e4 : word) = Some W_5c09c.
Proof. vm_refl. Qed.
Lemma D_5c09c : decode_any W_5c09c = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a0 : bv 32 := 0x00048513.
Lemma F_5c0a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c0e8 : word) = Some W_5c0a0.
Proof. vm_refl. Qed.
Lemma D_5c0a0 : decode_any W_5c0a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a4 : bv 32 := 0x00098613.
Lemma F_5c0a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c0ec : word) = Some W_5c0a4.
Proof. vm_refl. Qed.
Lemma D_5c0a4 : decode_any W_5c0a4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a8 : bv 32 := 0x00042703.
Lemma F_5c0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c0f0 : word) = Some W_5c0a8.
Proof. vm_refl. Qed.
Lemma D_5c0a8 : decode_any W_5c0a8 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0ac : bv 32 := 0xe81ff06f.
Lemma F_5c0ac : fetch_word AsanUbsan.M.loaded_segments (0x5c0f4 : word) = Some W_5c0ac.
Proof. vm_refl. Qed.
Lemma D_5c0ac : decode_any W_5c0ac = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b0 : bv 32 := 0xfe010113.
Lemma F_5c0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c0f8 : word) = Some W_5c0b0.
Proof. vm_refl. Qed.
Lemma D_5c0b0 : decode_any W_5c0b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b4 : bv 32 := 0x00113c23.
Lemma F_5c0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c0fc : word) = Some W_5c0b4.
Proof. vm_refl. Qed.
Lemma D_5c0b4 : decode_any W_5c0b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b8 : bv 32 := 0x00813823.
Lemma F_5c0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c100 : word) = Some W_5c0b8.
Proof. vm_refl. Qed.
Lemma D_5c0b8 : decode_any W_5c0b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0bc : bv 32 := 0x00913423.
Lemma F_5c0bc : fetch_word AsanUbsan.M.loaded_segments (0x5c104 : word) = Some W_5c0bc.
Proof. vm_refl. Qed.
Lemma D_5c0bc : decode_any W_5c0bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c0 : bv 32 := 0x01213023.
Lemma F_5c0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c108 : word) = Some W_5c0c0.
Proof. vm_refl. Qed.
Lemma D_5c0c0 : decode_any W_5c0c0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c4 : bv 32 := 0x00053703.
Lemma F_5c0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c10c : word) = Some W_5c0c4.
Proof. vm_refl. Qed.
Lemma D_5c0c4 : decode_any W_5c0c4 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c8 : bv 32 := 0xfff70693.
Lemma F_5c0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c110 : word) = Some W_5c0c8.
Proof. vm_refl. Qed.
Lemma D_5c0c8 : decode_any W_5c0c8 = Some (OpImm ALU_ADD 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0cc : bv 32 := 0x00c6f6b3.
Lemma F_5c0cc : fetch_word AsanUbsan.M.loaded_segments (0x5c114 : word) = Some W_5c0cc.
Proof. vm_refl. Qed.
Lemma D_5c0cc : decode_any W_5c0cc = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d0 : bv 32 := 0x12069263.
Lemma F_5c0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c118 : word) = Some W_5c0d0.
Proof. vm_refl. Qed.
Lemma D_5c0d0 : decode_any W_5c0d0 = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d4 : bv 32 := 0x26850693.
Lemma F_5c0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c11c : word) = Some W_5c0d4.
Proof. vm_refl. Qed.
Lemma D_5c0d4 : decode_any W_5c0d4 = Some (OpImm ALU_ADD 13 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d8 : bv 32 := 0x0ff00793.
Lemma F_5c0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c120 : word) = Some W_5c0d8.
Proof. vm_refl. Qed.
Lemma D_5c0d8 : decode_any W_5c0d8 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0dc : bv 32 := 0xffc6f813.
Lemma F_5c0dc : fetch_word AsanUbsan.M.loaded_segments (0x5c124 : word) = Some W_5c0dc.
Proof. vm_refl. Qed.
Lemma D_5c0dc : decode_any W_5c0dc = Some (OpImm ALU_AND 16 13 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e0 : bv 32 := 0x00100893.
Lemma F_5c0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c128 : word) = Some W_5c0e0.
Proof. vm_refl. Qed.
Lemma D_5c0e0 : decode_any W_5c0e0 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e4 : bv 32 := 0x140822af.
Lemma F_5c0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c12c : word) = Some W_5c0e4.
Proof. vm_refl. Qed.
Lemma D_5c0e4 : decode_any W_5c0e4 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e8 : bv 32 := 0x00088313.
Lemma F_5c0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c130 : word) = Some W_5c0e8.
Proof. vm_refl. Qed.
Lemma D_5c0e8 : decode_any W_5c0e8 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0ec : bv 32 := 0x0062c333.
Lemma F_5c0ec : fetch_word AsanUbsan.M.loaded_segments (0x5c134 : word) = Some W_5c0ec.
Proof. vm_refl. Qed.
Lemma D_5c0ec : decode_any W_5c0ec = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f0 : bv 32 := 0x00f37333.
Lemma F_5c0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c138 : word) = Some W_5c0f0.
Proof. vm_refl. Qed.
Lemma D_5c0f0 : decode_any W_5c0f0 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f4 : bv 32 := 0x0062c333.
Lemma F_5c0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5c13c : word) = Some W_5c0f4.
Proof. vm_refl. Qed.
Lemma D_5c0f4 : decode_any W_5c0f4 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f8 : bv 32 := 0x1868232f.
Lemma F_5c0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5c140 : word) = Some W_5c0f8.
Proof. vm_refl. Qed.
Lemma D_5c0f8 : decode_any W_5c0f8 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0fc : bv 32 := 0xfe0314e3.
Lemma F_5c0fc : fetch_word AsanUbsan.M.loaded_segments (0x5c144 : word) = Some W_5c0fc.
Proof. vm_refl. Qed.
Lemma D_5c0fc : decode_any W_5c0fc = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c100 : bv 32 := 0x0ff2f793.
Lemma F_5c100 : fetch_word AsanUbsan.M.loaded_segments (0x5c148 : word) = Some W_5c100.
Proof. vm_refl. Qed.
Lemma D_5c100 : decode_any W_5c100 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c104 : bv 32 := 0x40e60433.
Lemma F_5c104 : fetch_word AsanUbsan.M.loaded_segments (0x5c14c : word) = Some W_5c104.
Proof. vm_refl. Qed.
Lemma D_5c104 : decode_any W_5c104 = Some (Op ALU_SUB 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c108 : bv 32 := 0x10079663.
Lemma F_5c108 : fetch_word AsanUbsan.M.loaded_segments (0x5c150 : word) = Some W_5c108.
Proof. vm_refl. Qed.
Lemma D_5c108 : decode_any W_5c108 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c10c : bv 32 := 0x01843683.
Lemma F_5c10c : fetch_word AsanUbsan.M.loaded_segments (0x5c154 : word) = Some W_5c10c.
Proof. vm_refl. Qed.
Lemma D_5c10c : decode_any W_5c10c = Some (Load SZ8 true 13 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c110 : bv 32 := 0x00853783.
Lemma F_5c110 : fetch_word AsanUbsan.M.loaded_segments (0x5c158 : word) = Some W_5c110.
Proof. vm_refl. Qed.
Lemma D_5c110 : decode_any W_5c110 = Some (Load SZ8 true 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c114 : bv 32 := 0x00369613.
Lemma F_5c114 : fetch_word AsanUbsan.M.loaded_segments (0x5c15c : word) = Some W_5c114.
Proof. vm_refl. Qed.
Lemma D_5c114 : decode_any W_5c114 = Some (ShiftImm ALU_SLL 12 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c118 : bv 32 := 0x00c78633.
Lemma F_5c118 : fetch_word AsanUbsan.M.loaded_segments (0x5c160 : word) = Some W_5c118.
Proof. vm_refl. Qed.
Lemma D_5c118 : decode_any W_5c118 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c11c : bv 32 := 0x00063703.
Lemma F_5c11c : fetch_word AsanUbsan.M.loaded_segments (0x5c164 : word) = Some W_5c11c.
Proof. vm_refl. Qed.
Lemma D_5c11c : decode_any W_5c11c = Some (Load SZ8 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c120 : bv 32 := 0x12871263.
Lemma F_5c120 : fetch_word AsanUbsan.M.loaded_segments (0x5c168 : word) = Some W_5c120.
Proof. vm_refl. Qed.
Lemma D_5c120 : decode_any W_5c120 = Some (Branch BC_NE 14 8 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c124 : bv 32 := 0x03853703.
Lemma F_5c124 : fetch_word AsanUbsan.M.loaded_segments (0x5c16c : word) = Some W_5c124.
Proof. vm_refl. Qed.
Lemma D_5c124 : decode_any W_5c124 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c128 : bv 32 := 0x12e6fe63.
Lemma F_5c128 : fetch_word AsanUbsan.M.loaded_segments (0x5c170 : word) = Some W_5c128.
Proof. vm_refl. Qed.
Lemma D_5c128 : decode_any W_5c128 = Some (Branch BC_GEU 13 14 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c12c : bv 32 := 0x00371813.
Lemma F_5c12c : fetch_word AsanUbsan.M.loaded_segments (0x5c174 : word) = Some W_5c12c.
Proof. vm_refl. Qed.
Lemma D_5c12c : decode_any W_5c12c = Some (ShiftImm ALU_SLL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c130 : bv 32 := 0x00843883.
Lemma F_5c130 : fetch_word AsanUbsan.M.loaded_segments (0x5c178 : word) = Some W_5c130.
Proof. vm_refl. Qed.
Lemma D_5c130 : decode_any W_5c130 = Some (Load SZ8 true 17 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c134 : bv 32 := 0x00f807b3.
Lemma F_5c134 : fetch_word AsanUbsan.M.loaded_segments (0x5c17c : word) = Some W_5c134.
Proof. vm_refl. Qed.
Lemma D_5c134 : decode_any W_5c134 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c138 : bv 32 := 0x05053803.
Lemma F_5c138 : fetch_word AsanUbsan.M.loaded_segments (0x5c180 : word) = Some W_5c138.
Proof. vm_refl. Qed.
Lemma D_5c138 : decode_any W_5c138 = Some (Load SZ8 true 16 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c13c : bv 32 := 0x05853283.
Lemma F_5c13c : fetch_word AsanUbsan.M.loaded_segments (0x5c184 : word) = Some W_5c13c.
Proof. vm_refl. Qed.
Lemma D_5c13c : decode_any W_5c13c = Some (Load SZ8 true 5 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c140 : bv 32 := 0xfff70713.
Lemma F_5c140 : fetch_word AsanUbsan.M.loaded_segments (0x5c188 : word) = Some W_5c140.
Proof. vm_refl. Qed.
Lemma D_5c140 : decode_any W_5c140 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c144 : bv 32 := 0xff87b783.
Lemma F_5c144 : fetch_word AsanUbsan.M.loaded_segments (0x5c18c : word) = Some W_5c144.
Proof. vm_refl. Qed.
Lemma D_5c144 : decode_any W_5c144 = Some (Load SZ8 true 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c148 : bv 32 := 0x00180813.
Lemma F_5c148 : fetch_word AsanUbsan.M.loaded_segments (0x5c190 : word) = Some W_5c148.
Proof. vm_refl. Qed.
Lemma D_5c148 : decode_any W_5c148 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c14c : bv 32 := 0x411282b3.
Lemma F_5c14c : fetch_word AsanUbsan.M.loaded_segments (0x5c194 : word) = Some W_5c14c.
Proof. vm_refl. Qed.
Lemma D_5c14c : decode_any W_5c14c = Some (Op ALU_SUB 5 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c150 : bv 32 := 0x02e53c23.
Lemma F_5c150 : fetch_word AsanUbsan.M.loaded_segments (0x5c198 : word) = Some W_5c150.
Proof. vm_refl. Qed.
Lemma D_5c150 : decode_any W_5c150 = Some (Store SZ8 10 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c154 : bv 32 := 0x04050023.
Lemma F_5c154 : fetch_word AsanUbsan.M.loaded_segments (0x5c19c : word) = Some W_5c154.
Proof. vm_refl. Qed.
Lemma D_5c154 : decode_any W_5c154 = Some (Store SZ1 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c158 : bv 32 := 0x05053823.
Lemma F_5c158 : fetch_word AsanUbsan.M.loaded_segments (0x5c1a0 : word) = Some W_5c158.
Proof. vm_refl. Qed.
Lemma D_5c158 : decode_any W_5c158 = Some (Store SZ8 10 16 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c15c : bv 32 := 0x04553c23.
Lemma F_5c15c : fetch_word AsanUbsan.M.loaded_segments (0x5c1a4 : word) = Some W_5c15c.
Proof. vm_refl. Qed.
Lemma D_5c15c : decode_any W_5c15c = Some (Store SZ8 10 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c160 : bv 32 := 0x01058713.
Lemma F_5c160 : fetch_word AsanUbsan.M.loaded_segments (0x5c1a8 : word) = Some W_5c160.
Proof. vm_refl. Qed.
Lemma D_5c160 : decode_any W_5c160 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c164 : bv 32 := 0x41100833.
Lemma F_5c164 : fetch_word AsanUbsan.M.loaded_segments (0x5c1ac : word) = Some W_5c164.
Proof. vm_refl. Qed.
Lemma D_5c164 : decode_any W_5c164 = Some (Op ALU_SUB 16 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c168 : bv 32 := 0x00f63023.
Lemma F_5c168 : fetch_word AsanUbsan.M.loaded_segments (0x5c1b0 : word) = Some W_5c168.
Proof. vm_refl. Qed.
Lemma D_5c168 : decode_any W_5c168 = Some (Store SZ8 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c16c : bv 32 := 0x00d7bc23.
Lemma F_5c16c : fetch_word AsanUbsan.M.loaded_segments (0x5c1b4 : word) = Some W_5c16c.
Proof. vm_refl. Qed.
Lemma D_5c16c : decode_any W_5c16c = Some (Store SZ8 15 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c170 : bv 32 := 0x0107302f.
Lemma F_5c170 : fetch_word AsanUbsan.M.loaded_segments (0x5c1b8 : word) = Some W_5c170.
Proof. vm_refl. Qed.
Lemma D_5c170 : decode_any W_5c170 = Some (Amo AMO_ADD AD false false 0 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c174 : bv 32 := 0x00843603.
Lemma F_5c174 : fetch_word AsanUbsan.M.loaded_segments (0x5c1bc : word) = Some W_5c174.
Proof. vm_refl. Qed.
Lemma D_5c174 : decode_any W_5c174 = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c178 : bv 32 := 0x01858593.
Lemma F_5c178 : fetch_word AsanUbsan.M.loaded_segments (0x5c1c0 : word) = Some W_5c178.
Proof. vm_refl. Qed.
Lemma D_5c178 : decode_any W_5c178 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c17c : bv 32 := 0x40c00633.
Lemma F_5c17c : fetch_word AsanUbsan.M.loaded_segments (0x5c1c4 : word) = Some W_5c17c.
Proof. vm_refl. Qed.
Lemma D_5c17c : decode_any W_5c17c = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c180 : bv 32 := 0x00c5b02f.
Lemma F_5c180 : fetch_word AsanUbsan.M.loaded_segments (0x5c1c8 : word) = Some W_5c180.
Proof. vm_refl. Qed.
Lemma D_5c180 : decode_any W_5c180 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c184 : bv 32 := 0x0310000f.
Lemma F_5c184 : fetch_word AsanUbsan.M.loaded_segments (0x5c1cc : word) = Some W_5c184.
Proof. vm_refl. Qed.
Lemma D_5c184 : decode_any W_5c184 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c188 : bv 32 := 0x26050423.
Lemma F_5c188 : fetch_word AsanUbsan.M.loaded_segments (0x5c1d0 : word) = Some W_5c188.
Proof. vm_refl. Qed.
Lemma D_5c188 : decode_any W_5c188 = Some (Store SZ1 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c18c : bv 32 := 0x00043483.
Lemma F_5c18c : fetch_word AsanUbsan.M.loaded_segments (0x5c1d4 : word) = Some W_5c18c.
Proof. vm_refl. Qed.
Lemma D_5c18c : decode_any W_5c18c = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c190 : bv 32 := 0x00843903.
Lemma F_5c190 : fetch_word AsanUbsan.M.loaded_segments (0x5c1d8 : word) = Some W_5c190.
Proof. vm_refl. Qed.
Lemma D_5c190 : decode_any W_5c190 = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c194 : bv 32 := 0x00048513.
Lemma F_5c194 : fetch_word AsanUbsan.M.loaded_segments (0x5c1dc : word) = Some W_5c194.
Proof. vm_refl. Qed.
Lemma D_5c194 : decode_any W_5c194 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c198 : bv 32 := 0x00090593.
Lemma F_5c198 : fetch_word AsanUbsan.M.loaded_segments (0x5c1e0 : word) = Some W_5c198.
Proof. vm_refl. Qed.
Lemma D_5c198 : decode_any W_5c198 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c19c : bv 32 := 0x00000613.
Lemma F_5c19c : fetch_word AsanUbsan.M.loaded_segments (0x5c1e4 : word) = Some W_5c19c.
Proof. vm_refl. Qed.
Lemma D_5c19c : decode_any W_5c19c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a0 : bv 32 := 0x6f1250ef.
Lemma F_5c1a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c1e8 : word) = Some W_5c1a0.
Proof. vm_refl. Qed.
Lemma D_5c1a0 : decode_any W_5c1a0 = Some (Jal 1 155376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a4 : bv 32 := 0x00048513.
Lemma F_5c1a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c1ec : word) = Some W_5c1a4.
Proof. vm_refl. Qed.
Lemma D_5c1a4 : decode_any W_5c1a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a8 : bv 32 := 0x00090593.
Lemma F_5c1a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c1f0 : word) = Some W_5c1a8.
Proof. vm_refl. Qed.
Lemma D_5c1a8 : decode_any W_5c1a8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1ac : bv 32 := 0x0cd240ef.
Lemma F_5c1ac : fetch_word AsanUbsan.M.loaded_segments (0x5c1f4 : word) = Some W_5c1ac.
Proof. vm_refl. Qed.
Lemma D_5c1ac : decode_any W_5c1ac = Some (Jal 1 149708, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b0 : bv 32 := 0x6592d0ef.
Lemma F_5c1b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c1f8 : word) = Some W_5c1b0.
Proof. vm_refl. Qed.
Lemma D_5c1b0 : decode_any W_5c1b0 = Some (Jal 1 187992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b4 : bv 32 := 0x06053683.
Lemma F_5c1b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c1fc : word) = Some W_5c1b4.
Proof. vm_refl. Qed.
Lemma D_5c1b4 : decode_any W_5c1b4 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b8 : bv 32 := 0x05853703.
Lemma F_5c1b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c200 : word) = Some W_5c1b8.
Proof. vm_refl. Qed.
Lemma D_5c1b8 : decode_any W_5c1b8 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1bc : bv 32 := 0x00043603.
Lemma F_5c1bc : fetch_word AsanUbsan.M.loaded_segments (0x5c204 : word) = Some W_5c1bc.
Proof. vm_refl. Qed.
Lemma D_5c1bc : decode_any W_5c1bc = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c0 : bv 32 := 0x00843583.
Lemma F_5c1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c208 : word) = Some W_5c1c0.
Proof. vm_refl. Qed.
Lemma D_5c1c0 : decode_any W_5c1c0 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c4 : bv 32 := 0x012686b3.
Lemma F_5c1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c20c : word) = Some W_5c1c4.
Proof. vm_refl. Qed.
Lemma D_5c1c4 : decode_any W_5c1c4 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c8 : bv 32 := 0x00170713.
Lemma F_5c1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c210 : word) = Some W_5c1c8.
Proof. vm_refl. Qed.
Lemma D_5c1c8 : decode_any W_5c1c8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1cc : bv 32 := 0x04e53c23.
Lemma F_5c1cc : fetch_word AsanUbsan.M.loaded_segments (0x5c214 : word) = Some W_5c1cc.
Proof. vm_refl. Qed.
Lemma D_5c1cc : decode_any W_5c1cc = Some (Store SZ8 10 14 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d0 : bv 32 := 0x06d53023.
Lemma F_5c1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c218 : word) = Some W_5c1d0.
Proof. vm_refl. Qed.
Lemma D_5c1d0 : decode_any W_5c1d0 = Some (Store SZ8 10 13 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d4 : bv 32 := 0x00060513.
Lemma F_5c1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c21c : word) = Some W_5c1d4.
Proof. vm_refl. Qed.
Lemma D_5c1d4 : decode_any W_5c1d4 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d8 : bv 32 := 0x00000613.
Lemma F_5c1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c220 : word) = Some W_5c1d8.
Proof. vm_refl. Qed.
Lemma D_5c1d8 : decode_any W_5c1d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1dc : bv 32 := 0x01813083.
Lemma F_5c1dc : fetch_word AsanUbsan.M.loaded_segments (0x5c224 : word) = Some W_5c1dc.
Proof. vm_refl. Qed.
Lemma D_5c1dc : decode_any W_5c1dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e0 : bv 32 := 0x01013403.
Lemma F_5c1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c228 : word) = Some W_5c1e0.
Proof. vm_refl. Qed.
Lemma D_5c1e0 : decode_any W_5c1e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e4 : bv 32 := 0x00813483.
Lemma F_5c1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c22c : word) = Some W_5c1e4.
Proof. vm_refl. Qed.
Lemma D_5c1e4 : decode_any W_5c1e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e8 : bv 32 := 0x00013903.
Lemma F_5c1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c230 : word) = Some W_5c1e8.
Proof. vm_refl. Qed.
Lemma D_5c1e8 : decode_any W_5c1e8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1ec : bv 32 := 0x02010113.
Lemma F_5c1ec : fetch_word AsanUbsan.M.loaded_segments (0x5c234 : word) = Some W_5c1ec.
Proof. vm_refl. Qed.
Lemma D_5c1ec : decode_any W_5c1ec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1f0 : bv 32 := 0x0353806f.
Lemma F_5c1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c238 : word) = Some W_5c1f0.
Proof. vm_refl. Qed.
Lemma D_5c1f0 : decode_any W_5c1f0 = Some (Jal 0 231476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c27c : bv 32 := 0xfc010113.
Lemma F_5c27c : fetch_word AsanUbsan.M.loaded_segments (0x5c2c4 : word) = Some W_5c27c.
Proof. vm_refl. Qed.
Lemma D_5c27c : decode_any W_5c27c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c280 : bv 32 := 0x02113c23.
Lemma F_5c280 : fetch_word AsanUbsan.M.loaded_segments (0x5c2c8 : word) = Some W_5c280.
Proof. vm_refl. Qed.
Lemma D_5c280 : decode_any W_5c280 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c284 : bv 32 := 0x02013423.
Lemma F_5c284 : fetch_word AsanUbsan.M.loaded_segments (0x5c2cc : word) = Some W_5c284.
Proof. vm_refl. Qed.
Lemma D_5c284 : decode_any W_5c284 = Some (Store SZ8 2 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c288 : bv 32 := 0x02013823.
Lemma F_5c288 : fetch_word AsanUbsan.M.loaded_segments (0x5c2d0 : word) = Some W_5c288.
Proof. vm_refl. Qed.
Lemma D_5c288 : decode_any W_5c288 = Some (Store SZ8 2 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c28c : bv 32 := 0x0005a803.
Lemma F_5c28c : fetch_word AsanUbsan.M.loaded_segments (0x5c2d4 : word) = Some W_5c28c.
Proof. vm_refl. Qed.
Lemma D_5c28c : decode_any W_5c28c = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c290 : bv 32 := 0x0045e783.
Lemma F_5c290 : fetch_word AsanUbsan.M.loaded_segments (0x5c2d8 : word) = Some W_5c290.
Proof. vm_refl. Qed.
Lemma D_5c290 : decode_any W_5c290 = Some (Load SZ4 false 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c294 : bv 32 := 0x00c13423.
Lemma F_5c294 : fetch_word AsanUbsan.M.loaded_segments (0x5c2dc : word) = Some W_5c294.
Proof. vm_refl. Qed.
Lemma D_5c294 : decode_any W_5c294 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c298 : bv 32 := 0x00013823.
Lemma F_5c298 : fetch_word AsanUbsan.M.loaded_segments (0x5c2e0 : word) = Some W_5c298.
Proof. vm_refl. Qed.
Lemma D_5c298 : decode_any W_5c298 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c29c : bv 32 := 0x00013c23.
Lemma F_5c29c : fetch_word AsanUbsan.M.loaded_segments (0x5c2e4 : word) = Some W_5c29c.
Proof. vm_refl. Qed.
Lemma D_5c29c : decode_any W_5c29c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a0 : bv 32 := 0x02013023.
Lemma F_5c2a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c2e8 : word) = Some W_5c2a0.
Proof. vm_refl. Qed.
Lemma D_5c2a0 : decode_any W_5c2a0 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a4 : bv 32 := 0x0017d793.
Lemma F_5c2a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c2ec : word) = Some W_5c2a4.
Proof. vm_refl. Qed.
Lemma D_5c2a4 : decode_any W_5c2a4 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a8 : bv 32 := 0x02081713.
Lemma F_5c2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c2f0 : word) = Some W_5c2a8.
Proof. vm_refl. Qed.
Lemma D_5c2a8 : decode_any W_5c2a8 = Some (ShiftImm ALU_SLL 14 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2ac : bv 32 := 0x02075713.
Lemma F_5c2ac : fetch_word AsanUbsan.M.loaded_segments (0x5c2f4 : word) = Some W_5c2ac.
Proof. vm_refl. Qed.
Lemma D_5c2ac : decode_any W_5c2ac = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b0 : bv 32 := 0x04f86663.
Lemma F_5c2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c2f8 : word) = Some W_5c2b0.
Proof. vm_refl. Qed.
Lemma D_5c2b0 : decode_any W_5c2b0 = Some (Branch BC_LTU 16 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b4 : bv 32 := 0x40f70733.
Lemma F_5c2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c2fc : word) = Some W_5c2b4.
Proof. vm_refl. Qed.
Lemma D_5c2b4 : decode_any W_5c2b4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b8 : bv 32 := 0x7ff50513.
Lemma F_5c2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c300 : word) = Some W_5c2b8.
Proof. vm_refl. Qed.
Lemma D_5c2b8 : decode_any W_5c2b8 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2bc : bv 32 := 0x00e5a023.
Lemma F_5c2bc : fetch_word AsanUbsan.M.loaded_segments (0x5c304 : word) = Some W_5c2bc.
Proof. vm_refl. Qed.
Lemma D_5c2bc : decode_any W_5c2bc = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c0 : bv 32 := 0x20150813.
Lemma F_5c2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c308 : word) = Some W_5c2c0.
Proof. vm_refl. Qed.
Lemma D_5c2c0 : decode_any W_5c2c0 = Some (OpImm ALU_ADD 16 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c4 : bv 32 := 0x00271713.
Lemma F_5c2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c30c : word) = Some W_5c2c4.
Proof. vm_refl. Qed.
Lemma D_5c2c4 : decode_any W_5c2c4 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c8 : bv 32 := 0x00e585b3.
Lemma F_5c2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c310 : word) = Some W_5c2c8.
Proof. vm_refl. Qed.
Lemma D_5c2c8 : decode_any W_5c2c8 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2cc : bv 32 := 0x01058713.
Lemma F_5c2cc : fetch_word AsanUbsan.M.loaded_segments (0x5c314 : word) = Some W_5c2cc.
Proof. vm_refl. Qed.
Lemma D_5c2cc : decode_any W_5c2cc = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d0 : bv 32 := 0x00810593.
Lemma F_5c2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c318 : word) = Some W_5c2d0.
Proof. vm_refl. Qed.
Lemma D_5c2d0 : decode_any W_5c2d0 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d4 : bv 32 := 0x00060513.
Lemma F_5c2d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c31c : word) = Some W_5c2d4.
Proof. vm_refl. Qed.
Lemma D_5c2d4 : decode_any W_5c2d4 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d8 : bv 32 := 0x00080613.
Lemma F_5c2d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c320 : word) = Some W_5c2d8.
Proof. vm_refl. Qed.
Lemma D_5c2d8 : decode_any W_5c2d8 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2dc : bv 32 := 0x144000ef.
Lemma F_5c2dc : fetch_word AsanUbsan.M.loaded_segments (0x5c324 : word) = Some W_5c2dc.
Proof. vm_refl. Qed.
Lemma D_5c2dc : decode_any W_5c2dc = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e0 : bv 32 := 0x02013503.
Lemma F_5c2e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c328 : word) = Some W_5c2e0.
Proof. vm_refl. Qed.
Lemma D_5c2e0 : decode_any W_5c2e0 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e4 : bv 32 := 0x02813583.
Lemma F_5c2e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c32c : word) = Some W_5c2e4.
Proof. vm_refl. Qed.
Lemma D_5c2e4 : decode_any W_5c2e4 = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e8 : bv 32 := 0x00000613.
Lemma F_5c2e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c330 : word) = Some W_5c2e8.
Proof. vm_refl. Qed.
Lemma D_5c2e8 : decode_any W_5c2e8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2ec : bv 32 := 0x738380ef.
Lemma F_5c2ec : fetch_word AsanUbsan.M.loaded_segments (0x5c334 : word) = Some W_5c2ec.
Proof. vm_refl. Qed.
Lemma D_5c2ec : decode_any W_5c2ec = Some (Jal 1 231224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f0 : bv 32 := 0x03813083.
Lemma F_5c2f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c338 : word) = Some W_5c2f0.
Proof. vm_refl. Qed.
Lemma D_5c2f0 : decode_any W_5c2f0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f4 : bv 32 := 0x04010113.
Lemma F_5c2f4 : fetch_word AsanUbsan.M.loaded_segments (0x5c33c : word) = Some W_5c2f4.
Proof. vm_refl. Qed.
Lemma D_5c2f4 : decode_any W_5c2f4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f8 : bv 32 := 0x00008067.
Lemma F_5c2f8 : fetch_word AsanUbsan.M.loaded_segments (0x5c340 : word) = Some W_5c2f8.
Proof. vm_refl. Qed.
Lemma D_5c2f8 : decode_any W_5c2f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c420 : bv 32 := 0xf8010113.
Lemma F_5c420 : fetch_word AsanUbsan.M.loaded_segments (0x5c468 : word) = Some W_5c420.
Proof. vm_refl. Qed.
Lemma D_5c420 : decode_any W_5c420 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c424 : bv 32 := 0x06113c23.
Lemma F_5c424 : fetch_word AsanUbsan.M.loaded_segments (0x5c46c : word) = Some W_5c424.
Proof. vm_refl. Qed.
Lemma D_5c424 : decode_any W_5c424 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c428 : bv 32 := 0x06813823.
Lemma F_5c428 : fetch_word AsanUbsan.M.loaded_segments (0x5c470 : word) = Some W_5c428.
Proof. vm_refl. Qed.
Lemma D_5c428 : decode_any W_5c428 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c42c : bv 32 := 0x06913423.
Lemma F_5c42c : fetch_word AsanUbsan.M.loaded_segments (0x5c474 : word) = Some W_5c42c.
Proof. vm_refl. Qed.
Lemma D_5c42c : decode_any W_5c42c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c430 : bv 32 := 0x07213023.
Lemma F_5c430 : fetch_word AsanUbsan.M.loaded_segments (0x5c478 : word) = Some W_5c430.
Proof. vm_refl. Qed.
Lemma D_5c430 : decode_any W_5c430 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c434 : bv 32 := 0x05313c23.
Lemma F_5c434 : fetch_word AsanUbsan.M.loaded_segments (0x5c47c : word) = Some W_5c434.
Proof. vm_refl. Qed.
Lemma D_5c434 : decode_any W_5c434 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c438 : bv 32 := 0x05413823.
Lemma F_5c438 : fetch_word AsanUbsan.M.loaded_segments (0x5c480 : word) = Some W_5c438.
Proof. vm_refl. Qed.
Lemma D_5c438 : decode_any W_5c438 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c43c : bv 32 := 0x05513423.
Lemma F_5c43c : fetch_word AsanUbsan.M.loaded_segments (0x5c484 : word) = Some W_5c43c.
Proof. vm_refl. Qed.
Lemma D_5c43c : decode_any W_5c43c = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c440 : bv 32 := 0x05613023.
Lemma F_5c440 : fetch_word AsanUbsan.M.loaded_segments (0x5c488 : word) = Some W_5c440.
Proof. vm_refl. Qed.
Lemma D_5c440 : decode_any W_5c440 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c444 : bv 32 := 0x03713c23.
Lemma F_5c444 : fetch_word AsanUbsan.M.loaded_segments (0x5c48c : word) = Some W_5c444.
Proof. vm_refl. Qed.
Lemma D_5c444 : decode_any W_5c444 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c448 : bv 32 := 0x03813823.
Lemma F_5c448 : fetch_word AsanUbsan.M.loaded_segments (0x5c490 : word) = Some W_5c448.
Proof. vm_refl. Qed.
Lemma D_5c448 : decode_any W_5c448 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c44c : bv 32 := 0x03913423.
Lemma F_5c44c : fetch_word AsanUbsan.M.loaded_segments (0x5c494 : word) = Some W_5c44c.
Proof. vm_refl. Qed.
Lemma D_5c44c : decode_any W_5c44c = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c450 : bv 32 := 0x03a13023.
Lemma F_5c450 : fetch_word AsanUbsan.M.loaded_segments (0x5c498 : word) = Some W_5c450.
Proof. vm_refl. Qed.
Lemma D_5c450 : decode_any W_5c450 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c454 : bv 32 := 0x01b13c23.
Lemma F_5c454 : fetch_word AsanUbsan.M.loaded_segments (0x5c49c : word) = Some W_5c454.
Proof. vm_refl. Qed.
Lemma D_5c454 : decode_any W_5c454 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c458 : bv 32 := 0x00078a93.
Lemma F_5c458 : fetch_word AsanUbsan.M.loaded_segments (0x5c4a0 : word) = Some W_5c458.
Proof. vm_refl. Qed.
Lemma D_5c458 : decode_any W_5c458 = Some (OpImm ALU_ADD 21 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c45c : bv 32 := 0x00070b13.
Lemma F_5c45c : fetch_word AsanUbsan.M.loaded_segments (0x5c4a4 : word) = Some W_5c45c.
Proof. vm_refl. Qed.
Lemma D_5c45c : decode_any W_5c45c = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c460 : bv 32 := 0x00068913.
Lemma F_5c460 : fetch_word AsanUbsan.M.loaded_segments (0x5c4a8 : word) = Some W_5c460.
Proof. vm_refl. Qed.
Lemma D_5c460 : decode_any W_5c460 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c464 : bv 32 := 0x00058993.
Lemma F_5c464 : fetch_word AsanUbsan.M.loaded_segments (0x5c4ac : word) = Some W_5c464.
Proof. vm_refl. Qed.
Lemma D_5c464 : decode_any W_5c464 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c468 : bv 32 := 0x00050a13.
Lemma F_5c468 : fetch_word AsanUbsan.M.loaded_segments (0x5c4b0 : word) = Some W_5c468.
Proof. vm_refl. Qed.
Lemma D_5c468 : decode_any W_5c468 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c46c : bv 32 := 0x00000513.
Lemma F_5c46c : fetch_word AsanUbsan.M.loaded_segments (0x5c4b4 : word) = Some W_5c46c.
Proof. vm_refl. Qed.
Lemma D_5c46c : decode_any W_5c46c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c470 : bv 32 := 0x00100d93.
Lemma F_5c470 : fetch_word AsanUbsan.M.loaded_segments (0x5c4b8 : word) = Some W_5c470.
Proof. vm_refl. Qed.
Lemma D_5c470 : decode_any W_5c470 = Some (OpImm ALU_ADD 27 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c474 : bv 32 := 0x020a3603.
Lemma F_5c474 : fetch_word AsanUbsan.M.loaded_segments (0x5c4bc : word) = Some W_5c474.
Proof. vm_refl. Qed.
Lemma D_5c474 : decode_any W_5c474 = Some (Load SZ8 true 12 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c478 : bv 32 := 0x030a3403.
Lemma F_5c478 : fetch_word AsanUbsan.M.loaded_segments (0x5c4c0 : word) = Some W_5c478.
Proof. vm_refl. Qed.
Lemma D_5c478 : decode_any W_5c478 = Some (Load SZ8 true 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c47c : bv 32 := 0x00769693.
Lemma F_5c47c : fetch_word AsanUbsan.M.loaded_segments (0x5c4c4 : word) = Some W_5c47c.
Proof. vm_refl. Qed.
Lemma D_5c47c : decode_any W_5c47c = Some (ShiftImm ALU_SLL 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c480 : bv 32 := 0x02091713.
Lemma F_5c480 : fetch_word AsanUbsan.M.loaded_segments (0x5c4c8 : word) = Some W_5c480.
Proof. vm_refl. Qed.
Lemma D_5c480 : decode_any W_5c480 = Some (ShiftImm ALU_SLL 14 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c484 : bv 32 := 0x00700793.
Lemma F_5c484 : fetch_word AsanUbsan.M.loaded_segments (0x5c4cc : word) = Some W_5c484.
Proof. vm_refl. Qed.
Lemma D_5c484 : decode_any W_5c484 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c488 : bv 32 := 0xfff00593.
Lemma F_5c488 : fetch_word AsanUbsan.M.loaded_segments (0x5c4d0 : word) = Some W_5c488.
Proof. vm_refl. Qed.
Lemma D_5c488 : decode_any W_5c488 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c48c : bv 32 := 0x03dd9c13.
Lemma F_5c48c : fetch_word AsanUbsan.M.loaded_segments (0x5c4d4 : word) = Some W_5c48c.
Proof. vm_refl. Qed.
Lemma D_5c48c : decode_any W_5c48c = Some (ShiftImm ALU_SLL 24 27 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c490 : bv 32 := 0x01d79793.
Lemma F_5c490 : fetch_word AsanUbsan.M.loaded_segments (0x5c4d8 : word) = Some W_5c490.
Proof. vm_refl. Qed.
Lemma D_5c490 : decode_any W_5c490 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c494 : bv 32 := 0x028d9b93.
Lemma F_5c494 : fetch_word AsanUbsan.M.loaded_segments (0x5c4dc : word) = Some W_5c494.
Proof. vm_refl. Qed.
Lemma D_5c494 : decode_any W_5c494 = Some (ShiftImm ALU_SLL 23 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c498 : bv 32 := 0x001b8813.
Lemma F_5c498 : fetch_word AsanUbsan.M.loaded_segments (0x5c4e0 : word) = Some W_5c498.
Proof. vm_refl. Qed.
Lemma D_5c498 : decode_any W_5c498 = Some (OpImm ALU_ADD 16 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c49c : bv 32 := 0x01481813.
Lemma F_5c49c : fetch_word AsanUbsan.M.loaded_segments (0x5c4e4 : word) = Some W_5c49c.
Proof. vm_refl. Qed.
Lemma D_5c49c : decode_any W_5c49c = Some (ShiftImm ALU_SLL 16 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4a0 : bv 32 := 0x00d40433.
Lemma F_5c4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c4e8 : word) = Some W_5c4a0.
Proof. vm_refl. Qed.
Lemma D_5c4a0 : decode_any W_5c4a0 = Some (Op ALU_ADD 8 8 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4a4 : bv 32 := 0x00e60633.
Lemma F_5c4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c4ec : word) = Some W_5c4a4.
Proof. vm_refl. Qed.
Lemma D_5c4a4 : decode_any W_5c4a4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4a8 : bv 32 := 0xfff80d13.
Lemma F_5c4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c4f0 : word) = Some W_5c4a8.
Proof. vm_refl. Qed.
Lemma D_5c4a8 : decode_any W_5c4a8 = Some (OpImm ALU_ADD 26 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4ac : bv 32 := 0x00f60cb3.
Lemma F_5c4ac : fetch_word AsanUbsan.M.loaded_segments (0x5c4f4 : word) = Some W_5c4ac.
Proof. vm_refl. Qed.
Lemma D_5c4ac : decode_any W_5c4ac = Some (Op ALU_ADD 25 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4b0 : bv 32 := 0x00043683.
Lemma F_5c4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c4f8 : word) = Some W_5c4b0.
Proof. vm_refl. Qed.
Lemma D_5c4b0 : decode_any W_5c4b0 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4b4 : bv 32 := 0x00840713.
Lemma F_5c4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c4fc : word) = Some W_5c4b4.
Proof. vm_refl. Qed.
Lemma D_5c4b4 : decode_any W_5c4b4 = Some (OpImm ALU_ADD 14 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4b8 : bv 32 := 0x00e13823.
Lemma F_5c4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c500 : word) = Some W_5c4b8.
Proof. vm_refl. Qed.
Lemma D_5c4b8 : decode_any W_5c4b8 = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4bc : bv 32 := 0x03cd9d93.
Lemma F_5c4bc : fetch_word AsanUbsan.M.loaded_segments (0x5c504 : word) = Some W_5c4bc.
Proof. vm_refl. Qed.
Lemma D_5c4bc : decode_any W_5c4bc = Some (ShiftImm ALU_SLL 27 27 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4c0 : bv 32 := 0x5dc00893.
Lemma F_5c4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c508 : word) = Some W_5c4c0.
Proof. vm_refl. Qed.
Lemma D_5c4c0 : decode_any W_5c4c0 = Some (OpImm ALU_ADD 17 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4c4 : bv 32 := 0x03d59493.
Lemma F_5c4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c50c : word) = Some W_5c4c4.
Proof. vm_refl. Qed.
Lemma D_5c4c4 : decode_any W_5c4c4 = Some (ShiftImm ALU_SLL 9 11 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4c8 : bv 32 := 0xfff48493.
Lemma F_5c4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c510 : word) = Some W_5c4c8.
Proof. vm_refl. Qed.
Lemma D_5c4c8 : decode_any W_5c4c8 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4cc : bv 32 := 0x01a6f733.
Lemma F_5c4cc : fetch_word AsanUbsan.M.loaded_segments (0x5c514 : word) = Some W_5c4cc.
Proof. vm_refl. Qed.
Lemma D_5c4cc : decode_any W_5c4cc = Some (Op ALU_AND 14 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4d0 : bv 32 := 0x02071663.
Lemma F_5c4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c518 : word) = Some W_5c4d0.
Proof. vm_refl. Qed.
Lemma D_5c4d0 : decode_any W_5c4d0 = Some (Branch BC_NE 14 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4d4 : bv 32 := 0x01b6e733.
Lemma F_5c4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c51c : word) = Some W_5c4d4.
Proof. vm_refl. Qed.
Lemma D_5c4d4 : decode_any W_5c4d4 = Some (Op ALU_OR 14 13 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4d8 : bv 32 := 0x00e5f7b3.
Lemma F_5c4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c520 : word) = Some W_5c4d8.
Proof. vm_refl. Qed.
Lemma D_5c4d8 : decode_any W_5c4d8 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4dc : bv 32 := 0x1604372f.
Lemma F_5c4dc : fetch_word AsanUbsan.M.loaded_segments (0x5c524 : word) = Some W_5c4dc.
Proof. vm_refl. Qed.
Lemma D_5c4dc : decode_any W_5c4dc = Some (Lr AD true true 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4e0 : bv 32 := 0x00d71663.
Lemma F_5c4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c528 : word) = Some W_5c4e0.
Proof. vm_refl. Qed.
Lemma D_5c4e0 : decode_any W_5c4e0 = Some (Branch BC_NE 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4e4 : bv 32 := 0x1af4382f.
Lemma F_5c4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c52c : word) = Some W_5c4e4.
Proof. vm_refl. Qed.
Lemma D_5c4e4 : decode_any W_5c4e4 = Some (Sc AD false true 16 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4e8 : bv 32 := 0xfe081ae3.
Lemma F_5c4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c530 : word) = Some W_5c4e8.
Proof. vm_refl. Qed.
Lemma D_5c4e8 : decode_any W_5c4e8 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c4ec : bv 32 := 0x08d70063.
Lemma F_5c4ec : fetch_word AsanUbsan.M.loaded_segments (0x5c534 : word) = Some W_5c4ec.
Proof. vm_refl. Qed.
Lemma D_5c4ec : decode_any W_5c4ec = Some (Branch BC_EQ 14 13 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c56c : bv 32 := 0x01043483.
Lemma F_5c56c : fetch_word AsanUbsan.M.loaded_segments (0x5c5b4 : word) = Some W_5c56c.
Proof. vm_refl. Qed.
Lemma D_5c56c : decode_any W_5c56c = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c570 : bv 32 := 0x01548bb3.
Lemma F_5c570 : fetch_word AsanUbsan.M.loaded_segments (0x5c5b8 : word) = Some W_5c570.
Proof. vm_refl. Qed.
Lemma D_5c570 : decode_any W_5c570 = Some (Op ALU_ADD 23 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c574 : bv 32 := 0x000a0513.
Lemma F_5c574 : fetch_word AsanUbsan.M.loaded_segments (0x5c5bc : word) = Some W_5c574.
Proof. vm_refl. Qed.
Lemma D_5c574 : decode_any W_5c574 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c578 : bv 32 := 0x00040593.
Lemma F_5c578 : fetch_word AsanUbsan.M.loaded_segments (0x5c5c0 : word) = Some W_5c578.
Proof. vm_refl. Qed.
Lemma D_5c578 : decode_any W_5c578 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c57c : bv 32 := 0x000b8693.
Lemma F_5c57c : fetch_word AsanUbsan.M.loaded_segments (0x5c5c4 : word) = Some W_5c57c.
Proof. vm_refl. Qed.
Lemma D_5c57c : decode_any W_5c57c = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c580 : bv 32 := 0x1c8000ef.
Lemma F_5c580 : fetch_word AsanUbsan.M.loaded_segments (0x5c5c8 : word) = Some W_5c580.
Proof. vm_refl. Qed.
Lemma D_5c580 : decode_any W_5c580 = Some (Jal 1 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c584 : bv 32 := 0x18050463.
Lemma F_5c584 : fetch_word AsanUbsan.M.loaded_segments (0x5c5cc : word) = Some W_5c584.
Proof. vm_refl. Qed.
Lemma D_5c584 : decode_any W_5c584 = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c588 : bv 32 := 0x020a8463.
Lemma F_5c588 : fetch_word AsanUbsan.M.loaded_segments (0x5c5d0 : word) = Some W_5c588.
Proof. vm_refl. Qed.
Lemma D_5c588 : decode_any W_5c588 = Some (Branch BC_EQ 21 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c58c : bv 32 := 0x00249493.
Lemma F_5c58c : fetch_word AsanUbsan.M.loaded_segments (0x5c5d4 : word) = Some W_5c58c.
Proof. vm_refl. Qed.
Lemma D_5c58c : decode_any W_5c58c = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c590 : bv 32 := 0x009c8cb3.
Lemma F_5c590 : fetch_word AsanUbsan.M.loaded_segments (0x5c5d8 : word) = Some W_5c590.
Proof. vm_refl. Qed.
Lemma D_5c590 : decode_any W_5c590 = Some (Op ALU_ADD 25 25 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c594 : bv 32 := 0x002a9513.
Lemma F_5c594 : fetch_word AsanUbsan.M.loaded_segments (0x5c5dc : word) = Some W_5c594.
Proof. vm_refl. Qed.
Lemma D_5c594 : decode_any W_5c594 = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c598 : bv 32 := 0x00ab0533.
Lemma F_5c598 : fetch_word AsanUbsan.M.loaded_segments (0x5c5e0 : word) = Some W_5c598.
Proof. vm_refl. Qed.
Lemma D_5c598 : decode_any W_5c598 = Some (Op ALU_ADD 10 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c59c : bv 32 := 0x000b2583.
Lemma F_5c59c : fetch_word AsanUbsan.M.loaded_segments (0x5c5e4 : word) = Some W_5c59c.
Proof. vm_refl. Qed.
Lemma D_5c59c : decode_any W_5c59c = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5a0 : bv 32 := 0x004b0b13.
Lemma F_5c5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c5e8 : word) = Some W_5c5a0.
Proof. vm_refl. Qed.
Lemma D_5c5a0 : decode_any W_5c5a0 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5a4 : bv 32 := 0x00bca023.
Lemma F_5c5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c5ec : word) = Some W_5c5a4.
Proof. vm_refl. Qed.
Lemma D_5c5a4 : decode_any W_5c5a4 = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5a8 : bv 32 := 0x004c8c93.
Lemma F_5c5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c5f0 : word) = Some W_5c5a8.
Proof. vm_refl. Qed.
Lemma D_5c5a8 : decode_any W_5c5a8 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5ac : bv 32 := 0xfeab18e3.
Lemma F_5c5ac : fetch_word AsanUbsan.M.loaded_segments (0x5c5f4 : word) = Some W_5c5ac.
Proof. vm_refl. Qed.
Lemma D_5c5ac : decode_any W_5c5ac = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5b0 : bv 32 := 0x05043503.
Lemma F_5c5b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c5f8 : word) = Some W_5c5b0.
Proof. vm_refl. Qed.
Lemma D_5c5b0 : decode_any W_5c5b0 = Some (Load SZ8 true 10 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5b4 : bv 32 := 0x01743823.
Lemma F_5c5b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c5fc : word) = Some W_5c5b4.
Proof. vm_refl. Qed.
Lemma D_5c5b4 : decode_any W_5c5b4 = Some (Store SZ8 8 23 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5b8 : bv 32 := 0x01550533.
Lemma F_5c5b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c600 : word) = Some W_5c5b8.
Proof. vm_refl. Qed.
Lemma D_5c5b8 : decode_any W_5c5b8 = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5bc : bv 32 := 0x04a43823.
Lemma F_5c5bc : fetch_word AsanUbsan.M.loaded_segments (0x5c604 : word) = Some W_5c5bc.
Proof. vm_refl. Qed.
Lemma D_5c5bc : decode_any W_5c5bc = Some (Store SZ8 8 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c0 : bv 32 := 0x000a0513.
Lemma F_5c5c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c608 : word) = Some W_5c5c0.
Proof. vm_refl. Qed.
Lemma D_5c5c0 : decode_any W_5c5c0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c4 : bv 32 := 0x00098593.
Lemma F_5c5c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c60c : word) = Some W_5c5c4.
Proof. vm_refl. Qed.
Lemma D_5c5c4 : decode_any W_5c5c4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c8 : bv 32 := 0x00090613.
Lemma F_5c5c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c610 : word) = Some W_5c5c8.
Proof. vm_refl. Qed.
Lemma D_5c5c8 : decode_any W_5c5c8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5cc : bv 32 := 0x00000693.
Lemma F_5c5cc : fetch_word AsanUbsan.M.loaded_segments (0x5c614 : word) = Some W_5c5cc.
Proof. vm_refl. Qed.
Lemma D_5c5cc : decode_any W_5c5cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5d0 : bv 32 := 0x2f8000ef.
Lemma F_5c5d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c618 : word) = Some W_5c5d0.
Proof. vm_refl. Qed.
Lemma D_5c5d0 : decode_any W_5c5d0 = Some (Jal 1 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5d4 : bv 32 := 0x00043503.
Lemma F_5c5d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c61c : word) = Some W_5c5d4.
Proof. vm_refl. Qed.
Lemma D_5c5d4 : decode_any W_5c5d4 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5d8 : bv 32 := 0xfff00813.
Lemma F_5c5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c620 : word) = Some W_5c5d8.
Proof. vm_refl. Qed.
Lemma D_5c5d8 : decode_any W_5c5d8 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5dc : bv 32 := 0x00300613.
Lemma F_5c5dc : fetch_word AsanUbsan.M.loaded_segments (0x5c624 : word) = Some W_5c5dc.
Proof. vm_refl. Qed.
Lemma D_5c5dc : decode_any W_5c5dc = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5e0 : bv 32 := 0x001005b7.
Lemma F_5c5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c628 : word) = Some W_5c5e0.
Proof. vm_refl. Qed.
Lemma D_5c5e0 : decode_any W_5c5e0 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5e4 : bv 32 := 0xfffb4697.
Lemma F_5c5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c62c : word) = Some W_5c5e4.
Proof. vm_refl. Qed.
Lemma D_5c5e4 : decode_any W_5c5e4 = Some (Auipc 13 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5e8 : bv 32 := 0x03c81713.
Lemma F_5c5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c630 : word) = Some W_5c5e8.
Proof. vm_refl. Qed.
Lemma D_5c5e8 : decode_any W_5c5e8 = Some (ShiftImm ALU_SLL 14 16 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5ec : bv 32 := 0x03d61613.
Lemma F_5c5ec : fetch_word AsanUbsan.M.loaded_segments (0x5c634 : word) = Some W_5c5ec.
Proof. vm_refl. Qed.
Lemma D_5c5ec : decode_any W_5c5ec = Some (ShiftImm ALU_SLL 12 12 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5f0 : bv 32 := 0xfff58593.
Lemma F_5c5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c638 : word) = Some W_5c5f0.
Proof. vm_refl. Qed.
Lemma D_5c5f0 : decode_any W_5c5f0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5f4 : bv 32 := 0xe2c6b683.
Lemma F_5c5f4 : fetch_word AsanUbsan.M.loaded_segments (0x5c63c : word) = Some W_5c5f4.
Proof. vm_refl. Qed.
Lemma D_5c5f4 : decode_any W_5c5f4 = Some (Load SZ8 true 13 13 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5f8 : bv 32 := 0xfff70713.
Lemma F_5c5f8 : fetch_word AsanUbsan.M.loaded_segments (0x5c640 : word) = Some W_5c5f8.
Proof. vm_refl. Qed.
Lemma D_5c5f8 : decode_any W_5c5f8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5fc : bv 32 := 0x02859793.
Lemma F_5c5fc : fetch_word AsanUbsan.M.loaded_segments (0x5c644 : word) = Some W_5c5fc.
Proof. vm_refl. Qed.
Lemma D_5c5fc : decode_any W_5c5fc = Some (ShiftImm ALU_SLL 15 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c600 : bv 32 := 0x02881813.
Lemma F_5c600 : fetch_word AsanUbsan.M.loaded_segments (0x5c648 : word) = Some W_5c600.
Proof. vm_refl. Qed.
Lemma D_5c600 : decode_any W_5c600 = Some (ShiftImm ALU_SLL 16 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c604 : bv 32 := 0x00100893.
Lemma F_5c604 : fetch_word AsanUbsan.M.loaded_segments (0x5c64c : word) = Some W_5c604.
Proof. vm_refl. Qed.
Lemma D_5c604 : decode_any W_5c604 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c608 : bv 32 := 0x03e89893.
Lemma F_5c608 : fetch_word AsanUbsan.M.loaded_segments (0x5c650 : word) = Some W_5c608.
Proof. vm_refl. Qed.
Lemma D_5c608 : decode_any W_5c608 = Some (ShiftImm ALU_SLL 17 17 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c60c : bv 32 := 0x01c0006f.
Lemma F_5c60c : fetch_word AsanUbsan.M.loaded_segments (0x5c654 : word) = Some W_5c60c.
Proof. vm_refl. Qed.
Lemma D_5c60c : decode_any W_5c60c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c610 : bv 32 := 0x1604332f.
Lemma F_5c610 : fetch_word AsanUbsan.M.loaded_segments (0x5c658 : word) = Some W_5c610.
Proof. vm_refl. Qed.
Lemma D_5c610 : decode_any W_5c610 = Some (Lr AD true true 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c614 : bv 32 := 0x00a31663.
Lemma F_5c614 : fetch_word AsanUbsan.M.loaded_segments (0x5c65c : word) = Some W_5c614.
Proof. vm_refl. Qed.
Lemma D_5c614 : decode_any W_5c614 = Some (Branch BC_NE 6 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c618 : bv 32 := 0x1a5433af.
Lemma F_5c618 : fetch_word AsanUbsan.M.loaded_segments (0x5c660 : word) = Some W_5c618.
Proof. vm_refl. Qed.
Lemma D_5c618 : decode_any W_5c618 = Some (Sc AD false true 7 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c61c : bv 32 := 0xfe039ae3.
Lemma F_5c61c : fetch_word AsanUbsan.M.loaded_segments (0x5c664 : word) = Some W_5c61c.
Proof. vm_refl. Qed.
Lemma D_5c61c : decode_any W_5c61c = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c620 : bv 32 := 0x06a30463.
Lemma F_5c620 : fetch_word AsanUbsan.M.loaded_segments (0x5c668 : word) = Some W_5c620.
Proof. vm_refl. Qed.
Lemma D_5c620 : decode_any W_5c620 = Some (Branch BC_EQ 6 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c628 : bv 32 := 0x00c575b3.
Lemma F_5c628 : fetch_word AsanUbsan.M.loaded_segments (0x5c670 : word) = Some W_5c628.
Proof. vm_refl. Qed.
Lemma D_5c628 : decode_any W_5c628 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c62c : bv 32 := 0x00e572b3.
Lemma F_5c62c : fetch_word AsanUbsan.M.loaded_segments (0x5c674 : word) = Some W_5c62c.
Proof. vm_refl. Qed.
Lemma D_5c62c : decode_any W_5c62c = Some (Op ALU_AND 5 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c630 : bv 32 := 0x02059663.
Lemma F_5c630 : fetch_word AsanUbsan.M.loaded_segments (0x5c678 : word) = Some W_5c630.
Proof. vm_refl. Qed.
Lemma D_5c630 : decode_any W_5c630 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c634 : bv 32 := 0x00f575b3.
Lemma F_5c634 : fetch_word AsanUbsan.M.loaded_segments (0x5c67c : word) = Some W_5c634.
Proof. vm_refl. Qed.
Lemma D_5c634 : decode_any W_5c634 = Some (Op ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c638 : bv 32 := 0x02058263.
Lemma F_5c638 : fetch_word AsanUbsan.M.loaded_segments (0x5c680 : word) = Some W_5c638.
Proof. vm_refl. Qed.
Lemma D_5c638 : decode_any W_5c638 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c65c : bv 32 := 0x018575b3.
Lemma F_5c65c : fetch_word AsanUbsan.M.loaded_segments (0x5c6a4 : word) = Some W_5c65c.
Proof. vm_refl. Qed.
Lemma D_5c65c : decode_any W_5c65c = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c660 : bv 32 := 0x00b035b3.
Lemma F_5c660 : fetch_word AsanUbsan.M.loaded_segments (0x5c6a8 : word) = Some W_5c660.
Proof. vm_refl. Qed.
Lemma D_5c660 : decode_any W_5c660 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c664 : bv 32 := 0x01455313.
Lemma F_5c664 : fetch_word AsanUbsan.M.loaded_segments (0x5c6ac : word) = Some W_5c664.
Proof. vm_refl. Qed.
Lemma D_5c664 : decode_any W_5c664 = Some (ShiftImm ALU_SRL 6 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c668 : bv 32 := 0xfff58593.
Lemma F_5c668 : fetch_word AsanUbsan.M.loaded_segments (0x5c6b0 : word) = Some W_5c668.
Proof. vm_refl. Qed.
Lemma D_5c668 : decode_any W_5c668 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c66c : bv 32 := 0x00b375b3.
Lemma F_5c66c : fetch_word AsanUbsan.M.loaded_segments (0x5c6b4 : word) = Some W_5c66c.
Proof. vm_refl. Qed.
Lemma D_5c66c : decode_any W_5c66c = Some (Op ALU_AND 11 6 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c670 : bv 32 := 0x02c59593.
Lemma F_5c670 : fetch_word AsanUbsan.M.loaded_segments (0x5c6b8 : word) = Some W_5c670.
Proof. vm_refl. Qed.
Lemma D_5c670 : decode_any W_5c670 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c674 : bv 32 := 0x02c5d593.
Lemma F_5c674 : fetch_word AsanUbsan.M.loaded_segments (0x5c6bc : word) = Some W_5c674.
Proof. vm_refl. Qed.
Lemma D_5c674 : decode_any W_5c674 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c678 : bv 32 := 0xf8058ce3.
Lemma F_5c678 : fetch_word AsanUbsan.M.loaded_segments (0x5c6c0 : word) = Some W_5c678.
Proof. vm_refl. Qed.
Lemma D_5c678 : decode_any W_5c678 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c688 : bv 32 := 0x0a059c63.
Lemma F_5c688 : fetch_word AsanUbsan.M.loaded_segments (0x5c6d0 : word) = Some W_5c688.
Proof. vm_refl. Qed.
Lemma D_5c688 : decode_any W_5c688 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c68c : bv 32 := 0x07813083.
Lemma F_5c68c : fetch_word AsanUbsan.M.loaded_segments (0x5c6d4 : word) = Some W_5c68c.
Proof. vm_refl. Qed.
Lemma D_5c68c : decode_any W_5c68c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c690 : bv 32 := 0x07013403.
Lemma F_5c690 : fetch_word AsanUbsan.M.loaded_segments (0x5c6d8 : word) = Some W_5c690.
Proof. vm_refl. Qed.
Lemma D_5c690 : decode_any W_5c690 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c694 : bv 32 := 0x06813483.
Lemma F_5c694 : fetch_word AsanUbsan.M.loaded_segments (0x5c6dc : word) = Some W_5c694.
Proof. vm_refl. Qed.
Lemma D_5c694 : decode_any W_5c694 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c698 : bv 32 := 0x06013903.
Lemma F_5c698 : fetch_word AsanUbsan.M.loaded_segments (0x5c6e0 : word) = Some W_5c698.
Proof. vm_refl. Qed.
Lemma D_5c698 : decode_any W_5c698 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c69c : bv 32 := 0x05813983.
Lemma F_5c69c : fetch_word AsanUbsan.M.loaded_segments (0x5c6e4 : word) = Some W_5c69c.
Proof. vm_refl. Qed.
Lemma D_5c69c : decode_any W_5c69c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6a0 : bv 32 := 0x05013a03.
Lemma F_5c6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c6e8 : word) = Some W_5c6a0.
Proof. vm_refl. Qed.
Lemma D_5c6a0 : decode_any W_5c6a0 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6a4 : bv 32 := 0x04813a83.
Lemma F_5c6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c6ec : word) = Some W_5c6a4.
Proof. vm_refl. Qed.
Lemma D_5c6a4 : decode_any W_5c6a4 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6a8 : bv 32 := 0x04013b03.
Lemma F_5c6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5c6f0 : word) = Some W_5c6a8.
Proof. vm_refl. Qed.
Lemma D_5c6a8 : decode_any W_5c6a8 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6ac : bv 32 := 0x03813b83.
Lemma F_5c6ac : fetch_word AsanUbsan.M.loaded_segments (0x5c6f4 : word) = Some W_5c6ac.
Proof. vm_refl. Qed.
Lemma D_5c6ac : decode_any W_5c6ac = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b0 : bv 32 := 0x03013c03.
Lemma F_5c6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5c6f8 : word) = Some W_5c6b0.
Proof. vm_refl. Qed.
Lemma D_5c6b0 : decode_any W_5c6b0 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b4 : bv 32 := 0x02813c83.
Lemma F_5c6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5c6fc : word) = Some W_5c6b4.
Proof. vm_refl. Qed.
Lemma D_5c6b4 : decode_any W_5c6b4 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b8 : bv 32 := 0x02013d03.
Lemma F_5c6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5c700 : word) = Some W_5c6b8.
Proof. vm_refl. Qed.
Lemma D_5c6b8 : decode_any W_5c6b8 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6bc : bv 32 := 0x01813d83.
Lemma F_5c6bc : fetch_word AsanUbsan.M.loaded_segments (0x5c704 : word) = Some W_5c6bc.
Proof. vm_refl. Qed.
Lemma D_5c6bc : decode_any W_5c6bc = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6c0 : bv 32 := 0x08010113.
Lemma F_5c6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5c708 : word) = Some W_5c6c0.
Proof. vm_refl. Qed.
Lemma D_5c6c0 : decode_any W_5c6c0 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6c4 : bv 32 := 0x00008067.
Lemma F_5c6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5c70c : word) = Some W_5c6c4.
Proof. vm_refl. Qed.
Lemma D_5c6c4 : decode_any W_5c6c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c748 : bv 32 := 0xfd010113.
Lemma F_5c748 : fetch_word AsanUbsan.M.loaded_segments (0x5c790 : word) = Some W_5c748.
Proof. vm_refl. Qed.
Lemma D_5c748 : decode_any W_5c748 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c74c : bv 32 := 0x02113423.
Lemma F_5c74c : fetch_word AsanUbsan.M.loaded_segments (0x5c794 : word) = Some W_5c74c.
Proof. vm_refl. Qed.
Lemma D_5c74c : decode_any W_5c74c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c750 : bv 32 := 0x02813023.
Lemma F_5c750 : fetch_word AsanUbsan.M.loaded_segments (0x5c798 : word) = Some W_5c750.
Proof. vm_refl. Qed.
Lemma D_5c750 : decode_any W_5c750 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c754 : bv 32 := 0x00913c23.
Lemma F_5c754 : fetch_word AsanUbsan.M.loaded_segments (0x5c79c : word) = Some W_5c754.
Proof. vm_refl. Qed.
Lemma D_5c754 : decode_any W_5c754 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c758 : bv 32 := 0x01213823.
Lemma F_5c758 : fetch_word AsanUbsan.M.loaded_segments (0x5c7a0 : word) = Some W_5c758.
Proof. vm_refl. Qed.
Lemma D_5c758 : decode_any W_5c758 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c75c : bv 32 := 0x01313423.
Lemma F_5c75c : fetch_word AsanUbsan.M.loaded_segments (0x5c7a4 : word) = Some W_5c75c.
Proof. vm_refl. Qed.
Lemma D_5c75c : decode_any W_5c75c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c760 : bv 32 := 0x0185b703.
Lemma F_5c760 : fetch_word AsanUbsan.M.loaded_segments (0x5c7a8 : word) = Some W_5c760.
Proof. vm_refl. Qed.
Lemma D_5c760 : decode_any W_5c760 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c764 : bv 32 := 0x00269793.
Lemma F_5c764 : fetch_word AsanUbsan.M.loaded_segments (0x5c7ac : word) = Some W_5c764.
Proof. vm_refl. Qed.
Lemma D_5c764 : decode_any W_5c764 = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c768 : bv 32 := 0x00100693.
Lemma F_5c768 : fetch_word AsanUbsan.M.loaded_segments (0x5c7b0 : word) = Some W_5c768.
Proof. vm_refl. Qed.
Lemma D_5c768 : decode_any W_5c768 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c76c : bv 32 := 0x0cf77063.
Lemma F_5c76c : fetch_word AsanUbsan.M.loaded_segments (0x5c7b4 : word) = Some W_5c76c.
Proof. vm_refl. Qed.
Lemma D_5c76c : decode_any W_5c76c = Some (Branch BC_GEU 14 15 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c770 : bv 32 := 0x000406b7.
Lemma F_5c770 : fetch_word AsanUbsan.M.loaded_segments (0x5c7b8 : word) = Some W_5c770.
Proof. vm_refl. Qed.
Lemma D_5c770 : decode_any W_5c770 = Some (Lui 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c774 : bv 32 := 0xfff6869b.
Lemma F_5c774 : fetch_word AsanUbsan.M.loaded_segments (0x5c7bc : word) = Some W_5c774.
Proof. vm_refl. Qed.
Lemma D_5c774 : decode_any W_5c774 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c778 : bv 32 := 0x00d786b3.
Lemma F_5c778 : fetch_word AsanUbsan.M.loaded_segments (0x5c7c0 : word) = Some W_5c778.
Proof. vm_refl. Qed.
Lemma D_5c778 : decode_any W_5c778 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c77c : bv 32 := 0xfffc0437.
Lemma F_5c77c : fetch_word AsanUbsan.M.loaded_segments (0x5c7c4 : word) = Some W_5c77c.
Proof. vm_refl. Qed.
Lemma D_5c77c : decode_any W_5c77c = Some (Lui 8 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c780 : bv 32 := 0x0086f433.
Lemma F_5c780 : fetch_word AsanUbsan.M.loaded_segments (0x5c7c8 : word) = Some W_5c780.
Proof. vm_refl. Qed.
Lemma D_5c780 : decode_any W_5c780 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c784 : bv 32 := 0x200006b7.
Lemma F_5c784 : fetch_word AsanUbsan.M.loaded_segments (0x5c7cc : word) = Some W_5c784.
Proof. vm_refl. Qed.
Lemma D_5c784 : decode_any W_5c784 = Some (Lui 13 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c788 : bv 32 := 0x0016869b.
Lemma F_5c788 : fetch_word AsanUbsan.M.loaded_segments (0x5c7d0 : word) = Some W_5c788.
Proof. vm_refl. Qed.
Lemma D_5c788 : decode_any W_5c788 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c78c : bv 32 := 0x0cd47063.
Lemma F_5c78c : fetch_word AsanUbsan.M.loaded_segments (0x5c7d4 : word) = Some W_5c78c.
Proof. vm_refl. Qed.
Lemma D_5c78c : decode_any W_5c78c = Some (Branch BC_GEU 8 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c790 : bv 32 := 0x03854683.
Lemma F_5c790 : fetch_word AsanUbsan.M.loaded_segments (0x5c7d8 : word) = Some W_5c790.
Proof. vm_refl. Qed.
Lemma D_5c790 : decode_any W_5c790 = Some (Load SZ1 false 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c794 : bv 32 := 0x00700793.
Lemma F_5c794 : fetch_word AsanUbsan.M.loaded_segments (0x5c7dc : word) = Some W_5c794.
Proof. vm_refl. Qed.
Lemma D_5c794 : decode_any W_5c794 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c798 : bv 32 := 0x01d79793.
Lemma F_5c798 : fetch_word AsanUbsan.M.loaded_segments (0x5c7e0 : word) = Some W_5c798.
Proof. vm_refl. Qed.
Lemma D_5c798 : decode_any W_5c798 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c79c : bv 32 := 0x00f60633.
Lemma F_5c79c : fetch_word AsanUbsan.M.loaded_segments (0x5c7e4 : word) = Some W_5c79c.
Proof. vm_refl. Qed.
Lemma D_5c79c : decode_any W_5c79c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7a0 : bv 32 := 0x00c704b3.
Lemma F_5c7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5c7e8 : word) = Some W_5c7a0.
Proof. vm_refl. Qed.
Lemma D_5c7a0 : decode_any W_5c7a0 = Some (Op ALU_ADD 9 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7a4 : bv 32 := 0x02068463.
Lemma F_5c7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5c7ec : word) = Some W_5c7a4.
Proof. vm_refl. Qed.
Lemma D_5c7a4 : decode_any W_5c7a4 = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7cc : bv 32 := 0x00058993.
Lemma F_5c7cc : fetch_word AsanUbsan.M.loaded_segments (0x5c814 : word) = Some W_5c7cc.
Proof. vm_refl. Qed.
Lemma D_5c7cc : decode_any W_5c7cc = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7d0 : bv 32 := 0x40e40933.
Lemma F_5c7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c818 : word) = Some W_5c7d0.
Proof. vm_refl. Qed.
Lemma D_5c7d0 : decode_any W_5c7d0 = Some (Op ALU_SUB 18 8 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7d4 : bv 32 := 0xfffbe597.
Lemma F_5c7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c81c : word) = Some W_5c7d4.
Proof. vm_refl. Qed.
Lemma D_5c7d4 : decode_any W_5c7d4 = Some (Auipc 11 1048510, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7d8 : bv 32 := 0xa1158693.
Lemma F_5c7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c820 : word) = Some W_5c7d8.
Proof. vm_refl. Qed.
Lemma D_5c7d8 : decode_any W_5c7d8 = Some (OpImm ALU_ADD 13 11 2577, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7dc : bv 32 := 0x00048593.
Lemma F_5c7dc : fetch_word AsanUbsan.M.loaded_segments (0x5c824 : word) = Some W_5c7dc.
Proof. vm_refl. Qed.
Lemma D_5c7dc : decode_any W_5c7dc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7e0 : bv 32 := 0x00090613.
Lemma F_5c7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c828 : word) = Some W_5c7e0.
Proof. vm_refl. Qed.
Lemma D_5c7e0 : decode_any W_5c7e0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7e4 : bv 32 := 0x141400ef.
Lemma F_5c7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c82c : word) = Some W_5c7e4.
Proof. vm_refl. Qed.
Lemma D_5c7e4 : decode_any W_5c7e4 = Some (Jal 1 264512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7e8 : bv 32 := 0x08050263.
Lemma F_5c7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c830 : word) = Some W_5c7e8.
Proof. vm_refl. Qed.
Lemma D_5c7e8 : decode_any W_5c7e8 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7ec : bv 32 := 0x00050713.
Lemma F_5c7ec : fetch_word AsanUbsan.M.loaded_segments (0x5c834 : word) = Some W_5c7ec.
Proof. vm_refl. Qed.
Lemma D_5c7ec : decode_any W_5c7ec = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7f0 : bv 32 := 0x08a49263.
Lemma F_5c7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c838 : word) = Some W_5c7f0.
Proof. vm_refl. Qed.
Lemma D_5c7f0 : decode_any W_5c7f0 = Some (Branch BC_NE 9 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7f4 : bv 32 := 0x0fa00613.
Lemma F_5c7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5c83c : word) = Some W_5c7f4.
Proof. vm_refl. Qed.
Lemma D_5c7f4 : decode_any W_5c7f4 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7f8 : bv 32 := 0x00048513.
Lemma F_5c7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5c840 : word) = Some W_5c7f8.
Proof. vm_refl. Qed.
Lemma D_5c7f8 : decode_any W_5c7f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c7fc : bv 32 := 0x00090593.
Lemma F_5c7fc : fetch_word AsanUbsan.M.loaded_segments (0x5c844 : word) = Some W_5c7fc.
Proof. vm_refl. Qed.
Lemma D_5c7fc : decode_any W_5c7fc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c800 : bv 32 := 0x091250ef.
Lemma F_5c800 : fetch_word AsanUbsan.M.loaded_segments (0x5c848 : word) = Some W_5c800.
Proof. vm_refl. Qed.
Lemma D_5c800 : decode_any W_5c800 = Some (Jal 1 153744, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c804 : bv 32 := 0x0052d0ef.
Lemma F_5c804 : fetch_word AsanUbsan.M.loaded_segments (0x5c84c : word) = Some W_5c804.
Proof. vm_refl. Qed.
Lemma D_5c804 : decode_any W_5c804 = Some (Jal 1 186372, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c808 : bv 32 := 0x05053583.
Lemma F_5c808 : fetch_word AsanUbsan.M.loaded_segments (0x5c850 : word) = Some W_5c808.
Proof. vm_refl. Qed.
Lemma D_5c808 : decode_any W_5c808 = Some (Load SZ8 true 11 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c80c : bv 32 := 0x04853603.
Lemma F_5c80c : fetch_word AsanUbsan.M.loaded_segments (0x5c854 : word) = Some W_5c80c.
Proof. vm_refl. Qed.
Lemma D_5c80c : decode_any W_5c80c = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c810 : bv 32 := 0x012585b3.
Lemma F_5c810 : fetch_word AsanUbsan.M.loaded_segments (0x5c858 : word) = Some W_5c810.
Proof. vm_refl. Qed.
Lemma D_5c810 : decode_any W_5c810 = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c814 : bv 32 := 0x00160613.
Lemma F_5c814 : fetch_word AsanUbsan.M.loaded_segments (0x5c85c : word) = Some W_5c814.
Proof. vm_refl. Qed.
Lemma D_5c814 : decode_any W_5c814 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c818 : bv 32 := 0x04c53423.
Lemma F_5c818 : fetch_word AsanUbsan.M.loaded_segments (0x5c860 : word) = Some W_5c818.
Proof. vm_refl. Qed.
Lemma D_5c818 : decode_any W_5c818 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c81c : bv 32 := 0x04b53823.
Lemma F_5c81c : fetch_word AsanUbsan.M.loaded_segments (0x5c864 : word) = Some W_5c81c.
Proof. vm_refl. Qed.
Lemma D_5c81c : decode_any W_5c81c = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c820 : bv 32 := 0x00098593.
Lemma F_5c820 : fetch_word AsanUbsan.M.loaded_segments (0x5c868 : word) = Some W_5c820.
Proof. vm_refl. Qed.
Lemma D_5c820 : decode_any W_5c820 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c824 : bv 32 := 0x0085bc23.
Lemma F_5c824 : fetch_word AsanUbsan.M.loaded_segments (0x5c86c : word) = Some W_5c824.
Proof. vm_refl. Qed.
Lemma D_5c824 : decode_any W_5c824 = Some (Store SZ8 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c828 : bv 32 := 0x00100693.
Lemma F_5c828 : fetch_word AsanUbsan.M.loaded_segments (0x5c870 : word) = Some W_5c828.
Proof. vm_refl. Qed.
Lemma D_5c828 : decode_any W_5c828 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c82c : bv 32 := 0x00068513.
Lemma F_5c82c : fetch_word AsanUbsan.M.loaded_segments (0x5c874 : word) = Some W_5c82c.
Proof. vm_refl. Qed.
Lemma D_5c82c : decode_any W_5c82c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c830 : bv 32 := 0x02813083.
Lemma F_5c830 : fetch_word AsanUbsan.M.loaded_segments (0x5c878 : word) = Some W_5c830.
Proof. vm_refl. Qed.
Lemma D_5c830 : decode_any W_5c830 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c834 : bv 32 := 0x02013403.
Lemma F_5c834 : fetch_word AsanUbsan.M.loaded_segments (0x5c87c : word) = Some W_5c834.
Proof. vm_refl. Qed.
Lemma D_5c834 : decode_any W_5c834 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c838 : bv 32 := 0x01813483.
Lemma F_5c838 : fetch_word AsanUbsan.M.loaded_segments (0x5c880 : word) = Some W_5c838.
Proof. vm_refl. Qed.
Lemma D_5c838 : decode_any W_5c838 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c83c : bv 32 := 0x01013903.
Lemma F_5c83c : fetch_word AsanUbsan.M.loaded_segments (0x5c884 : word) = Some W_5c83c.
Proof. vm_refl. Qed.
Lemma D_5c83c : decode_any W_5c83c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c840 : bv 32 := 0x00813983.
Lemma F_5c840 : fetch_word AsanUbsan.M.loaded_segments (0x5c888 : word) = Some W_5c840.
Proof. vm_refl. Qed.
Lemma D_5c840 : decode_any W_5c840 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c844 : bv 32 := 0x03010113.
Lemma F_5c844 : fetch_word AsanUbsan.M.loaded_segments (0x5c88c : word) = Some W_5c844.
Proof. vm_refl. Qed.
Lemma D_5c844 : decode_any W_5c844 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c848 : bv 32 := 0x00008067.
Lemma F_5c848 : fetch_word AsanUbsan.M.loaded_segments (0x5c890 : word) = Some W_5c848.
Proof. vm_refl. Qed.
Lemma D_5c848 : decode_any W_5c848 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8c8 : bv 32 := 0xfb010113.
Lemma F_5c8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5c910 : word) = Some W_5c8c8.
Proof. vm_refl. Qed.
Lemma D_5c8c8 : decode_any W_5c8c8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8cc : bv 32 := 0x04113423.
Lemma F_5c8cc : fetch_word AsanUbsan.M.loaded_segments (0x5c914 : word) = Some W_5c8cc.
Proof. vm_refl. Qed.
Lemma D_5c8cc : decode_any W_5c8cc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8d0 : bv 32 := 0x04813023.
Lemma F_5c8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5c918 : word) = Some W_5c8d0.
Proof. vm_refl. Qed.
Lemma D_5c8d0 : decode_any W_5c8d0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8d4 : bv 32 := 0x02913c23.
Lemma F_5c8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5c91c : word) = Some W_5c8d4.
Proof. vm_refl. Qed.
Lemma D_5c8d4 : decode_any W_5c8d4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8d8 : bv 32 := 0x03213823.
Lemma F_5c8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5c920 : word) = Some W_5c8d8.
Proof. vm_refl. Qed.
Lemma D_5c8d8 : decode_any W_5c8d8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8dc : bv 32 := 0x03313423.
Lemma F_5c8dc : fetch_word AsanUbsan.M.loaded_segments (0x5c924 : word) = Some W_5c8dc.
Proof. vm_refl. Qed.
Lemma D_5c8dc : decode_any W_5c8dc = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8e0 : bv 32 := 0x03413023.
Lemma F_5c8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5c928 : word) = Some W_5c8e0.
Proof. vm_refl. Qed.
Lemma D_5c8e0 : decode_any W_5c8e0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8e4 : bv 32 := 0x01513c23.
Lemma F_5c8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5c92c : word) = Some W_5c8e4.
Proof. vm_refl. Qed.
Lemma D_5c8e4 : decode_any W_5c8e4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8e8 : bv 32 := 0x01613823.
Lemma F_5c8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5c930 : word) = Some W_5c8e8.
Proof. vm_refl. Qed.
Lemma D_5c8e8 : decode_any W_5c8e8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8ec : bv 32 := 0x01713423.
Lemma F_5c8ec : fetch_word AsanUbsan.M.loaded_segments (0x5c934 : word) = Some W_5c8ec.
Proof. vm_refl. Qed.
Lemma D_5c8ec : decode_any W_5c8ec = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8f0 : bv 32 := 0x00068a93.
Lemma F_5c8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5c938 : word) = Some W_5c8f0.
Proof. vm_refl. Qed.
Lemma D_5c8f0 : decode_any W_5c8f0 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8f4 : bv 32 := 0x00060493.
Lemma F_5c8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5c93c : word) = Some W_5c8f4.
Proof. vm_refl. Qed.
Lemma D_5c8f4 : decode_any W_5c8f4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8f8 : bv 32 := 0x00058413.
Lemma F_5c8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5c940 : word) = Some W_5c8f8.
Proof. vm_refl. Qed.
Lemma D_5c8f8 : decode_any W_5c8f8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c8fc : bv 32 := 0x00050993.
Lemma F_5c8fc : fetch_word AsanUbsan.M.loaded_segments (0x5c944 : word) = Some W_5c8fc.
Proof. vm_refl. Qed.
Lemma D_5c8fc : decode_any W_5c8fc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c900 : bv 32 := 0x03053b03.
Lemma F_5c900 : fetch_word AsanUbsan.M.loaded_segments (0x5c948 : word) = Some W_5c900.
Proof. vm_refl. Qed.
Lemma D_5c900 : decode_any W_5c900 = Some (Load SZ8 true 22 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c904 : bv 32 := 0x01f00513.
Lemma F_5c904 : fetch_word AsanUbsan.M.loaded_segments (0x5c94c : word) = Some W_5c904.
Proof. vm_refl. Qed.
Lemma D_5c904 : decode_any W_5c904 = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c908 : bv 32 := 0x00761593.
Lemma F_5c908 : fetch_word AsanUbsan.M.loaded_segments (0x5c950 : word) = Some W_5c908.
Proof. vm_refl. Qed.
Lemma D_5c908 : decode_any W_5c908 = Some (ShiftImm ALU_SLL 11 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c90c : bv 32 := 0x18a60863.
Lemma F_5c90c : fetch_word AsanUbsan.M.loaded_segments (0x5c954 : word) = Some W_5c90c.
Proof. vm_refl. Qed.
Lemma D_5c90c : decode_any W_5c90c = Some (Branch BC_EQ 12 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c910 : bv 32 := 0x01000513.
Lemma F_5c910 : fetch_word AsanUbsan.M.loaded_segments (0x5c958 : word) = Some W_5c910.
Proof. vm_refl. Qed.
Lemma D_5c910 : decode_any W_5c910 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c914 : bv 32 := 0x00956663.
Lemma F_5c914 : fetch_word AsanUbsan.M.loaded_segments (0x5c95c : word) = Some W_5c914.
Proof. vm_refl. Qed.
Lemma D_5c914 : decode_any W_5c914 = Some (Branch BC_LTU 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c918 : bv 32 := 0x00549913.
Lemma F_5c918 : fetch_word AsanUbsan.M.loaded_segments (0x5c960 : word) = Some W_5c918.
Proof. vm_refl. Qed.
Lemma D_5c918 : decode_any W_5c918 = Some (ShiftImm ALU_SLL 18 9 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c91c : bv 32 := 0x0280006f.
Lemma F_5c91c : fetch_word AsanUbsan.M.loaded_segments (0x5c964 : word) = Some W_5c91c.
Proof. vm_refl. Qed.
Lemma D_5c91c : decode_any W_5c91c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c920 : bv 32 := 0xff048513.
Lemma F_5c920 : fetch_word AsanUbsan.M.loaded_segments (0x5c968 : word) = Some W_5c920.
Proof. vm_refl. Qed.
Lemma D_5c920 : decode_any W_5c920 = Some (OpImm ALU_ADD 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c924 : bv 32 := 0x20000613.
Lemma F_5c924 : fetch_word AsanUbsan.M.loaded_segments (0x5c96c : word) = Some W_5c924.
Proof. vm_refl. Qed.
Lemma D_5c924 : decode_any W_5c924 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c928 : bv 32 := 0x03f49693.
Lemma F_5c928 : fetch_word AsanUbsan.M.loaded_segments (0x5c970 : word) = Some W_5c928.
Proof. vm_refl. Qed.
Lemma D_5c928 : decode_any W_5c928 = Some (ShiftImm ALU_SLL 13 9 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c92c : bv 32 := 0x00155513.
Lemma F_5c92c : fetch_word AsanUbsan.M.loaded_segments (0x5c974 : word) = Some W_5c92c.
Proof. vm_refl. Qed.
Lemma D_5c92c : decode_any W_5c92c = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c930 : bv 32 := 0x00a61933.
Lemma F_5c930 : fetch_word AsanUbsan.M.loaded_segments (0x5c978 : word) = Some W_5c930.
Proof. vm_refl. Qed.
Lemma D_5c930 : decode_any W_5c930 = Some (Op ALU_SLL 18 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c934 : bv 32 := 0x00195513.
Lemma F_5c934 : fetch_word AsanUbsan.M.loaded_segments (0x5c97c : word) = Some W_5c934.
Proof. vm_refl. Qed.
Lemma D_5c934 : decode_any W_5c934 = Some (ShiftImm ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c938 : bv 32 := 0x43f6d693.
Lemma F_5c938 : fetch_word AsanUbsan.M.loaded_segments (0x5c980 : word) = Some W_5c938.
Proof. vm_refl. Qed.
Lemma D_5c938 : decode_any W_5c938 = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c93c : bv 32 := 0x00a6f533.
Lemma F_5c93c : fetch_word AsanUbsan.M.loaded_segments (0x5c984 : word) = Some W_5c93c.
Proof. vm_refl. Qed.
Lemma D_5c93c : decode_any W_5c93c = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c940 : bv 32 := 0x01250933.
Lemma F_5c940 : fetch_word AsanUbsan.M.loaded_segments (0x5c988 : word) = Some W_5c940.
Proof. vm_refl. Qed.
Lemma D_5c940 : decode_any W_5c940 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c944 : bv 32 := 0x000f8517.
Lemma F_5c944 : fetch_word AsanUbsan.M.loaded_segments (0x5c98c : word) = Some W_5c944.
Proof. vm_refl. Qed.
Lemma D_5c944 : decode_any W_5c944 = Some (Auipc 10 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c948 : bv 32 := 0xb5453a03.
Lemma F_5c948 : fetch_word AsanUbsan.M.loaded_segments (0x5c990 : word) = Some W_5c948.
Proof. vm_refl. Qed.
Lemma D_5c948 : decode_any W_5c948 = Some (Load SZ8 true 20 10 2900, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c94c : bv 32 := 0x000a3503.
Lemma F_5c94c : fetch_word AsanUbsan.M.loaded_segments (0x5c994 : word) = Some W_5c94c.
Proof. vm_refl. Qed.
Lemma D_5c94c : decode_any W_5c94c = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c950 : bv 32 := 0x00bb0b33.
Lemma F_5c950 : fetch_word AsanUbsan.M.loaded_segments (0x5c998 : word) = Some W_5c950.
Proof. vm_refl. Qed.
Lemma D_5c950 : decode_any W_5c950 = Some (Op ALU_ADD 22 22 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c954 : bv 32 := 0x00050a63.
Lemma F_5c954 : fetch_word AsanUbsan.M.loaded_segments (0x5c99c : word) = Some W_5c954.
Proof. vm_refl. Qed.
Lemma D_5c954 : decode_any W_5c954 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c958 : bv 32 := 0x010b3a03.
Lemma F_5c958 : fetch_word AsanUbsan.M.loaded_segments (0x5c9a0 : word) = Some W_5c958.
Proof. vm_refl. Qed.
Lemma D_5c958 : decode_any W_5c958 = Some (Load SZ8 true 20 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c95c : bv 32 := 0x032a05b3.
Lemma F_5c95c : fetch_word AsanUbsan.M.loaded_segments (0x5c9a4 : word) = Some W_5c95c.
Proof. vm_refl. Qed.
Lemma D_5c95c : decode_any W_5c95c = Some (Mul M_MUL 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c960 : bv 32 := 0x00a5fe63.
Lemma F_5c960 : fetch_word AsanUbsan.M.loaded_segments (0x5c9a8 : word) = Some W_5c960.
Proof. vm_refl. Qed.
Lemma D_5c960 : decode_any W_5c960 = Some (Branch BC_GEU 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c964 : bv 32 := 0x10c0006f.
Lemma F_5c964 : fetch_word AsanUbsan.M.loaded_segments (0x5c9ac : word) = Some W_5c964.
Proof. vm_refl. Qed.
Lemma D_5c964 : decode_any W_5c964 = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c97c : bv 32 := 0x050b3583.
Lemma F_5c97c : fetch_word AsanUbsan.M.loaded_segments (0x5c9c4 : word) = Some W_5c97c.
Proof. vm_refl. Qed.
Lemma D_5c97c : decode_any W_5c97c = Some (Load SZ8 true 11 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c980 : bv 32 := 0x058b3603.
Lemma F_5c980 : fetch_word AsanUbsan.M.loaded_segments (0x5c9c8 : word) = Some W_5c980.
Proof. vm_refl. Qed.
Lemma D_5c980 : decode_any W_5c980 = Some (Load SZ8 true 12 22 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c984 : bv 32 := 0x40c585b3.
Lemma F_5c984 : fetch_word AsanUbsan.M.loaded_segments (0x5c9cc : word) = Some W_5c984.
Proof. vm_refl. Qed.
Lemma D_5c984 : decode_any W_5c984 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c988 : bv 32 := 0x032585b3.
Lemma F_5c988 : fetch_word AsanUbsan.M.loaded_segments (0x5c9d0 : word) = Some W_5c988.
Proof. vm_refl. Qed.
Lemma D_5c988 : decode_any W_5c988 = Some (Mul M_MUL 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c98c : bv 32 := 0x0ea5e263.
Lemma F_5c98c : fetch_word AsanUbsan.M.loaded_segments (0x5c9d4 : word) = Some W_5c98c.
Proof. vm_refl. Qed.
Lemma D_5c98c : decode_any W_5c98c = Some (Branch BC_LTU 11 10 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c990 : bv 32 := 0x020a9a63.
Lemma F_5c990 : fetch_word AsanUbsan.M.loaded_segments (0x5c9d8 : word) = Some W_5c990.
Proof. vm_refl. Qed.
Lemma D_5c990 : decode_any W_5c990 = Some (Branch BC_NE 21 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c994 : bv 32 := 0x0289a583.
Lemma F_5c994 : fetch_word AsanUbsan.M.loaded_segments (0x5c9dc : word) = Some W_5c994.
Proof. vm_refl. Qed.
Lemma D_5c994 : decode_any W_5c994 = Some (Load SZ4 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c998 : bv 32 := 0x0c05cc63.
Lemma F_5c998 : fetch_word AsanUbsan.M.loaded_segments (0x5c9e0 : word) = Some W_5c998.
Proof. vm_refl. Qed.
Lemma D_5c998 : decode_any W_5c998 = Some (Branch BC_LT 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca70 : bv 32 := 0x04813083.
Lemma F_5ca70 : fetch_word AsanUbsan.M.loaded_segments (0x5cab8 : word) = Some W_5ca70.
Proof. vm_refl. Qed.
Lemma D_5ca70 : decode_any W_5ca70 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca74 : bv 32 := 0x04013403.
Lemma F_5ca74 : fetch_word AsanUbsan.M.loaded_segments (0x5cabc : word) = Some W_5ca74.
Proof. vm_refl. Qed.
Lemma D_5ca74 : decode_any W_5ca74 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca78 : bv 32 := 0x03813483.
Lemma F_5ca78 : fetch_word AsanUbsan.M.loaded_segments (0x5cac0 : word) = Some W_5ca78.
Proof. vm_refl. Qed.
Lemma D_5ca78 : decode_any W_5ca78 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca7c : bv 32 := 0x03013903.
Lemma F_5ca7c : fetch_word AsanUbsan.M.loaded_segments (0x5cac4 : word) = Some W_5ca7c.
Proof. vm_refl. Qed.
Lemma D_5ca7c : decode_any W_5ca7c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca80 : bv 32 := 0x02813983.
Lemma F_5ca80 : fetch_word AsanUbsan.M.loaded_segments (0x5cac8 : word) = Some W_5ca80.
Proof. vm_refl. Qed.
Lemma D_5ca80 : decode_any W_5ca80 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca84 : bv 32 := 0x02013a03.
Lemma F_5ca84 : fetch_word AsanUbsan.M.loaded_segments (0x5cacc : word) = Some W_5ca84.
Proof. vm_refl. Qed.
Lemma D_5ca84 : decode_any W_5ca84 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca88 : bv 32 := 0x01813a83.
Lemma F_5ca88 : fetch_word AsanUbsan.M.loaded_segments (0x5cad0 : word) = Some W_5ca88.
Proof. vm_refl. Qed.
Lemma D_5ca88 : decode_any W_5ca88 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca8c : bv 32 := 0x01013b03.
Lemma F_5ca8c : fetch_word AsanUbsan.M.loaded_segments (0x5cad4 : word) = Some W_5ca8c.
Proof. vm_refl. Qed.
Lemma D_5ca8c : decode_any W_5ca8c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca90 : bv 32 := 0x00813b83.
Lemma F_5ca90 : fetch_word AsanUbsan.M.loaded_segments (0x5cad8 : word) = Some W_5ca90.
Proof. vm_refl. Qed.
Lemma D_5ca90 : decode_any W_5ca90 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca94 : bv 32 := 0x05010113.
Lemma F_5ca94 : fetch_word AsanUbsan.M.loaded_segments (0x5cadc : word) = Some W_5ca94.
Proof. vm_refl. Qed.
Lemma D_5ca94 : decode_any W_5ca94 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca98 : bv 32 := 0x00008067.
Lemma F_5ca98 : fetch_word AsanUbsan.M.loaded_segments (0x5cae0 : word) = Some W_5ca98.
Proof. vm_refl. Qed.
Lemma D_5ca98 : decode_any W_5ca98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

