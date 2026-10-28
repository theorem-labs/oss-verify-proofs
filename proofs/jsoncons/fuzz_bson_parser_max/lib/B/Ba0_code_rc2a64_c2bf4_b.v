(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_11dc1c : bv 32 := 0x0284b503.
Lemma F_11dc1c : fetch_word AsanUbsan.M.loaded_segments (0x12020c : word) = Some W_11dc1c.
Proof. vm_refl. Qed.
Lemma D_11dc1c : decode_any W_11dc1c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc20 : bv 32 := 0x0384b603.
Lemma F_11dc20 : fetch_word AsanUbsan.M.loaded_segments (0x120210 : word) = Some W_11dc20.
Proof. vm_refl. Qed.
Lemma D_11dc20 : decode_any W_11dc20 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc24 : bv 32 := 0x40c50b33.
Lemma F_11dc24 : fetch_word AsanUbsan.M.loaded_segments (0x120214 : word) = Some W_11dc24.
Proof. vm_refl. Qed.
Lemma D_11dc24 : decode_any W_11dc24 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc28 : bv 32 := 0x00c546b3.
Lemma F_11dc28 : fetch_word AsanUbsan.M.loaded_segments (0x120218 : word) = Some W_11dc28.
Proof. vm_refl. Qed.
Lemma D_11dc28 : decode_any W_11dc28 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc2c : bv 32 := 0x00c13423.
Lemma F_11dc2c : fetch_word AsanUbsan.M.loaded_segments (0x12021c : word) = Some W_11dc2c.
Proof. vm_refl. Qed.
Lemma D_11dc2c : decode_any W_11dc2c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc30 : bv 32 := 0x01613823.
Lemma F_11dc30 : fetch_word AsanUbsan.M.loaded_segments (0x120220 : word) = Some W_11dc30.
Proof. vm_refl. Qed.
Lemma D_11dc30 : decode_any W_11dc30 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc34 : bv 32 := 0x00b13c23.
Lemma F_11dc34 : fetch_word AsanUbsan.M.loaded_segments (0x120224 : word) = Some W_11dc34.
Proof. vm_refl. Qed.
Lemma D_11dc34 : decode_any W_11dc34 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc38 : bv 32 := 0x02813023.
Lemma F_11dc38 : fetch_word AsanUbsan.M.loaded_segments (0x120228 : word) = Some W_11dc38.
Proof. vm_refl. Qed.
Lemma D_11dc38 : decode_any W_11dc38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc3c : bv 32 := 0x008b0b33.
Lemma F_11dc3c : fetch_word AsanUbsan.M.loaded_segments (0x12022c : word) = Some W_11dc3c.
Proof. vm_refl. Qed.
Lemma D_11dc3c : decode_any W_11dc3c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc40 : bv 32 := 0x00d03933.
Lemma F_11dc40 : fetch_word AsanUbsan.M.loaded_segments (0x120230 : word) = Some W_11dc40.
Proof. vm_refl. Qed.
Lemma D_11dc40 : decode_any W_11dc40 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc44 : bv 32 := 0x00c50663.
Lemma F_11dc44 : fetch_word AsanUbsan.M.loaded_segments (0x120234 : word) = Some W_11dc44.
Proof. vm_refl. Qed.
Lemma D_11dc44 : decode_any W_11dc44 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc48 : bv 32 := 0x00810993.
Lemma F_11dc48 : fetch_word AsanUbsan.M.loaded_segments (0x120238 : word) = Some W_11dc48.
Proof. vm_refl. Qed.
Lemma D_11dc48 : decode_any W_11dc48 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc4c : bv 32 := 0x0080006f.
Lemma F_11dc4c : fetch_word AsanUbsan.M.loaded_segments (0x12023c : word) = Some W_11dc4c.
Proof. vm_refl. Qed.
Lemma D_11dc4c : decode_any W_11dc4c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc50 : bv 32 := 0x01810993.
Lemma F_11dc50 : fetch_word AsanUbsan.M.loaded_segments (0x120240 : word) = Some W_11dc50.
Proof. vm_refl. Qed.
Lemma D_11dc50 : decode_any W_11dc50 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc54 : bv 32 := 0x0784a503.
Lemma F_11dc54 : fetch_word AsanUbsan.M.loaded_segments (0x120244 : word) = Some W_11dc54.
Proof. vm_refl. Qed.
Lemma D_11dc54 : decode_any W_11dc54 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc58 : bv 32 := 0x00190913.
Lemma F_11dc58 : fetch_word AsanUbsan.M.loaded_segments (0x120248 : word) = Some W_11dc58.
Proof. vm_refl. Qed.
Lemma D_11dc58 : decode_any W_11dc58 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc5c : bv 32 := 0x04200893.
Lemma F_11dc5c : fetch_word AsanUbsan.M.loaded_segments (0x12024c : word) = Some W_11dc5c.
Proof. vm_refl. Qed.
Lemma D_11dc5c : decode_any W_11dc5c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc60 : bv 32 := 0x00098593.
Lemma F_11dc60 : fetch_word AsanUbsan.M.loaded_segments (0x120250 : word) = Some W_11dc60.
Proof. vm_refl. Qed.
Lemma D_11dc60 : decode_any W_11dc60 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc64 : bv 32 := 0x00090613.
Lemma F_11dc64 : fetch_word AsanUbsan.M.loaded_segments (0x120254 : word) = Some W_11dc64.
Proof. vm_refl. Qed.
Lemma D_11dc64 : decode_any W_11dc64 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc6c : bv 32 := 0x975f80ef.
Lemma F_11dc6c : fetch_word AsanUbsan.M.loaded_segments (0x12025c : word) = Some W_11dc6c.
Proof. vm_refl. Qed.
Lemma D_11dc6c : decode_any W_11dc6c = Some (Jal 1 2066804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dc70 : bv 32 := 0x09651863.
Lemma F_11dc70 : fetch_word AsanUbsan.M.loaded_segments (0x120260 : word) = Some W_11dc70.
Proof. vm_refl. Qed.
Lemma D_11dc70 : decode_any W_11dc70 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcc4 : bv 32 := 0x00800713.
Lemma F_11dcc4 : fetch_word AsanUbsan.M.loaded_segments (0x1202b4 : word) = Some W_11dcc4.
Proof. vm_refl. Qed.
Lemma D_11dcc4 : decode_any W_11dcc4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcc8 : bv 32 := 0x000a0593.
Lemma F_11dcc8 : fetch_word AsanUbsan.M.loaded_segments (0x1202b8 : word) = Some W_11dcc8.
Proof. vm_refl. Qed.
Lemma D_11dcc8 : decode_any W_11dcc8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dccc : bv 32 := 0x00e98733.
Lemma F_11dccc : fetch_word AsanUbsan.M.loaded_segments (0x1202bc : word) = Some W_11dccc.
Proof. vm_refl. Qed.
Lemma D_11dccc : decode_any W_11dccc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcd0 : bv 32 := 0x00073783.
Lemma F_11dcd0 : fetch_word AsanUbsan.M.loaded_segments (0x1202c0 : word) = Some W_11dcd0.
Proof. vm_refl. Qed.
Lemma D_11dcd0 : decode_any W_11dcd0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcd4 : bv 32 := 0x40ab0b33.
Lemma F_11dcd4 : fetch_word AsanUbsan.M.loaded_segments (0x1202c4 : word) = Some W_11dcd4.
Proof. vm_refl. Qed.
Lemma D_11dcd4 : decode_any W_11dcd4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcd8 : bv 32 := 0x0784a503.
Lemma F_11dcd8 : fetch_word AsanUbsan.M.loaded_segments (0x1202c8 : word) = Some W_11dcd8.
Proof. vm_refl. Qed.
Lemma D_11dcd8 : decode_any W_11dcd8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcdc : bv 32 := 0x40c9093b.
Lemma F_11dcdc : fetch_word AsanUbsan.M.loaded_segments (0x1202cc : word) = Some W_11dcdc.
Proof. vm_refl. Qed.
Lemma D_11dcdc : decode_any W_11dcdc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dce0 : bv 32 := 0x40d787b3.
Lemma F_11dce0 : fetch_word AsanUbsan.M.loaded_segments (0x1202d0 : word) = Some W_11dce0.
Proof. vm_refl. Qed.
Lemma D_11dce0 : decode_any W_11dce0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dce4 : bv 32 := 0x00f73023.
Lemma F_11dce4 : fetch_word AsanUbsan.M.loaded_segments (0x1202d4 : word) = Some W_11dce4.
Proof. vm_refl. Qed.
Lemma D_11dce4 : decode_any W_11dce4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dce8 : bv 32 := 0x04200893.
Lemma F_11dce8 : fetch_word AsanUbsan.M.loaded_segments (0x1202d8 : word) = Some W_11dce8.
Proof. vm_refl. Qed.
Lemma D_11dce8 : decode_any W_11dce8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcec : bv 32 := 0x00090613.
Lemma F_11dcec : fetch_word AsanUbsan.M.loaded_segments (0x1202dc : word) = Some W_11dcec.
Proof. vm_refl. Qed.
Lemma D_11dcec : decode_any W_11dcec = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcf4 : bv 32 := 0x8edf80ef.
Lemma F_11dcf4 : fetch_word AsanUbsan.M.loaded_segments (0x1202e4 : word) = Some W_11dcf4.
Proof. vm_refl. Qed.
Lemma D_11dcf4 : decode_any W_11dcf4 = Some (Jal 1 2066668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcf8 : bv 32 := 0x000a0993.
Lemma F_11dcf8 : fetch_word AsanUbsan.M.loaded_segments (0x1202e8 : word) = Some W_11dcf8.
Proof. vm_refl. Qed.
Lemma D_11dcf8 : decode_any W_11dcf8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dcfc : bv 32 := 0xf7650ce3.
Lemma F_11dcfc : fetch_word AsanUbsan.M.loaded_segments (0x1202ec : word) = Some W_11dcfc.
Proof. vm_refl. Qed.
Lemma D_11dcfc : decode_any W_11dcfc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd00 : bv 32 := 0x02054c63.
Lemma F_11dd00 : fetch_word AsanUbsan.M.loaded_segments (0x1202f0 : word) = Some W_11dd00.
Proof. vm_refl. Qed.
Lemma D_11dd00 : decode_any W_11dd00 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd04 : bv 32 := 0x0089b583.
Lemma F_11dd04 : fetch_word AsanUbsan.M.loaded_segments (0x1202f4 : word) = Some W_11dd04.
Proof. vm_refl. Qed.
Lemma D_11dd04 : decode_any W_11dd04 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd08 : bv 32 := 0x00a5b633.
Lemma F_11dd08 : fetch_word AsanUbsan.M.loaded_segments (0x1202f8 : word) = Some W_11dd08.
Proof. vm_refl. Qed.
Lemma D_11dd08 : decode_any W_11dd08 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd0c : bv 32 := 0x00461a13.
Lemma F_11dd0c : fetch_word AsanUbsan.M.loaded_segments (0x1202fc : word) = Some W_11dd0c.
Proof. vm_refl. Qed.
Lemma D_11dd0c : decode_any W_11dd0c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd10 : bv 32 := 0x01498a33.
Lemma F_11dd10 : fetch_word AsanUbsan.M.loaded_segments (0x120300 : word) = Some W_11dd10.
Proof. vm_refl. Qed.
Lemma D_11dd10 : decode_any W_11dd10 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd14 : bv 32 := 0x000a3703.
Lemma F_11dd14 : fetch_word AsanUbsan.M.loaded_segments (0x120304 : word) = Some W_11dd14.
Proof. vm_refl. Qed.
Lemma D_11dd14 : decode_any W_11dd14 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd18 : bv 32 := 0x40c006b3.
Lemma F_11dd18 : fetch_word AsanUbsan.M.loaded_segments (0x120308 : word) = Some W_11dd18.
Proof. vm_refl. Qed.
Lemma D_11dd18 : decode_any W_11dd18 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd1c : bv 32 := 0x00b6f6b3.
Lemma F_11dd1c : fetch_word AsanUbsan.M.loaded_segments (0x12030c : word) = Some W_11dd1c.
Proof. vm_refl. Qed.
Lemma D_11dd1c : decode_any W_11dd1c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd20 : bv 32 := 0x40d506b3.
Lemma F_11dd20 : fetch_word AsanUbsan.M.loaded_segments (0x120310 : word) = Some W_11dd20.
Proof. vm_refl. Qed.
Lemma D_11dd20 : decode_any W_11dd20 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd24 : bv 32 := 0x00d70733.
Lemma F_11dd24 : fetch_word AsanUbsan.M.loaded_segments (0x120314 : word) = Some W_11dd24.
Proof. vm_refl. Qed.
Lemma D_11dd24 : decode_any W_11dd24 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd28 : bv 32 := 0x00ea3023.
Lemma F_11dd28 : fetch_word AsanUbsan.M.loaded_segments (0x120318 : word) = Some W_11dd28.
Proof. vm_refl. Qed.
Lemma D_11dd28 : decode_any W_11dd28 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd2c : bv 32 := 0xf8a5fce3.
Lemma F_11dd2c : fetch_word AsanUbsan.M.loaded_segments (0x12031c : word) = Some W_11dd2c.
Proof. vm_refl. Qed.
Lemma D_11dd2c : decode_any W_11dd2c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd30 : bv 32 := 0x01800713.
Lemma F_11dd30 : fetch_word AsanUbsan.M.loaded_segments (0x120320 : word) = Some W_11dd30.
Proof. vm_refl. Qed.
Lemma D_11dd30 : decode_any W_11dd30 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11dd34 : bv 32 := 0xf95ff06f.
Lemma F_11dd34 : fetch_word AsanUbsan.M.loaded_segments (0x120324 : word) = Some W_11dd34.
Proof. vm_refl. Qed.
Lemma D_11dd34 : decode_any W_11dd34 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
