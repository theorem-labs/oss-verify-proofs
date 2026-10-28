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
Definition W_5dcc4 : bv 32 := 0xfe010113.
Lemma F_5dcc4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0dc : word) = Some W_5dcc4.
Proof. vm_refl. Qed.
Lemma D_5dcc4 : decode_any W_5dcc4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcc8 : bv 32 := 0x00113c23.
Lemma F_5dcc8 : fetch_word AsanUbsan.M.loaded_segments (0x5e0e0 : word) = Some W_5dcc8.
Proof. vm_refl. Qed.
Lemma D_5dcc8 : decode_any W_5dcc8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dccc : bv 32 := 0x00813823.
Lemma F_5dccc : fetch_word AsanUbsan.M.loaded_segments (0x5e0e4 : word) = Some W_5dccc.
Proof. vm_refl. Qed.
Lemma D_5dccc : decode_any W_5dccc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcd0 : bv 32 := 0x00913423.
Lemma F_5dcd0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0e8 : word) = Some W_5dcd0.
Proof. vm_refl. Qed.
Lemma D_5dcd0 : decode_any W_5dcd0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcd4 : bv 32 := 0x01213023.
Lemma F_5dcd4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0ec : word) = Some W_5dcd4.
Proof. vm_refl. Qed.
Lemma D_5dcd4 : decode_any W_5dcd4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcd8 : bv 32 := 0x02010413.
Lemma F_5dcd8 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f0 : word) = Some W_5dcd8.
Proof. vm_refl. Qed.
Lemma D_5dcd8 : decode_any W_5dcd8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcdc : bv 32 := 0x000da517.
Lemma F_5dcdc : fetch_word AsanUbsan.M.loaded_segments (0x5e0f4 : word) = Some W_5dcdc.
Proof. vm_refl. Qed.
Lemma D_5dcdc : decode_any W_5dcdc = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dce0 : bv 32 := 0x1c450513.
Lemma F_5dce0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f8 : word) = Some W_5dce0.
Proof. vm_refl. Qed.
Lemma D_5dce0 : decode_any W_5dce0 = Some (OpImm ALU_ADD 10 10 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dce4 : bv 32 := 0x2f4050ef.
Lemma F_5dce4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0fc : word) = Some W_5dce4.
Proof. vm_refl. Qed.
Lemma D_5dce4 : decode_any W_5dce4 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dce8 : bv 32 := 0x00053483.
Lemma F_5dce8 : fetch_word AsanUbsan.M.loaded_segments (0x5e100 : word) = Some W_5dce8.
Proof. vm_refl. Qed.
Lemma D_5dce8 : decode_any W_5dce8 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcec : bv 32 := 0x08048863.
Lemma F_5dcec : fetch_word AsanUbsan.M.loaded_segments (0x5e104 : word) = Some W_5dcec.
Proof. vm_refl. Qed.
Lemma D_5dcec : decode_any W_5dcec = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf0 : bv 32 := 0x0604c503.
Lemma F_5dcf0 : fetch_word AsanUbsan.M.loaded_segments (0x5e108 : word) = Some W_5dcf0.
Proof. vm_refl. Qed.
Lemma D_5dcf0 : decode_any W_5dcf0 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf4 : bv 32 := 0x0584b903.
Lemma F_5dcf4 : fetch_word AsanUbsan.M.loaded_segments (0x5e10c : word) = Some W_5dcf4.
Proof. vm_refl. Qed.
Lemma D_5dcf4 : decode_any W_5dcf4 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf8 : bv 32 := 0x00050863.
Lemma F_5dcf8 : fetch_word AsanUbsan.M.loaded_segments (0x5e110 : word) = Some W_5dcf8.
Proof. vm_refl. Qed.
Lemma D_5dcf8 : decode_any W_5dcf8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcfc : bv 32 := 0x00048513.
Lemma F_5dcfc : fetch_word AsanUbsan.M.loaded_segments (0x5e114 : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd00 : bv 32 := 0x00040593.
Lemma F_5dd00 : fetch_word AsanUbsan.M.loaded_segments (0x5e118 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd04 : bv 32 := 0xec4ff0ef.
Lemma F_5dd04 : fetch_word AsanUbsan.M.loaded_segments (0x5e11c : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (Jal 1 2094788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd08 : bv 32 := 0xff590593.
Lemma F_5dd08 : fetch_word AsanUbsan.M.loaded_segments (0x5e120 : word) = Some W_5dd08.
Proof. vm_refl. Qed.
Lemma D_5dd08 : decode_any W_5dd08 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd0c : bv 32 := 0x00100513.
Lemma F_5dd0c : fetch_word AsanUbsan.M.loaded_segments (0x5e124 : word) = Some W_5dd0c.
Proof. vm_refl. Qed.
Lemma D_5dd0c : decode_any W_5dd0c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd10 : bv 32 := 0x00b51533.
Lemma F_5dd10 : fetch_word AsanUbsan.M.loaded_segments (0x5e128 : word) = Some W_5dd10.
Proof. vm_refl. Qed.
Lemma D_5dd10 : decode_any W_5dd10 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd14 : bv 32 := 0x0005061b.
Lemma F_5dd14 : fetch_word AsanUbsan.M.loaded_segments (0x5e12c : word) = Some W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : decode_any W_5dd14 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd18 : bv 32 := 0x08c05263.
Lemma F_5dd18 : fetch_word AsanUbsan.M.loaded_segments (0x5e130 : word) = Some W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : decode_any W_5dd18 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd1c : bv 32 := 0x000016b7.
Lemma F_5dd1c : fetch_word AsanUbsan.M.loaded_segments (0x5e134 : word) = Some W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : decode_any W_5dd1c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd20 : bv 32 := 0xff190613.
Lemma F_5dd20 : fetch_word AsanUbsan.M.loaded_segments (0x5e138 : word) = Some W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : decode_any W_5dd20 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd24 : bv 32 := 0x3e000713.
Lemma F_5dd24 : fetch_word AsanUbsan.M.loaded_segments (0x5e13c : word) = Some W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : decode_any W_5dd24 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd28 : bv 32 := 0xfff00793.
Lemma F_5dd28 : fetch_word AsanUbsan.M.loaded_segments (0x5e140 : word) = Some W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : decode_any W_5dd28 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd2c : bv 32 := 0x00c71733.
Lemma F_5dd2c : fetch_word AsanUbsan.M.loaded_segments (0x5e144 : word) = Some W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : decode_any W_5dd2c = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd30 : bv 32 := 0x0284b603.
Lemma F_5dd30 : fetch_word AsanUbsan.M.loaded_segments (0x5e148 : word) = Some W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : decode_any W_5dd30 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd34 : bv 32 := 0x00b797b3.
Lemma F_5dd34 : fetch_word AsanUbsan.M.loaded_segments (0x5e14c : word) = Some W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : decode_any W_5dd34 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd38 : bv 32 := 0xfff50813.
Lemma F_5dd38 : fetch_word AsanUbsan.M.loaded_segments (0x5e150 : word) = Some W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : decode_any W_5dd38 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd3c : bv 32 := 0x00d485b3.
Lemma F_5dd3c : fetch_word AsanUbsan.M.loaded_segments (0x5e154 : word) = Some W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : decode_any W_5dd3c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd40 : bv 32 := 0x00e586b3.
Lemma F_5dd40 : fetch_word AsanUbsan.M.loaded_segments (0x5e158 : word) = Some W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : decode_any W_5dd40 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd44 : bv 32 := 0xfff7c713.
Lemma F_5dd44 : fetch_word AsanUbsan.M.loaded_segments (0x5e15c : word) = Some W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : decode_any W_5dd44 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd48 : bv 32 := 0x02081813.
Lemma F_5dd48 : fetch_word AsanUbsan.M.loaded_segments (0x5e160 : word) = Some W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : decode_any W_5dd48 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd4c : bv 32 := 0x02085793.
Lemma F_5dd4c : fetch_word AsanUbsan.M.loaded_segments (0x5e164 : word) = Some W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : decode_any W_5dd4c = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd50 : bv 32 := 0x00f607b3.
Lemma F_5dd50 : fetch_word AsanUbsan.M.loaded_segments (0x5e168 : word) = Some W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : decode_any W_5dd50 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd54 : bv 32 := 0x00178813.
Lemma F_5dd54 : fetch_word AsanUbsan.M.loaded_segments (0x5e16c : word) = Some W_5dd54.
Proof. vm_refl. Qed.
Lemma D_5dd54 : decode_any W_5dd54 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd58 : bv 32 := 0x00e678b3.
Lemma F_5dd58 : fetch_word AsanUbsan.M.loaded_segments (0x5e170 : word) = Some W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : decode_any W_5dd58 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd5c : bv 32 := 0x011687b3.
Lemma F_5dd5c : fetch_word AsanUbsan.M.loaded_segments (0x5e174 : word) = Some W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : decode_any W_5dd5c = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd60 : bv 32 := 0x0007c283.
Lemma F_5dd60 : fetch_word AsanUbsan.M.loaded_segments (0x5e178 : word) = Some W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : decode_any W_5dd60 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd64 : bv 32 := 0x06028663.
Lemma F_5dd64 : fetch_word AsanUbsan.M.loaded_segments (0x5e17c : word) = Some W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : decode_any W_5dd64 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd68 : bv 32 := 0xfff5051b.
Lemma F_5dd68 : fetch_word AsanUbsan.M.loaded_segments (0x5e180 : word) = Some W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : decode_any W_5dd68 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd6c : bv 32 := 0x00160613.
Lemma F_5dd6c : fetch_word AsanUbsan.M.loaded_segments (0x5e184 : word) = Some W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : decode_any W_5dd6c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd70 : bv 32 := 0xfe0514e3.
Lemma F_5dd70 : fetch_word AsanUbsan.M.loaded_segments (0x5e188 : word) = Some W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : decode_any W_5dd70 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd74 : bv 32 := 0x0304b423.
Lemma F_5dd74 : fetch_word AsanUbsan.M.loaded_segments (0x5e18c : word) = Some W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : decode_any W_5dd74 = Some (Store SZ8 9 16 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd78 : bv 32 := 0x0400006f.
Lemma F_5dd78 : fetch_word AsanUbsan.M.loaded_segments (0x5e190 : word) = Some W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : decode_any W_5dd78 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd7c : bv 32 := 0x000d9517.
Lemma F_5dd7c : fetch_word AsanUbsan.M.loaded_segments (0x5e194 : word) = Some W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : decode_any W_5dd7c = Some (Auipc 10 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd80 : bv 32 := 0x38453503.
Lemma F_5dd80 : fetch_word AsanUbsan.M.loaded_segments (0x5e198 : word) = Some W_5dd80.
Proof. vm_refl. Qed.
Lemma D_5dd80 : decode_any W_5dd80 = Some (Load SZ8 true 10 10 900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd84 : bv 32 := 0x00052503.
Lemma F_5dd84 : fetch_word AsanUbsan.M.loaded_segments (0x5e19c : word) = Some W_5dd84.
Proof. vm_refl. Qed.
Lemma D_5dd84 : decode_any W_5dd84 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd88 : bv 32 := 0x02050863.
Lemma F_5dd88 : fetch_word AsanUbsan.M.loaded_segments (0x5e1a0 : word) = Some W_5dd88.
Proof. vm_refl. Qed.
Lemma D_5dd88 : decode_any W_5dd88 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd8c : bv 32 := 0x740250ef.
Lemma F_5dd8c : fetch_word AsanUbsan.M.loaded_segments (0x5e1a4 : word) = Some W_5dd8c.
Proof. vm_refl. Qed.
Lemma D_5dd8c : decode_any W_5dd8c = Some (Jal 1 153408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd90 : bv 32 := 0x02050463.
Lemma F_5dd90 : fetch_word AsanUbsan.M.loaded_segments (0x5e1a8 : word) = Some W_5dd90.
Proof. vm_refl. Qed.
Lemma D_5dd90 : decode_any W_5dd90 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd94 : bv 32 := 0x02850583.
Lemma F_5dd94 : fetch_word AsanUbsan.M.loaded_segments (0x5e1ac : word) = Some W_5dd94.
Proof. vm_refl. Qed.
Lemma D_5dd94 : decode_any W_5dd94 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd98 : bv 32 := 0x10058e63.
Lemma F_5dd98 : fetch_word AsanUbsan.M.loaded_segments (0x5e1b0 : word) = Some W_5dd98.
Proof. vm_refl. Qed.
Lemma D_5dd98 : decode_any W_5dd98 = Some (Branch BC_EQ 11 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd9c : bv 32 := 0x00000513.
Lemma F_5dd9c : fetch_word AsanUbsan.M.loaded_segments (0x5e1b4 : word) = Some W_5dd9c.
Proof. vm_refl. Qed.
Lemma D_5dd9c : decode_any W_5dd9c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda0 : bv 32 := 0x01813083.
Lemma F_5dda0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1b8 : word) = Some W_5dda0.
Proof. vm_refl. Qed.
Lemma D_5dda0 : decode_any W_5dda0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda4 : bv 32 := 0x01013403.
Lemma F_5dda4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1bc : word) = Some W_5dda4.
Proof. vm_refl. Qed.
Lemma D_5dda4 : decode_any W_5dda4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dda8 : bv 32 := 0x00813483.
Lemma F_5dda8 : fetch_word AsanUbsan.M.loaded_segments (0x5e1c0 : word) = Some W_5dda8.
Proof. vm_refl. Qed.
Lemma D_5dda8 : decode_any W_5dda8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddac : bv 32 := 0x00013903.
Lemma F_5ddac : fetch_word AsanUbsan.M.loaded_segments (0x5e1c4 : word) = Some W_5ddac.
Proof. vm_refl. Qed.
Lemma D_5ddac : decode_any W_5ddac = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb0 : bv 32 := 0x02010113.
Lemma F_5ddb0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1c8 : word) = Some W_5ddb0.
Proof. vm_refl. Qed.
Lemma D_5ddb0 : decode_any W_5ddb0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb4 : bv 32 := 0x00008067.
Lemma F_5ddb4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1cc : word) = Some W_5ddb4.
Proof. vm_refl. Qed.
Lemma D_5ddb4 : decode_any W_5ddb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddb8 : bv 32 := 0x01813083.
Lemma F_5ddb8 : fetch_word AsanUbsan.M.loaded_segments (0x5e1d0 : word) = Some W_5ddb8.
Proof. vm_refl. Qed.
Lemma D_5ddb8 : decode_any W_5ddb8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddbc : bv 32 := 0x01013403.
Lemma F_5ddbc : fetch_word AsanUbsan.M.loaded_segments (0x5e1d4 : word) = Some W_5ddbc.
Proof. vm_refl. Qed.
Lemma D_5ddbc : decode_any W_5ddbc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc0 : bv 32 := 0x00813483.
Lemma F_5ddc0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1d8 : word) = Some W_5ddc0.
Proof. vm_refl. Qed.
Lemma D_5ddc0 : decode_any W_5ddc0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc4 : bv 32 := 0x00013903.
Lemma F_5ddc4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1dc : word) = Some W_5ddc4.
Proof. vm_refl. Qed.
Lemma D_5ddc4 : decode_any W_5ddc4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddc8 : bv 32 := 0x02010113.
Lemma F_5ddc8 : fetch_word AsanUbsan.M.loaded_segments (0x5e1e0 : word) = Some W_5ddc8.
Proof. vm_refl. Qed.
Lemma D_5ddc8 : decode_any W_5ddc8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddcc : bv 32 := 0x00008067.
Lemma F_5ddcc : fetch_word AsanUbsan.M.loaded_segments (0x5e1e4 : word) = Some W_5ddcc.
Proof. vm_refl. Qed.
Lemma D_5ddcc : decode_any W_5ddcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddd0 : bv 32 := 0x00160613.
Lemma F_5ddd0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1e8 : word) = Some W_5ddd0.
Proof. vm_refl. Qed.
Lemma D_5ddd0 : decode_any W_5ddd0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddd4 : bv 32 := 0x00100513.
Lemma F_5ddd4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1ec : word) = Some W_5ddd4.
Proof. vm_refl. Qed.
Lemma D_5ddd4 : decode_any W_5ddd4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddd8 : bv 32 := 0xffb90693.
Lemma F_5ddd8 : fetch_word AsanUbsan.M.loaded_segments (0x5e1f0 : word) = Some W_5ddd8.
Proof. vm_refl. Qed.
Lemma D_5ddd8 : decode_any W_5ddd8 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dddc : bv 32 := 0x02c4b423.
Lemma F_5dddc : fetch_word AsanUbsan.M.loaded_segments (0x5e1f4 : word) = Some W_5dddc.
Proof. vm_refl. Qed.
Lemma D_5dddc : decode_any W_5dddc = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dde0 : bv 32 := 0x00a78023.
Lemma F_5dde0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1f8 : word) = Some W_5dde0.
Proof. vm_refl. Qed.
Lemma D_5dde0 : decode_any W_5dde0 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dde4 : bv 32 := 0x00d51533.
Lemma F_5dde4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1fc : word) = Some W_5dde4.
Proof. vm_refl. Qed.
Lemma D_5dde4 : decode_any W_5dde4 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dde8 : bv 32 := 0x00500613.
Lemma F_5dde8 : fetch_word AsanUbsan.M.loaded_segments (0x5e200 : word) = Some W_5dde8.
Proof. vm_refl. Qed.
Lemma D_5dde8 : decode_any W_5dde8 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddec : bv 32 := 0x00b89893.
Lemma F_5ddec : fetch_word AsanUbsan.M.loaded_segments (0x5e204 : word) = Some W_5ddec.
Proof. vm_refl. Qed.
Lemma D_5ddec : decode_any W_5ddec = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddf0 : bv 32 := 0x01261633.
Lemma F_5ddf0 : fetch_word AsanUbsan.M.loaded_segments (0x5e208 : word) = Some W_5ddf0.
Proof. vm_refl. Qed.
Lemma D_5ddf0 : decode_any W_5ddf0 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddf4 : bv 32 := 0x00a58533.
Lemma F_5ddf4 : fetch_word AsanUbsan.M.loaded_segments (0x5e20c : word) = Some W_5ddf4.
Proof. vm_refl. Qed.
Lemma D_5ddf4 : decode_any W_5ddf4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddf8 : bv 32 := 0x01160633.
Lemma F_5ddf8 : fetch_word AsanUbsan.M.loaded_segments (0x5e210 : word) = Some W_5ddf8.
Proof. vm_refl. Qed.
Lemma D_5ddf8 : decode_any W_5ddf8 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ddfc : bv 32 := 0x00c504b3.
Lemma F_5ddfc : fetch_word AsanUbsan.M.loaded_segments (0x5e214 : word) = Some W_5ddfc.
Proof. vm_refl. Qed.
Lemma D_5ddfc : decode_any W_5ddfc = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de00 : bv 32 := 0x0084bc23.
Lemma F_5de00 : fetch_word AsanUbsan.M.loaded_segments (0x5e218 : word) = Some W_5de00.
Proof. vm_refl. Qed.
Lemma D_5de00 : decode_any W_5de00 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de04 : bv 32 := 0x7ef4bc23.
Lemma F_5de04 : fetch_word AsanUbsan.M.loaded_segments (0x5e21c : word) = Some W_5de04.
Proof. vm_refl. Qed.
Lemma D_5de04 : decode_any W_5de04 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de08 : bv 32 := 0x00048513.
Lemma F_5de08 : fetch_word AsanUbsan.M.loaded_segments (0x5e220 : word) = Some W_5de08.
Proof. vm_refl. Qed.
Lemma D_5de08 : decode_any W_5de08 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de0c : bv 32 := 0x178000ef.
Lemma F_5de0c : fetch_word AsanUbsan.M.loaded_segments (0x5e224 : word) = Some W_5de0c.
Proof. vm_refl. Qed.
Lemma D_5de0c : decode_any W_5de0c = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de10 : bv 32 := 0x00050593.
Lemma F_5de10 : fetch_word AsanUbsan.M.loaded_segments (0x5e228 : word) = Some W_5de10.
Proof. vm_refl. Qed.
Lemma D_5de10 : decode_any W_5de10 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de14 : bv 32 := 0x00048513.
Lemma F_5de14 : fetch_word AsanUbsan.M.loaded_segments (0x5e22c : word) = Some W_5de14.
Proof. vm_refl. Qed.
Lemma D_5de14 : decode_any W_5de14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de18 : bv 32 := 0x00000613.
Lemma F_5de18 : fetch_word AsanUbsan.M.loaded_segments (0x5e230 : word) = Some W_5de18.
Proof. vm_refl. Qed.
Lemma D_5de18 : decode_any W_5de18 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de1c : bv 32 := 0x0005b023.
Lemma F_5de1c : fetch_word AsanUbsan.M.loaded_segments (0x5e234 : word) = Some W_5de1c.
Proof. vm_refl. Qed.
Lemma D_5de1c : decode_any W_5de1c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de20 : bv 32 := 0x0005b423.
Lemma F_5de20 : fetch_word AsanUbsan.M.loaded_segments (0x5e238 : word) = Some W_5de20.
Proof. vm_refl. Qed.
Lemma D_5de20 : decode_any W_5de20 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de24 : bv 32 := 0x0005b823.
Lemma F_5de24 : fetch_word AsanUbsan.M.loaded_segments (0x5e23c : word) = Some W_5de24.
Proof. vm_refl. Qed.
Lemma D_5de24 : decode_any W_5de24 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de28 : bv 32 := 0x0005bc23.
Lemma F_5de28 : fetch_word AsanUbsan.M.loaded_segments (0x5e240 : word) = Some W_5de28.
Proof. vm_refl. Qed.
Lemma D_5de28 : decode_any W_5de28 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de2c : bv 32 := 0x0205b023.
Lemma F_5de2c : fetch_word AsanUbsan.M.loaded_segments (0x5e244 : word) = Some W_5de2c.
Proof. vm_refl. Qed.
Lemma D_5de2c : decode_any W_5de2c = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de30 : bv 32 := 0x0205b423.
Lemma F_5de30 : fetch_word AsanUbsan.M.loaded_segments (0x5e248 : word) = Some W_5de30.
Proof. vm_refl. Qed.
Lemma D_5de30 : decode_any W_5de30 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de34 : bv 32 := 0x0205b823.
Lemma F_5de34 : fetch_word AsanUbsan.M.loaded_segments (0x5e24c : word) = Some W_5de34.
Proof. vm_refl. Qed.
Lemma D_5de34 : decode_any W_5de34 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de38 : bv 32 := 0x0205bc23.
Lemma F_5de38 : fetch_word AsanUbsan.M.loaded_segments (0x5e250 : word) = Some W_5de38.
Proof. vm_refl. Qed.
Lemma D_5de38 : decode_any W_5de38 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de3c : bv 32 := 0x0405b023.
Lemma F_5de3c : fetch_word AsanUbsan.M.loaded_segments (0x5e254 : word) = Some W_5de3c.
Proof. vm_refl. Qed.
Lemma D_5de3c : decode_any W_5de3c = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de40 : bv 32 := 0x0405b423.
Lemma F_5de40 : fetch_word AsanUbsan.M.loaded_segments (0x5e258 : word) = Some W_5de40.
Proof. vm_refl. Qed.
Lemma D_5de40 : decode_any W_5de40 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de44 : bv 32 := 0x0405b823.
Lemma F_5de44 : fetch_word AsanUbsan.M.loaded_segments (0x5e25c : word) = Some W_5de44.
Proof. vm_refl. Qed.
Lemma D_5de44 : decode_any W_5de44 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de48 : bv 32 := 0x0405bc23.
Lemma F_5de48 : fetch_word AsanUbsan.M.loaded_segments (0x5e260 : word) = Some W_5de48.
Proof. vm_refl. Qed.
Lemma D_5de48 : decode_any W_5de48 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de4c : bv 32 := 0x0605b023.
Lemma F_5de4c : fetch_word AsanUbsan.M.loaded_segments (0x5e264 : word) = Some W_5de4c.
Proof. vm_refl. Qed.
Lemma D_5de4c : decode_any W_5de4c = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de50 : bv 32 := 0x0605b423.
Lemma F_5de50 : fetch_word AsanUbsan.M.loaded_segments (0x5e268 : word) = Some W_5de50.
Proof. vm_refl. Qed.
Lemma D_5de50 : decode_any W_5de50 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de54 : bv 32 := 0x0605b823.
Lemma F_5de54 : fetch_word AsanUbsan.M.loaded_segments (0x5e26c : word) = Some W_5de54.
Proof. vm_refl. Qed.
Lemma D_5de54 : decode_any W_5de54 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de58 : bv 32 := 0x0605bc23.
Lemma F_5de58 : fetch_word AsanUbsan.M.loaded_segments (0x5e270 : word) = Some W_5de58.
Proof. vm_refl. Qed.
Lemma D_5de58 : decode_any W_5de58 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de5c : bv 32 := 0x0805b023.
Lemma F_5de5c : fetch_word AsanUbsan.M.loaded_segments (0x5e274 : word) = Some W_5de5c.
Proof. vm_refl. Qed.
Lemma D_5de5c : decode_any W_5de5c = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de60 : bv 32 := 0x0805b423.
Lemma F_5de60 : fetch_word AsanUbsan.M.loaded_segments (0x5e278 : word) = Some W_5de60.
Proof. vm_refl. Qed.
Lemma D_5de60 : decode_any W_5de60 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de64 : bv 32 := 0x0805b823.
Lemma F_5de64 : fetch_word AsanUbsan.M.loaded_segments (0x5e27c : word) = Some W_5de64.
Proof. vm_refl. Qed.
Lemma D_5de64 : decode_any W_5de64 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de68 : bv 32 := 0x0805bc23.
Lemma F_5de68 : fetch_word AsanUbsan.M.loaded_segments (0x5e280 : word) = Some W_5de68.
Proof. vm_refl. Qed.
Lemma D_5de68 : decode_any W_5de68 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de6c : bv 32 := 0x0a05b023.
Lemma F_5de6c : fetch_word AsanUbsan.M.loaded_segments (0x5e284 : word) = Some W_5de6c.
Proof. vm_refl. Qed.
Lemma D_5de6c : decode_any W_5de6c = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de70 : bv 32 := 0x0a05b423.
Lemma F_5de70 : fetch_word AsanUbsan.M.loaded_segments (0x5e288 : word) = Some W_5de70.
Proof. vm_refl. Qed.
Lemma D_5de70 : decode_any W_5de70 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de74 : bv 32 := 0x0a05b823.
Lemma F_5de74 : fetch_word AsanUbsan.M.loaded_segments (0x5e28c : word) = Some W_5de74.
Proof. vm_refl. Qed.
Lemma D_5de74 : decode_any W_5de74 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de78 : bv 32 := 0x0a05bc23.
Lemma F_5de78 : fetch_word AsanUbsan.M.loaded_segments (0x5e290 : word) = Some W_5de78.
Proof. vm_refl. Qed.
Lemma D_5de78 : decode_any W_5de78 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de7c : bv 32 := 0x0c05b023.
Lemma F_5de7c : fetch_word AsanUbsan.M.loaded_segments (0x5e294 : word) = Some W_5de7c.
Proof. vm_refl. Qed.
Lemma D_5de7c : decode_any W_5de7c = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de80 : bv 32 := 0x0c05b423.
Lemma F_5de80 : fetch_word AsanUbsan.M.loaded_segments (0x5e298 : word) = Some W_5de80.
Proof. vm_refl. Qed.
Lemma D_5de80 : decode_any W_5de80 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de84 : bv 32 := 0x0c05b823.
Lemma F_5de84 : fetch_word AsanUbsan.M.loaded_segments (0x5e29c : word) = Some W_5de84.
Proof. vm_refl. Qed.
Lemma D_5de84 : decode_any W_5de84 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de88 : bv 32 := 0x0c05bc23.
Lemma F_5de88 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a0 : word) = Some W_5de88.
Proof. vm_refl. Qed.
Lemma D_5de88 : decode_any W_5de88 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de8c : bv 32 := 0x0e05b023.
Lemma F_5de8c : fetch_word AsanUbsan.M.loaded_segments (0x5e2a4 : word) = Some W_5de8c.
Proof. vm_refl. Qed.
Lemma D_5de8c : decode_any W_5de8c = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de90 : bv 32 := 0x0e05b423.
Lemma F_5de90 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a8 : word) = Some W_5de90.
Proof. vm_refl. Qed.
Lemma D_5de90 : decode_any W_5de90 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de94 : bv 32 := 0x0e05b823.
Lemma F_5de94 : fetch_word AsanUbsan.M.loaded_segments (0x5e2ac : word) = Some W_5de94.
Proof. vm_refl. Qed.
Lemma D_5de94 : decode_any W_5de94 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de98 : bv 32 := 0x0e05bc23.
Lemma F_5de98 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b0 : word) = Some W_5de98.
Proof. vm_refl. Qed.
Lemma D_5de98 : decode_any W_5de98 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5de9c : bv 32 := 0x01813083.
Lemma F_5de9c : fetch_word AsanUbsan.M.loaded_segments (0x5e2b4 : word) = Some W_5de9c.
Proof. vm_refl. Qed.
Lemma D_5de9c : decode_any W_5de9c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea0 : bv 32 := 0x01013403.
Lemma F_5dea0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b8 : word) = Some W_5dea0.
Proof. vm_refl. Qed.
Lemma D_5dea0 : decode_any W_5dea0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea4 : bv 32 := 0x00813483.
Lemma F_5dea4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2bc : word) = Some W_5dea4.
Proof. vm_refl. Qed.
Lemma D_5dea4 : decode_any W_5dea4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dea8 : bv 32 := 0x00013903.
Lemma F_5dea8 : fetch_word AsanUbsan.M.loaded_segments (0x5e2c0 : word) = Some W_5dea8.
Proof. vm_refl. Qed.
Lemma D_5dea8 : decode_any W_5dea8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deac : bv 32 := 0x02010113.
Lemma F_5deac : fetch_word AsanUbsan.M.loaded_segments (0x5e2c4 : word) = Some W_5deac.
Proof. vm_refl. Qed.
Lemma D_5deac : decode_any W_5deac = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb0 : bv 32 := 0x00008067.
Lemma F_5deb0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2c8 : word) = Some W_5deb0.
Proof. vm_refl. Qed.
Lemma D_5deb0 : decode_any W_5deb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb4 : bv 32 := 0x04853483.
Lemma F_5deb4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2cc : word) = Some W_5deb4.
Proof. vm_refl. Qed.
Lemma D_5deb4 : decode_any W_5deb4 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deb8 : bv 32 := 0x00100593.
Lemma F_5deb8 : fetch_word AsanUbsan.M.loaded_segments (0x5e2d0 : word) = Some W_5deb8.
Proof. vm_refl. Qed.
Lemma D_5deb8 : decode_any W_5deb8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5debc : bv 32 := 0x0095e663.
Lemma F_5debc : fetch_word AsanUbsan.M.loaded_segments (0x5e2d4 : word) = Some W_5debc.
Proof. vm_refl. Qed.
Lemma D_5debc : decode_any W_5debc = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec0 : bv 32 := 0x081250ef.
Lemma F_5dec0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2d8 : word) = Some W_5dec0.
Proof. vm_refl. Qed.
Lemma D_5dec0 : decode_any W_5dec0 = Some (Jal 1 153728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec4 : bv 32 := 0x00050493.
Lemma F_5dec4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2dc : word) = Some W_5dec4.
Proof. vm_refl. Qed.
Lemma D_5dec4 : decode_any W_5dec4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dec8 : bv 32 := 0xe20494e3.
Lemma F_5dec8 : fetch_word AsanUbsan.M.loaded_segments (0x5e2e0 : word) = Some W_5dec8.
Proof. vm_refl. Qed.
Lemma D_5dec8 : decode_any W_5dec8 = Some (Branch BC_NE 9 0 7720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5decc : bv 32 := 0xed1ff06f.
Lemma F_5decc : fetch_word AsanUbsan.M.loaded_segments (0x5e2e4 : word) = Some W_5decc.
Proof. vm_refl. Qed.
Lemma D_5decc : decode_any W_5decc = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.
