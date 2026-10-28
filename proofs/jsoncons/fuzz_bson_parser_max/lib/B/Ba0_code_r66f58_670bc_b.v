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
Definition W_80dd0 : bv 32 := 0xfb010113.
Lemma F_80dd0 : fetch_word AsanUbsan.M.loaded_segments (0x811e8 : word) = Some W_80dd0.
Proof. vm_refl. Qed.
Lemma D_80dd0 : decode_any W_80dd0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80dd4 : bv 32 := 0x04113423.
Lemma F_80dd4 : fetch_word AsanUbsan.M.loaded_segments (0x811ec : word) = Some W_80dd4.
Proof. vm_refl. Qed.
Lemma D_80dd4 : decode_any W_80dd4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80dd8 : bv 32 := 0x04813023.
Lemma F_80dd8 : fetch_word AsanUbsan.M.loaded_segments (0x811f0 : word) = Some W_80dd8.
Proof. vm_refl. Qed.
Lemma D_80dd8 : decode_any W_80dd8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ddc : bv 32 := 0x02913c23.
Lemma F_80ddc : fetch_word AsanUbsan.M.loaded_segments (0x811f4 : word) = Some W_80ddc.
Proof. vm_refl. Qed.
Lemma D_80ddc : decode_any W_80ddc = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80de0 : bv 32 := 0x03213823.
Lemma F_80de0 : fetch_word AsanUbsan.M.loaded_segments (0x811f8 : word) = Some W_80de0.
Proof. vm_refl. Qed.
Lemma D_80de0 : decode_any W_80de0 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80de4 : bv 32 := 0x03313423.
Lemma F_80de4 : fetch_word AsanUbsan.M.loaded_segments (0x811fc : word) = Some W_80de4.
Proof. vm_refl. Qed.
Lemma D_80de4 : decode_any W_80de4 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80de8 : bv 32 := 0x000bf517.
Lemma F_80de8 : fetch_word AsanUbsan.M.loaded_segments (0x81200 : word) = Some W_80de8.
Proof. vm_refl. Qed.
Lemma D_80de8 : decode_any W_80de8 = Some (Auipc 10 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80dec : bv 32 := 0x71850493.
Lemma F_80dec : fetch_word AsanUbsan.M.loaded_segments (0x81204 : word) = Some W_80dec.
Proof. vm_refl. Qed.
Lemma D_80dec : decode_any W_80dec = Some (OpImm ALU_ADD 9 10 1816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80df0 : bv 32 := 0x00048503.
Lemma F_80df0 : fetch_word AsanUbsan.M.loaded_segments (0x81208 : word) = Some W_80df0.
Proof. vm_refl. Qed.
Lemma D_80df0 : decode_any W_80df0 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80df4 : bv 32 := 0x00100593.
Lemma F_80df4 : fetch_word AsanUbsan.M.loaded_segments (0x8120c : word) = Some W_80df4.
Proof. vm_refl. Qed.
Lemma D_80df4 : decode_any W_80df4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80df8 : bv 32 := 0x0230000f.
Lemma F_80df8 : fetch_word AsanUbsan.M.loaded_segments (0x81210 : word) = Some W_80df8.
Proof. vm_refl. Qed.
Lemma D_80df8 : decode_any W_80df8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80dfc : bv 32 := 0x10b51e63.
Lemma F_80dfc : fetch_word AsanUbsan.M.loaded_segments (0x81214 : word) = Some W_80dfc.
Proof. vm_refl. Qed.
Lemma D_80dfc : decode_any W_80dfc = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e00 : bv 32 := 0xbe1fa0ef.
Lemma F_80e00 : fetch_word AsanUbsan.M.loaded_segments (0x81218 : word) = Some W_80e00.
Proof. vm_refl. Qed.
Lemma D_80e00 : decode_any W_80e00 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e04 : bv 32 := 0x0e051663.
Lemma F_80e04 : fetch_word AsanUbsan.M.loaded_segments (0x8121c : word) = Some W_80e04.
Proof. vm_refl. Qed.
Lemma D_80e04 : decode_any W_80e04 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e08 : bv 32 := 0xfff8f517.
Lemma F_80e08 : fetch_word AsanUbsan.M.loaded_segments (0x81220 : word) = Some W_80e08.
Proof. vm_refl. Qed.
Lemma D_80e08 : decode_any W_80e08 = Some (Auipc 10 1048463, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e0c : bv 32 := 0x24053403.
Lemma F_80e0c : fetch_word AsanUbsan.M.loaded_segments (0x81224 : word) = Some W_80e0c.
Proof. vm_refl. Qed.
Lemma D_80e0c : decode_any W_80e0c = Some (Load SZ8 true 8 10 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e10 : bv 32 := 0x02813023.
Lemma F_80e10 : fetch_word AsanUbsan.M.loaded_segments (0x81228 : word) = Some W_80e10.
Proof. vm_refl. Qed.
Lemma D_80e10 : decode_any W_80e10 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e14 : bv 32 := 0x00813c23.
Lemma F_80e14 : fetch_word AsanUbsan.M.loaded_segments (0x8122c : word) = Some W_80e14.
Proof. vm_refl. Qed.
Lemma D_80e14 : decode_any W_80e14 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e18 : bv 32 := 0x6b4020ef.
Lemma F_80e18 : fetch_word AsanUbsan.M.loaded_segments (0x81230 : word) = Some W_80e18.
Proof. vm_refl. Qed.
Lemma D_80e18 : decode_any W_80e18 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e1c : bv 32 := 0x08050263.
Lemma F_80e1c : fetch_word AsanUbsan.M.loaded_segments (0x81234 : word) = Some W_80e1c.
Proof. vm_refl. Qed.
Lemma D_80e1c : decode_any W_80e1c = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e20 : bv 32 := 0x000b6597.
Lemma F_80e20 : fetch_word AsanUbsan.M.loaded_segments (0x81238 : word) = Some W_80e20.
Proof. vm_refl. Qed.
Lemma D_80e20 : decode_any W_80e20 = Some (Auipc 11 182, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e24 : bv 32 := 0x2685b903.
Lemma F_80e24 : fetch_word AsanUbsan.M.loaded_segments (0x8123c : word) = Some W_80e24.
Proof. vm_refl. Qed.
Lemma D_80e24 : decode_any W_80e24 = Some (Load SZ8 true 18 11 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e28 : bv 32 := 0x00093403.
Lemma F_80e28 : fetch_word AsanUbsan.M.loaded_segments (0x81240 : word) = Some W_80e28.
Proof. vm_refl. Qed.
Lemma D_80e28 : decode_any W_80e28 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e2c : bv 32 := 0x00041c63.
Lemma F_80e2c : fetch_word AsanUbsan.M.loaded_segments (0x81244 : word) = Some W_80e2c.
Proof. vm_refl. Qed.
Lemma D_80e2c : decode_any W_80e2c = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e44 : bv 32 := 0x04d020ef.
Lemma F_80e44 : fetch_word AsanUbsan.M.loaded_segments (0x8125c : word) = Some W_80e44.
Proof. vm_refl. Qed.
Lemma D_80e44 : decode_any W_80e44 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e48 : bv 32 := 0x00050613.
Lemma F_80e48 : fetch_word AsanUbsan.M.loaded_segments (0x81260 : word) = Some W_80e48.
Proof. vm_refl. Qed.
Lemma D_80e48 : decode_any W_80e48 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e4c : bv 32 := 0x00a13c23.
Lemma F_80e4c : fetch_word AsanUbsan.M.loaded_segments (0x81264 : word) = Some W_80e4c.
Proof. vm_refl. Qed.
Lemma D_80e4c : decode_any W_80e4c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e50 : bv 32 := 0x01010513.
Lemma F_80e50 : fetch_word AsanUbsan.M.loaded_segments (0x81268 : word) = Some W_80e50.
Proof. vm_refl. Qed.
Lemma D_80e50 : decode_any W_80e50 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e54 : bv 32 := 0x40850533.
Lemma F_80e54 : fetch_word AsanUbsan.M.loaded_segments (0x8126c : word) = Some W_80e54.
Proof. vm_refl. Qed.
Lemma D_80e54 : decode_any W_80e54 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e58 : bv 32 := 0x408006b3.
Lemma F_80e58 : fetch_word AsanUbsan.M.loaded_segments (0x81270 : word) = Some W_80e58.
Proof. vm_refl. Qed.
Lemma D_80e58 : decode_any W_80e58 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e5c : bv 32 := 0x00d576b3.
Lemma F_80e5c : fetch_word AsanUbsan.M.loaded_segments (0x81274 : word) = Some W_80e5c.
Proof. vm_refl. Qed.
Lemma D_80e5c : decode_any W_80e5c = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e60 : bv 32 := 0x02d13023.
Lemma F_80e60 : fetch_word AsanUbsan.M.loaded_segments (0x81278 : word) = Some W_80e60.
Proof. vm_refl. Qed.
Lemma D_80e60 : decode_any W_80e60 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e64 : bv 32 := 0x40d60733.
Lemma F_80e64 : fetch_word AsanUbsan.M.loaded_segments (0x8127c : word) = Some W_80e64.
Proof. vm_refl. Qed.
Lemma D_80e64 : decode_any W_80e64 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e68 : bv 32 := 0x04000537.
Lemma F_80e68 : fetch_word AsanUbsan.M.loaded_segments (0x81280 : word) = Some W_80e68.
Proof. vm_refl. Qed.
Lemma D_80e68 : decode_any W_80e68 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e6c : bv 32 := 0x0015051b.
Lemma F_80e6c : fetch_word AsanUbsan.M.loaded_segments (0x81284 : word) = Some W_80e6c.
Proof. vm_refl. Qed.
Lemma D_80e6c : decode_any W_80e6c = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80e70 : bv 32 := 0x06a76263.
Lemma F_80e70 : fetch_word AsanUbsan.M.loaded_segments (0x81288 : word) = Some W_80e70.
Proof. vm_refl. Qed.
Lemma D_80e70 : decode_any W_80e70 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ed4 : bv 32 := 0x00770713.
Lemma F_80ed4 : fetch_word AsanUbsan.M.loaded_segments (0x812ec : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ed8 : bv 32 := 0x10000537.
Lemma F_80ed8 : fetch_word AsanUbsan.M.loaded_segments (0x812f0 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80edc : bv 32 := 0xff85051b.
Lemma F_80edc : fetch_word AsanUbsan.M.loaded_segments (0x812f4 : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee0 : bv 32 := 0x00a775b3.
Lemma F_80ee0 : fetch_word AsanUbsan.M.loaded_segments (0x812f8 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee4 : bv 32 := 0x00068513.
Lemma F_80ee4 : fetch_word AsanUbsan.M.loaded_segments (0x812fc : word) = Some W_80ee4.
Proof. vm_refl. Qed.
Lemma D_80ee4 : decode_any W_80ee4 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ee8 : bv 32 := 0x00000613.
Lemma F_80ee8 : fetch_word AsanUbsan.M.loaded_segments (0x81300 : word) = Some W_80ee8.
Proof. vm_refl. Qed.
Lemma D_80ee8 : decode_any W_80ee8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80eec : bv 32 := 0x835f90ef.
Lemma F_80eec : fetch_word AsanUbsan.M.loaded_segments (0x81304 : word) = Some W_80eec.
Proof. vm_refl. Qed.
Lemma D_80eec : decode_any W_80eec = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef0 : bv 32 := 0x5dc020ef.
Lemma F_80ef0 : fetch_word AsanUbsan.M.loaded_segments (0x81308 : word) = Some W_80ef0.
Proof. vm_refl. Qed.
Lemma D_80ef0 : decode_any W_80ef0 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef4 : bv 32 := 0x02050263.
Lemma F_80ef4 : fetch_word AsanUbsan.M.loaded_segments (0x8130c : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ef8 : bv 32 := 0x02850583.
Lemma F_80ef8 : fetch_word AsanUbsan.M.loaded_segments (0x81310 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80efc : bv 32 := 0x00059e63.
Lemma F_80efc : fetch_word AsanUbsan.M.loaded_segments (0x81314 : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f00 : bv 32 := 0x04853503.
Lemma F_80f00 : fetch_word AsanUbsan.M.loaded_segments (0x81318 : word) = Some W_80f00.
Proof. vm_refl. Qed.
Lemma D_80f00 : decode_any W_80f00 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f04 : bv 32 := 0x00253593.
Lemma F_80f04 : fetch_word AsanUbsan.M.loaded_segments (0x8131c : word) = Some W_80f04.
Proof. vm_refl. Qed.
Lemma D_80f04 : decode_any W_80f04 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f08 : bv 32 := 0xfff58593.
Lemma F_80f08 : fetch_word AsanUbsan.M.loaded_segments (0x81320 : word) = Some W_80f08.
Proof. vm_refl. Qed.
Lemma D_80f08 : decode_any W_80f08 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f0c : bv 32 := 0x00a5f533.
Lemma F_80f0c : fetch_word AsanUbsan.M.loaded_segments (0x81324 : word) = Some W_80f0c.
Proof. vm_refl. Qed.
Lemma D_80f0c : decode_any W_80f0c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f10 : bv 32 := 0x00050463.
Lemma F_80f10 : fetch_word AsanUbsan.M.loaded_segments (0x81328 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f14 : bv 32 := 0xf9cdc0ef.
Lemma F_80f14 : fetch_word AsanUbsan.M.loaded_segments (0x8132c : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (Jal 1 1951644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f18 : bv 32 := 0x04813083.
Lemma F_80f18 : fetch_word AsanUbsan.M.loaded_segments (0x81330 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f1c : bv 32 := 0x04013403.
Lemma F_80f1c : fetch_word AsanUbsan.M.loaded_segments (0x81334 : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f20 : bv 32 := 0x03813483.
Lemma F_80f20 : fetch_word AsanUbsan.M.loaded_segments (0x81338 : word) = Some W_80f20.
Proof. vm_refl. Qed.
Lemma D_80f20 : decode_any W_80f20 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f24 : bv 32 := 0x03013903.
Lemma F_80f24 : fetch_word AsanUbsan.M.loaded_segments (0x8133c : word) = Some W_80f24.
Proof. vm_refl. Qed.
Lemma D_80f24 : decode_any W_80f24 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f28 : bv 32 := 0x02813983.
Lemma F_80f28 : fetch_word AsanUbsan.M.loaded_segments (0x81340 : word) = Some W_80f28.
Proof. vm_refl. Qed.
Lemma D_80f28 : decode_any W_80f28 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f2c : bv 32 := 0x05010113.
Lemma F_80f2c : fetch_word AsanUbsan.M.loaded_segments (0x81344 : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80f30 : bv 32 := 0x00008067.
Lemma F_80f30 : fetch_word AsanUbsan.M.loaded_segments (0x81348 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
