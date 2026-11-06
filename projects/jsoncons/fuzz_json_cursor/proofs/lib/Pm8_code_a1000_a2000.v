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

Definition W_a1154 : bv 32 := 0x00058613.
Lemma F_a1154 : fetch_word Asan.M.loaded_segments (0xa11a4 : word) = Some W_a1154.
Proof. vm_refl. Qed.
Lemma D_a1154 : decode_any W_a1154 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1158 : bv 32 := 0x0019d597.
Lemma F_a1158 : fetch_word Asan.M.loaded_segments (0xa11a8 : word) = Some W_a1158.
Proof. vm_refl. Qed.
Lemma D_a1158 : decode_any W_a1158 = Some (Auipc 11 413, 4%Z).
Proof. vm_refl. Qed.

Definition W_a115c : bv 32 := 0x6f058593.
Lemma F_a115c : fetch_word Asan.M.loaded_segments (0xa11ac : word) = Some W_a115c.
Proof. vm_refl. Qed.
Lemma D_a115c : decode_any W_a115c = Some (OpImm ALU_ADD 11 11 1776, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1160 : bv 32 := 0x00050693.
Lemma F_a1160 : fetch_word Asan.M.loaded_segments (0xa11b0 : word) = Some W_a1160.
Proof. vm_refl. Qed.
Lemma D_a1160 : decode_any W_a1160 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1164 : bv 32 := 0x00058513.
Lemma F_a1164 : fetch_word Asan.M.loaded_segments (0xa11b4 : word) = Some W_a1164.
Proof. vm_refl. Qed.
Lemma D_a1164 : decode_any W_a1164 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1168 : bv 32 := 0x00068593.
Lemma F_a1168 : fetch_word Asan.M.loaded_segments (0xa11b8 : word) = Some W_a1168.
Proof. vm_refl. Qed.
Lemma D_a1168 : decode_any W_a1168 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a116c : bv 32 := 0x00000693.
Lemma F_a116c : fetch_word Asan.M.loaded_segments (0xa11bc : word) = Some W_a116c.
Proof. vm_refl. Qed.
Lemma D_a116c : decode_any W_a116c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1170 : bv 32 := 0x0040006f.
Lemma F_a1170 : fetch_word Asan.M.loaded_segments (0xa11c0 : word) = Some W_a1170.
Proof. vm_refl. Qed.
Lemma D_a1170 : decode_any W_a1170 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1174 : bv 32 := 0xf9010113.
Lemma F_a1174 : fetch_word Asan.M.loaded_segments (0xa11c4 : word) = Some W_a1174.
Proof. vm_refl. Qed.
Lemma D_a1174 : decode_any W_a1174 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1178 : bv 32 := 0x06113423.
Lemma F_a1178 : fetch_word Asan.M.loaded_segments (0xa11c8 : word) = Some W_a1178.
Proof. vm_refl. Qed.
Lemma D_a1178 : decode_any W_a1178 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a117c : bv 32 := 0x06813023.
Lemma F_a117c : fetch_word Asan.M.loaded_segments (0xa11cc : word) = Some W_a117c.
Proof. vm_refl. Qed.
Lemma D_a117c : decode_any W_a117c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1180 : bv 32 := 0x04913c23.
Lemma F_a1180 : fetch_word Asan.M.loaded_segments (0xa11d0 : word) = Some W_a1180.
Proof. vm_refl. Qed.
Lemma D_a1180 : decode_any W_a1180 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1184 : bv 32 := 0x05213823.
Lemma F_a1184 : fetch_word Asan.M.loaded_segments (0xa11d4 : word) = Some W_a1184.
Proof. vm_refl. Qed.
Lemma D_a1184 : decode_any W_a1184 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1188 : bv 32 := 0x05313423.
Lemma F_a1188 : fetch_word Asan.M.loaded_segments (0xa11d8 : word) = Some W_a1188.
Proof. vm_refl. Qed.
Lemma D_a1188 : decode_any W_a1188 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a118c : bv 32 := 0x05413023.
Lemma F_a118c : fetch_word Asan.M.loaded_segments (0xa11dc : word) = Some W_a118c.
Proof. vm_refl. Qed.
Lemma D_a118c : decode_any W_a118c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1190 : bv 32 := 0x03513c23.
Lemma F_a1190 : fetch_word Asan.M.loaded_segments (0xa11e0 : word) = Some W_a1190.
Proof. vm_refl. Qed.
Lemma D_a1190 : decode_any W_a1190 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1194 : bv 32 := 0x03613823.
Lemma F_a1194 : fetch_word Asan.M.loaded_segments (0xa11e4 : word) = Some W_a1194.
Proof. vm_refl. Qed.
Lemma D_a1194 : decode_any W_a1194 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1198 : bv 32 := 0x03713423.
Lemma F_a1198 : fetch_word Asan.M.loaded_segments (0xa11e8 : word) = Some W_a1198.
Proof. vm_refl. Qed.
Lemma D_a1198 : decode_any W_a1198 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a119c : bv 32 := 0x03813023.
Lemma F_a119c : fetch_word Asan.M.loaded_segments (0xa11ec : word) = Some W_a119c.
Proof. vm_refl. Qed.
Lemma D_a119c : decode_any W_a119c = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11a0 : bv 32 := 0x01913c23.
Lemma F_a11a0 : fetch_word Asan.M.loaded_segments (0xa11f0 : word) = Some W_a11a0.
Proof. vm_refl. Qed.
Lemma D_a11a0 : decode_any W_a11a0 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11a4 : bv 32 := 0x00068413.
Lemma F_a11a4 : fetch_word Asan.M.loaded_segments (0xa11f4 : word) = Some W_a11a4.
Proof. vm_refl. Qed.
Lemma D_a11a4 : decode_any W_a11a4 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11a8 : bv 32 := 0x00050493.
Lemma F_a11a8 : fetch_word Asan.M.loaded_segments (0xa11f8 : word) = Some W_a11a8.
Proof. vm_refl. Qed.
Lemma D_a11a8 : decode_any W_a11a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11ac : bv 32 := 0x00b13423.
Lemma F_a11ac : fetch_word Asan.M.loaded_segments (0xa11fc : word) = Some W_a11ac.
Proof. vm_refl. Qed.
Lemma D_a11ac : decode_any W_a11ac = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11b0 : bv 32 := 0x00c13823.
Lemma F_a11b0 : fetch_word Asan.M.loaded_segments (0xa1200 : word) = Some W_a11b0.
Proof. vm_refl. Qed.
Lemma D_a11b0 : decode_any W_a11b0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11b4 : bv 32 := 0x00068463.
Lemma F_a11b4 : fetch_word Asan.M.loaded_segments (0xa1204 : word) = Some W_a11b4.
Proof. vm_refl. Qed.
Lemma D_a11b4 : decode_any W_a11b4 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11bc : bv 32 := 0x0006069b.
Lemma F_a11bc : fetch_word Asan.M.loaded_segments (0xa120c : word) = Some W_a11bc.
Proof. vm_refl. Qed.
Lemma D_a11bc : decode_any W_a11bc = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11c0 : bv 32 := 0x00000513.
Lemma F_a11c0 : fetch_word Asan.M.loaded_segments (0xa1210 : word) = Some W_a11c0.
Proof. vm_refl. Qed.
Lemma D_a11c0 : decode_any W_a11c0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11c4 : bv 32 := 0x1c068a63.
Lemma F_a11c4 : fetch_word Asan.M.loaded_segments (0xa1214 : word) = Some W_a11c4.
Proof. vm_refl. Qed.
Lemma D_a11c4 : decode_any W_a11c4 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11c8 : bv 32 := 0x1c058863.
Lemma F_a11c8 : fetch_word Asan.M.loaded_segments (0xa1218 : word) = Some W_a11c8.
Proof. vm_refl. Qed.
Lemma D_a11c8 : decode_any W_a11c8 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11cc : bv 32 := 0x02065693.
Lemma F_a11cc : fetch_word Asan.M.loaded_segments (0xa121c : word) = Some W_a11cc.
Proof. vm_refl. Qed.
Lemma D_a11cc : decode_any W_a11cc = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11d0 : bv 32 := 0xfff00513.
Lemma F_a11d0 : fetch_word Asan.M.loaded_segments (0xa1220 : word) = Some W_a11d0.
Proof. vm_refl. Qed.
Lemma D_a11d0 : decode_any W_a11d0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11d4 : bv 32 := 0xfff6f717.
Lemma F_a11d4 : fetch_word Asan.M.loaded_segments (0xa1224 : word) = Some W_a11d4.
Proof. vm_refl. Qed.
Lemma D_a11d4 : decode_any W_a11d4 = Some (Auipc 14 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11d8 : bv 32 := 0xfff6f797.
Lemma F_a11d8 : fetch_word Asan.M.loaded_segments (0xa1228 : word) = Some W_a11d8.
Proof. vm_refl. Qed.
Lemma D_a11d8 : decode_any W_a11d8 = Some (Auipc 15 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11dc : bv 32 := 0x02055513.
Lemma F_a11dc : fetch_word Asan.M.loaded_segments (0xa122c : word) = Some W_a11dc.
Proof. vm_refl. Qed.
Lemma D_a11dc : decode_any W_a11dc = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11e0 : bv 32 := 0x1007b783.
Lemma F_a11e0 : fetch_word Asan.M.loaded_segments (0xa1230 : word) = Some W_a11e0.
Proof. vm_refl. Qed.
Lemma D_a11e0 : decode_any W_a11e0 = Some (Load SZ8 true 15 15 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11e4 : bv 32 := 0x00a67633.
Lemma F_a11e4 : fetch_word Asan.M.loaded_segments (0xa1234 : word) = Some W_a11e4.
Proof. vm_refl. Qed.
Lemma D_a11e4 : decode_any W_a11e4 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11e8 : bv 32 := 0xfff6f517.
Lemma F_a11e8 : fetch_word Asan.M.loaded_segments (0xa1238 : word) = Some W_a11e8.
Proof. vm_refl. Qed.
Lemma D_a11e8 : decode_any W_a11e8 = Some (Auipc 10 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11ec : bv 32 := 0x20053803.
Lemma F_a11ec : fetch_word Asan.M.loaded_segments (0xa123c : word) = Some W_a11ec.
Proof. vm_refl. Qed.
Lemma D_a11ec : decode_any W_a11ec = Some (Load SZ8 true 16 10 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11f0 : bv 32 := 0x0c473503.
Lemma F_a11f0 : fetch_word Asan.M.loaded_segments (0xa1240 : word) = Some W_a11f0.
Proof. vm_refl. Qed.
Lemma D_a11f0 : decode_any W_a11f0 = Some (Load SZ8 true 10 14 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11f4 : bv 32 := 0x02f60733.
Lemma F_a11f4 : fetch_word Asan.M.loaded_segments (0xa1244 : word) = Some W_a11f4.
Proof. vm_refl. Qed.
Lemma D_a11f4 : decode_any W_a11f4 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11f8 : bv 32 := 0x00361793.
Lemma F_a11f8 : fetch_word Asan.M.loaded_segments (0xa1248 : word) = Some W_a11f8.
Proof. vm_refl. Qed.
Lemma D_a11f8 : decode_any W_a11f8 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a11fc : bv 32 := 0x01074633.
Lemma F_a11fc : fetch_word Asan.M.loaded_segments (0xa124c : word) = Some W_a11fc.
Proof. vm_refl. Qed.
Lemma D_a11fc : decode_any W_a11fc = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1200 : bv 32 := 0x00f58733.
Lemma F_a1200 : fetch_word Asan.M.loaded_segments (0xa1250 : word) = Some W_a1200.
Proof. vm_refl. Qed.
Lemma D_a1200 : decode_any W_a1200 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1204 : bv 32 := 0x0005b783.
Lemma F_a1204 : fetch_word Asan.M.loaded_segments (0xa1254 : word) = Some W_a1204.
Proof. vm_refl. Qed.
Lemma D_a1204 : decode_any W_a1204 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1208 : bv 32 := 0x00858593.
Lemma F_a1208 : fetch_word Asan.M.loaded_segments (0xa1258 : word) = Some W_a1208.
Proof. vm_refl. Qed.
Lemma D_a1208 : decode_any W_a1208 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a120c : bv 32 := 0x02a787b3.
Lemma F_a120c : fetch_word Asan.M.loaded_segments (0xa125c : word) = Some W_a120c.
Proof. vm_refl. Qed.
Lemma D_a120c : decode_any W_a120c = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1210 : bv 32 := 0x02f7d813.
Lemma F_a1210 : fetch_word Asan.M.loaded_segments (0xa1260 : word) = Some W_a1210.
Proof. vm_refl. Qed.
Lemma D_a1210 : decode_any W_a1210 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1214 : bv 32 := 0x00f847b3.
Lemma F_a1214 : fetch_word Asan.M.loaded_segments (0xa1264 : word) = Some W_a1214.
Proof. vm_refl. Qed.
Lemma D_a1214 : decode_any W_a1214 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1218 : bv 32 := 0x02a787b3.
Lemma F_a1218 : fetch_word Asan.M.loaded_segments (0xa1268 : word) = Some W_a1218.
Proof. vm_refl. Qed.
Lemma D_a1218 : decode_any W_a1218 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a121c : bv 32 := 0x00c7c633.
Lemma F_a121c : fetch_word Asan.M.loaded_segments (0xa126c : word) = Some W_a121c.
Proof. vm_refl. Qed.
Lemma D_a121c : decode_any W_a121c = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1220 : bv 32 := 0x02a60633.
Lemma F_a1220 : fetch_word Asan.M.loaded_segments (0xa1270 : word) = Some W_a1220.
Proof. vm_refl. Qed.
Lemma D_a1220 : decode_any W_a1220 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1224 : bv 32 := 0xfee590e3.
Lemma F_a1224 : fetch_word Asan.M.loaded_segments (0xa1274 : word) = Some W_a1224.
Proof. vm_refl. Qed.
Lemma D_a1224 : decode_any W_a1224 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1228 : bv 32 := 0x00010b37.
Lemma F_a1228 : fetch_word Asan.M.loaded_segments (0xa1278 : word) = Some W_a1228.
Proof. vm_refl. Qed.
Lemma D_a1228 : decode_any W_a1228 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a122c : bv 32 := 0x80000bb7.
Lemma F_a122c : fetch_word Asan.M.loaded_segments (0xa127c : word) = Some W_a122c.
Proof. vm_refl. Qed.
Lemma D_a122c : decode_any W_a122c = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1230 : bv 32 := 0x02a685b3.
Lemma F_a1230 : fetch_word Asan.M.loaded_segments (0xa1280 : word) = Some W_a1230.
Proof. vm_refl. Qed.
Lemma D_a1230 : decode_any W_a1230 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1234 : bv 32 := 0x004006b7.
Lemma F_a1234 : fetch_word Asan.M.loaded_segments (0xa1284 : word) = Some W_a1234.
Proof. vm_refl. Qed.
Lemma D_a1234 : decode_any W_a1234 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1238 : bv 32 := 0xfffb0b1b.
Lemma F_a1238 : fetch_word Asan.M.loaded_segments (0xa1288 : word) = Some W_a1238.
Proof. vm_refl. Qed.
Lemma D_a1238 : decode_any W_a1238 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a123c : bv 32 := 0xfffb8b9b.
Lemma F_a123c : fetch_word Asan.M.loaded_segments (0xa128c : word) = Some W_a123c.
Proof. vm_refl. Qed.
Lemma D_a123c : decode_any W_a123c = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1240 : bv 32 := 0x02f5d713.
Lemma F_a1240 : fetch_word Asan.M.loaded_segments (0xa1290 : word) = Some W_a1240.
Proof. vm_refl. Qed.
Lemma D_a1240 : decode_any W_a1240 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1244 : bv 32 := 0x00b745b3.
Lemma F_a1244 : fetch_word Asan.M.loaded_segments (0xa1294 : word) = Some W_a1244.
Proof. vm_refl. Qed.
Lemma D_a1244 : decode_any W_a1244 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1248 : bv 32 := 0x02a585b3.
Lemma F_a1248 : fetch_word Asan.M.loaded_segments (0xa1298 : word) = Some W_a1248.
Proof. vm_refl. Qed.
Lemma D_a1248 : decode_any W_a1248 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a124c : bv 32 := 0x00c5c5b3.
Lemma F_a124c : fetch_word Asan.M.loaded_segments (0xa129c : word) = Some W_a124c.
Proof. vm_refl. Qed.
Lemma D_a124c : decode_any W_a124c = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1250 : bv 32 := 0x02a585b3.
Lemma F_a1250 : fetch_word Asan.M.loaded_segments (0xa12a0 : word) = Some W_a1250.
Proof. vm_refl. Qed.
Lemma D_a1250 : decode_any W_a1250 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1254 : bv 32 := 0x02f5d613.
Lemma F_a1254 : fetch_word Asan.M.loaded_segments (0xa12a4 : word) = Some W_a1254.
Proof. vm_refl. Qed.
Lemma D_a1254 : decode_any W_a1254 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1258 : bv 32 := 0x00b645b3.
Lemma F_a1258 : fetch_word Asan.M.loaded_segments (0xa12a8 : word) = Some W_a1258.
Proof. vm_refl. Qed.
Lemma D_a1258 : decode_any W_a1258 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a125c : bv 32 := 0x02a58533.
Lemma F_a125c : fetch_word Asan.M.loaded_segments (0xa12ac : word) = Some W_a125c.
Proof. vm_refl. Qed.
Lemma D_a125c : decode_any W_a125c = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1260 : bv 32 := 0x02f55593.
Lemma F_a1260 : fetch_word Asan.M.loaded_segments (0xa12b0 : word) = Some W_a1260.
Proof. vm_refl. Qed.
Lemma D_a1260 : decode_any W_a1260 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1264 : bv 32 := 0x00a5c9b3.
Lemma F_a1264 : fetch_word Asan.M.loaded_segments (0xa12b4 : word) = Some W_a1264.
Proof. vm_refl. Qed.
Lemma D_a1264 : decode_any W_a1264 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1268 : bv 32 := 0x02c99513.
Lemma F_a1268 : fetch_word Asan.M.loaded_segments (0xa12b8 : word) = Some W_a1268.
Proof. vm_refl. Qed.
Lemma D_a1268 : decode_any W_a1268 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a126c : bv 32 := 0x02a55513.
Lemma F_a126c : fetch_word Asan.M.loaded_segments (0xa12bc : word) = Some W_a126c.
Proof. vm_refl. Qed.
Lemma D_a126c : decode_any W_a126c = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1270 : bv 32 := 0x00a48933.
Lemma F_a1270 : fetch_word Asan.M.loaded_segments (0xa12c0 : word) = Some W_a1270.
Proof. vm_refl. Qed.
Lemma D_a1270 : decode_any W_a1270 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1274 : bv 32 := 0x00092503.
Lemma F_a1274 : fetch_word Asan.M.loaded_segments (0xa12c4 : word) = Some W_a1274.
Proof. vm_refl. Qed.
Lemma D_a1274 : decode_any W_a1274 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1278 : bv 32 := 0x01068c1b.
Lemma F_a1278 : fetch_word Asan.M.loaded_segments (0xa12c8 : word) = Some W_a1278.
Proof. vm_refl. Qed.
Lemma D_a1278 : decode_any W_a1278 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a127c : bv 32 := 0x01848c33.
Lemma F_a127c : fetch_word Asan.M.loaded_segments (0xa12cc : word) = Some W_a127c.
Proof. vm_refl. Qed.
Lemma D_a127c : decode_any W_a127c = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1280 : bv 32 := 0x0230000f.
Lemma F_a1280 : fetch_word Asan.M.loaded_segments (0xa12d0 : word) = Some W_a1280.
Proof. vm_refl. Qed.
Lemma D_a1280 : decode_any W_a1280 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1284 : bv 32 := 0x01757cb3.
Lemma F_a1284 : fetch_word Asan.M.loaded_segments (0xa12d4 : word) = Some W_a1284.
Proof. vm_refl. Qed.
Lemma D_a1284 : decode_any W_a1284 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1288 : bv 32 := 0x0086869b.
Lemma F_a1288 : fetch_word Asan.M.loaded_segments (0xa12d8 : word) = Some W_a1288.
Proof. vm_refl. Qed.
Lemma D_a1288 : decode_any W_a1288 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a128c : bv 32 := 0x00d48a33.
Lemma F_a128c : fetch_word Asan.M.loaded_segments (0xa12dc : word) = Some W_a128c.
Proof. vm_refl. Qed.
Lemma D_a128c : decode_any W_a128c = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1290 : bv 32 := 0x000c8593.
Lemma F_a1290 : fetch_word Asan.M.loaded_segments (0xa12e0 : word) = Some W_a1290.
Proof. vm_refl. Qed.
Lemma D_a1290 : decode_any W_a1290 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1294 : bv 32 := 0x04058c63.
Lemma F_a1294 : fetch_word Asan.M.loaded_segments (0xa12e4 : word) = Some W_a1294.
Proof. vm_refl. Qed.
Lemma D_a1294 : decode_any W_a1294 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1298 : bv 32 := 0x00058513.
Lemma F_a1298 : fetch_word Asan.M.loaded_segments (0xa12e8 : word) = Some W_a1298.
Proof. vm_refl. Qed.
Lemma D_a1298 : decode_any W_a1298 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a129c : bv 32 := 0x0105d59b.
Lemma F_a129c : fetch_word Asan.M.loaded_segments (0xa12ec : word) = Some W_a129c.
Proof. vm_refl. Qed.
Lemma D_a129c : decode_any W_a129c = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a0 : bv 32 := 0x00359613.
Lemma F_a12a0 : fetch_word Asan.M.loaded_segments (0xa12f0 : word) = Some W_a12a0.
Proof. vm_refl. Qed.
Lemma D_a12a0 : decode_any W_a12a0 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a4 : bv 32 := 0x00cc0633.
Lemma F_a12a4 : fetch_word Asan.M.loaded_segments (0xa12f4 : word) = Some W_a12a4.
Proof. vm_refl. Qed.
Lemma D_a12a4 : decode_any W_a12a4 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a8 : bv 32 := 0x00063603.
Lemma F_a12a8 : fetch_word Asan.M.loaded_segments (0xa12f8 : word) = Some W_a12a8.
Proof. vm_refl. Qed.
Lemma D_a12a8 : decode_any W_a12a8 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12ac : bv 32 := 0x02060463.
Lemma F_a12ac : fetch_word Asan.M.loaded_segments (0xa12fc : word) = Some W_a12ac.
Proof. vm_refl. Qed.
Lemma D_a12ac : decode_any W_a12ac = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b0 : bv 32 := 0x02051593.
Lemma F_a12b0 : fetch_word Asan.M.loaded_segments (0xa1300 : word) = Some W_a12b0.
Proof. vm_refl. Qed.
Lemma D_a12b0 : decode_any W_a12b0 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b4 : bv 32 := 0x0205d593.
Lemma F_a12b4 : fetch_word Asan.M.loaded_segments (0xa1304 : word) = Some W_a12b4.
Proof. vm_refl. Qed.
Lemma D_a12b4 : decode_any W_a12b4 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b8 : bv 32 := 0x0165f5b3.
Lemma F_a12b8 : fetch_word Asan.M.loaded_segments (0xa1308 : word) = Some W_a12b8.
Proof. vm_refl. Qed.
Lemma D_a12b8 : decode_any W_a12b8 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12bc : bv 32 := 0x00459593.
Lemma F_a12bc : fetch_word Asan.M.loaded_segments (0xa130c : word) = Some W_a12bc.
Proof. vm_refl. Qed.
Lemma D_a12bc : decode_any W_a12bc = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c0 : bv 32 := 0x00b605b3.
Lemma F_a12c0 : fetch_word Asan.M.loaded_segments (0xa1310 : word) = Some W_a12c0.
Proof. vm_refl. Qed.
Lemma D_a12c0 : decode_any W_a12c0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c4 : bv 32 := 0x0005b603.
Lemma F_a12c4 : fetch_word Asan.M.loaded_segments (0xa1314 : word) = Some W_a12c4.
Proof. vm_refl. Qed.
Lemma D_a12c4 : decode_any W_a12c4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c8 : bv 32 := 0x0085a583.
Lemma F_a12c8 : fetch_word Asan.M.loaded_segments (0xa1318 : word) = Some W_a12c8.
Proof. vm_refl. Qed.
Lemma D_a12c8 : decode_any W_a12c8 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12cc : bv 32 := 0xfcc994e3.
Lemma F_a12cc : fetch_word Asan.M.loaded_segments (0xa131c : word) = Some W_a12cc.
Proof. vm_refl. Qed.
Lemma D_a12cc : decode_any W_a12cc = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12d0 : bv 32 := 0x0c80006f.
Lemma F_a12d0 : fetch_word Asan.M.loaded_segments (0xa1320 : word) = Some W_a12d0.
Proof. vm_refl. Qed.
Lemma D_a12d0 : decode_any W_a12d0 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12ec : bv 32 := 0x00090513.
Lemma F_a12ec : fetch_word Asan.M.loaded_segments (0xa133c : word) = Some W_a12ec.
Proof. vm_refl. Qed.
Lemma D_a12ec : decode_any W_a12ec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f0 : bv 32 := 0x5f8000ef.
Lemma F_a12f0 : fetch_word Asan.M.loaded_segments (0xa1340 : word) = Some W_a12f0.
Proof. vm_refl. Qed.
Lemma D_a12f0 : decode_any W_a12f0 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f4 : bv 32 := 0x00050a93.
Lemma F_a12f4 : fetch_word Asan.M.loaded_segments (0xa1344 : word) = Some W_a12f4.
Proof. vm_refl. Qed.
Lemma D_a12f4 : decode_any W_a12f4 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f8 : bv 32 := 0x03950663.
Lemma F_a12f8 : fetch_word Asan.M.loaded_segments (0xa1348 : word) = Some W_a12f8.
Proof. vm_refl. Qed.
Lemma D_a12f8 : decode_any W_a12f8 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1324 : bv 32 := 0x00400537.
Lemma F_a1324 : fetch_word Asan.M.loaded_segments (0xa1374 : word) = Some W_a1324.
Proof. vm_refl. Qed.
Lemma D_a1324 : decode_any W_a1324 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1328 : bv 32 := 0x00a48533.
Lemma F_a1328 : fetch_word Asan.M.loaded_segments (0xa1378 : word) = Some W_a1328.
Proof. vm_refl. Qed.
Lemma D_a1328 : decode_any W_a1328 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a132c : bv 32 := 0x00100593.
Lemma F_a132c : fetch_word Asan.M.loaded_segments (0xa137c : word) = Some W_a132c.
Proof. vm_refl. Qed.
Lemma D_a132c : decode_any W_a132c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1330 : bv 32 := 0x00b5252f.
Lemma F_a1330 : fetch_word Asan.M.loaded_segments (0xa1380 : word) = Some W_a1330.
Proof. vm_refl. Qed.
Lemma D_a1330 : decode_any W_a1330 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1334 : bv 32 := 0x0015051b.
Lemma F_a1334 : fetch_word Asan.M.loaded_segments (0xa1384 : word) = Some W_a1334.
Proof. vm_refl. Qed.
Lemma D_a1334 : decode_any W_a1334 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1338 : bv 32 := 0x02051493.
Lemma F_a1338 : fetch_word Asan.M.loaded_segments (0xa1388 : word) = Some W_a1338.
Proof. vm_refl. Qed.
Lemma D_a1338 : decode_any W_a1338 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a133c : bv 32 := 0x0204d493.
Lemma F_a133c : fetch_word Asan.M.loaded_segments (0xa138c : word) = Some W_a133c.
Proof. vm_refl. Qed.
Lemma D_a133c : decode_any W_a133c = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1340 : bv 32 := 0x08054663.
Lemma F_a1340 : fetch_word Asan.M.loaded_segments (0xa1390 : word) = Some W_a1340.
Proof. vm_refl. Qed.
Lemma D_a1340 : decode_any W_a1340 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1344 : bv 32 := 0x00050b93.
Lemma F_a1344 : fetch_word Asan.M.loaded_segments (0xa1394 : word) = Some W_a1344.
Proof. vm_refl. Qed.
Lemma D_a1344 : decode_any W_a1344 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1348 : bv 32 := 0x0104d593.
Lemma F_a1348 : fetch_word Asan.M.loaded_segments (0xa1398 : word) = Some W_a1348.
Proof. vm_refl. Qed.
Lemma D_a1348 : decode_any W_a1348 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a134c : bv 32 := 0x00359513.
Lemma F_a134c : fetch_word Asan.M.loaded_segments (0xa139c : word) = Some W_a134c.
Proof. vm_refl. Qed.
Lemma D_a134c : decode_any W_a134c = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1350 : bv 32 := 0x00ac0533.
Lemma F_a1350 : fetch_word Asan.M.loaded_segments (0xa13a0 : word) = Some W_a1350.
Proof. vm_refl. Qed.
Lemma D_a1350 : decode_any W_a1350 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1354 : bv 32 := 0x00053503.
Lemma F_a1354 : fetch_word Asan.M.loaded_segments (0xa13a4 : word) = Some W_a1354.
Proof. vm_refl. Qed.
Lemma D_a1354 : decode_any W_a1354 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1358 : bv 32 := 0x08050a63.
Lemma F_a1358 : fetch_word Asan.M.loaded_segments (0xa13a8 : word) = Some W_a1358.
Proof. vm_refl. Qed.
Lemma D_a1358 : decode_any W_a1358 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_a135c : bv 32 := 0x0164f5b3.
Lemma F_a135c : fetch_word Asan.M.loaded_segments (0xa13ac : word) = Some W_a135c.
Proof. vm_refl. Qed.
Lemma D_a135c : decode_any W_a135c = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1360 : bv 32 := 0x00459593.
Lemma F_a1360 : fetch_word Asan.M.loaded_segments (0xa13b0 : word) = Some W_a1360.
Proof. vm_refl. Qed.
Lemma D_a1360 : decode_any W_a1360 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1364 : bv 32 := 0x00b504b3.
Lemma F_a1364 : fetch_word Asan.M.loaded_segments (0xa13b4 : word) = Some W_a1364.
Proof. vm_refl. Qed.
Lemma D_a1364 : decode_any W_a1364 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1368 : bv 32 := 0x00810613.
Lemma F_a1368 : fetch_word Asan.M.loaded_segments (0xa13b8 : word) = Some W_a1368.
Proof. vm_refl. Qed.
Lemma D_a1368 : decode_any W_a1368 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a136c : bv 32 := 0x00048513.
Lemma F_a136c : fetch_word Asan.M.loaded_segments (0xa13bc : word) = Some W_a136c.
Proof. vm_refl. Qed.
Lemma D_a136c : decode_any W_a136c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1370 : bv 32 := 0x00000593.
Lemma F_a1370 : fetch_word Asan.M.loaded_segments (0xa13c0 : word) = Some W_a1370.
Proof. vm_refl. Qed.
Lemma D_a1370 : decode_any W_a1370 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1374 : bv 32 := 0x00098693.
Lemma F_a1374 : fetch_word Asan.M.loaded_segments (0xa13c4 : word) = Some W_a1374.
Proof. vm_refl. Qed.
Lemma D_a1374 : decode_any W_a1374 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1378 : bv 32 := 0xaf5ff0ef.
Lemma F_a1378 : fetch_word Asan.M.loaded_segments (0xa13c8 : word) = Some W_a1378.
Proof. vm_refl. Qed.
Lemma D_a1378 : decode_any W_a1378 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_a137c : bv 32 := 0x0154a423.
Lemma F_a137c : fetch_word Asan.M.loaded_segments (0xa13cc : word) = Some W_a137c.
Proof. vm_refl. Qed.
Lemma D_a137c : decode_any W_a137c = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1380 : bv 32 := 0x0310000f.
Lemma F_a1380 : fetch_word Asan.M.loaded_segments (0xa13d0 : word) = Some W_a1380.
Proof. vm_refl. Qed.
Lemma D_a1380 : decode_any W_a1380 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1384 : bv 32 := 0x000b8513.
Lemma F_a1384 : fetch_word Asan.M.loaded_segments (0xa13d4 : word) = Some W_a1384.
Proof. vm_refl. Qed.
Lemma D_a1384 : decode_any W_a1384 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1388 : bv 32 := 0x01792023.
Lemma F_a1388 : fetch_word Asan.M.loaded_segments (0xa13d8 : word) = Some W_a1388.
Proof. vm_refl. Qed.
Lemma D_a1388 : decode_any W_a1388 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a138c : bv 32 := 0x00040663.
Lemma F_a138c : fetch_word Asan.M.loaded_segments (0xa13dc : word) = Some W_a138c.
Proof. vm_refl. Qed.
Lemma D_a138c : decode_any W_a138c = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1398 : bv 32 := 0x06813083.
Lemma F_a1398 : fetch_word Asan.M.loaded_segments (0xa13e8 : word) = Some W_a1398.
Proof. vm_refl. Qed.
Lemma D_a1398 : decode_any W_a1398 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a139c : bv 32 := 0x06013403.
Lemma F_a139c : fetch_word Asan.M.loaded_segments (0xa13ec : word) = Some W_a139c.
Proof. vm_refl. Qed.
Lemma D_a139c : decode_any W_a139c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13a0 : bv 32 := 0x05813483.
Lemma F_a13a0 : fetch_word Asan.M.loaded_segments (0xa13f0 : word) = Some W_a13a0.
Proof. vm_refl. Qed.
Lemma D_a13a0 : decode_any W_a13a0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13a4 : bv 32 := 0x05013903.
Lemma F_a13a4 : fetch_word Asan.M.loaded_segments (0xa13f4 : word) = Some W_a13a4.
Proof. vm_refl. Qed.
Lemma D_a13a4 : decode_any W_a13a4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13a8 : bv 32 := 0x04813983.
Lemma F_a13a8 : fetch_word Asan.M.loaded_segments (0xa13f8 : word) = Some W_a13a8.
Proof. vm_refl. Qed.
Lemma D_a13a8 : decode_any W_a13a8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13ac : bv 32 := 0x04013a03.
Lemma F_a13ac : fetch_word Asan.M.loaded_segments (0xa13fc : word) = Some W_a13ac.
Proof. vm_refl. Qed.
Lemma D_a13ac : decode_any W_a13ac = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13b0 : bv 32 := 0x03813a83.
Lemma F_a13b0 : fetch_word Asan.M.loaded_segments (0xa1400 : word) = Some W_a13b0.
Proof. vm_refl. Qed.
Lemma D_a13b0 : decode_any W_a13b0 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13b4 : bv 32 := 0x03013b03.
Lemma F_a13b4 : fetch_word Asan.M.loaded_segments (0xa1404 : word) = Some W_a13b4.
Proof. vm_refl. Qed.
Lemma D_a13b4 : decode_any W_a13b4 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13b8 : bv 32 := 0x02813b83.
Lemma F_a13b8 : fetch_word Asan.M.loaded_segments (0xa1408 : word) = Some W_a13b8.
Proof. vm_refl. Qed.
Lemma D_a13b8 : decode_any W_a13b8 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13bc : bv 32 := 0x02013c03.
Lemma F_a13bc : fetch_word Asan.M.loaded_segments (0xa140c : word) = Some W_a13bc.
Proof. vm_refl. Qed.
Lemma D_a13bc : decode_any W_a13bc = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13c0 : bv 32 := 0x01813c83.
Lemma F_a13c0 : fetch_word Asan.M.loaded_segments (0xa1410 : word) = Some W_a13c0.
Proof. vm_refl. Qed.
Lemma D_a13c0 : decode_any W_a13c0 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13c4 : bv 32 := 0x07010113.
Lemma F_a13c4 : fetch_word Asan.M.loaded_segments (0xa1414 : word) = Some W_a13c4.
Proof. vm_refl. Qed.
Lemma D_a13c4 : decode_any W_a13c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a13c8 : bv 32 := 0x00008067.
Lemma F_a13c8 : fetch_word Asan.M.loaded_segments (0xa1418 : word) = Some W_a13c8.
Proof. vm_refl. Qed.
Lemma D_a13c8 : decode_any W_a13c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18e8 : bv 32 := 0xfd010113.
Lemma F_a18e8 : fetch_word Asan.M.loaded_segments (0xa1938 : word) = Some W_a18e8.
Proof. vm_refl. Qed.
Lemma D_a18e8 : decode_any W_a18e8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18ec : bv 32 := 0x02113423.
Lemma F_a18ec : fetch_word Asan.M.loaded_segments (0xa193c : word) = Some W_a18ec.
Proof. vm_refl. Qed.
Lemma D_a18ec : decode_any W_a18ec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f0 : bv 32 := 0x02813023.
Lemma F_a18f0 : fetch_word Asan.M.loaded_segments (0xa1940 : word) = Some W_a18f0.
Proof. vm_refl. Qed.
Lemma D_a18f0 : decode_any W_a18f0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f4 : bv 32 := 0x00913c23.
Lemma F_a18f4 : fetch_word Asan.M.loaded_segments (0xa1944 : word) = Some W_a18f4.
Proof. vm_refl. Qed.
Lemma D_a18f4 : decode_any W_a18f4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f8 : bv 32 := 0x01213823.
Lemma F_a18f8 : fetch_word Asan.M.loaded_segments (0xa1948 : word) = Some W_a18f8.
Proof. vm_refl. Qed.
Lemma D_a18f8 : decode_any W_a18f8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18fc : bv 32 := 0x01313423.
Lemma F_a18fc : fetch_word Asan.M.loaded_segments (0xa194c : word) = Some W_a18fc.
Proof. vm_refl. Qed.
Lemma D_a18fc : decode_any W_a18fc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1900 : bv 32 := 0x00050413.
Lemma F_a1900 : fetch_word Asan.M.loaded_segments (0xa1950 : word) = Some W_a1900.
Proof. vm_refl. Qed.
Lemma D_a1900 : decode_any W_a1900 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1904 : bv 32 := 0x00000593.
Lemma F_a1904 : fetch_word Asan.M.loaded_segments (0xa1954 : word) = Some W_a1904.
Proof. vm_refl. Qed.
Lemma D_a1904 : decode_any W_a1904 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1908 : bv 32 := 0x800004b7.
Lemma F_a1908 : fetch_word Asan.M.loaded_segments (0xa1958 : word) = Some W_a1908.
Proof. vm_refl. Qed.
Lemma D_a1908 : decode_any W_a1908 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a190c : bv 32 := 0x00900913.
Lemma F_a190c : fetch_word Asan.M.loaded_segments (0xa195c : word) = Some W_a190c.
Proof. vm_refl. Qed.
Lemma D_a190c : decode_any W_a190c = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1910 : bv 32 := 0x00052503.
Lemma F_a1910 : fetch_word Asan.M.loaded_segments (0xa1960 : word) = Some W_a1910.
Proof. vm_refl. Qed.
Lemma D_a1910 : decode_any W_a1910 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1914 : bv 32 := 0x00055a63.
Lemma F_a1914 : fetch_word Asan.M.loaded_segments (0xa1964 : word) = Some W_a1914.
Proof. vm_refl. Qed.
Lemma D_a1914 : decode_any W_a1914 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1928 : bv 32 := 0x00956633.
Lemma F_a1928 : fetch_word Asan.M.loaded_segments (0xa1978 : word) = Some W_a1928.
Proof. vm_refl. Qed.
Lemma D_a1928 : decode_any W_a1928 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a192c : bv 32 := 0x160426af.
Lemma F_a192c : fetch_word Asan.M.loaded_segments (0xa197c : word) = Some W_a192c.
Proof. vm_refl. Qed.
Lemma D_a192c : decode_any W_a192c = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1930 : bv 32 := 0x00a69663.
Lemma F_a1930 : fetch_word Asan.M.loaded_segments (0xa1980 : word) = Some W_a1930.
Proof. vm_refl. Qed.
Lemma D_a1930 : decode_any W_a1930 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1934 : bv 32 := 0x1ac4272f.
Lemma F_a1934 : fetch_word Asan.M.loaded_segments (0xa1984 : word) = Some W_a1934.
Proof. vm_refl. Qed.
Lemma D_a1934 : decode_any W_a1934 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1938 : bv 32 := 0xfe071ae3.
Lemma F_a1938 : fetch_word Asan.M.loaded_segments (0xa1988 : word) = Some W_a1938.
Proof. vm_refl. Qed.
Lemma D_a1938 : decode_any W_a1938 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a193c : bv 32 := 0x02a68063.
Lemma F_a193c : fetch_word Asan.M.loaded_segments (0xa198c : word) = Some W_a193c.
Proof. vm_refl. Qed.
Lemma D_a193c : decode_any W_a193c = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a195c : bv 32 := 0x02813083.
Lemma F_a195c : fetch_word Asan.M.loaded_segments (0xa19ac : word) = Some W_a195c.
Proof. vm_refl. Qed.
Lemma D_a195c : decode_any W_a195c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1960 : bv 32 := 0x02013403.
Lemma F_a1960 : fetch_word Asan.M.loaded_segments (0xa19b0 : word) = Some W_a1960.
Proof. vm_refl. Qed.
Lemma D_a1960 : decode_any W_a1960 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1964 : bv 32 := 0x01813483.
Lemma F_a1964 : fetch_word Asan.M.loaded_segments (0xa19b4 : word) = Some W_a1964.
Proof. vm_refl. Qed.
Lemma D_a1964 : decode_any W_a1964 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1968 : bv 32 := 0x01013903.
Lemma F_a1968 : fetch_word Asan.M.loaded_segments (0xa19b8 : word) = Some W_a1968.
Proof. vm_refl. Qed.
Lemma D_a1968 : decode_any W_a1968 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a196c : bv 32 := 0x00813983.
Lemma F_a196c : fetch_word Asan.M.loaded_segments (0xa19bc : word) = Some W_a196c.
Proof. vm_refl. Qed.
Lemma D_a196c : decode_any W_a196c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1970 : bv 32 := 0x03010113.
Lemma F_a1970 : fetch_word Asan.M.loaded_segments (0xa19c0 : word) = Some W_a1970.
Proof. vm_refl. Qed.
Lemma D_a1970 : decode_any W_a1970 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1974 : bv 32 := 0x00008067.
Lemma F_a1974 : fetch_word Asan.M.loaded_segments (0xa19c4 : word) = Some W_a1974.
Proof. vm_refl. Qed.
Lemma D_a1974 : decode_any W_a1974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ad8 : bv 32 := 0x00008513.
Lemma F_a1ad8 : fetch_word Asan.M.loaded_segments (0xa1b28 : word) = Some W_a1ad8.
Proof. vm_refl. Qed.
Lemma D_a1ad8 : decode_any W_a1ad8 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1adc : bv 32 := 0x00008067.
Lemma F_a1adc : fetch_word Asan.M.loaded_segments (0xa1b2c : word) = Some W_a1adc.
Proof. vm_refl. Qed.
Lemma D_a1adc : decode_any W_a1adc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ae0 : bv 32 := 0xfc010113.
Lemma F_a1ae0 : fetch_word Asan.M.loaded_segments (0xa1b30 : word) = Some W_a1ae0.
Proof. vm_refl. Qed.
Lemma D_a1ae0 : decode_any W_a1ae0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ae4 : bv 32 := 0x02113c23.
Lemma F_a1ae4 : fetch_word Asan.M.loaded_segments (0xa1b34 : word) = Some W_a1ae4.
Proof. vm_refl. Qed.
Lemma D_a1ae4 : decode_any W_a1ae4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ae8 : bv 32 := 0x02813823.
Lemma F_a1ae8 : fetch_word Asan.M.loaded_segments (0xa1b38 : word) = Some W_a1ae8.
Proof. vm_refl. Qed.
Lemma D_a1ae8 : decode_any W_a1ae8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1aec : bv 32 := 0x02913423.
Lemma F_a1aec : fetch_word Asan.M.loaded_segments (0xa1b3c : word) = Some W_a1aec.
Proof. vm_refl. Qed.
Lemma D_a1aec : decode_any W_a1aec = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1af0 : bv 32 := 0x03213023.
Lemma F_a1af0 : fetch_word Asan.M.loaded_segments (0xa1b40 : word) = Some W_a1af0.
Proof. vm_refl. Qed.
Lemma D_a1af0 : decode_any W_a1af0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1af4 : bv 32 := 0x01313c23.
Lemma F_a1af4 : fetch_word Asan.M.loaded_segments (0xa1b44 : word) = Some W_a1af4.
Proof. vm_refl. Qed.
Lemma D_a1af4 : decode_any W_a1af4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1af8 : bv 32 := 0x01413823.
Lemma F_a1af8 : fetch_word Asan.M.loaded_segments (0xa1b48 : word) = Some W_a1af8.
Proof. vm_refl. Qed.
Lemma D_a1af8 : decode_any W_a1af8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1afc : bv 32 := 0x01513423.
Lemma F_a1afc : fetch_word Asan.M.loaded_segments (0xa1b4c : word) = Some W_a1afc.
Proof. vm_refl. Qed.
Lemma D_a1afc : decode_any W_a1afc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b00 : bv 32 := 0x01613023.
Lemma F_a1b00 : fetch_word Asan.M.loaded_segments (0xa1b50 : word) = Some W_a1b00.
Proof. vm_refl. Qed.
Lemma D_a1b00 : decode_any W_a1b00 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b04 : bv 32 := 0x00068493.
Lemma F_a1b04 : fetch_word Asan.M.loaded_segments (0xa1b54 : word) = Some W_a1b04.
Proof. vm_refl. Qed.
Lemma D_a1b04 : decode_any W_a1b04 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b08 : bv 32 := 0x02079413.
Lemma F_a1b08 : fetch_word Asan.M.loaded_segments (0xa1b58 : word) = Some W_a1b08.
Proof. vm_refl. Qed.
Lemma D_a1b08 : decode_any W_a1b08 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b0c : bv 32 := 0x00100693.
Lemma F_a1b0c : fetch_word Asan.M.loaded_segments (0xa1b5c : word) = Some W_a1b0c.
Proof. vm_refl. Qed.
Lemma D_a1b0c : decode_any W_a1b0c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b10 : bv 32 := 0x02045413.
Lemma F_a1b10 : fetch_word Asan.M.loaded_segments (0xa1b60 : word) = Some W_a1b10.
Proof. vm_refl. Qed.
Lemma D_a1b10 : decode_any W_a1b10 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b14 : bv 32 := 0x0ef6f863.
Lemma F_a1b14 : fetch_word Asan.M.loaded_segments (0xa1b64 : word) = Some W_a1b14.
Proof. vm_refl. Qed.
Lemma D_a1b14 : decode_any W_a1b14 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b18 : bv 32 := 0x000b1697.
Lemma F_a1b18 : fetch_word Asan.M.loaded_segments (0xa1b68 : word) = Some W_a1b18.
Proof. vm_refl. Qed.
Lemma D_a1b18 : decode_any W_a1b18 = Some (Auipc 13 177, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b1c : bv 32 := 0x5b06b903.
Lemma F_a1b1c : fetch_word Asan.M.loaded_segments (0xa1b6c : word) = Some W_a1b1c.
Proof. vm_refl. Qed.
Lemma D_a1b1c : decode_any W_a1b1c = Some (Load SZ8 true 18 13 1456, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b20 : bv 32 := 0x00093683.
Lemma F_a1b20 : fetch_word Asan.M.loaded_segments (0xa1b70 : word) = Some W_a1b20.
Proof. vm_refl. Qed.
Lemma D_a1b20 : decode_any W_a1b20 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b24 : bv 32 := 0x00068e63.
Lemma F_a1b24 : fetch_word Asan.M.loaded_segments (0xa1b74 : word) = Some W_a1b24.
Proof. vm_refl. Qed.
Lemma D_a1b24 : decode_any W_a1b24 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b28 : bv 32 := 0x00100793.
Lemma F_a1b28 : fetch_word Asan.M.loaded_segments (0xa1b78 : word) = Some W_a1b28.
Proof. vm_refl. Qed.
Lemma D_a1b28 : decode_any W_a1b28 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b2c : bv 32 := 0x00c4d813.
Lemma F_a1b2c : fetch_word Asan.M.loaded_segments (0xa1b7c : word) = Some W_a1b2c.
Proof. vm_refl. Qed.
Lemma D_a1b2c : decode_any W_a1b2c = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b30 : bv 32 := 0x00f52423.
Lemma F_a1b30 : fetch_word Asan.M.loaded_segments (0xa1b80 : word) = Some W_a1b30.
Proof. vm_refl. Qed.
Lemma D_a1b30 : decode_any W_a1b30 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b34 : bv 32 := 0x00b53823.
Lemma F_a1b34 : fetch_word Asan.M.loaded_segments (0xa1b84 : word) = Some W_a1b34.
Proof. vm_refl. Qed.
Lemma D_a1b34 : decode_any W_a1b34 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b38 : bv 32 := 0x04081463.
Lemma F_a1b38 : fetch_word Asan.M.loaded_segments (0xa1b88 : word) = Some W_a1b38.
Proof. vm_refl. Qed.
Lemma D_a1b38 : decode_any W_a1b38 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b80 : bv 32 := 0x0a977263.
Lemma F_a1b80 : fetch_word Asan.M.loaded_segments (0xa1bd0 : word) = Some W_a1b80.
Proof. vm_refl. Qed.
Lemma D_a1b80 : decode_any W_a1b80 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b84 : bv 32 := 0x04c77c63.
Lemma F_a1b84 : fetch_word Asan.M.loaded_segments (0xa1bd4 : word) = Some W_a1b84.
Proof. vm_refl. Qed.
Lemma D_a1b84 : decode_any W_a1b84 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b88 : bv 32 := 0xff048493.
Lemma F_a1b88 : fetch_word Asan.M.loaded_segments (0xa1bd8 : word) = Some W_a1b88.
Proof. vm_refl. Qed.
Lemma D_a1b88 : decode_any W_a1b88 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b8c : bv 32 := 0x04967863.
Lemma F_a1b8c : fetch_word Asan.M.loaded_segments (0xa1bdc : word) = Some W_a1b8c.
Proof. vm_refl. Qed.
Lemma D_a1b8c : decode_any W_a1b8c = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b90 : bv 32 := 0x00767713.
Lemma F_a1b90 : fetch_word Asan.M.loaded_segments (0xa1be0 : word) = Some W_a1b90.
Proof. vm_refl. Qed.
Lemma D_a1b90 : decode_any W_a1b90 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b94 : bv 32 := 0x04071463.
Lemma F_a1b94 : fetch_word Asan.M.loaded_segments (0xa1be4 : word) = Some W_a1b94.
Proof. vm_refl. Qed.
Lemma D_a1b94 : decode_any W_a1b94 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b98 : bv 32 := 0x01050713.
Lemma F_a1b98 : fetch_word Asan.M.loaded_segments (0xa1be8 : word) = Some W_a1b98.
Proof. vm_refl. Qed.
Lemma D_a1b98 : decode_any W_a1b98 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b9c : bv 32 := 0x00100793.
Lemma F_a1b9c : fetch_word Asan.M.loaded_segments (0xa1bec : word) = Some W_a1b9c.
Proof. vm_refl. Qed.
Lemma D_a1b9c : decode_any W_a1b9c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba0 : bv 32 := 0x0287fe63.
Lemma F_a1ba0 : fetch_word Asan.M.loaded_segments (0xa1bf0 : word) = Some W_a1ba0.
Proof. vm_refl. Qed.
Lemma D_a1ba0 : decode_any W_a1ba0 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba4 : bv 32 := 0xff863803.
Lemma F_a1ba4 : fetch_word Asan.M.loaded_segments (0xa1bf4 : word) = Some W_a1ba4.
Proof. vm_refl. Qed.
Lemma D_a1ba4 : decode_any W_a1ba4 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba8 : bv 32 := 0x02d86a63.
Lemma F_a1ba8 : fetch_word Asan.M.loaded_segments (0xa1bf8 : word) = Some W_a1ba8.
Proof. vm_refl. Qed.
Lemma D_a1ba8 : decode_any W_a1ba8 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bac : bv 32 := 0x00b80c63.
Lemma F_a1bac : fetch_word Asan.M.loaded_segments (0xa1bfc : word) = Some W_a1bac.
Proof. vm_refl. Qed.
Lemma D_a1bac : decode_any W_a1bac = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb0 : bv 32 := 0x00379893.
Lemma F_a1bb0 : fetch_word Asan.M.loaded_segments (0xa1c00 : word) = Some W_a1bb0.
Proof. vm_refl. Qed.
Lemma D_a1bb0 : decode_any W_a1bb0 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb4 : bv 32 := 0x00178793.
Lemma F_a1bb4 : fetch_word Asan.M.loaded_segments (0xa1c04 : word) = Some W_a1bb4.
Proof. vm_refl. Qed.
Lemma D_a1bb4 : decode_any W_a1bb4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb8 : bv 32 := 0x011708b3.
Lemma F_a1bb8 : fetch_word Asan.M.loaded_segments (0xa1c08 : word) = Some W_a1bb8.
Proof. vm_refl. Qed.
Lemma D_a1bb8 : decode_any W_a1bb8 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bbc : bv 32 := 0x00f52423.
Lemma F_a1bbc : fetch_word Asan.M.loaded_segments (0xa1c0c : word) = Some W_a1bbc.
Proof. vm_refl. Qed.
Lemma D_a1bbc : decode_any W_a1bbc = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc0 : bv 32 := 0x0108b023.
Lemma F_a1bc0 : fetch_word Asan.M.loaded_segments (0xa1c10 : word) = Some W_a1bc0.
Proof. vm_refl. Qed.
Lemma D_a1bc0 : decode_any W_a1bc0 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc4 : bv 32 := 0xff063803.
Lemma F_a1bc4 : fetch_word Asan.M.loaded_segments (0xa1c14 : word) = Some W_a1bc4.
Proof. vm_refl. Qed.
Lemma D_a1bc4 : decode_any W_a1bc4 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc8 : bv 32 := 0x01067a63.
Lemma F_a1bc8 : fetch_word Asan.M.loaded_segments (0xa1c18 : word) = Some W_a1bc8.
Proof. vm_refl. Qed.
Lemma D_a1bc8 : decode_any W_a1bc8 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bcc : bv 32 := 0x00987863.
Lemma F_a1bcc : fetch_word Asan.M.loaded_segments (0xa1c1c : word) = Some W_a1bcc.
Proof. vm_refl. Qed.
Lemma D_a1bcc : decode_any W_a1bcc = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd0 : bv 32 := 0x00787893.
Lemma F_a1bd0 : fetch_word Asan.M.loaded_segments (0xa1c20 : word) = Some W_a1bd0.
Proof. vm_refl. Qed.
Lemma D_a1bd0 : decode_any W_a1bd0 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd4 : bv 32 := 0x00080613.
Lemma F_a1bd4 : fetch_word Asan.M.loaded_segments (0xa1c24 : word) = Some W_a1bd4.
Proof. vm_refl. Qed.
Lemma D_a1bd4 : decode_any W_a1bd4 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd8 : bv 32 := 0xfc0884e3.
Lemma F_a1bd8 : fetch_word Asan.M.loaded_segments (0xa1c28 : word) = Some W_a1bd8.
Proof. vm_refl. Qed.
Lemma D_a1bd8 : decode_any W_a1bd8 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bdc : bv 32 := 0x03813083.
Lemma F_a1bdc : fetch_word Asan.M.loaded_segments (0xa1c2c : word) = Some W_a1bdc.
Proof. vm_refl. Qed.
Lemma D_a1bdc : decode_any W_a1bdc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be0 : bv 32 := 0x03013403.
Lemma F_a1be0 : fetch_word Asan.M.loaded_segments (0xa1c30 : word) = Some W_a1be0.
Proof. vm_refl. Qed.
Lemma D_a1be0 : decode_any W_a1be0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be4 : bv 32 := 0x02813483.
Lemma F_a1be4 : fetch_word Asan.M.loaded_segments (0xa1c34 : word) = Some W_a1be4.
Proof. vm_refl. Qed.
Lemma D_a1be4 : decode_any W_a1be4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be8 : bv 32 := 0x02013903.
Lemma F_a1be8 : fetch_word Asan.M.loaded_segments (0xa1c38 : word) = Some W_a1be8.
Proof. vm_refl. Qed.
Lemma D_a1be8 : decode_any W_a1be8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bec : bv 32 := 0x01813983.
Lemma F_a1bec : fetch_word Asan.M.loaded_segments (0xa1c3c : word) = Some W_a1bec.
Proof. vm_refl. Qed.
Lemma D_a1bec : decode_any W_a1bec = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf0 : bv 32 := 0x01013a03.
Lemma F_a1bf0 : fetch_word Asan.M.loaded_segments (0xa1c40 : word) = Some W_a1bf0.
Proof. vm_refl. Qed.
Lemma D_a1bf0 : decode_any W_a1bf0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf4 : bv 32 := 0x00813a83.
Lemma F_a1bf4 : fetch_word Asan.M.loaded_segments (0xa1c44 : word) = Some W_a1bf4.
Proof. vm_refl. Qed.
Lemma D_a1bf4 : decode_any W_a1bf4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf8 : bv 32 := 0x00013b03.
Lemma F_a1bf8 : fetch_word Asan.M.loaded_segments (0xa1c48 : word) = Some W_a1bf8.
Proof. vm_refl. Qed.
Lemma D_a1bf8 : decode_any W_a1bf8 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bfc : bv 32 := 0x04010113.
Lemma F_a1bfc : fetch_word Asan.M.loaded_segments (0xa1c4c : word) = Some W_a1bfc.
Proof. vm_refl. Qed.
Lemma D_a1bfc : decode_any W_a1bfc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c00 : bv 32 := 0x00008067.
Lemma F_a1c00 : fetch_word Asan.M.loaded_segments (0xa1c50 : word) = Some W_a1c00.
Proof. vm_refl. Qed.
Lemma D_a1c00 : decode_any W_a1c00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

