(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a11f8 : bv 32 := 0x02d61863.
Lemma F_a11f8 : fetch_word Plain.M.loaded_segments (0xa1244 : word) = Some W_a11f8.
Proof. vm_refl. Qed.
Lemma D_a11f8 : decode_any W_a11f8 = Some (Branch BC_NE 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1218 : bv 32 := 0x02e5b423.
Lemma F_a1218 : fetch_word Plain.M.loaded_segments (0xa1264 : word) = Some W_a1218.
Proof. vm_refl. Qed.
Lemma D_a1218 : decode_any W_a1218 = Some (Store SZ8 11 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1228 : bv 32 := 0x0100006f.
Lemma F_a1228 : fetch_word Plain.M.loaded_segments (0xa1274 : word) = Some W_a1228.
Proof. vm_refl. Qed.
Lemma D_a1228 : decode_any W_a1228 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a122c : bv 32 := 0x00058513.
Lemma F_a122c : fetch_word Plain.M.loaded_segments (0xa1278 : word) = Some W_a122c.
Proof. vm_refl. Qed.
Lemma D_a122c : decode_any W_a122c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1254 : bv 32 := 0x08c48413.
Lemma F_a1254 : fetch_word Plain.M.loaded_segments (0xa12a0 : word) = Some W_a1254.
Proof. vm_refl. Qed.
Lemma D_a1254 : decode_any W_a1254 = Some (OpImm ALU_ADD 8 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1290 : bv 32 := 0x0204b583.
Lemma F_a1290 : fetch_word Plain.M.loaded_segments (0xa12dc : word) = Some W_a1290.
Proof. vm_refl. Qed.
Lemma D_a1290 : decode_any W_a1290 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a129c : bv 32 := 0x00150593.
Lemma F_a129c : fetch_word Plain.M.loaded_segments (0xa12e8 : word) = Some W_a129c.
Proof. vm_refl. Qed.
Lemma D_a129c : decode_any W_a129c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a0 : bv 32 := 0x02b4b423.
Lemma F_a12a0 : fetch_word Plain.M.loaded_segments (0xa12ec : word) = Some W_a12a0.
Proof. vm_refl. Qed.
Lemma D_a12a0 : decode_any W_a12a0 = Some (Store SZ8 9 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a4 : bv 32 := 0x01250023.
Lemma F_a12a4 : fetch_word Plain.M.loaded_segments (0xa12f0 : word) = Some W_a12a4.
Proof. vm_refl. Qed.
Lemma D_a12a4 : decode_any W_a12a4 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12a8 : bv 32 := 0x0140006f.
Lemma F_a12a8 : fetch_word Plain.M.loaded_segments (0xa12f4 : word) = Some W_a12a8.
Proof. vm_refl. Qed.
Lemma D_a12a8 : decode_any W_a12a8 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12ac : bv 32 := 0x00048513.
Lemma F_a12ac : fetch_word Plain.M.loaded_segments (0xa12f8 : word) = Some W_a12ac.
Proof. vm_refl. Qed.
Lemma D_a12ac : decode_any W_a12ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b0 : bv 32 := 0x00068593.
Lemma F_a12b0 : fetch_word Plain.M.loaded_segments (0xa12fc : word) = Some W_a12b0.
Proof. vm_refl. Qed.
Lemma D_a12b0 : decode_any W_a12b0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b4 : bv 32 := 0x07c000ef.
Lemma F_a12b4 : fetch_word Plain.M.loaded_segments (0xa1300 : word) = Some W_a12b4.
Proof. vm_refl. Qed.
Lemma D_a12b4 : decode_any W_a12b4 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12b8 : bv 32 := 0x00050693.
Lemma F_a12b8 : fetch_word Plain.M.loaded_segments (0xa1304 : word) = Some W_a12b8.
Proof. vm_refl. Qed.
Lemma D_a12b8 : decode_any W_a12b8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12bc : bv 32 := 0x00000513.
Lemma F_a12bc : fetch_word Plain.M.loaded_segments (0xa1308 : word) = Some W_a12bc.
Proof. vm_refl. Qed.
Lemma D_a12bc : decode_any W_a12bc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c0 : bv 32 := 0x00042583.
Lemma F_a12c0 : fetch_word Plain.M.loaded_segments (0xa130c : word) = Some W_a12c0.
Proof. vm_refl. Qed.
Lemma D_a12c0 : decode_any W_a12c0 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c4 : bv 32 := 0x1604262f.
Lemma F_a12c4 : fetch_word Plain.M.loaded_segments (0xa1310 : word) = Some W_a12c4.
Proof. vm_refl. Qed.
Lemma D_a12c4 : decode_any W_a12c4 = Some (Lr AW true true 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12c8 : bv 32 := 0x00b61663.
Lemma F_a12c8 : fetch_word Plain.M.loaded_segments (0xa1314 : word) = Some W_a12c8.
Proof. vm_refl. Qed.
Lemma D_a12c8 : decode_any W_a12c8 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12cc : bv 32 := 0x1ea4272f.
Lemma F_a12cc : fetch_word Plain.M.loaded_segments (0xa1318 : word) = Some W_a12cc.
Proof. vm_refl. Qed.
Lemma D_a12cc : decode_any W_a12cc = Some (Sc AW true true 14 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12d0 : bv 32 := 0xfe071ae3.
Lemma F_a12d0 : fetch_word Plain.M.loaded_segments (0xa131c : word) = Some W_a12d0.
Proof. vm_refl. Qed.
Lemma D_a12d0 : decode_any W_a12d0 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12d4 : bv 32 := 0x0006061b.
Lemma F_a12d4 : fetch_word Plain.M.loaded_segments (0xa1320 : word) = Some W_a12d4.
Proof. vm_refl. Qed.
Lemma D_a12d4 : decode_any W_a12d4 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12d8 : bv 32 := 0xfeb614e3.
Lemma F_a12d8 : fetch_word Plain.M.loaded_segments (0xa1324 : word) = Some W_a12d8.
Proof. vm_refl. Qed.
Lemma D_a12d8 : decode_any W_a12d8 = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12dc : bv 32 := 0x02159593.
Lemma F_a12dc : fetch_word Plain.M.loaded_segments (0xa1328 : word) = Some W_a12dc.
Proof. vm_refl. Qed.
Lemma D_a12dc : decode_any W_a12dc = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12e0 : bv 32 := 0x0205da63.
Lemma F_a12e0 : fetch_word Plain.M.loaded_segments (0xa132c : word) = Some W_a12e0.
Proof. vm_refl. Qed.
Lemma D_a12e0 : decode_any W_a12e0 = Some (Branch BC_GE 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12e4 : bv 32 := 0x06200893.
Lemma F_a12e4 : fetch_word Plain.M.loaded_segments (0xa1330 : word) = Some W_a12e4.
Proof. vm_refl. Qed.
Lemma D_a12e4 : decode_any W_a12e4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12e8 : bv 32 := 0x08100593.
Lemma F_a12e8 : fetch_word Plain.M.loaded_segments (0xa1334 : word) = Some W_a12e8.
Proof. vm_refl. Qed.
Lemma D_a12e8 : decode_any W_a12e8 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12ec : bv 32 := 0x00100613.
Lemma F_a12ec : fetch_word Plain.M.loaded_segments (0xa1338 : word) = Some W_a12ec.
Proof. vm_refl. Qed.
Lemma D_a12ec : decode_any W_a12ec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f0 : bv 32 := 0xfda00713.
Lemma F_a12f0 : fetch_word Plain.M.loaded_segments (0xa133c : word) = Some W_a12f0.
Proof. vm_refl. Qed.
Lemma D_a12f0 : decode_any W_a12f0 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f4 : bv 32 := 0x00040513.
Lemma F_a12f4 : fetch_word Plain.M.loaded_segments (0xa1340 : word) = Some W_a12f4.
Proof. vm_refl. Qed.
Lemma D_a12f4 : decode_any W_a12f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a12f8 : bv 32 := 0x00000073.
Lemma F_a12f8 : fetch_word Plain.M.loaded_segments (0xa1344 : word) = Some W_a12f8.
Proof. vm_refl. Qed.
Lemma D_a12f8 : decode_any W_a12f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a12f8 : is_ecall W_a12f8 = true.
Proof. reflexivity. Qed.

Definition W_a12fc : bv 32 := 0x00e51c63.
Lemma F_a12fc : fetch_word Plain.M.loaded_segments (0xa1348 : word) = Some W_a12fc.
Proof. vm_refl. Qed.
Lemma D_a12fc : decode_any W_a12fc = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1300 : bv 32 := 0x06200893.
Lemma F_a1300 : fetch_word Plain.M.loaded_segments (0xa134c : word) = Some W_a1300.
Proof. vm_refl. Qed.
Lemma D_a1300 : decode_any W_a1300 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1304 : bv 32 := 0x00100593.
Lemma F_a1304 : fetch_word Plain.M.loaded_segments (0xa1350 : word) = Some W_a1304.
Proof. vm_refl. Qed.
Lemma D_a1304 : decode_any W_a1304 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1308 : bv 32 := 0x00100613.
Lemma F_a1308 : fetch_word Plain.M.loaded_segments (0xa1354 : word) = Some W_a1308.
Proof. vm_refl. Qed.
Lemma D_a1308 : decode_any W_a1308 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a130c : bv 32 := 0x00040513.
Lemma F_a130c : fetch_word Plain.M.loaded_segments (0xa1358 : word) = Some W_a130c.
Proof. vm_refl. Qed.
Lemma D_a130c : decode_any W_a130c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1310 : bv 32 := 0x00000073.
Lemma F_a1310 : fetch_word Plain.M.loaded_segments (0xa135c : word) = Some W_a1310.
Proof. vm_refl. Qed.
Lemma D_a1310 : decode_any W_a1310 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a1310 : is_ecall W_a1310 = true.
Proof. reflexivity. Qed.

Definition W_a1314 : bv 32 := 0x00068513.
Lemma F_a1314 : fetch_word Plain.M.loaded_segments (0xa1360 : word) = Some W_a1314.
Proof. vm_refl. Qed.
Lemma D_a1314 : decode_any W_a1314 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1318 : bv 32 := 0x01813083.
Lemma F_a1318 : fetch_word Plain.M.loaded_segments (0xa1364 : word) = Some W_a1318.
Proof. vm_refl. Qed.
Lemma D_a1318 : decode_any W_a1318 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a131c : bv 32 := 0x01013403.
Lemma F_a131c : fetch_word Plain.M.loaded_segments (0xa1368 : word) = Some W_a131c.
Proof. vm_refl. Qed.
Lemma D_a131c : decode_any W_a131c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1320 : bv 32 := 0x00813483.
Lemma F_a1320 : fetch_word Plain.M.loaded_segments (0xa136c : word) = Some W_a1320.
Proof. vm_refl. Qed.
Lemma D_a1320 : decode_any W_a1320 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1324 : bv 32 := 0x00013903.
Lemma F_a1324 : fetch_word Plain.M.loaded_segments (0xa1370 : word) = Some W_a1324.
Proof. vm_refl. Qed.
Lemma D_a1324 : decode_any W_a1324 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1328 : bv 32 := 0x02010113.
Lemma F_a1328 : fetch_word Plain.M.loaded_segments (0xa1374 : word) = Some W_a1328.
Proof. vm_refl. Qed.
Lemma D_a1328 : decode_any W_a1328 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a132c : bv 32 := 0x00008067.
Lemma F_a132c : fetch_word Plain.M.loaded_segments (0xa1378 : word) = Some W_a132c.
Proof. vm_refl. Qed.
Lemma D_a132c : decode_any W_a132c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1330 : bv 32 := 0xfd010113.
Lemma F_a1330 : fetch_word Plain.M.loaded_segments (0xa137c : word) = Some W_a1330.
Proof. vm_refl. Qed.
Lemma D_a1330 : decode_any W_a1330 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1334 : bv 32 := 0x02113423.
Lemma F_a1334 : fetch_word Plain.M.loaded_segments (0xa1380 : word) = Some W_a1334.
Proof. vm_refl. Qed.
Lemma D_a1334 : decode_any W_a1334 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1338 : bv 32 := 0x02813023.
Lemma F_a1338 : fetch_word Plain.M.loaded_segments (0xa1384 : word) = Some W_a1338.
Proof. vm_refl. Qed.
Lemma D_a1338 : decode_any W_a1338 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a133c : bv 32 := 0x00913c23.
Lemma F_a133c : fetch_word Plain.M.loaded_segments (0xa1388 : word) = Some W_a133c.
Proof. vm_refl. Qed.
Lemma D_a133c : decode_any W_a133c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1340 : bv 32 := 0x01213823.
Lemma F_a1340 : fetch_word Plain.M.loaded_segments (0xa138c : word) = Some W_a1340.
Proof. vm_refl. Qed.
Lemma D_a1340 : decode_any W_a1340 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1344 : bv 32 := 0x00017617.
Lemma F_a1344 : fetch_word Plain.M.loaded_segments (0xa1390 : word) = Some W_a1344.
Proof. vm_refl. Qed.
Lemma D_a1344 : decode_any W_a1344 = Some (Auipc 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1348 : bv 32 := 0xf1063403.
Lemma F_a1348 : fetch_word Plain.M.loaded_segments (0xa1394 : word) = Some W_a1348.
Proof. vm_refl. Qed.
Lemma D_a1348 : decode_any W_a1348 = Some (Load SZ8 true 8 12 3856, 4%Z).
Proof. vm_refl. Qed.

Definition W_a134c : bv 32 := 0x00043603.
Lemma F_a134c : fetch_word Plain.M.loaded_segments (0xa1398 : word) = Some W_a134c.
Proof. vm_refl. Qed.
Lemma D_a134c : decode_any W_a134c = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1350 : bv 32 := 0x00c13423.
Lemma F_a1350 : fetch_word Plain.M.loaded_segments (0xa139c : word) = Some W_a1350.
Proof. vm_refl. Qed.
Lemma D_a1350 : decode_any W_a1350 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1354 : bv 32 := 0x02053683.
Lemma F_a1354 : fetch_word Plain.M.loaded_segments (0xa13a0 : word) = Some W_a1354.
Proof. vm_refl. Qed.
Lemma D_a1354 : decode_any W_a1354 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1358 : bv 32 := 0x00b103a3.
Lemma F_a1358 : fetch_word Plain.M.loaded_segments (0xa13a4 : word) = Some W_a1358.
Proof. vm_refl. Qed.
Lemma D_a1358 : decode_any W_a1358 = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a135c : bv 32 := 0x02068c63.
Lemma F_a135c : fetch_word Plain.M.loaded_segments (0xa13a8 : word) = Some W_a135c.
Proof. vm_refl. Qed.
Lemma D_a135c : decode_any W_a135c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1360 : bv 32 := 0x02853603.
Lemma F_a1360 : fetch_word Plain.M.loaded_segments (0xa13ac : word) = Some W_a1360.
Proof. vm_refl. Qed.
Lemma D_a1360 : decode_any W_a1360 = Some (Load SZ8 true 12 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1364 : bv 32 := 0x00d60863.
Lemma F_a1364 : fetch_word Plain.M.loaded_segments (0xa13b0 : word) = Some W_a1364.
Proof. vm_refl. Qed.
Lemma D_a1364 : decode_any W_a1364 = Some (Branch BC_EQ 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1368 : bv 32 := 0x09052703.
Lemma F_a1368 : fetch_word Plain.M.loaded_segments (0xa13b4 : word) = Some W_a1368.
Proof. vm_refl. Qed.
Lemma D_a1368 : decode_any W_a1368 = Some (Load SZ4 true 14 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a136c : bv 32 := 0x0ff5f793.
Lemma F_a136c : fetch_word Plain.M.loaded_segments (0xa13b8 : word) = Some W_a136c.
Proof. vm_refl. Qed.
Lemma D_a136c : decode_any W_a136c = Some (OpImm ALU_AND 15 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1370 : bv 32 := 0x02f71e63.
Lemma F_a1370 : fetch_word Plain.M.loaded_segments (0xa13bc : word) = Some W_a1370.
Proof. vm_refl. Qed.
Lemma D_a1370 : decode_any W_a1370 = Some (Branch BC_NE 14 15 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1374 : bv 32 := 0x04853683.
Lemma F_a1374 : fetch_word Plain.M.loaded_segments (0xa13c0 : word) = Some W_a1374.
Proof. vm_refl. Qed.
Lemma D_a1374 : decode_any W_a1374 = Some (Load SZ8 true 13 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1378 : bv 32 := 0x00710593.
Lemma F_a1378 : fetch_word Plain.M.loaded_segments (0xa13c4 : word) = Some W_a1378.
Proof. vm_refl. Qed.
Lemma D_a1378 : decode_any W_a1378 = Some (OpImm ALU_ADD 11 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a137c : bv 32 := 0x00100613.
Lemma F_a137c : fetch_word Plain.M.loaded_segments (0xa13c8 : word) = Some W_a137c.
Proof. vm_refl. Qed.
Lemma D_a137c : decode_any W_a137c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a141c : bv 32 := 0x06053683.
Lemma F_a141c : fetch_word Plain.M.loaded_segments (0xa1468 : word) = Some W_a141c.
Proof. vm_refl. Qed.
Lemma D_a141c : decode_any W_a141c = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1420 : bv 32 := 0x02c53c23.
Lemma F_a1420 : fetch_word Plain.M.loaded_segments (0xa146c : word) = Some W_a1420.
Proof. vm_refl. Qed.
Lemma D_a1420 : decode_any W_a1420 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a142c : bv 32 := 0x00053823.
Lemma F_a142c : fetch_word Plain.M.loaded_segments (0xa1478 : word) = Some W_a142c.
Proof. vm_refl. Qed.
Lemma D_a142c : decode_any W_a142c = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1430 : bv 32 := 0x02d53023.
Lemma F_a1430 : fetch_word Plain.M.loaded_segments (0xa147c : word) = Some W_a1430.
Proof. vm_refl. Qed.
Lemma D_a1430 : decode_any W_a1430 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1434 : bv 32 := 0x02c53423.
Lemma F_a1434 : fetch_word Plain.M.loaded_segments (0xa1480 : word) = Some W_a1434.
Proof. vm_refl. Qed.
Lemma D_a1434 : decode_any W_a1434 = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1438 : bv 32 := 0x00000513.
Lemma F_a1438 : fetch_word Plain.M.loaded_segments (0xa1484 : word) = Some W_a1438.
Proof. vm_refl. Qed.
Lemma D_a1438 : decode_any W_a1438 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a143c : bv 32 := 0x00008067.
Lemma F_a143c : fetch_word Plain.M.loaded_segments (0xa1488 : word) = Some W_a143c.
Proof. vm_refl. Qed.
Lemma D_a143c : decode_any W_a143c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1440 : bv 32 := 0x0205e593.
Lemma F_a1440 : fetch_word Plain.M.loaded_segments (0xa148c : word) = Some W_a1440.
Proof. vm_refl. Qed.
Lemma D_a1440 : decode_any W_a1440 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1444 : bv 32 := 0x00b52023.
Lemma F_a1444 : fetch_word Plain.M.loaded_segments (0xa1490 : word) = Some W_a1444.
Proof. vm_refl. Qed.
Lemma D_a1444 : decode_any W_a1444 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1448 : bv 32 := 0xfff00513.
Lemma F_a1448 : fetch_word Plain.M.loaded_segments (0xa1494 : word) = Some W_a1448.
Proof. vm_refl. Qed.
Lemma D_a1448 : decode_any W_a1448 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a144c : bv 32 := 0x00008067.
Lemma F_a144c : fetch_word Plain.M.loaded_segments (0xa1498 : word) = Some W_a144c.
Proof. vm_refl. Qed.
Lemma D_a144c : decode_any W_a144c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1450 : bv 32 := 0xff010113.
Lemma F_a1450 : fetch_word Plain.M.loaded_segments (0xa149c : word) = Some W_a1450.
Proof. vm_refl. Qed.
Lemma D_a1450 : decode_any W_a1450 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1454 : bv 32 := 0x00113423.
Lemma F_a1454 : fetch_word Plain.M.loaded_segments (0xa14a0 : word) = Some W_a1454.
Proof. vm_refl. Qed.
Lemma D_a1454 : decode_any W_a1454 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1458 : bv 32 := 0x00813023.
Lemma F_a1458 : fetch_word Plain.M.loaded_segments (0xa14a4 : word) = Some W_a1458.
Proof. vm_refl. Qed.
Lemma D_a1458 : decode_any W_a1458 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a145c : bv 32 := 0x41c000ef.
Lemma F_a145c : fetch_word Plain.M.loaded_segments (0xa14a8 : word) = Some W_a145c.
Proof. vm_refl. Qed.
Lemma D_a145c : decode_any W_a145c = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1460 : bv 32 := 0x00053403.
Lemma F_a1460 : fetch_word Plain.M.loaded_segments (0xa14ac : word) = Some W_a1460.
Proof. vm_refl. Qed.
Lemma D_a1460 : decode_any W_a1460 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1464 : bv 32 := 0x12041663.
Lemma F_a1464 : fetch_word Plain.M.loaded_segments (0xa14b0 : word) = Some W_a1464.
Proof. vm_refl. Qed.
Lemma D_a1464 : decode_any W_a1464 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1468 : bv 32 := 0x0004a517.
Lemma F_a1468 : fetch_word Plain.M.loaded_segments (0xa14b4 : word) = Some W_a1468.
Proof. vm_refl. Qed.
Lemma D_a1468 : decode_any W_a1468 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_a146c : bv 32 := 0x35453403.
Lemma F_a146c : fetch_word Plain.M.loaded_segments (0xa14b8 : word) = Some W_a146c.
Proof. vm_refl. Qed.
Lemma D_a146c : decode_any W_a146c = Some (Load SZ8 true 8 10 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1470 : bv 32 := 0x04040a63.
Lemma F_a1470 : fetch_word Plain.M.loaded_segments (0xa14bc : word) = Some W_a1470.
Proof. vm_refl. Qed.
Lemma D_a1470 : decode_any W_a1470 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14c4 : bv 32 := 0x00018517.
Lemma F_a14c4 : fetch_word Plain.M.loaded_segments (0xa1510 : word) = Some W_a14c4.
Proof. vm_refl. Qed.
Lemma D_a14c4 : decode_any W_a14c4 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14c8 : bv 32 := 0x08053403.
Lemma F_a14c8 : fetch_word Plain.M.loaded_segments (0xa1514 : word) = Some W_a14c8.
Proof. vm_refl. Qed.
Lemma D_a14c8 : decode_any W_a14c8 = Some (Load SZ8 true 8 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14cc : bv 32 := 0x04040a63.
Lemma F_a14cc : fetch_word Plain.M.loaded_segments (0xa1518 : word) = Some W_a14cc.
Proof. vm_refl. Qed.
Lemma D_a14cc : decode_any W_a14cc = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14d0 : bv 32 := 0x08c42503.
Lemma F_a14d0 : fetch_word Plain.M.loaded_segments (0xa151c : word) = Some W_a14d0.
Proof. vm_refl. Qed.
Lemma D_a14d0 : decode_any W_a14d0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14d4 : bv 32 := 0x00054663.
Lemma F_a14d4 : fetch_word Plain.M.loaded_segments (0xa1520 : word) = Some W_a14d4.
Proof. vm_refl. Qed.
Lemma D_a14d4 : decode_any W_a14d4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14e0 : bv 32 := 0x02843503.
Lemma F_a14e0 : fetch_word Plain.M.loaded_segments (0xa152c : word) = Some W_a14e0.
Proof. vm_refl. Qed.
Lemma D_a14e0 : decode_any W_a14e0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14e4 : bv 32 := 0x03843583.
Lemma F_a14e4 : fetch_word Plain.M.loaded_segments (0xa1530 : word) = Some W_a14e4.
Proof. vm_refl. Qed.
Lemma D_a14e4 : decode_any W_a14e4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14e8 : bv 32 := 0x00b50c63.
Lemma F_a14e8 : fetch_word Plain.M.loaded_segments (0xa1534 : word) = Some W_a14e8.
Proof. vm_refl. Qed.
Lemma D_a14e8 : decode_any W_a14e8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14ec : bv 32 := 0x04843683.
Lemma F_a14ec : fetch_word Plain.M.loaded_segments (0xa1538 : word) = Some W_a14ec.
Proof. vm_refl. Qed.
Lemma D_a14ec : decode_any W_a14ec = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14f0 : bv 32 := 0x00040513.
Lemma F_a14f0 : fetch_word Plain.M.loaded_segments (0xa153c : word) = Some W_a14f0.
Proof. vm_refl. Qed.
Lemma D_a14f0 : decode_any W_a14f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14f4 : bv 32 := 0x00000593.
Lemma F_a14f4 : fetch_word Plain.M.loaded_segments (0xa1540 : word) = Some W_a14f4.
Proof. vm_refl. Qed.
Lemma D_a14f4 : decode_any W_a14f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14f8 : bv 32 := 0x00000613.
Lemma F_a14f8 : fetch_word Plain.M.loaded_segments (0xa1544 : word) = Some W_a14f8.
Proof. vm_refl. Qed.
Lemma D_a14f8 : decode_any W_a14f8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14fc : bv 32 := 0x000680e7.
Lemma F_a14fc : fetch_word Plain.M.loaded_segments (0xa1548 : word) = Some W_a14fc.
Proof. vm_refl. Qed.
Lemma D_a14fc : decode_any W_a14fc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1500 : bv 32 := 0x00843503.
Lemma F_a1500 : fetch_word Plain.M.loaded_segments (0xa154c : word) = Some W_a1500.
Proof. vm_refl. Qed.
Lemma D_a1500 : decode_any W_a1500 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1504 : bv 32 := 0x01043583.
Lemma F_a1504 : fetch_word Plain.M.loaded_segments (0xa1550 : word) = Some W_a1504.
Proof. vm_refl. Qed.
Lemma D_a1504 : decode_any W_a1504 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1508 : bv 32 := 0x00b50c63.
Lemma F_a1508 : fetch_word Plain.M.loaded_segments (0xa1554 : word) = Some W_a1508.
Proof. vm_refl. Qed.
Lemma D_a1508 : decode_any W_a1508 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1520 : bv 32 := 0x00018517.
Lemma F_a1520 : fetch_word Plain.M.loaded_segments (0xa156c : word) = Some W_a1520.
Proof. vm_refl. Qed.
Lemma D_a1520 : decode_any W_a1520 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1524 : bv 32 := 0xf3453403.
Lemma F_a1524 : fetch_word Plain.M.loaded_segments (0xa1570 : word) = Some W_a1524.
Proof. vm_refl. Qed.
Lemma D_a1524 : decode_any W_a1524 = Some (Load SZ8 true 8 10 3892, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1528 : bv 32 := 0x0a040e63.
Lemma F_a1528 : fetch_word Plain.M.loaded_segments (0xa1574 : word) = Some W_a1528.
Proof. vm_refl. Qed.
Lemma D_a1528 : decode_any W_a1528 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_a152c : bv 32 := 0x08c42503.
Lemma F_a152c : fetch_word Plain.M.loaded_segments (0xa1578 : word) = Some W_a152c.
Proof. vm_refl. Qed.
Lemma D_a152c : decode_any W_a152c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1530 : bv 32 := 0x00054663.
Lemma F_a1530 : fetch_word Plain.M.loaded_segments (0xa157c : word) = Some W_a1530.
Proof. vm_refl. Qed.
Lemma D_a1530 : decode_any W_a1530 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a153c : bv 32 := 0x02843503.
Lemma F_a153c : fetch_word Plain.M.loaded_segments (0xa1588 : word) = Some W_a153c.
Proof. vm_refl. Qed.
Lemma D_a153c : decode_any W_a153c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1540 : bv 32 := 0x03843583.
Lemma F_a1540 : fetch_word Plain.M.loaded_segments (0xa158c : word) = Some W_a1540.
Proof. vm_refl. Qed.
Lemma D_a1540 : decode_any W_a1540 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1544 : bv 32 := 0x00b50c63.
Lemma F_a1544 : fetch_word Plain.M.loaded_segments (0xa1590 : word) = Some W_a1544.
Proof. vm_refl. Qed.
Lemma D_a1544 : decode_any W_a1544 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a155c : bv 32 := 0x00843503.
Lemma F_a155c : fetch_word Plain.M.loaded_segments (0xa15a8 : word) = Some W_a155c.
Proof. vm_refl. Qed.
Lemma D_a155c : decode_any W_a155c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1560 : bv 32 := 0x01043583.
Lemma F_a1560 : fetch_word Plain.M.loaded_segments (0xa15ac : word) = Some W_a1560.
Proof. vm_refl. Qed.
Lemma D_a1560 : decode_any W_a1560 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1564 : bv 32 := 0x08b50063.
Lemma F_a1564 : fetch_word Plain.M.loaded_segments (0xa15b0 : word) = Some W_a1564.
Proof. vm_refl. Qed.
Lemma D_a1564 : decode_any W_a1564 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e4 : bv 32 := 0x00813083.
Lemma F_a15e4 : fetch_word Plain.M.loaded_segments (0xa1630 : word) = Some W_a15e4.
Proof. vm_refl. Qed.
Lemma D_a15e4 : decode_any W_a15e4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e8 : bv 32 := 0x00013403.
Lemma F_a15e8 : fetch_word Plain.M.loaded_segments (0xa1634 : word) = Some W_a15e8.
Proof. vm_refl. Qed.
Lemma D_a15e8 : decode_any W_a15e8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15ec : bv 32 := 0x01010113.
Lemma F_a15ec : fetch_word Plain.M.loaded_segments (0xa1638 : word) = Some W_a15ec.
Proof. vm_refl. Qed.
Lemma D_a15ec : decode_any W_a15ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f0 : bv 32 := 0x00008067.
Lemma F_a15f0 : fetch_word Plain.M.loaded_segments (0xa163c : word) = Some W_a15f0.
Proof. vm_refl. Qed.
Lemma D_a15f0 : decode_any W_a15f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
