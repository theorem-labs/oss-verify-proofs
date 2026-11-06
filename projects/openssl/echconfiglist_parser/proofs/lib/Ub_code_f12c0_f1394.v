(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_f12c0 : bv 32 := 0xfe010113.
Lemma F_f12c0 : fetch_word Ubsan.M.loaded_segments (0xf1308 : word) = Some W_f12c0.
Proof. vm_refl. Qed.
Lemma D_f12c0 : decode_any W_f12c0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12c4 : bv 32 := 0x00113c23.
Lemma F_f12c4 : fetch_word Ubsan.M.loaded_segments (0xf130c : word) = Some W_f12c4.
Proof. vm_refl. Qed.
Lemma D_f12c4 : decode_any W_f12c4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12c8 : bv 32 := 0x00813823.
Lemma F_f12c8 : fetch_word Ubsan.M.loaded_segments (0xf1310 : word) = Some W_f12c8.
Proof. vm_refl. Qed.
Lemma D_f12c8 : decode_any W_f12c8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12cc : bv 32 := 0x00913423.
Lemma F_f12cc : fetch_word Ubsan.M.loaded_segments (0xf1314 : word) = Some W_f12cc.
Proof. vm_refl. Qed.
Lemma D_f12cc : decode_any W_f12cc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12d0 : bv 32 := 0x02010413.
Lemma F_f12d0 : fetch_word Ubsan.M.loaded_segments (0xf1318 : word) = Some W_f12d0.
Proof. vm_refl. Qed.
Lemma D_f12d0 : decode_any W_f12d0 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12d4 : bv 32 := 0x00242517.
Lemma F_f12d4 : fetch_word Ubsan.M.loaded_segments (0xf131c : word) = Some W_f12d4.
Proof. vm_refl. Qed.
Lemma D_f12d4 : decode_any W_f12d4 = Some (Auipc 10 578, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12d8 : bv 32 := 0x43c50493.
Lemma F_f12d8 : fetch_word Ubsan.M.loaded_segments (0xf1320 : word) = Some W_f12d8.
Proof. vm_refl. Qed.
Lemma D_f12d8 : decode_any W_f12d8 = Some (OpImm ALU_ADD 9 10 1084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12dc : bv 32 := 0x0004c503.
Lemma F_f12dc : fetch_word Ubsan.M.loaded_segments (0xf1324 : word) = Some W_f12dc.
Proof. vm_refl. Qed.
Lemma D_f12dc : decode_any W_f12dc = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12e0 : bv 32 := 0x0a050063.
Lemma F_f12e0 : fetch_word Ubsan.M.loaded_segments (0xf1328 : word) = Some W_f12e0.
Proof. vm_refl. Qed.
Lemma D_f12e0 : decode_any W_f12e0 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12e4 : bv 32 := 0x0044c503.
Lemma F_f12e4 : fetch_word Ubsan.M.loaded_segments (0xf132c : word) = Some W_f12e4.
Proof. vm_refl. Qed.
Lemma D_f12e4 : decode_any W_f12e4 = Some (Load SZ1 false 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12e8 : bv 32 := 0x00157513.
Lemma F_f12e8 : fetch_word Ubsan.M.loaded_segments (0xf1330 : word) = Some W_f12e8.
Proof. vm_refl. Qed.
Lemma D_f12e8 : decode_any W_f12e8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12ec : bv 32 := 0x08050a63.
Lemma F_f12ec : fetch_word Ubsan.M.loaded_segments (0xf1334 : word) = Some W_f12ec.
Proof. vm_refl. Qed.
Lemma D_f12ec : decode_any W_f12ec = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12f0 : bv 32 := 0x0084c503.
Lemma F_f12f0 : fetch_word Ubsan.M.loaded_segments (0xf1338 : word) = Some W_f12f0.
Proof. vm_refl. Qed.
Lemma D_f12f0 : decode_any W_f12f0 = Some (Load SZ1 false 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12f4 : bv 32 := 0x00157513.
Lemma F_f12f4 : fetch_word Ubsan.M.loaded_segments (0xf133c : word) = Some W_f12f4.
Proof. vm_refl. Qed.
Lemma D_f12f4 : decode_any W_f12f4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12f8 : bv 32 := 0x08051463.
Lemma F_f12f8 : fetch_word Ubsan.M.loaded_segments (0xf1340 : word) = Some W_f12f8.
Proof. vm_refl. Qed.
Lemma D_f12f8 : decode_any W_f12f8 = Some (Branch BC_NE 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f12fc : bv 32 := 0x00100513.
Lemma F_f12fc : fetch_word Ubsan.M.loaded_segments (0xf1344 : word) = Some W_f12fc.
Proof. vm_refl. Qed.
Lemma D_f12fc : decode_any W_f12fc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1300 : bv 32 := 0x00a48423.
Lemma F_f1300 : fetch_word Ubsan.M.loaded_segments (0xf1348 : word) = Some W_f1300.
Proof. vm_refl. Qed.
Lemma D_f1300 : decode_any W_f1300 = Some (Store SZ1 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1304 : bv 32 := 0x821f60ef.
Lemma F_f1304 : fetch_word Ubsan.M.loaded_segments (0xf134c : word) = Some W_f1304.
Proof. vm_refl. Qed.
Lemma D_f1304 : decode_any W_f1304 = Some (Jal 1 2058272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1308 : bv 32 := 0x0504b503.
Lemma F_f1308 : fetch_word Ubsan.M.loaded_segments (0xf1350 : word) = Some W_f1308.
Proof. vm_refl. Qed.
Lemma D_f1308 : decode_any W_f1308 = Some (Load SZ8 true 10 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f130c : bv 32 := 0x818f50ef.
Lemma F_f130c : fetch_word Ubsan.M.loaded_segments (0xf1354 : word) = Some W_f130c.
Proof. vm_refl. Qed.
Lemma D_f130c : decode_any W_f130c = Some (Jal 1 2052120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1310 : bv 32 := 0x0584b503.
Lemma F_f1310 : fetch_word Ubsan.M.loaded_segments (0xf1358 : word) = Some W_f1310.
Proof. vm_refl. Qed.
Lemma D_f1310 : decode_any W_f1310 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1314 : bv 32 := 0x0404b823.
Lemma F_f1314 : fetch_word Ubsan.M.loaded_segments (0xf135c : word) = Some W_f1314.
Proof. vm_refl. Qed.
Lemma D_f1314 : decode_any W_f1314 = Some (Store SZ8 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1318 : bv 32 := 0x80cf50ef.
Lemma F_f1318 : fetch_word Ubsan.M.loaded_segments (0xf1360 : word) = Some W_f1318.
Proof. vm_refl. Qed.
Lemma D_f1318 : decode_any W_f1318 = Some (Jal 1 2052108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f131c : bv 32 := 0x0404bc23.
Lemma F_f131c : fetch_word Ubsan.M.loaded_segments (0xf1364 : word) = Some W_f131c.
Proof. vm_refl. Qed.
Lemma D_f131c : decode_any W_f131c = Some (Store SZ8 9 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1320 : bv 32 := 0x01c48513.
Lemma F_f1320 : fetch_word Ubsan.M.loaded_segments (0xf1368 : word) = Some W_f1320.
Proof. vm_refl. Qed.
Lemma D_f1320 : decode_any W_f1320 = Some (OpImm ALU_ADD 10 9 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1324 : bv 32 := 0x91cf50ef.
Lemma F_f1324 : fetch_word Ubsan.M.loaded_segments (0xf136c : word) = Some W_f1324.
Proof. vm_refl. Qed.
Lemma D_f1324 : decode_any W_f1324 = Some (Jal 1 2052380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1328 : bv 32 := 0x734000ef.
Lemma F_f1328 : fetch_word Ubsan.M.loaded_segments (0xf1370 : word) = Some W_f1328.
Proof. vm_refl. Qed.
Lemma D_f1328 : decode_any W_f1328 = Some (Jal 1 1844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f132c : bv 32 := 0x750000ef.
Lemma F_f132c : fetch_word Ubsan.M.loaded_segments (0xf1374 : word) = Some W_f132c.
Proof. vm_refl. Qed.
Lemma D_f132c : decode_any W_f132c = Some (Jal 1 1872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1330 : bv 32 := 0x76c000ef.
Lemma F_f1330 : fetch_word Ubsan.M.loaded_segments (0xf1378 : word) = Some W_f1330.
Proof. vm_refl. Qed.
Lemma D_f1330 : decode_any W_f1330 = Some (Jal 1 1900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1334 : bv 32 := 0x00c4c503.
Lemma F_f1334 : fetch_word Ubsan.M.loaded_segments (0xf137c : word) = Some W_f1334.
Proof. vm_refl. Qed.
Lemma D_f1334 : decode_any W_f1334 = Some (Load SZ1 false 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1338 : bv 32 := 0x00050463.
Lemma F_f1338 : fetch_word Ubsan.M.loaded_segments (0xf1380 : word) = Some W_f1338.
Proof. vm_refl. Qed.
Lemma D_f1338 : decode_any W_f1338 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f133c : bv 32 := 0x7a4000ef.
Lemma F_f133c : fetch_word Ubsan.M.loaded_segments (0xf1384 : word) = Some W_f133c.
Proof. vm_refl. Qed.
Lemma D_f133c : decode_any W_f133c = Some (Jal 1 1956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1340 : bv 32 := 0x7c0000ef.
Lemma F_f1340 : fetch_word Ubsan.M.loaded_segments (0xf1388 : word) = Some W_f1340.
Proof. vm_refl. Qed.
Lemma D_f1340 : decode_any W_f1340 = Some (Jal 1 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1344 : bv 32 := 0x0a1be0ef.
Lemma F_f1344 : fetch_word Ubsan.M.loaded_segments (0xf138c : word) = Some W_f1344.
Proof. vm_refl. Qed.
Lemma D_f1344 : decode_any W_f1344 = Some (Jal 1 780448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1348 : bv 32 := 0x001bd097.
Lemma F_f1348 : fetch_word Ubsan.M.loaded_segments (0xf1390 : word) = Some W_f1348.
Proof. vm_refl. Qed.
Lemma D_f1348 : decode_any W_f1348 = Some (Auipc 1 445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f134c : bv 32 := 0x6bc080e7.
Lemma F_f134c : fetch_word Ubsan.M.loaded_segments (0xf1394 : word) = Some W_f134c.
Proof. vm_refl. Qed.
Lemma D_f134c : decode_any W_f134c = Some (Jalr 1 1 1724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1350 : bv 32 := 0x929f50ef.
Lemma F_f1350 : fetch_word Ubsan.M.loaded_segments (0xf1398 : word) = Some W_f1350.
Proof. vm_refl. Qed.
Lemma D_f1350 : decode_any W_f1350 = Some (Jal 1 2054440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1354 : bv 32 := 0xd58f60ef.
Lemma F_f1354 : fetch_word Ubsan.M.loaded_segments (0xf139c : word) = Some W_f1354.
Proof. vm_refl. Qed.
Lemma D_f1354 : decode_any W_f1354 = Some (Jal 1 2057560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1358 : bv 32 := 0x1511a0ef.
Lemma F_f1358 : fetch_word Ubsan.M.loaded_segments (0xf13a0 : word) = Some W_f1358.
Proof. vm_refl. Qed.
Lemma D_f1358 : decode_any W_f1358 = Some (Jal 1 108880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f135c : bv 32 := 0x7a4b50ef.
Lemma F_f135c : fetch_word Ubsan.M.loaded_segments (0xf13a4 : word) = Some W_f135c.
Proof. vm_refl. Qed.
Lemma D_f135c : decode_any W_f135c = Some (Jal 1 743332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1360 : bv 32 := 0x650080ef.
Lemma F_f1360 : fetch_word Ubsan.M.loaded_segments (0xf13a8 : word) = Some W_f1360.
Proof. vm_refl. Qed.
Lemma D_f1360 : decode_any W_f1360 = Some (Jal 1 34384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1364 : bv 32 := 0x848f30ef.
Lemma F_f1364 : fetch_word Ubsan.M.loaded_segments (0xf13ac : word) = Some W_f1364.
Proof. vm_refl. Qed.
Lemma D_f1364 : decode_any W_f1364 = Some (Jal 1 2043976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1368 : bv 32 := 0xcf8f80ef.
Lemma F_f1368 : fetch_word Ubsan.M.loaded_segments (0xf13b0 : word) = Some W_f1368.
Proof. vm_refl. Qed.
Lemma D_f1368 : decode_any W_f1368 = Some (Jal 1 2065656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f136c : bv 32 := 0x001bd097.
Lemma F_f136c : fetch_word Ubsan.M.loaded_segments (0xf13b4 : word) = Some W_f136c.
Proof. vm_refl. Qed.
Lemma D_f136c : decode_any W_f136c = Some (Auipc 1 445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1370 : bv 32 := 0x708080e7.
Lemma F_f1370 : fetch_word Ubsan.M.loaded_segments (0xf13b8 : word) = Some W_f1370.
Proof. vm_refl. Qed.
Lemma D_f1370 : decode_any W_f1370 = Some (Jalr 1 1 1800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1374 : bv 32 := 0x001bd097.
Lemma F_f1374 : fetch_word Ubsan.M.loaded_segments (0xf13bc : word) = Some W_f1374.
Proof. vm_refl. Qed.
Lemma D_f1374 : decode_any W_f1374 = Some (Auipc 1 445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1378 : bv 32 := 0x728080e7.
Lemma F_f1378 : fetch_word Ubsan.M.loaded_segments (0xf13c0 : word) = Some W_f1378.
Proof. vm_refl. Qed.
Lemma D_f1378 : decode_any W_f1378 = Some (Jalr 1 1 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f137c : bv 32 := 0x00048023.
Lemma F_f137c : fetch_word Ubsan.M.loaded_segments (0xf13c4 : word) = Some W_f137c.
Proof. vm_refl. Qed.
Lemma D_f137c : decode_any W_f137c = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1380 : bv 32 := 0x01813083.
Lemma F_f1380 : fetch_word Ubsan.M.loaded_segments (0xf13c8 : word) = Some W_f1380.
Proof. vm_refl. Qed.
Lemma D_f1380 : decode_any W_f1380 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1384 : bv 32 := 0x01013403.
Lemma F_f1384 : fetch_word Ubsan.M.loaded_segments (0xf13cc : word) = Some W_f1384.
Proof. vm_refl. Qed.
Lemma D_f1384 : decode_any W_f1384 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1388 : bv 32 := 0x00813483.
Lemma F_f1388 : fetch_word Ubsan.M.loaded_segments (0xf13d0 : word) = Some W_f1388.
Proof. vm_refl. Qed.
Lemma D_f1388 : decode_any W_f1388 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f138c : bv 32 := 0x02010113.
Lemma F_f138c : fetch_word Ubsan.M.loaded_segments (0xf13d4 : word) = Some W_f138c.
Proof. vm_refl. Qed.
Lemma D_f138c : decode_any W_f138c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f1390 : bv 32 := 0x00008067.
Lemma F_f1390 : fetch_word Ubsan.M.loaded_segments (0xf13d8 : word) = Some W_f1390.
Proof. vm_refl. Qed.
Lemma D_f1390 : decode_any W_f1390 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
