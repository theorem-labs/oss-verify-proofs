(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_1337c : bv 32 := 0xffffd197.
Lemma F_1337c : fetch_word Ubsan.M.loaded_segments (0x13434 : word) = Some W_1337c.
Proof. vm_refl. Qed.
Lemma D_1337c : decode_any W_1337c = Some (Auipc 3 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13380 : bv 32 := 0x3cc18193.
Lemma F_13380 : fetch_word Ubsan.M.loaded_segments (0x13438 : word) = Some W_13380.
Proof. vm_refl. Qed.
Lemma D_13380 : decode_any W_13380 = Some (OpImm ALU_ADD 3 3 972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13384 : bv 32 := 0x00010513.
Lemma F_13384 : fetch_word Ubsan.M.loaded_segments (0x1343c : word) = Some W_13384.
Proof. vm_refl. Qed.
Lemma D_13384 : decode_any W_13384 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13388 : bv 32 := 0xfffed597.
Lemma F_13388 : fetch_word Ubsan.M.loaded_segments (0x13440 : word) = Some W_13388.
Proof. vm_refl. Qed.
Lemma D_13388 : decode_any W_13388 = Some (Auipc 11 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1338c : bv 32 := 0xbc058593.
Lemma F_1338c : fetch_word Ubsan.M.loaded_segments (0x13444 : word) = Some W_1338c.
Proof. vm_refl. Qed.
Lemma D_1338c : decode_any W_1338c = Some (OpImm ALU_ADD 11 11 3008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13390 : bv 32 := 0xff017113.
Lemma F_13390 : fetch_word Ubsan.M.loaded_segments (0x13448 : word) = Some W_13390.
Proof. vm_refl. Qed.
Lemma D_13390 : decode_any W_13390 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13394 : bv 32 := 0x0040006f.
Lemma F_13394 : fetch_word Ubsan.M.loaded_segments (0x1344c : word) = Some W_13394.
Proof. vm_refl. Qed.
Lemma D_13394 : decode_any W_13394 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13398 : bv 32 := 0x00052583.
Lemma F_13398 : fetch_word Ubsan.M.loaded_segments (0x13450 : word) = Some W_13398.
Proof. vm_refl. Qed.
Lemma D_13398 : decode_any W_13398 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1339c : bv 32 := 0x0001f617.
Lemma F_1339c : fetch_word Ubsan.M.loaded_segments (0x13454 : word) = Some W_1339c.
Proof. vm_refl. Qed.
Lemma D_1339c : decode_any W_1339c = Some (Auipc 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133a0 : bv 32 := 0x0001f697.
Lemma F_133a0 : fetch_word Ubsan.M.loaded_segments (0x13458 : word) = Some W_133a0.
Proof. vm_refl. Qed.
Lemma D_133a0 : decode_any W_133a0 = Some (Auipc 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133a4 : bv 32 := 0x0001f717.
Lemma F_133a4 : fetch_word Ubsan.M.loaded_segments (0x1345c : word) = Some W_133a4.
Proof. vm_refl. Qed.
Lemma D_133a4 : decode_any W_133a4 = Some (Auipc 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133a8 : bv 32 := 0xc6463783.
Lemma F_133a8 : fetch_word Ubsan.M.loaded_segments (0x13460 : word) = Some W_133a8.
Proof. vm_refl. Qed.
Lemma D_133a8 : decode_any W_133a8 = Some (Load SZ8 true 15 12 3172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133ac : bv 32 := 0xc686b683.
Lemma F_133ac : fetch_word Ubsan.M.loaded_segments (0x13464 : word) = Some W_133ac.
Proof. vm_refl. Qed.
Lemma D_133ac : decode_any W_133ac = Some (Load SZ8 true 13 13 3176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133b0 : bv 32 := 0xc6c73703.
Lemma F_133b0 : fetch_word Ubsan.M.loaded_segments (0x13468 : word) = Some W_133b0.
Proof. vm_refl. Qed.
Lemma D_133b0 : decode_any W_133b0 = Some (Load SZ8 true 14 14 3180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133b4 : bv 32 := 0x00850613.
Lemma F_133b4 : fetch_word Ubsan.M.loaded_segments (0x1346c : word) = Some W_133b4.
Proof. vm_refl. Qed.
Lemma D_133b4 : decode_any W_133b4 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133b8 : bv 32 := 0x00078513.
Lemma F_133b8 : fetch_word Ubsan.M.loaded_segments (0x13470 : word) = Some W_133b8.
Proof. vm_refl. Qed.
Lemma D_133b8 : decode_any W_133b8 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133bc : bv 32 := 0x00000793.
Lemma F_133bc : fetch_word Ubsan.M.loaded_segments (0x13474 : word) = Some W_133bc.
Proof. vm_refl. Qed.
Lemma D_133bc : decode_any W_133bc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133c0 : bv 32 := 0x72c1506f.
Lemma F_133c0 : fetch_word Ubsan.M.loaded_segments (0x13478 : word) = Some W_133c0.
Proof. vm_refl. Qed.
Lemma D_133c0 : decode_any W_133c0 = Some (Jal 0 87852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133c4 : bv 32 := 0xff010113.
Lemma F_133c4 : fetch_word Ubsan.M.loaded_segments (0x1347c : word) = Some W_133c4.
Proof. vm_refl. Qed.
Lemma D_133c4 : decode_any W_133c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133c8 : bv 32 := 0x00113423.
Lemma F_133c8 : fetch_word Ubsan.M.loaded_segments (0x13480 : word) = Some W_133c8.
Proof. vm_refl. Qed.
Lemma D_133c8 : decode_any W_133c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133cc : bv 32 := 0x00813023.
Lemma F_133cc : fetch_word Ubsan.M.loaded_segments (0x13484 : word) = Some W_133cc.
Proof. vm_refl. Qed.
Lemma D_133cc : decode_any W_133cc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133d0 : bv 32 := 0x01010413.
Lemma F_133d0 : fetch_word Ubsan.M.loaded_segments (0x13488 : word) = Some W_133d0.
Proof. vm_refl. Qed.
Lemma D_133d0 : decode_any W_133d0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133d4 : bv 32 := 0x00021517.
Lemma F_133d4 : fetch_word Ubsan.M.loaded_segments (0x1348c : word) = Some W_133d4.
Proof. vm_refl. Qed.
Lemma D_133d4 : decode_any W_133d4 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133d8 : bv 32 := 0xc0450513.
Lemma F_133d8 : fetch_word Ubsan.M.loaded_segments (0x13490 : word) = Some W_133d8.
Proof. vm_refl. Qed.
Lemma D_133d8 : decode_any W_133d8 = Some (OpImm ALU_ADD 10 10 3076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133dc : bv 32 := 0x00054503.
Lemma F_133dc : fetch_word Ubsan.M.loaded_segments (0x13494 : word) = Some W_133dc.
Proof. vm_refl. Qed.
Lemma D_133dc : decode_any W_133dc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133e0 : bv 32 := 0x00157513.
Lemma F_133e0 : fetch_word Ubsan.M.loaded_segments (0x13498 : word) = Some W_133e0.
Proof. vm_refl. Qed.
Lemma D_133e0 : decode_any W_133e0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133e4 : bv 32 := 0x00050663.
Lemma F_133e4 : fetch_word Ubsan.M.loaded_segments (0x1349c : word) = Some W_133e4.
Proof. vm_refl. Qed.
Lemma D_133e4 : decode_any W_133e4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133f0 : bv 32 := 0x00021517.
Lemma F_133f0 : fetch_word Ubsan.M.loaded_segments (0x134a8 : word) = Some W_133f0.
Proof. vm_refl. Qed.
Lemma D_133f0 : decode_any W_133f0 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133f4 : bv 32 := 0xbe850593.
Lemma F_133f4 : fetch_word Ubsan.M.loaded_segments (0x134ac : word) = Some W_133f4.
Proof. vm_refl. Qed.
Lemma D_133f4 : decode_any W_133f4 = Some (OpImm ALU_ADD 11 10 3048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133f8 : bv 32 := 0x00100513.
Lemma F_133f8 : fetch_word Ubsan.M.loaded_segments (0x134b0 : word) = Some W_133f8.
Proof. vm_refl. Qed.
Lemma D_133f8 : decode_any W_133f8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_133fc : bv 32 := 0x00a58023.
Lemma F_133fc : fetch_word Ubsan.M.loaded_segments (0x134b4 : word) = Some W_133fc.
Proof. vm_refl. Qed.
Lemma D_133fc : decode_any W_133fc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13400 : bv 32 := 0x0001f517.
Lemma F_13400 : fetch_word Ubsan.M.loaded_segments (0x134b8 : word) = Some W_13400.
Proof. vm_refl. Qed.
Lemma D_13400 : decode_any W_13400 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13404 : bv 32 := 0xc1853503.
Lemma F_13404 : fetch_word Ubsan.M.loaded_segments (0x134bc : word) = Some W_13404.
Proof. vm_refl. Qed.
Lemma D_13404 : decode_any W_13404 = Some (Load SZ8 true 10 10 3096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13408 : bv 32 := 0x02050063.
Lemma F_13408 : fetch_word Ubsan.M.loaded_segments (0x134c0 : word) = Some W_13408.
Proof. vm_refl. Qed.
Lemma D_13408 : decode_any W_13408 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13428 : bv 32 := 0x00813083.
Lemma F_13428 : fetch_word Ubsan.M.loaded_segments (0x134e0 : word) = Some W_13428.
Proof. vm_refl. Qed.
Lemma D_13428 : decode_any W_13428 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1342c : bv 32 := 0x00013403.
Lemma F_1342c : fetch_word Ubsan.M.loaded_segments (0x134e4 : word) = Some W_1342c.
Proof. vm_refl. Qed.
Lemma D_1342c : decode_any W_1342c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13430 : bv 32 := 0x01010113.
Lemma F_13430 : fetch_word Ubsan.M.loaded_segments (0x134e8 : word) = Some W_13430.
Proof. vm_refl. Qed.
Lemma D_13430 : decode_any W_13430 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13434 : bv 32 := 0x00008067.
Lemma F_13434 : fetch_word Ubsan.M.loaded_segments (0x134ec : word) = Some W_13434.
Proof. vm_refl. Qed.
Lemma D_13434 : decode_any W_13434 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13438 : bv 32 := 0xff010113.
Lemma F_13438 : fetch_word Ubsan.M.loaded_segments (0x134f0 : word) = Some W_13438.
Proof. vm_refl. Qed.
Lemma D_13438 : decode_any W_13438 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1343c : bv 32 := 0x00113423.
Lemma F_1343c : fetch_word Ubsan.M.loaded_segments (0x134f4 : word) = Some W_1343c.
Proof. vm_refl. Qed.
Lemma D_1343c : decode_any W_1343c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13440 : bv 32 := 0x00813023.
Lemma F_13440 : fetch_word Ubsan.M.loaded_segments (0x134f8 : word) = Some W_13440.
Proof. vm_refl. Qed.
Lemma D_13440 : decode_any W_13440 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13444 : bv 32 := 0x01010413.
Lemma F_13444 : fetch_word Ubsan.M.loaded_segments (0x134fc : word) = Some W_13444.
Proof. vm_refl. Qed.
Lemma D_13444 : decode_any W_13444 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13448 : bv 32 := 0x00021517.
Lemma F_13448 : fetch_word Ubsan.M.loaded_segments (0x13500 : word) = Some W_13448.
Proof. vm_refl. Qed.
Lemma D_13448 : decode_any W_13448 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1344c : bv 32 := 0xbd850513.
Lemma F_1344c : fetch_word Ubsan.M.loaded_segments (0x13504 : word) = Some W_1344c.
Proof. vm_refl. Qed.
Lemma D_1344c : decode_any W_1344c = Some (OpImm ALU_ADD 10 10 3032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13450 : bv 32 := 0x00054503.
Lemma F_13450 : fetch_word Ubsan.M.loaded_segments (0x13508 : word) = Some W_13450.
Proof. vm_refl. Qed.
Lemma D_13450 : decode_any W_13450 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13454 : bv 32 := 0x00157513.
Lemma F_13454 : fetch_word Ubsan.M.loaded_segments (0x1350c : word) = Some W_13454.
Proof. vm_refl. Qed.
Lemma D_13454 : decode_any W_13454 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13458 : bv 32 := 0x00050663.
Lemma F_13458 : fetch_word Ubsan.M.loaded_segments (0x13510 : word) = Some W_13458.
Proof. vm_refl. Qed.
Lemma D_13458 : decode_any W_13458 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13464 : bv 32 := 0x00021517.
Lemma F_13464 : fetch_word Ubsan.M.loaded_segments (0x1351c : word) = Some W_13464.
Proof. vm_refl. Qed.
Lemma D_13464 : decode_any W_13464 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13468 : bv 32 := 0xbbc50593.
Lemma F_13468 : fetch_word Ubsan.M.loaded_segments (0x13520 : word) = Some W_13468.
Proof. vm_refl. Qed.
Lemma D_13468 : decode_any W_13468 = Some (OpImm ALU_ADD 11 10 3004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1346c : bv 32 := 0x00100513.
Lemma F_1346c : fetch_word Ubsan.M.loaded_segments (0x13524 : word) = Some W_1346c.
Proof. vm_refl. Qed.
Lemma D_1346c : decode_any W_1346c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13470 : bv 32 := 0x00a58023.
Lemma F_13470 : fetch_word Ubsan.M.loaded_segments (0x13528 : word) = Some W_13470.
Proof. vm_refl. Qed.
Lemma D_13470 : decode_any W_13470 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13474 : bv 32 := 0x0001f517.
Lemma F_13474 : fetch_word Ubsan.M.loaded_segments (0x1352c : word) = Some W_13474.
Proof. vm_refl. Qed.
Lemma D_13474 : decode_any W_13474 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13478 : bv 32 := 0xbac53503.
Lemma F_13478 : fetch_word Ubsan.M.loaded_segments (0x13530 : word) = Some W_13478.
Proof. vm_refl. Qed.
Lemma D_13478 : decode_any W_13478 = Some (Load SZ8 true 10 10 2988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1347c : bv 32 := 0x00050e63.
Lemma F_1347c : fetch_word Ubsan.M.loaded_segments (0x13534 : word) = Some W_1347c.
Proof. vm_refl. Qed.
Lemma D_1347c : decode_any W_1347c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13498 : bv 32 := 0x0001f517.
Lemma F_13498 : fetch_word Ubsan.M.loaded_segments (0x13550 : word) = Some W_13498.
Proof. vm_refl. Qed.
Lemma D_13498 : decode_any W_13498 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1349c : bv 32 := 0xb9053503.
Lemma F_1349c : fetch_word Ubsan.M.loaded_segments (0x13554 : word) = Some W_1349c.
Proof. vm_refl. Qed.
Lemma D_1349c : decode_any W_1349c = Some (Load SZ8 true 10 10 2960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_134a0 : bv 32 := 0x00050c63.
Lemma F_134a0 : fetch_word Ubsan.M.loaded_segments (0x13558 : word) = Some W_134a0.
Proof. vm_refl. Qed.
Lemma D_134a0 : decode_any W_134a0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_134b8 : bv 32 := 0x00813083.
Lemma F_134b8 : fetch_word Ubsan.M.loaded_segments (0x13570 : word) = Some W_134b8.
Proof. vm_refl. Qed.
Lemma D_134b8 : decode_any W_134b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_134bc : bv 32 := 0x00013403.
Lemma F_134bc : fetch_word Ubsan.M.loaded_segments (0x13574 : word) = Some W_134bc.
Proof. vm_refl. Qed.
Lemma D_134bc : decode_any W_134bc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_134c0 : bv 32 := 0x01010113.
Lemma F_134c0 : fetch_word Ubsan.M.loaded_segments (0x13578 : word) = Some W_134c0.
Proof. vm_refl. Qed.
Lemma D_134c0 : decode_any W_134c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_134c4 : bv 32 := 0x00008067.
Lemma F_134c4 : fetch_word Ubsan.M.loaded_segments (0x1357c : word) = Some W_134c4.
Proof. vm_refl. Qed.
Lemma D_134c4 : decode_any W_134c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1351c : bv 32 := 0x24050a63.
Lemma F_1351c : fetch_word Ubsan.M.loaded_segments (0x135d4 : word) = Some W_1351c.
Proof. vm_refl. Qed.
Lemma D_1351c : decode_any W_1351c = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13520 : bv 32 := 0x00050b93.
Lemma F_13520 : fetch_word Ubsan.M.loaded_segments (0x135d8 : word) = Some W_13520.
Proof. vm_refl. Qed.
Lemma D_13520 : decode_any W_13520 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13524 : bv 32 := 0x00000993.
Lemma F_13524 : fetch_word Ubsan.M.loaded_segments (0x135dc : word) = Some W_13524.
Proof. vm_refl. Qed.
Lemma D_13524 : decode_any W_13524 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13528 : bv 32 := 0x00021517.
Lemma F_13528 : fetch_word Ubsan.M.loaded_segments (0x135e0 : word) = Some W_13528.
Proof. vm_refl. Qed.
Lemma D_13528 : decode_any W_13528 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1352c : bv 32 := 0xaf950b13.
Lemma F_1352c : fetch_word Ubsan.M.loaded_segments (0x135e4 : word) = Some W_1352c.
Proof. vm_refl. Qed.
Lemma D_1352c : decode_any W_1352c = Some (OpImm ALU_ADD 22 10 2809, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13530 : bv 32 := 0x03501263.
Lemma F_13530 : fetch_word Ubsan.M.loaded_segments (0x135e8 : word) = Some W_13530.
Proof. vm_refl. Qed.
Lemma D_13530 : decode_any W_13530 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13538 : bv 32 := 0x01348533.
Lemma F_13538 : fetch_word Ubsan.M.loaded_segments (0x135f0 : word) = Some W_13538.
Proof. vm_refl. Qed.
Lemma D_13538 : decode_any W_13538 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1353c : bv 32 := 0x000b0593.
Lemma F_1353c : fetch_word Ubsan.M.loaded_segments (0x135f4 : word) = Some W_1353c.
Proof. vm_refl. Qed.
Lemma D_1353c : decode_any W_1353c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13540 : bv 32 := 0x000b8613.
Lemma F_13540 : fetch_word Ubsan.M.loaded_segments (0x135f8 : word) = Some W_13540.
Proof. vm_refl. Qed.
Lemma D_13540 : decode_any W_13540 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13544 : bv 32 := 0x0b01d0ef.
Lemma F_13544 : fetch_word Ubsan.M.loaded_segments (0x135fc : word) = Some W_13544.
Proof. vm_refl. Qed.
Lemma D_13544 : decode_any W_13544 = Some (Jal 1 118960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13548 : bv 32 := 0x013b89b3.
Lemma F_13548 : fetch_word Ubsan.M.loaded_segments (0x13600 : word) = Some W_13548.
Proof. vm_refl. Qed.
Lemma D_13548 : decode_any W_13548 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1354c : bv 32 := 0x00048b93.
Lemma F_1354c : fetch_word Ubsan.M.loaded_segments (0x13604 : word) = Some W_1354c.
Proof. vm_refl. Qed.
Lemma D_1354c : decode_any W_1354c = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13550 : bv 32 := 0x01598663.
Lemma F_13550 : fetch_word Ubsan.M.loaded_segments (0x13608 : word) = Some W_13550.
Proof. vm_refl. Qed.
Lemma D_13550 : decode_any W_13550 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13554 : bv 32 := 0x000b8493.
Lemma F_13554 : fetch_word Ubsan.M.loaded_segments (0x1360c : word) = Some W_13554.
Proof. vm_refl. Qed.
Lemma D_13554 : decode_any W_13554 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13558 : bv 32 := 0x03c0006f.
Lemma F_13558 : fetch_word Ubsan.M.loaded_segments (0x13610 : word) = Some W_13558.
Proof. vm_refl. Qed.
Lemma D_13558 : decode_any W_13558 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13594 : bv 32 := 0x413a8633.
Lemma F_13594 : fetch_word Ubsan.M.loaded_segments (0x1364c : word) = Some W_13594.
Proof. vm_refl. Qed.
Lemma D_13594 : decode_any W_13594 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13598 : bv 32 := 0x00010537.
Lemma F_13598 : fetch_word Ubsan.M.loaded_segments (0x13650 : word) = Some W_13598.
Proof. vm_refl. Qed.
Lemma D_13598 : decode_any W_13598 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1359c : bv 32 := 0x00a66463.
Lemma F_1359c : fetch_word Ubsan.M.loaded_segments (0x13654 : word) = Some W_1359c.
Proof. vm_refl. Qed.
Lemma D_1359c : decode_any W_1359c = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a0 : bv 32 := 0x00010637.
Lemma F_135a0 : fetch_word Ubsan.M.loaded_segments (0x13658 : word) = Some W_135a0.
Proof. vm_refl. Qed.
Lemma D_135a0 : decode_any W_135a0 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a4 : bv 32 := 0x000a0513.
Lemma F_135a4 : fetch_word Ubsan.M.loaded_segments (0x1365c : word) = Some W_135a4.
Proof. vm_refl. Qed.
Lemma D_135a4 : decode_any W_135a4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a8 : bv 32 := 0x000b0593.
Lemma F_135a8 : fetch_word Ubsan.M.loaded_segments (0x13660 : word) = Some W_135a8.
Proof. vm_refl. Qed.
Lemma D_135a8 : decode_any W_135a8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135ac : bv 32 := 0x1f11d0ef.
Lemma F_135ac : fetch_word Ubsan.M.loaded_segments (0x13664 : word) = Some W_135ac.
Proof. vm_refl. Qed.
Lemma D_135ac : decode_any W_135ac = Some (Jal 1 121328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b0 : bv 32 := 0x14054263.
Lemma F_135b0 : fetch_word Ubsan.M.loaded_segments (0x13668 : word) = Some W_135b0.
Proof. vm_refl. Qed.
Lemma D_135b0 : decode_any W_135b0 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b4 : bv 32 := 0x00050b93.
Lemma F_135b4 : fetch_word Ubsan.M.loaded_segments (0x1366c : word) = Some W_135b4.
Proof. vm_refl. Qed.
Lemma D_135b4 : decode_any W_135b4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b8 : bv 32 := 0xf80510e3.
Lemma F_135b8 : fetch_word Ubsan.M.loaded_segments (0x13670 : word) = Some W_135b8.
Proof. vm_refl. Qed.
Lemma D_135b8 : decode_any W_135b8 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135bc : bv 32 := 0x000a0513.
Lemma F_135bc : fetch_word Ubsan.M.loaded_segments (0x13674 : word) = Some W_135bc.
Proof. vm_refl. Qed.
Lemma D_135bc : decode_any W_135bc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135c0 : bv 32 := 0x17d1d0ef.
Lemma F_135c0 : fetch_word Ubsan.M.loaded_segments (0x13678 : word) = Some W_135c0.
Proof. vm_refl. Qed.
Lemma D_135c0 : decode_any W_135c0 = Some (Jal 1 121212, 4%Z).
Proof. vm_refl. Qed.

