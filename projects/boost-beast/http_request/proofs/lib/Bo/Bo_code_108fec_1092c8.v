(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_108fec : bv 32 := 0xff010113.
Lemma F_108fec : fetch_word AsanUbsan.M.loaded_segments (0x108fec : word) = Some W_108fec.
Proof. vm_refl. Qed.
Lemma D_108fec : decode_any W_108fec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ff0 : bv 32 := 0x00113423.
Lemma F_108ff0 : fetch_word AsanUbsan.M.loaded_segments (0x108ff0 : word) = Some W_108ff0.
Proof. vm_refl. Qed.
Lemma D_108ff0 : decode_any W_108ff0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ff4 : bv 32 := 0x07852503.
Lemma F_108ff4 : fetch_word AsanUbsan.M.loaded_segments (0x108ff4 : word) = Some W_108ff4.
Proof. vm_refl. Qed.
Lemma D_108ff4 : decode_any W_108ff4 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ff8 : bv 32 := 0xff1ff0ef.
Lemma F_108ff8 : fetch_word AsanUbsan.M.loaded_segments (0x108ff8 : word) = Some W_108ff8.
Proof. vm_refl. Qed.
Lemma D_108ff8 : decode_any W_108ff8 = Some (Jal 1 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ffc : bv 32 := 0x03900893.
Lemma F_108ffc : fetch_word AsanUbsan.M.loaded_segments (0x108ffc : word) = Some W_108ffc.
Proof. vm_refl. Qed.
Lemma D_108ffc : decode_any W_108ffc = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109000 : bv 32 := 0x00000073.
Lemma F_109000 : fetch_word AsanUbsan.M.loaded_segments (0x109000 : word) = Some W_109000.
Proof. vm_refl. Qed.
Lemma D_109000 : decode_any W_109000 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_109000 : is_ecall W_109000 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_109004 : bv 32 := 0x93dfa0ef.
Lemma F_109004 : fetch_word AsanUbsan.M.loaded_segments (0x109004 : word) = Some W_109004.
Proof. vm_refl. Qed.
Lemma D_109004 : decode_any W_109004 = Some (Jal 1 2074940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109008 : bv 32 := 0x0005051b.
Lemma F_109008 : fetch_word AsanUbsan.M.loaded_segments (0x109008 : word) = Some W_109008.
Proof. vm_refl. Qed.
Lemma D_109008 : decode_any W_109008 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10900c : bv 32 := 0x00813083.
Lemma F_10900c : fetch_word AsanUbsan.M.loaded_segments (0x10900c : word) = Some W_10900c.
Proof. vm_refl. Qed.
Lemma D_10900c : decode_any W_10900c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109010 : bv 32 := 0x01010113.
Lemma F_109010 : fetch_word AsanUbsan.M.loaded_segments (0x109010 : word) = Some W_109010.
Proof. vm_refl. Qed.
Lemma D_109010 : decode_any W_109010 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109014 : bv 32 := 0x00008067.
Lemma F_109014 : fetch_word AsanUbsan.M.loaded_segments (0x109014 : word) = Some W_109014.
Proof. vm_refl. Qed.
Lemma D_109014 : decode_any W_109014 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109018 : bv 32 := 0xfb010113.
Lemma F_109018 : fetch_word AsanUbsan.M.loaded_segments (0x109018 : word) = Some W_109018.
Proof. vm_refl. Qed.
Lemma D_109018 : decode_any W_109018 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10901c : bv 32 := 0x04113423.
Lemma F_10901c : fetch_word AsanUbsan.M.loaded_segments (0x10901c : word) = Some W_10901c.
Proof. vm_refl. Qed.
Lemma D_10901c : decode_any W_10901c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109020 : bv 32 := 0x04813023.
Lemma F_109020 : fetch_word AsanUbsan.M.loaded_segments (0x109020 : word) = Some W_109020.
Proof. vm_refl. Qed.
Lemma D_109020 : decode_any W_109020 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109024 : bv 32 := 0x02913c23.
Lemma F_109024 : fetch_word AsanUbsan.M.loaded_segments (0x109024 : word) = Some W_109024.
Proof. vm_refl. Qed.
Lemma D_109024 : decode_any W_109024 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109028 : bv 32 := 0x03213823.
Lemma F_109028 : fetch_word AsanUbsan.M.loaded_segments (0x109028 : word) = Some W_109028.
Proof. vm_refl. Qed.
Lemma D_109028 : decode_any W_109028 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10902c : bv 32 := 0x03313423.
Lemma F_10902c : fetch_word AsanUbsan.M.loaded_segments (0x10902c : word) = Some W_10902c.
Proof. vm_refl. Qed.
Lemma D_10902c : decode_any W_10902c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109030 : bv 32 := 0x00060413.
Lemma F_109030 : fetch_word AsanUbsan.M.loaded_segments (0x109030 : word) = Some W_109030.
Proof. vm_refl. Qed.
Lemma D_109030 : decode_any W_109030 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109034 : bv 32 := 0x00058913.
Lemma F_109034 : fetch_word AsanUbsan.M.loaded_segments (0x109034 : word) = Some W_109034.
Proof. vm_refl. Qed.
Lemma D_109034 : decode_any W_109034 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109038 : bv 32 := 0x00050493.
Lemma F_109038 : fetch_word AsanUbsan.M.loaded_segments (0x109038 : word) = Some W_109038.
Proof. vm_refl. Qed.
Lemma D_109038 : decode_any W_109038 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10903c : bv 32 := 0x00017517.
Lemma F_10903c : fetch_word AsanUbsan.M.loaded_segments (0x10903c : word) = Some W_10903c.
Proof. vm_refl. Qed.
Lemma D_10903c : decode_any W_10903c = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109040 : bv 32 := 0x3b453983.
Lemma F_109040 : fetch_word AsanUbsan.M.loaded_segments (0x109040 : word) = Some W_109040.
Proof. vm_refl. Qed.
Lemma D_109040 : decode_any W_109040 = Some (Load SZ8 true 19 10 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109044 : bv 32 := 0x0009b503.
Lemma F_109044 : fetch_word AsanUbsan.M.loaded_segments (0x109044 : word) = Some W_109044.
Proof. vm_refl. Qed.
Lemma D_109044 : decode_any W_109044 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109048 : bv 32 := 0x02a13023.
Lemma F_109048 : fetch_word AsanUbsan.M.loaded_segments (0x109048 : word) = Some W_109048.
Proof. vm_refl. Qed.
Lemma D_109048 : decode_any W_109048 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10904c : bv 32 := 0x0604b603.
Lemma F_10904c : fetch_word AsanUbsan.M.loaded_segments (0x10904c : word) = Some W_10904c.
Proof. vm_refl. Qed.
Lemma D_10904c : decode_any W_10904c = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109050 : bv 32 := 0x0584b583.
Lemma F_109050 : fetch_word AsanUbsan.M.loaded_segments (0x109050 : word) = Some W_109050.
Proof. vm_refl. Qed.
Lemma D_109050 : decode_any W_109050 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109054 : bv 32 := 0x0784a503.
Lemma F_109054 : fetch_word AsanUbsan.M.loaded_segments (0x109054 : word) = Some W_109054.
Proof. vm_refl. Qed.
Lemma D_109054 : decode_any W_109054 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109058 : bv 32 := 0x00c036b3.
Lemma F_109058 : fetch_word AsanUbsan.M.loaded_segments (0x109058 : word) = Some W_109058.
Proof. vm_refl. Qed.
Lemma D_109058 : decode_any W_109058 = Some (Op ALU_SLTU 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10905c : bv 32 := 0x40d406b3.
Lemma F_10905c : fetch_word AsanUbsan.M.loaded_segments (0x10905c : word) = Some W_10905c.
Proof. vm_refl. Qed.
Lemma D_10905c : decode_any W_10905c = Some (Op ALU_SUB 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109060 : bv 32 := 0x01213023.
Lemma F_109060 : fetch_word AsanUbsan.M.loaded_segments (0x109060 : word) = Some W_109060.
Proof. vm_refl. Qed.
Lemma D_109060 : decode_any W_109060 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109064 : bv 32 := 0x00d13423.
Lemma F_109064 : fetch_word AsanUbsan.M.loaded_segments (0x109064 : word) = Some W_109064.
Proof. vm_refl. Qed.
Lemma D_109064 : decode_any W_109064 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109068 : bv 32 := 0x00b13823.
Lemma F_109068 : fetch_word AsanUbsan.M.loaded_segments (0x109068 : word) = Some W_109068.
Proof. vm_refl. Qed.
Lemma D_109068 : decode_any W_109068 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10906c : bv 32 := 0x00c13c23.
Lemma F_10906c : fetch_word AsanUbsan.M.loaded_segments (0x10906c : word) = Some W_10906c.
Proof. vm_refl. Qed.
Lemma D_10906c : decode_any W_10906c = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109070 : bv 32 := 0x04068c63.
Lemma F_109070 : fetch_word AsanUbsan.M.loaded_segments (0x109070 : word) = Some W_109070.
Proof. vm_refl. Qed.
Lemma D_109070 : decode_any W_109070 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109074 : bv 32 := 0x04100893.
Lemma F_109074 : fetch_word AsanUbsan.M.loaded_segments (0x109074 : word) = Some W_109074.
Proof. vm_refl. Qed.
Lemma D_109074 : decode_any W_109074 = Some (OpImm ALU_ADD 17 0 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109078 : bv 32 := 0x00010593.
Lemma F_109078 : fetch_word AsanUbsan.M.loaded_segments (0x109078 : word) = Some W_109078.
Proof. vm_refl. Qed.
Lemma D_109078 : decode_any W_109078 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10907c : bv 32 := 0x00200613.
Lemma F_10907c : fetch_word AsanUbsan.M.loaded_segments (0x10907c : word) = Some W_10907c.
Proof. vm_refl. Qed.
Lemma D_10907c : decode_any W_10907c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109080 : bv 32 := 0x00000073.
Lemma F_109080 : fetch_word AsanUbsan.M.loaded_segments (0x109080 : word) = Some W_109080.
Proof. vm_refl. Qed.
Lemma D_109080 : decode_any W_109080 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_109080 : is_ecall W_109080 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_109084 : bv 32 := 0x8bdfa0ef.
Lemma F_109084 : fetch_word AsanUbsan.M.loaded_segments (0x109084 : word) = Some W_109084.
Proof. vm_refl. Qed.
Lemma D_109084 : decode_any W_109084 = Some (Jal 1 2074812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109088 : bv 32 := 0x04a05863.
Lemma F_109088 : fetch_word AsanUbsan.M.loaded_segments (0x109088 : word) = Some W_109088.
Proof. vm_refl. Qed.
Lemma D_109088 : decode_any W_109088 = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10908c : bv 32 := 0x00813603.
Lemma F_10908c : fetch_word AsanUbsan.M.loaded_segments (0x10908c : word) = Some W_10908c.
Proof. vm_refl. Qed.
Lemma D_10908c : decode_any W_10908c = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109090 : bv 32 := 0x04a67a63.
Lemma F_109090 : fetch_word AsanUbsan.M.loaded_segments (0x109090 : word) = Some W_109090.
Proof. vm_refl. Qed.
Lemma D_109090 : decode_any W_109090 = Some (Branch BC_GEU 12 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109094 : bv 32 := 0x0584b583.
Lemma F_109094 : fetch_word AsanUbsan.M.loaded_segments (0x109094 : word) = Some W_109094.
Proof. vm_refl. Qed.
Lemma D_109094 : decode_any W_109094 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109098 : bv 32 := 0x0604b683.
Lemma F_109098 : fetch_word AsanUbsan.M.loaded_segments (0x109098 : word) = Some W_109098.
Proof. vm_refl. Qed.
Lemma D_109098 : decode_any W_109098 = Some (Load SZ8 true 13 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10909c : bv 32 := 0x40c50533.
Lemma F_10909c : fetch_word AsanUbsan.M.loaded_segments (0x10909c : word) = Some W_10909c.
Proof. vm_refl. Qed.
Lemma D_10909c : decode_any W_10909c = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090a0 : bv 32 := 0x00a58533.
Lemma F_1090a0 : fetch_word AsanUbsan.M.loaded_segments (0x1090a0 : word) = Some W_1090a0.
Proof. vm_refl. Qed.
Lemma D_1090a0 : decode_any W_1090a0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090a4 : bv 32 := 0x00b4b423.
Lemma F_1090a4 : fetch_word AsanUbsan.M.loaded_segments (0x1090a4 : word) = Some W_1090a4.
Proof. vm_refl. Qed.
Lemma D_1090a4 : decode_any W_1090a4 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090a8 : bv 32 := 0x00a4b823.
Lemma F_1090a8 : fetch_word AsanUbsan.M.loaded_segments (0x1090a8 : word) = Some W_1090a8.
Proof. vm_refl. Qed.
Lemma D_1090a8 : decode_any W_1090a8 = Some (Store SZ8 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090ac : bv 32 := 0x04068a63.
Lemma F_1090ac : fetch_word AsanUbsan.M.loaded_segments (0x1090ac : word) = Some W_1090ac.
Proof. vm_refl. Qed.
Lemma D_1090ac : decode_any W_1090ac = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090b0 : bv 32 := 0x00158513.
Lemma F_1090b0 : fetch_word AsanUbsan.M.loaded_segments (0x1090b0 : word) = Some W_1090b0.
Proof. vm_refl. Qed.
Lemma D_1090b0 : decode_any W_1090b0 = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090b4 : bv 32 := 0x00a4b423.
Lemma F_1090b4 : fetch_word AsanUbsan.M.loaded_segments (0x1090b4 : word) = Some W_1090b4.
Proof. vm_refl. Qed.
Lemma D_1090b4 : decode_any W_1090b4 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090b8 : bv 32 := 0x0005c503.
Lemma F_1090b8 : fetch_word AsanUbsan.M.loaded_segments (0x1090b8 : word) = Some W_1090b8.
Proof. vm_refl. Qed.
Lemma D_1090b8 : decode_any W_1090b8 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090bc : bv 32 := 0x00890933.
Lemma F_1090bc : fetch_word AsanUbsan.M.loaded_segments (0x1090bc : word) = Some W_1090bc.
Proof. vm_refl. Qed.
Lemma D_1090bc : decode_any W_1090bc = Some (Op ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090c0 : bv 32 := 0xfea90fa3.
Lemma F_1090c0 : fetch_word AsanUbsan.M.loaded_segments (0x1090c0 : word) = Some W_1090c0.
Proof. vm_refl. Qed.
Lemma D_1090c0 : decode_any W_1090c0 = Some (Store SZ1 18 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090c4 : bv 32 := 0x03c0006f.
Lemma F_1090c4 : fetch_word AsanUbsan.M.loaded_segments (0x1090c4 : word) = Some W_1090c4.
Proof. vm_refl. Qed.
Lemma D_1090c4 : decode_any W_1090c4 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090c8 : bv 32 := 0x03f00893.
Lemma F_1090c8 : fetch_word AsanUbsan.M.loaded_segments (0x1090c8 : word) = Some W_1090c8.
Proof. vm_refl. Qed.
Lemma D_1090c8 : decode_any W_1090c8 = Some (OpImm ALU_ADD 17 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090cc : bv 32 := 0x00000073.
Lemma F_1090cc : fetch_word AsanUbsan.M.loaded_segments (0x1090cc : word) = Some W_1090cc.
Proof. vm_refl. Qed.
Lemma D_1090cc : decode_any W_1090cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1090cc : is_ecall W_1090cc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1090d0 : bv 32 := 0x871fa0ef.
Lemma F_1090d0 : fetch_word AsanUbsan.M.loaded_segments (0x1090d0 : word) = Some W_1090d0.
Proof. vm_refl. Qed.
Lemma D_1090d0 : decode_any W_1090d0 = Some (Jal 1 2074736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090d4 : bv 32 := 0xfaa04ce3.
Lemma F_1090d4 : fetch_word AsanUbsan.M.loaded_segments (0x1090d4 : word) = Some W_1090d4.
Proof. vm_refl. Qed.
Lemma D_1090d4 : decode_any W_1090d4 = Some (Branch BC_LT 0 10 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090d8 : bv 32 := 0x00050a63.
Lemma F_1090d8 : fetch_word AsanUbsan.M.loaded_segments (0x1090d8 : word) = Some W_1090d8.
Proof. vm_refl. Qed.
Lemma D_1090d8 : decode_any W_1090d8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090dc : bv 32 := 0x02000513.
Lemma F_1090dc : fetch_word AsanUbsan.M.loaded_segments (0x1090dc : word) = Some W_1090dc.
Proof. vm_refl. Qed.
Lemma D_1090dc : decode_any W_1090dc = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090e0 : bv 32 := 0x0100006f.
Lemma F_1090e0 : fetch_word AsanUbsan.M.loaded_segments (0x1090e0 : word) = Some W_1090e0.
Proof. vm_refl. Qed.
Lemma D_1090e0 : decode_any W_1090e0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090e4 : bv 32 := 0x00050413.
Lemma F_1090e4 : fetch_word AsanUbsan.M.loaded_segments (0x1090e4 : word) = Some W_1090e4.
Proof. vm_refl. Qed.
Lemma D_1090e4 : decode_any W_1090e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090e8 : bv 32 := 0x0180006f.
Lemma F_1090e8 : fetch_word AsanUbsan.M.loaded_segments (0x1090e8 : word) = Some W_1090e8.
Proof. vm_refl. Qed.
Lemma D_1090e8 : decode_any W_1090e8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090ec : bv 32 := 0x01000513.
Lemma F_1090ec : fetch_word AsanUbsan.M.loaded_segments (0x1090ec : word) = Some W_1090ec.
Proof. vm_refl. Qed.
Lemma D_1090ec : decode_any W_1090ec = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090f0 : bv 32 := 0x00000413.
Lemma F_1090f0 : fetch_word AsanUbsan.M.loaded_segments (0x1090f0 : word) = Some W_1090f0.
Proof. vm_refl. Qed.
Lemma D_1090f0 : decode_any W_1090f0 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090f4 : bv 32 := 0x0004a583.
Lemma F_1090f4 : fetch_word AsanUbsan.M.loaded_segments (0x1090f4 : word) = Some W_1090f4.
Proof. vm_refl. Qed.
Lemma D_1090f4 : decode_any W_1090f4 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090f8 : bv 32 := 0x00a5e533.
Lemma F_1090f8 : fetch_word AsanUbsan.M.loaded_segments (0x1090f8 : word) = Some W_1090f8.
Proof. vm_refl. Qed.
Lemma D_1090f8 : decode_any W_1090f8 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1090fc : bv 32 := 0x00a4a023.
Lemma F_1090fc : fetch_word AsanUbsan.M.loaded_segments (0x1090fc : word) = Some W_1090fc.
Proof. vm_refl. Qed.
Lemma D_1090fc : decode_any W_1090fc = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109100 : bv 32 := 0x0009b503.
Lemma F_109100 : fetch_word AsanUbsan.M.loaded_segments (0x109100 : word) = Some W_109100.
Proof. vm_refl. Qed.
Lemma D_109100 : decode_any W_109100 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109104 : bv 32 := 0x02013583.
Lemma F_109104 : fetch_word AsanUbsan.M.loaded_segments (0x109104 : word) = Some W_109104.
Proof. vm_refl. Qed.
Lemma D_109104 : decode_any W_109104 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109108 : bv 32 := 0x02b51263.
Lemma F_109108 : fetch_word AsanUbsan.M.loaded_segments (0x109108 : word) = Some W_109108.
Proof. vm_refl. Qed.
Lemma D_109108 : decode_any W_109108 = Some (Branch BC_NE 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10910c : bv 32 := 0x00040513.
Lemma F_10910c : fetch_word AsanUbsan.M.loaded_segments (0x10910c : word) = Some W_10910c.
Proof. vm_refl. Qed.
Lemma D_10910c : decode_any W_10910c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109110 : bv 32 := 0x04813083.
Lemma F_109110 : fetch_word AsanUbsan.M.loaded_segments (0x109110 : word) = Some W_109110.
Proof. vm_refl. Qed.
Lemma D_109110 : decode_any W_109110 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109114 : bv 32 := 0x04013403.
Lemma F_109114 : fetch_word AsanUbsan.M.loaded_segments (0x109114 : word) = Some W_109114.
Proof. vm_refl. Qed.
Lemma D_109114 : decode_any W_109114 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109118 : bv 32 := 0x03813483.
Lemma F_109118 : fetch_word AsanUbsan.M.loaded_segments (0x109118 : word) = Some W_109118.
Proof. vm_refl. Qed.
Lemma D_109118 : decode_any W_109118 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10911c : bv 32 := 0x03013903.
Lemma F_10911c : fetch_word AsanUbsan.M.loaded_segments (0x10911c : word) = Some W_10911c.
Proof. vm_refl. Qed.
Lemma D_10911c : decode_any W_10911c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109120 : bv 32 := 0x02813983.
Lemma F_109120 : fetch_word AsanUbsan.M.loaded_segments (0x109120 : word) = Some W_109120.
Proof. vm_refl. Qed.
Lemma D_109120 : decode_any W_109120 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109124 : bv 32 := 0x05010113.
Lemma F_109124 : fetch_word AsanUbsan.M.loaded_segments (0x109124 : word) = Some W_109124.
Proof. vm_refl. Qed.
Lemma D_109124 : decode_any W_109124 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109128 : bv 32 := 0x00008067.
Lemma F_109128 : fetch_word AsanUbsan.M.loaded_segments (0x109128 : word) = Some W_109128.
Proof. vm_refl. Qed.
Lemma D_109128 : decode_any W_109128 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10912c : bv 32 := 0x9a8fa0ef.
Lemma F_10912c : fetch_word AsanUbsan.M.loaded_segments (0x10912c : word) = Some W_10912c.
Proof. vm_refl. Qed.
Lemma D_10912c : decode_any W_10912c = Some (Jal 1 2073000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109130 : bv 32 := 0x07852503.
Lemma F_109130 : fetch_word AsanUbsan.M.loaded_segments (0x109130 : word) = Some W_109130.
Proof. vm_refl. Qed.
Lemma D_109130 : decode_any W_109130 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109134 : bv 32 := 0x5440f06f.
Lemma F_109134 : fetch_word AsanUbsan.M.loaded_segments (0x109134 : word) = Some W_109134.
Proof. vm_refl. Qed.
Lemma D_109134 : decode_any W_109134 = Some (Jal 0 62788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109138 : bv 32 := 0xf9010113.
Lemma F_109138 : fetch_word AsanUbsan.M.loaded_segments (0x109138 : word) = Some W_109138.
Proof. vm_refl. Qed.
Lemma D_109138 : decode_any W_109138 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10913c : bv 32 := 0x06113423.
Lemma F_10913c : fetch_word AsanUbsan.M.loaded_segments (0x10913c : word) = Some W_10913c.
Proof. vm_refl. Qed.
Lemma D_10913c : decode_any W_10913c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109140 : bv 32 := 0x06813023.
Lemma F_109140 : fetch_word AsanUbsan.M.loaded_segments (0x109140 : word) = Some W_109140.
Proof. vm_refl. Qed.
Lemma D_109140 : decode_any W_109140 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109144 : bv 32 := 0x04913c23.
Lemma F_109144 : fetch_word AsanUbsan.M.loaded_segments (0x109144 : word) = Some W_109144.
Proof. vm_refl. Qed.
Lemma D_109144 : decode_any W_109144 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109148 : bv 32 := 0x05213823.
Lemma F_109148 : fetch_word AsanUbsan.M.loaded_segments (0x109148 : word) = Some W_109148.
Proof. vm_refl. Qed.
Lemma D_109148 : decode_any W_109148 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10914c : bv 32 := 0x05313423.
Lemma F_10914c : fetch_word AsanUbsan.M.loaded_segments (0x10914c : word) = Some W_10914c.
Proof. vm_refl. Qed.
Lemma D_10914c : decode_any W_10914c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109150 : bv 32 := 0x05413023.
Lemma F_109150 : fetch_word AsanUbsan.M.loaded_segments (0x109150 : word) = Some W_109150.
Proof. vm_refl. Qed.
Lemma D_109150 : decode_any W_109150 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109154 : bv 32 := 0x03513c23.
Lemma F_109154 : fetch_word AsanUbsan.M.loaded_segments (0x109154 : word) = Some W_109154.
Proof. vm_refl. Qed.
Lemma D_109154 : decode_any W_109154 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109158 : bv 32 := 0x03613823.
Lemma F_109158 : fetch_word AsanUbsan.M.loaded_segments (0x109158 : word) = Some W_109158.
Proof. vm_refl. Qed.
Lemma D_109158 : decode_any W_109158 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10915c : bv 32 := 0x00060413.
Lemma F_10915c : fetch_word AsanUbsan.M.loaded_segments (0x10915c : word) = Some W_10915c.
Proof. vm_refl. Qed.
Lemma D_10915c : decode_any W_10915c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109160 : bv 32 := 0x00050493.
Lemma F_109160 : fetch_word AsanUbsan.M.loaded_segments (0x109160 : word) = Some W_109160.
Proof. vm_refl. Qed.
Lemma D_109160 : decode_any W_109160 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109164 : bv 32 := 0x00017517.
Lemma F_109164 : fetch_word AsanUbsan.M.loaded_segments (0x109164 : word) = Some W_109164.
Proof. vm_refl. Qed.
Lemma D_109164 : decode_any W_109164 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109168 : bv 32 := 0x28c53a83.
Lemma F_109168 : fetch_word AsanUbsan.M.loaded_segments (0x109168 : word) = Some W_109168.
Proof. vm_refl. Qed.
Lemma D_109168 : decode_any W_109168 = Some (Load SZ8 true 21 10 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10916c : bv 32 := 0x000ab503.
Lemma F_10916c : fetch_word AsanUbsan.M.loaded_segments (0x10916c : word) = Some W_10916c.
Proof. vm_refl. Qed.
Lemma D_10916c : decode_any W_10916c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109170 : bv 32 := 0x02a13423.
Lemma F_109170 : fetch_word AsanUbsan.M.loaded_segments (0x109170 : word) = Some W_109170.
Proof. vm_refl. Qed.
Lemma D_109170 : decode_any W_109170 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109174 : bv 32 := 0x0284b503.
Lemma F_109174 : fetch_word AsanUbsan.M.loaded_segments (0x109174 : word) = Some W_109174.
Proof. vm_refl. Qed.
Lemma D_109174 : decode_any W_109174 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109178 : bv 32 := 0x0384b603.
Lemma F_109178 : fetch_word AsanUbsan.M.loaded_segments (0x109178 : word) = Some W_109178.
Proof. vm_refl. Qed.
Lemma D_109178 : decode_any W_109178 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10917c : bv 32 := 0x40c50b33.
Lemma F_10917c : fetch_word AsanUbsan.M.loaded_segments (0x10917c : word) = Some W_10917c.
Proof. vm_refl. Qed.
Lemma D_10917c : decode_any W_10917c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109180 : bv 32 := 0x00c546b3.
Lemma F_109180 : fetch_word AsanUbsan.M.loaded_segments (0x109180 : word) = Some W_109180.
Proof. vm_refl. Qed.
Lemma D_109180 : decode_any W_109180 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109184 : bv 32 := 0x00c13423.
Lemma F_109184 : fetch_word AsanUbsan.M.loaded_segments (0x109184 : word) = Some W_109184.
Proof. vm_refl. Qed.
Lemma D_109184 : decode_any W_109184 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109188 : bv 32 := 0x01613823.
Lemma F_109188 : fetch_word AsanUbsan.M.loaded_segments (0x109188 : word) = Some W_109188.
Proof. vm_refl. Qed.
Lemma D_109188 : decode_any W_109188 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10918c : bv 32 := 0x00b13c23.
Lemma F_10918c : fetch_word AsanUbsan.M.loaded_segments (0x10918c : word) = Some W_10918c.
Proof. vm_refl. Qed.
Lemma D_10918c : decode_any W_10918c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109190 : bv 32 := 0x02813023.
Lemma F_109190 : fetch_word AsanUbsan.M.loaded_segments (0x109190 : word) = Some W_109190.
Proof. vm_refl. Qed.
Lemma D_109190 : decode_any W_109190 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109194 : bv 32 := 0x008b0b33.
Lemma F_109194 : fetch_word AsanUbsan.M.loaded_segments (0x109194 : word) = Some W_109194.
Proof. vm_refl. Qed.
Lemma D_109194 : decode_any W_109194 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109198 : bv 32 := 0x00d03933.
Lemma F_109198 : fetch_word AsanUbsan.M.loaded_segments (0x109198 : word) = Some W_109198.
Proof. vm_refl. Qed.
Lemma D_109198 : decode_any W_109198 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10919c : bv 32 := 0x00c50663.
Lemma F_10919c : fetch_word AsanUbsan.M.loaded_segments (0x10919c : word) = Some W_10919c.
Proof. vm_refl. Qed.
Lemma D_10919c : decode_any W_10919c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091a0 : bv 32 := 0x00810993.
Lemma F_1091a0 : fetch_word AsanUbsan.M.loaded_segments (0x1091a0 : word) = Some W_1091a0.
Proof. vm_refl. Qed.
Lemma D_1091a0 : decode_any W_1091a0 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091a4 : bv 32 := 0x0080006f.
Lemma F_1091a4 : fetch_word AsanUbsan.M.loaded_segments (0x1091a4 : word) = Some W_1091a4.
Proof. vm_refl. Qed.
Lemma D_1091a4 : decode_any W_1091a4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091a8 : bv 32 := 0x01810993.
Lemma F_1091a8 : fetch_word AsanUbsan.M.loaded_segments (0x1091a8 : word) = Some W_1091a8.
Proof. vm_refl. Qed.
Lemma D_1091a8 : decode_any W_1091a8 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091ac : bv 32 := 0x0784a503.
Lemma F_1091ac : fetch_word AsanUbsan.M.loaded_segments (0x1091ac : word) = Some W_1091ac.
Proof. vm_refl. Qed.
Lemma D_1091ac : decode_any W_1091ac = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091b0 : bv 32 := 0x00190913.
Lemma F_1091b0 : fetch_word AsanUbsan.M.loaded_segments (0x1091b0 : word) = Some W_1091b0.
Proof. vm_refl. Qed.
Lemma D_1091b0 : decode_any W_1091b0 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091b4 : bv 32 := 0x04200893.
Lemma F_1091b4 : fetch_word AsanUbsan.M.loaded_segments (0x1091b4 : word) = Some W_1091b4.
Proof. vm_refl. Qed.
Lemma D_1091b4 : decode_any W_1091b4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091b8 : bv 32 := 0x00098593.
Lemma F_1091b8 : fetch_word AsanUbsan.M.loaded_segments (0x1091b8 : word) = Some W_1091b8.
Proof. vm_refl. Qed.
Lemma D_1091b8 : decode_any W_1091b8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091bc : bv 32 := 0x00090613.
Lemma F_1091bc : fetch_word AsanUbsan.M.loaded_segments (0x1091bc : word) = Some W_1091bc.
Proof. vm_refl. Qed.
Lemma D_1091bc : decode_any W_1091bc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091c0 : bv 32 := 0x00000073.
Lemma F_1091c0 : fetch_word AsanUbsan.M.loaded_segments (0x1091c0 : word) = Some W_1091c0.
Proof. vm_refl. Qed.
Lemma D_1091c0 : decode_any W_1091c0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1091c0 : is_ecall W_1091c0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1091c4 : bv 32 := 0xf7cfa0ef.
Lemma F_1091c4 : fetch_word AsanUbsan.M.loaded_segments (0x1091c4 : word) = Some W_1091c4.
Proof. vm_refl. Qed.
Lemma D_1091c4 : decode_any W_1091c4 = Some (Jal 1 2074492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091c8 : bv 32 := 0x09651863.
Lemma F_1091c8 : fetch_word AsanUbsan.M.loaded_segments (0x1091c8 : word) = Some W_1091c8.
Proof. vm_refl. Qed.
Lemma D_1091c8 : decode_any W_1091c8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091cc : bv 32 := 0x0584b503.
Lemma F_1091cc : fetch_word AsanUbsan.M.loaded_segments (0x1091cc : word) = Some W_1091cc.
Proof. vm_refl. Qed.
Lemma D_1091cc : decode_any W_1091cc = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091d0 : bv 32 := 0x0604b583.
Lemma F_1091d0 : fetch_word AsanUbsan.M.loaded_segments (0x1091d0 : word) = Some W_1091d0.
Proof. vm_refl. Qed.
Lemma D_1091d0 : decode_any W_1091d0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091d4 : bv 32 := 0x00b505b3.
Lemma F_1091d4 : fetch_word AsanUbsan.M.loaded_segments (0x1091d4 : word) = Some W_1091d4.
Proof. vm_refl. Qed.
Lemma D_1091d4 : decode_any W_1091d4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091d8 : bv 32 := 0x02b4b023.
Lemma F_1091d8 : fetch_word AsanUbsan.M.loaded_segments (0x1091d8 : word) = Some W_1091d8.
Proof. vm_refl. Qed.
Lemma D_1091d8 : decode_any W_1091d8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091dc : bv 32 := 0x02a4b423.
Lemma F_1091dc : fetch_word AsanUbsan.M.loaded_segments (0x1091dc : word) = Some W_1091dc.
Proof. vm_refl. Qed.
Lemma D_1091dc : decode_any W_1091dc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091e0 : bv 32 := 0x02a4bc23.
Lemma F_1091e0 : fetch_word AsanUbsan.M.loaded_segments (0x1091e0 : word) = Some W_1091e0.
Proof. vm_refl. Qed.
Lemma D_1091e0 : decode_any W_1091e0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091e4 : bv 32 := 0x00040513.
Lemma F_1091e4 : fetch_word AsanUbsan.M.loaded_segments (0x1091e4 : word) = Some W_1091e4.
Proof. vm_refl. Qed.
Lemma D_1091e4 : decode_any W_1091e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091e8 : bv 32 := 0x000ab583.
Lemma F_1091e8 : fetch_word AsanUbsan.M.loaded_segments (0x1091e8 : word) = Some W_1091e8.
Proof. vm_refl. Qed.
Lemma D_1091e8 : decode_any W_1091e8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091ec : bv 32 := 0x02813603.
Lemma F_1091ec : fetch_word AsanUbsan.M.loaded_segments (0x1091ec : word) = Some W_1091ec.
Proof. vm_refl. Qed.
Lemma D_1091ec : decode_any W_1091ec = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091f0 : bv 32 := 0x0cc59a63.
Lemma F_1091f0 : fetch_word AsanUbsan.M.loaded_segments (0x1091f0 : word) = Some W_1091f0.
Proof. vm_refl. Qed.
Lemma D_1091f0 : decode_any W_1091f0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091f4 : bv 32 := 0x06813083.
Lemma F_1091f4 : fetch_word AsanUbsan.M.loaded_segments (0x1091f4 : word) = Some W_1091f4.
Proof. vm_refl. Qed.
Lemma D_1091f4 : decode_any W_1091f4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091f8 : bv 32 := 0x06013403.
Lemma F_1091f8 : fetch_word AsanUbsan.M.loaded_segments (0x1091f8 : word) = Some W_1091f8.
Proof. vm_refl. Qed.
Lemma D_1091f8 : decode_any W_1091f8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1091fc : bv 32 := 0x05813483.
Lemma F_1091fc : fetch_word AsanUbsan.M.loaded_segments (0x1091fc : word) = Some W_1091fc.
Proof. vm_refl. Qed.
Lemma D_1091fc : decode_any W_1091fc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109200 : bv 32 := 0x05013903.
Lemma F_109200 : fetch_word AsanUbsan.M.loaded_segments (0x109200 : word) = Some W_109200.
Proof. vm_refl. Qed.
Lemma D_109200 : decode_any W_109200 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109204 : bv 32 := 0x04813983.
Lemma F_109204 : fetch_word AsanUbsan.M.loaded_segments (0x109204 : word) = Some W_109204.
Proof. vm_refl. Qed.
Lemma D_109204 : decode_any W_109204 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109208 : bv 32 := 0x04013a03.
Lemma F_109208 : fetch_word AsanUbsan.M.loaded_segments (0x109208 : word) = Some W_109208.
Proof. vm_refl. Qed.
Lemma D_109208 : decode_any W_109208 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10920c : bv 32 := 0x03813a83.
Lemma F_10920c : fetch_word AsanUbsan.M.loaded_segments (0x10920c : word) = Some W_10920c.
Proof. vm_refl. Qed.
Lemma D_10920c : decode_any W_10920c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109210 : bv 32 := 0x03013b03.
Lemma F_109210 : fetch_word AsanUbsan.M.loaded_segments (0x109210 : word) = Some W_109210.
Proof. vm_refl. Qed.
Lemma D_109210 : decode_any W_109210 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109214 : bv 32 := 0x07010113.
Lemma F_109214 : fetch_word AsanUbsan.M.loaded_segments (0x109214 : word) = Some W_109214.
Proof. vm_refl. Qed.
Lemma D_109214 : decode_any W_109214 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109218 : bv 32 := 0x00008067.
Lemma F_109218 : fetch_word AsanUbsan.M.loaded_segments (0x109218 : word) = Some W_109218.
Proof. vm_refl. Qed.
Lemma D_109218 : decode_any W_109218 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10921c : bv 32 := 0x00800713.
Lemma F_10921c : fetch_word AsanUbsan.M.loaded_segments (0x10921c : word) = Some W_10921c.
Proof. vm_refl. Qed.
Lemma D_10921c : decode_any W_10921c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109220 : bv 32 := 0x000a0593.
Lemma F_109220 : fetch_word AsanUbsan.M.loaded_segments (0x109220 : word) = Some W_109220.
Proof. vm_refl. Qed.
Lemma D_109220 : decode_any W_109220 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109224 : bv 32 := 0x00e98733.
Lemma F_109224 : fetch_word AsanUbsan.M.loaded_segments (0x109224 : word) = Some W_109224.
Proof. vm_refl. Qed.
Lemma D_109224 : decode_any W_109224 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109228 : bv 32 := 0x00073783.
Lemma F_109228 : fetch_word AsanUbsan.M.loaded_segments (0x109228 : word) = Some W_109228.
Proof. vm_refl. Qed.
Lemma D_109228 : decode_any W_109228 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10922c : bv 32 := 0x40ab0b33.
Lemma F_10922c : fetch_word AsanUbsan.M.loaded_segments (0x10922c : word) = Some W_10922c.
Proof. vm_refl. Qed.
Lemma D_10922c : decode_any W_10922c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109230 : bv 32 := 0x0784a503.
Lemma F_109230 : fetch_word AsanUbsan.M.loaded_segments (0x109230 : word) = Some W_109230.
Proof. vm_refl. Qed.
Lemma D_109230 : decode_any W_109230 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109234 : bv 32 := 0x40c9093b.
Lemma F_109234 : fetch_word AsanUbsan.M.loaded_segments (0x109234 : word) = Some W_109234.
Proof. vm_refl. Qed.
Lemma D_109234 : decode_any W_109234 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109238 : bv 32 := 0x40d787b3.
Lemma F_109238 : fetch_word AsanUbsan.M.loaded_segments (0x109238 : word) = Some W_109238.
Proof. vm_refl. Qed.
Lemma D_109238 : decode_any W_109238 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10923c : bv 32 := 0x00f73023.
Lemma F_10923c : fetch_word AsanUbsan.M.loaded_segments (0x10923c : word) = Some W_10923c.
Proof. vm_refl. Qed.
Lemma D_10923c : decode_any W_10923c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109240 : bv 32 := 0x04200893.
Lemma F_109240 : fetch_word AsanUbsan.M.loaded_segments (0x109240 : word) = Some W_109240.
Proof. vm_refl. Qed.
Lemma D_109240 : decode_any W_109240 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109244 : bv 32 := 0x00090613.
Lemma F_109244 : fetch_word AsanUbsan.M.loaded_segments (0x109244 : word) = Some W_109244.
Proof. vm_refl. Qed.
Lemma D_109244 : decode_any W_109244 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109248 : bv 32 := 0x00000073.
Lemma F_109248 : fetch_word AsanUbsan.M.loaded_segments (0x109248 : word) = Some W_109248.
Proof. vm_refl. Qed.
Lemma D_109248 : decode_any W_109248 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_109248 : is_ecall W_109248 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_10924c : bv 32 := 0xef4fa0ef.
Lemma F_10924c : fetch_word AsanUbsan.M.loaded_segments (0x10924c : word) = Some W_10924c.
Proof. vm_refl. Qed.
Lemma D_10924c : decode_any W_10924c = Some (Jal 1 2074356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109250 : bv 32 := 0x000a0993.
Lemma F_109250 : fetch_word AsanUbsan.M.loaded_segments (0x109250 : word) = Some W_109250.
Proof. vm_refl. Qed.
Lemma D_109250 : decode_any W_109250 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109254 : bv 32 := 0xf7650ce3.
Lemma F_109254 : fetch_word AsanUbsan.M.loaded_segments (0x109254 : word) = Some W_109254.
Proof. vm_refl. Qed.
Lemma D_109254 : decode_any W_109254 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109258 : bv 32 := 0x02054c63.
Lemma F_109258 : fetch_word AsanUbsan.M.loaded_segments (0x109258 : word) = Some W_109258.
Proof. vm_refl. Qed.
Lemma D_109258 : decode_any W_109258 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10925c : bv 32 := 0x0089b583.
Lemma F_10925c : fetch_word AsanUbsan.M.loaded_segments (0x10925c : word) = Some W_10925c.
Proof. vm_refl. Qed.
Lemma D_10925c : decode_any W_10925c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109260 : bv 32 := 0x00a5b633.
Lemma F_109260 : fetch_word AsanUbsan.M.loaded_segments (0x109260 : word) = Some W_109260.
Proof. vm_refl. Qed.
Lemma D_109260 : decode_any W_109260 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109264 : bv 32 := 0x00461a13.
Lemma F_109264 : fetch_word AsanUbsan.M.loaded_segments (0x109264 : word) = Some W_109264.
Proof. vm_refl. Qed.
Lemma D_109264 : decode_any W_109264 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109268 : bv 32 := 0x01498a33.
Lemma F_109268 : fetch_word AsanUbsan.M.loaded_segments (0x109268 : word) = Some W_109268.
Proof. vm_refl. Qed.
Lemma D_109268 : decode_any W_109268 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10926c : bv 32 := 0x000a3703.
Lemma F_10926c : fetch_word AsanUbsan.M.loaded_segments (0x10926c : word) = Some W_10926c.
Proof. vm_refl. Qed.
Lemma D_10926c : decode_any W_10926c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109270 : bv 32 := 0x40c006b3.
Lemma F_109270 : fetch_word AsanUbsan.M.loaded_segments (0x109270 : word) = Some W_109270.
Proof. vm_refl. Qed.
Lemma D_109270 : decode_any W_109270 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109274 : bv 32 := 0x00b6f6b3.
Lemma F_109274 : fetch_word AsanUbsan.M.loaded_segments (0x109274 : word) = Some W_109274.
Proof. vm_refl. Qed.
Lemma D_109274 : decode_any W_109274 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109278 : bv 32 := 0x40d506b3.
Lemma F_109278 : fetch_word AsanUbsan.M.loaded_segments (0x109278 : word) = Some W_109278.
Proof. vm_refl. Qed.
Lemma D_109278 : decode_any W_109278 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10927c : bv 32 := 0x00d70733.
Lemma F_10927c : fetch_word AsanUbsan.M.loaded_segments (0x10927c : word) = Some W_10927c.
Proof. vm_refl. Qed.
Lemma D_10927c : decode_any W_10927c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109280 : bv 32 := 0x00ea3023.
Lemma F_109280 : fetch_word AsanUbsan.M.loaded_segments (0x109280 : word) = Some W_109280.
Proof. vm_refl. Qed.
Lemma D_109280 : decode_any W_109280 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109284 : bv 32 := 0xf8a5fce3.
Lemma F_109284 : fetch_word AsanUbsan.M.loaded_segments (0x109284 : word) = Some W_109284.
Proof. vm_refl. Qed.
Lemma D_109284 : decode_any W_109284 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109288 : bv 32 := 0x01800713.
Lemma F_109288 : fetch_word AsanUbsan.M.loaded_segments (0x109288 : word) = Some W_109288.
Proof. vm_refl. Qed.
Lemma D_109288 : decode_any W_109288 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10928c : bv 32 := 0xf95ff06f.
Lemma F_10928c : fetch_word AsanUbsan.M.loaded_segments (0x10928c : word) = Some W_10928c.
Proof. vm_refl. Qed.
Lemma D_10928c : decode_any W_10928c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109290 : bv 32 := 0x00000513.
Lemma F_109290 : fetch_word AsanUbsan.M.loaded_segments (0x109290 : word) = Some W_109290.
Proof. vm_refl. Qed.
Lemma D_109290 : decode_any W_109290 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109294 : bv 32 := 0x0004a583.
Lemma F_109294 : fetch_word AsanUbsan.M.loaded_segments (0x109294 : word) = Some W_109294.
Proof. vm_refl. Qed.
Lemma D_109294 : decode_any W_109294 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_109298 : bv 32 := 0x0009091b.
Lemma F_109298 : fetch_word AsanUbsan.M.loaded_segments (0x109298 : word) = Some W_109298.
Proof. vm_refl. Qed.
Lemma D_109298 : decode_any W_109298 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10929c : bv 32 := 0x00200613.
Lemma F_10929c : fetch_word AsanUbsan.M.loaded_segments (0x10929c : word) = Some W_10929c.
Proof. vm_refl. Qed.
Lemma D_10929c : decode_any W_10929c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092a0 : bv 32 := 0x0205e593.
Lemma F_1092a0 : fetch_word AsanUbsan.M.loaded_segments (0x1092a0 : word) = Some W_1092a0.
Proof. vm_refl. Qed.
Lemma D_1092a0 : decode_any W_1092a0 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092a4 : bv 32 := 0x00b4a023.
Lemma F_1092a4 : fetch_word AsanUbsan.M.loaded_segments (0x1092a4 : word) = Some W_1092a4.
Proof. vm_refl. Qed.
Lemma D_1092a4 : decode_any W_1092a4 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092a8 : bv 32 := 0x0204b023.
Lemma F_1092a8 : fetch_word AsanUbsan.M.loaded_segments (0x1092a8 : word) = Some W_1092a8.
Proof. vm_refl. Qed.
Lemma D_1092a8 : decode_any W_1092a8 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092ac : bv 32 := 0x0204b423.
Lemma F_1092ac : fetch_word AsanUbsan.M.loaded_segments (0x1092ac : word) = Some W_1092ac.
Proof. vm_refl. Qed.
Lemma D_1092ac : decode_any W_1092ac = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092b0 : bv 32 := 0x0204bc23.
Lemma F_1092b0 : fetch_word AsanUbsan.M.loaded_segments (0x1092b0 : word) = Some W_1092b0.
Proof. vm_refl. Qed.
Lemma D_1092b0 : decode_any W_1092b0 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092b4 : bv 32 := 0xf2c90ae3.
Lemma F_1092b4 : fetch_word AsanUbsan.M.loaded_segments (0x1092b4 : word) = Some W_1092b4.
Proof. vm_refl. Qed.
Lemma D_1092b4 : decode_any W_1092b4 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092b8 : bv 32 := 0x0089b503.
Lemma F_1092b8 : fetch_word AsanUbsan.M.loaded_segments (0x1092b8 : word) = Some W_1092b8.
Proof. vm_refl. Qed.
Lemma D_1092b8 : decode_any W_1092b8 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092bc : bv 32 := 0x40a40533.
Lemma F_1092bc : fetch_word AsanUbsan.M.loaded_segments (0x1092bc : word) = Some W_1092bc.
Proof. vm_refl. Qed.
Lemma D_1092bc : decode_any W_1092bc = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092c0 : bv 32 := 0xf29ff06f.
Lemma F_1092c0 : fetch_word AsanUbsan.M.loaded_segments (0x1092c0 : word) = Some W_1092c0.
Proof. vm_refl. Qed.
Lemma D_1092c0 : decode_any W_1092c0 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1092c4 : bv 32 := 0x810fa0ef.
Lemma F_1092c4 : fetch_word AsanUbsan.M.loaded_segments (0x1092c4 : word) = Some W_1092c4.
Proof. vm_refl. Qed.
Lemma D_1092c4 : decode_any W_1092c4 = Some (Jal 1 2072592, 4%Z).
Proof. vm_refl. Qed.
