(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushS10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_15024 : bv 32 := 0xffffe517.
Lemma F_15024 : fetch_word Plain.M.loaded_segments (0x15024 : word) = Some W_15024.
Proof. vm_refl. Qed.
Lemma D_15024 : decode_any W_15024 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15028 : bv 32 := 0xa3c50513.
Lemma F_15028 : fetch_word Plain.M.loaded_segments (0x15028 : word) = Some W_15028.
Proof. vm_refl. Qed.
Lemma D_15028 : decode_any W_15028 = Some (OpImm ALU_ADD 10 10 2620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1502c : bv 32 := 0x00018597.
Lemma F_1502c : fetch_word Plain.M.loaded_segments (0x1502c : word) = Some W_1502c.
Proof. vm_refl. Qed.
Lemma D_1502c : decode_any W_1502c = Some (Auipc 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15030 : bv 32 := 0xf8c58593.
Lemma F_15030 : fetch_word Plain.M.loaded_segments (0x15030 : word) = Some W_15030.
Proof. vm_refl. Qed.
Lemma D_15030 : decode_any W_15030 = Some (OpImm ALU_ADD 11 11 3980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15034 : bv 32 := 0x000000ef.
Lemma F_15034 : fetch_word Plain.M.loaded_segments (0x15034 : word) = Some W_15034.
Proof. vm_refl. Qed.
Lemma D_15034 : decode_any W_15034 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15038 : bv 32 := 0x0040006f.
Lemma F_15038 : fetch_word Plain.M.loaded_segments (0x15038 : word) = Some W_15038.
Proof. vm_refl. Qed.
Lemma D_15038 : decode_any W_15038 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1503c : bv 32 := 0x00813083.
Lemma F_1503c : fetch_word Plain.M.loaded_segments (0x1503c : word) = Some W_1503c.
Proof. vm_refl. Qed.
Lemma D_1503c : decode_any W_1503c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15040 : bv 32 := 0x00013403.
Lemma F_15040 : fetch_word Plain.M.loaded_segments (0x15040 : word) = Some W_15040.
Proof. vm_refl. Qed.
Lemma D_15040 : decode_any W_15040 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15044 : bv 32 := 0x01010113.
Lemma F_15044 : fetch_word Plain.M.loaded_segments (0x15044 : word) = Some W_15044.
Proof. vm_refl. Qed.
Lemma D_15044 : decode_any W_15044 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15048 : bv 32 := 0x00008067.
Lemma F_15048 : fetch_word Plain.M.loaded_segments (0x15048 : word) = Some W_15048.
Proof. vm_refl. Qed.
Lemma D_15048 : decode_any W_15048 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1504c : bv 32 := 0xff010113.
Lemma F_1504c : fetch_word Plain.M.loaded_segments (0x1504c : word) = Some W_1504c.
Proof. vm_refl. Qed.
Lemma D_1504c : decode_any W_1504c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15050 : bv 32 := 0x00113423.
Lemma F_15050 : fetch_word Plain.M.loaded_segments (0x15050 : word) = Some W_15050.
Proof. vm_refl. Qed.
Lemma D_15050 : decode_any W_15050 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15054 : bv 32 := 0x00813023.
Lemma F_15054 : fetch_word Plain.M.loaded_segments (0x15054 : word) = Some W_15054.
Proof. vm_refl. Qed.
Lemma D_15054 : decode_any W_15054 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15058 : bv 32 := 0x01010413.
Lemma F_15058 : fetch_word Plain.M.loaded_segments (0x15058 : word) = Some W_15058.
Proof. vm_refl. Qed.
Lemma D_15058 : decode_any W_15058 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1505c : bv 32 := 0x00018517.
Lemma F_1505c : fetch_word Plain.M.loaded_segments (0x1505c : word) = Some W_1505c.
Proof. vm_refl. Qed.
Lemma D_1505c : decode_any W_1505c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15060 : bv 32 := 0xf9c50513.
Lemma F_15060 : fetch_word Plain.M.loaded_segments (0x15060 : word) = Some W_15060.
Proof. vm_refl. Qed.
Lemma D_15060 : decode_any W_15060 = Some (OpImm ALU_ADD 10 10 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15064 : bv 32 := 0x00054503.
Lemma F_15064 : fetch_word Plain.M.loaded_segments (0x15064 : word) = Some W_15064.
Proof. vm_refl. Qed.
Lemma D_15064 : decode_any W_15064 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15068 : bv 32 := 0x00157513.
Lemma F_15068 : fetch_word Plain.M.loaded_segments (0x15068 : word) = Some W_15068.
Proof. vm_refl. Qed.
Lemma D_15068 : decode_any W_15068 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1506c : bv 32 := 0x00050663.
Lemma F_1506c : fetch_word Plain.M.loaded_segments (0x1506c : word) = Some W_1506c.
Proof. vm_refl. Qed.
Lemma D_1506c : decode_any W_1506c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15070 : bv 32 := 0x0040006f.
Lemma F_15070 : fetch_word Plain.M.loaded_segments (0x15070 : word) = Some W_15070.
Proof. vm_refl. Qed.
Lemma D_15070 : decode_any W_15070 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15074 : bv 32 := 0x0580006f.
Lemma F_15074 : fetch_word Plain.M.loaded_segments (0x15074 : word) = Some W_15074.
Proof. vm_refl. Qed.
Lemma D_15074 : decode_any W_15074 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15078 : bv 32 := 0x00018517.
Lemma F_15078 : fetch_word Plain.M.loaded_segments (0x15078 : word) = Some W_15078.
Proof. vm_refl. Qed.
Lemma D_15078 : decode_any W_15078 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1507c : bv 32 := 0xf8050593.
Lemma F_1507c : fetch_word Plain.M.loaded_segments (0x1507c : word) = Some W_1507c.
Proof. vm_refl. Qed.
Lemma D_1507c : decode_any W_1507c = Some (OpImm ALU_ADD 11 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15080 : bv 32 := 0x00100513.
Lemma F_15080 : fetch_word Plain.M.loaded_segments (0x15080 : word) = Some W_15080.
Proof. vm_refl. Qed.
Lemma D_15080 : decode_any W_15080 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15084 : bv 32 := 0x00a58023.
Lemma F_15084 : fetch_word Plain.M.loaded_segments (0x15084 : word) = Some W_15084.
Proof. vm_refl. Qed.
Lemma D_15084 : decode_any W_15084 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15088 : bv 32 := 0x00017517.
Lemma F_15088 : fetch_word Plain.M.loaded_segments (0x15088 : word) = Some W_15088.
Proof. vm_refl. Qed.
Lemma D_15088 : decode_any W_15088 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1508c : bv 32 := 0x96853503.
Lemma F_1508c : fetch_word Plain.M.loaded_segments (0x1508c : word) = Some W_1508c.
Proof. vm_refl. Qed.
Lemma D_1508c : decode_any W_1508c = Some (Load SZ8 true 10 10 2408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15090 : bv 32 := 0x00050e63.
Lemma F_15090 : fetch_word Plain.M.loaded_segments (0x15090 : word) = Some W_15090.
Proof. vm_refl. Qed.
Lemma D_15090 : decode_any W_15090 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15094 : bv 32 := 0x0040006f.
Lemma F_15094 : fetch_word Plain.M.loaded_segments (0x15094 : word) = Some W_15094.
Proof. vm_refl. Qed.
Lemma D_15094 : decode_any W_15094 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15098 : bv 32 := 0x00018517.
Lemma F_15098 : fetch_word Plain.M.loaded_segments (0x15098 : word) = Some W_15098.
Proof. vm_refl. Qed.
Lemma D_15098 : decode_any W_15098 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1509c : bv 32 := 0x9c850513.
Lemma F_1509c : fetch_word Plain.M.loaded_segments (0x1509c : word) = Some W_1509c.
Proof. vm_refl. Qed.
Lemma D_1509c : decode_any W_1509c = Some (OpImm ALU_ADD 10 10 2504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a0 : bv 32 := 0x00053503.
Lemma F_150a0 : fetch_word Plain.M.loaded_segments (0x150a0 : word) = Some W_150a0.
Proof. vm_refl. Qed.
Lemma D_150a0 : decode_any W_150a0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a4 : bv 32 := 0x19d0d0ef.
Lemma F_150a4 : fetch_word Plain.M.loaded_segments (0x150a4 : word) = Some W_150a4.
Proof. vm_refl. Qed.
Lemma D_150a4 : decode_any W_150a4 = Some (Jal 1 55708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a8 : bv 32 := 0x0040006f.
Lemma F_150a8 : fetch_word Plain.M.loaded_segments (0x150a8 : word) = Some W_150a8.
Proof. vm_refl. Qed.
Lemma D_150a8 : decode_any W_150a8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150ac : bv 32 := 0x00017517.
Lemma F_150ac : fetch_word Plain.M.loaded_segments (0x150ac : word) = Some W_150ac.
Proof. vm_refl. Qed.
Lemma D_150ac : decode_any W_150ac = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b0 : bv 32 := 0x94c53503.
Lemma F_150b0 : fetch_word Plain.M.loaded_segments (0x150b0 : word) = Some W_150b0.
Proof. vm_refl. Qed.
Lemma D_150b0 : decode_any W_150b0 = Some (Load SZ8 true 10 10 2380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b4 : bv 32 := 0x00050c63.
Lemma F_150b4 : fetch_word Plain.M.loaded_segments (0x150b4 : word) = Some W_150b4.
Proof. vm_refl. Qed.
Lemma D_150b4 : decode_any W_150b4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b8 : bv 32 := 0x0040006f.
Lemma F_150b8 : fetch_word Plain.M.loaded_segments (0x150b8 : word) = Some W_150b8.
Proof. vm_refl. Qed.
Lemma D_150b8 : decode_any W_150b8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150bc : bv 32 := 0xffffe517.
Lemma F_150bc : fetch_word Plain.M.loaded_segments (0x150bc : word) = Some W_150bc.
Proof. vm_refl. Qed.
Lemma D_150bc : decode_any W_150bc = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c0 : bv 32 := 0x9a450513.
Lemma F_150c0 : fetch_word Plain.M.loaded_segments (0x150c0 : word) = Some W_150c0.
Proof. vm_refl. Qed.
Lemma D_150c0 : decode_any W_150c0 = Some (OpImm ALU_ADD 10 10 2468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c4 : bv 32 := 0x000000ef.
Lemma F_150c4 : fetch_word Plain.M.loaded_segments (0x150c4 : word) = Some W_150c4.
Proof. vm_refl. Qed.
Lemma D_150c4 : decode_any W_150c4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c8 : bv 32 := 0x0040006f.
Lemma F_150c8 : fetch_word Plain.M.loaded_segments (0x150c8 : word) = Some W_150c8.
Proof. vm_refl. Qed.
Lemma D_150c8 : decode_any W_150c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150cc : bv 32 := 0x00813083.
Lemma F_150cc : fetch_word Plain.M.loaded_segments (0x150cc : word) = Some W_150cc.
Proof. vm_refl. Qed.
Lemma D_150cc : decode_any W_150cc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d0 : bv 32 := 0x00013403.
Lemma F_150d0 : fetch_word Plain.M.loaded_segments (0x150d0 : word) = Some W_150d0.
Proof. vm_refl. Qed.
Lemma D_150d0 : decode_any W_150d0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d4 : bv 32 := 0x01010113.
Lemma F_150d4 : fetch_word Plain.M.loaded_segments (0x150d4 : word) = Some W_150d4.
Proof. vm_refl. Qed.
Lemma D_150d4 : decode_any W_150d4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d8 : bv 32 := 0x00008067.
Lemma F_150d8 : fetch_word Plain.M.loaded_segments (0x150d8 : word) = Some W_150d8.
Proof. vm_refl. Qed.
Lemma D_150d8 : decode_any W_150d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15504 : bv 32 := 0x00028517.
Lemma F_15504 : fetch_word Plain.M.loaded_segments (0x15504 : word) = Some W_15504.
Proof. vm_refl. Qed.
Lemma D_15504 : decode_any W_15504 = Some (Auipc 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15508 : bv 32 := 0xb0054503.
Lemma F_15508 : fetch_word Plain.M.loaded_segments (0x15508 : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (Load SZ1 false 10 10 2816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1550c : bv 32 := 0x00051463.
Lemma F_1550c : fetch_word Plain.M.loaded_segments (0x1550c : word) = Some W_1550c.
Proof. vm_refl. Qed.
Lemma D_1550c : decode_any W_1550c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15510 : bv 32 := 0x00008067.
Lemma F_15510 : fetch_word Plain.M.loaded_segments (0x15510 : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15514 : bv 32 := 0xff010113.
Lemma F_15514 : fetch_word Plain.M.loaded_segments (0x15514 : word) = Some W_15514.
Proof. vm_refl. Qed.
Lemma D_15514 : decode_any W_15514 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15518 : bv 32 := 0x00113423.
Lemma F_15518 : fetch_word Plain.M.loaded_segments (0x15518 : word) = Some W_15518.
Proof. vm_refl. Qed.
Lemma D_15518 : decode_any W_15518 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1551c : bv 32 := 0x00016517.
Lemma F_1551c : fetch_word Plain.M.loaded_segments (0x1551c : word) = Some W_1551c.
Proof. vm_refl. Qed.
Lemma D_1551c : decode_any W_1551c = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15520 : bv 32 := 0x4f453503.
Lemma F_15520 : fetch_word Plain.M.loaded_segments (0x15520 : word) = Some W_15520.
Proof. vm_refl. Qed.
Lemma D_15520 : decode_any W_15520 = Some (Load SZ8 true 10 10 1268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15524 : bv 32 := 0x00053503.
Lemma F_15524 : fetch_word Plain.M.loaded_segments (0x15524 : word) = Some W_15524.
Proof. vm_refl. Qed.
Lemma D_15524 : decode_any W_15524 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15528 : bv 32 := 0x68c0f0ef.
Lemma F_15528 : fetch_word Plain.M.loaded_segments (0x15528 : word) = Some W_15528.
Proof. vm_refl. Qed.
Lemma D_15528 : decode_any W_15528 = Some (Jal 1 63116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1552c : bv 32 := 0x04d00513.
Lemma F_1552c : fetch_word Plain.M.loaded_segments (0x1552c : word) = Some W_1552c.
Proof. vm_refl. Qed.
Lemma D_1552c : decode_any W_1552c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15530 : bv 32 := 0x3d0150ef.
Lemma F_15530 : fetch_word Plain.M.loaded_segments (0x15530 : word) = Some W_15530.
Proof. vm_refl. Qed.
Lemma D_15530 : decode_any W_15530 = Some (Jal 1 86992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22978 : bv 32 := 0xfd010113.
Lemma F_22978 : fetch_word Plain.M.loaded_segments (0x22978 : word) = Some W_22978.
Proof. vm_refl. Qed.
Lemma D_22978 : decode_any W_22978 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2297c : bv 32 := 0x02113423.
Lemma F_2297c : fetch_word Plain.M.loaded_segments (0x2297c : word) = Some W_2297c.
Proof. vm_refl. Qed.
Lemma D_2297c : decode_any W_2297c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22980 : bv 32 := 0x02813023.
Lemma F_22980 : fetch_word Plain.M.loaded_segments (0x22980 : word) = Some W_22980.
Proof. vm_refl. Qed.
Lemma D_22980 : decode_any W_22980 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22984 : bv 32 := 0x00913c23.
Lemma F_22984 : fetch_word Plain.M.loaded_segments (0x22984 : word) = Some W_22984.
Proof. vm_refl. Qed.
Lemma D_22984 : decode_any W_22984 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22988 : bv 32 := 0x01213823.
Lemma F_22988 : fetch_word Plain.M.loaded_segments (0x22988 : word) = Some W_22988.
Proof. vm_refl. Qed.
Lemma D_22988 : decode_any W_22988 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2298c : bv 32 := 0x01313423.
Lemma F_2298c : fetch_word Plain.M.loaded_segments (0x2298c : word) = Some W_2298c.
Proof. vm_refl. Qed.
Lemma D_2298c : decode_any W_2298c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22990 : bv 32 := 0x0003a517.
Lemma F_22990 : fetch_word Plain.M.loaded_segments (0x22990 : word) = Some W_22990.
Proof. vm_refl. Qed.
Lemma D_22990 : decode_any W_22990 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22994 : bv 32 := 0x7b050913.
Lemma F_22994 : fetch_word Plain.M.loaded_segments (0x22994 : word) = Some W_22994.
Proof. vm_refl. Qed.
Lemma D_22994 : decode_any W_22994 = Some (OpImm ALU_ADD 18 10 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22998 : bv 32 := 0x00490413.
Lemma F_22998 : fetch_word Plain.M.loaded_segments (0x22998 : word) = Some W_22998.
Proof. vm_refl. Qed.
Lemma D_22998 : decode_any W_22998 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2299c : bv 32 := 0x00040513.
Lemma F_2299c : fetch_word Plain.M.loaded_segments (0x2299c : word) = Some W_2299c.
Proof. vm_refl. Qed.
Lemma D_2299c : decode_any W_2299c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229a0 : bv 32 := 0x431070ef.
Lemma F_229a0 : fetch_word Plain.M.loaded_segments (0x229a0 : word) = Some W_229a0.
Proof. vm_refl. Qed.
Lemma D_229a0 : decode_any W_229a0 = Some (Jal 1 31792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229a4 : bv 32 := 0x01093503.
Lemma F_229a4 : fetch_word Plain.M.loaded_segments (0x229a4 : word) = Some W_229a4.
Proof. vm_refl. Qed.
Lemma D_229a4 : decode_any W_229a4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229a8 : bv 32 := 0x06050863.
Lemma F_229a8 : fetch_word Plain.M.loaded_segments (0x229a8 : word) = Some W_229a8.
Proof. vm_refl. Qed.
Lemma D_229a8 : decode_any W_229a8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229ac : bv 32 := 0x00892583.
Lemma F_229ac : fetch_word Plain.M.loaded_segments (0x229ac : word) = Some W_229ac.
Proof. vm_refl. Qed.
Lemma D_229ac : decode_any W_229ac = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229b0 : bv 32 := 0x0180006f.
Lemma F_229b0 : fetch_word Plain.M.loaded_segments (0x229b0 : word) = Some W_229b0.
Proof. vm_refl. Qed.
Lemma D_229b0 : decode_any W_229b0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229b4 : bv 32 := 0x00053503.
Lemma F_229b4 : fetch_word Plain.M.loaded_segments (0x229b4 : word) = Some W_229b4.
Proof. vm_refl. Qed.
Lemma D_229b4 : decode_any W_229b4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229b8 : bv 32 := 0x02000593.
Lemma F_229b8 : fetch_word Plain.M.loaded_segments (0x229b8 : word) = Some W_229b8.
Proof. vm_refl. Qed.
Lemma D_229b8 : decode_any W_229b8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229bc : bv 32 := 0x00b92423.
Lemma F_229bc : fetch_word Plain.M.loaded_segments (0x229bc : word) = Some W_229bc.
Proof. vm_refl. Qed.
Lemma D_229bc : decode_any W_229bc = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229c0 : bv 32 := 0x00a93823.
Lemma F_229c0 : fetch_word Plain.M.loaded_segments (0x229c0 : word) = Some W_229c0.
Proof. vm_refl. Qed.
Lemma D_229c0 : decode_any W_229c0 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229c4 : bv 32 := 0x04050a63.
Lemma F_229c4 : fetch_word Plain.M.loaded_segments (0x229c4 : word) = Some W_229c4.
Proof. vm_refl. Qed.
Lemma D_229c4 : decode_any W_229c4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229c8 : bv 32 := 0xfff5861b.
Lemma F_229c8 : fetch_word Plain.M.loaded_segments (0x229c8 : word) = Some W_229c8.
Proof. vm_refl. Qed.
Lemma D_229c8 : decode_any W_229c8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229cc : bv 32 := 0x00c92423.
Lemma F_229cc : fetch_word Plain.M.loaded_segments (0x229cc : word) = Some W_229cc.
Proof. vm_refl. Qed.
Lemma D_229cc : decode_any W_229cc = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229d0 : bv 32 := 0xfeb052e3.
Lemma F_229d0 : fetch_word Plain.M.loaded_segments (0x229d0 : word) = Some W_229d0.
Proof. vm_refl. Qed.
Lemma D_229d0 : decode_any W_229d0 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229d4 : bv 32 := 0x01093503.
Lemma F_229d4 : fetch_word Plain.M.loaded_segments (0x229d4 : word) = Some W_229d4.
Proof. vm_refl. Qed.
Lemma D_229d4 : decode_any W_229d4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229d8 : bv 32 := 0x00361613.
Lemma F_229d8 : fetch_word Plain.M.loaded_segments (0x229d8 : word) = Some W_229d8.
Proof. vm_refl. Qed.
Lemma D_229d8 : decode_any W_229d8 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229dc : bv 32 := 0x00c50533.
Lemma F_229dc : fetch_word Plain.M.loaded_segments (0x229dc : word) = Some W_229dc.
Proof. vm_refl. Qed.
Lemma D_229dc : decode_any W_229dc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229e0 : bv 32 := 0x00853983.
Lemma F_229e0 : fetch_word Plain.M.loaded_segments (0x229e0 : word) = Some W_229e0.
Proof. vm_refl. Qed.
Lemma D_229e0 : decode_any W_229e0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229e4 : bv 32 := 0x10853483.
Lemma F_229e4 : fetch_word Plain.M.loaded_segments (0x229e4 : word) = Some W_229e4.
Proof. vm_refl. Qed.
Lemma D_229e4 : decode_any W_229e4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229e8 : bv 32 := 0x00040513.
Lemma F_229e8 : fetch_word Plain.M.loaded_segments (0x229e8 : word) = Some W_229e8.
Proof. vm_refl. Qed.
Lemma D_229e8 : decode_any W_229e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229ec : bv 32 := 0x66d070ef.
Lemma F_229ec : fetch_word Plain.M.loaded_segments (0x229ec : word) = Some W_229ec.
Proof. vm_refl. Qed.
Lemma D_229ec : decode_any W_229ec = Some (Jal 1 32364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229f0 : bv 32 := 0x00048513.
Lemma F_229f0 : fetch_word Plain.M.loaded_segments (0x229f0 : word) = Some W_229f0.
Proof. vm_refl. Qed.
Lemma D_229f0 : decode_any W_229f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229f4 : bv 32 := 0x000980e7.
Lemma F_229f4 : fetch_word Plain.M.loaded_segments (0x229f4 : word) = Some W_229f4.
Proof. vm_refl. Qed.
Lemma D_229f4 : decode_any W_229f4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229f8 : bv 32 := 0x00040513.
Lemma F_229f8 : fetch_word Plain.M.loaded_segments (0x229f8 : word) = Some W_229f8.
Proof. vm_refl. Qed.
Lemma D_229f8 : decode_any W_229f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229fc : bv 32 := 0x3d5070ef.
Lemma F_229fc : fetch_word Plain.M.loaded_segments (0x229fc : word) = Some W_229fc.
Proof. vm_refl. Qed.
Lemma D_229fc : decode_any W_229fc = Some (Jal 1 31700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a00 : bv 32 := 0x00892503.
Lemma F_22a00 : fetch_word Plain.M.loaded_segments (0x22a00 : word) = Some W_22a00.
Proof. vm_refl. Qed.
Lemma D_22a00 : decode_any W_22a00 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a04 : bv 32 := 0xfff5061b.
Lemma F_22a04 : fetch_word Plain.M.loaded_segments (0x22a04 : word) = Some W_22a04.
Proof. vm_refl. Qed.
Lemma D_22a04 : decode_any W_22a04 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a08 : bv 32 := 0x00c92423.
Lemma F_22a08 : fetch_word Plain.M.loaded_segments (0x22a08 : word) = Some W_22a08.
Proof. vm_refl. Qed.
Lemma D_22a08 : decode_any W_22a08 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a0c : bv 32 := 0xfca044e3.
Lemma F_22a0c : fetch_word Plain.M.loaded_segments (0x22a0c : word) = Some W_22a0c.
Proof. vm_refl. Qed.
Lemma D_22a0c : decode_any W_22a0c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a10 : bv 32 := 0x01093503.
Lemma F_22a10 : fetch_word Plain.M.loaded_segments (0x22a10 : word) = Some W_22a10.
Proof. vm_refl. Qed.
Lemma D_22a10 : decode_any W_22a10 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a14 : bv 32 := 0xfa1ff06f.
Lemma F_22a14 : fetch_word Plain.M.loaded_segments (0x22a14 : word) = Some W_22a14.
Proof. vm_refl. Qed.
Lemma D_22a14 : decode_any W_22a14 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a18 : bv 32 := 0x00100513.
Lemma F_22a18 : fetch_word Plain.M.loaded_segments (0x22a18 : word) = Some W_22a18.
Proof. vm_refl. Qed.
Lemma D_22a18 : decode_any W_22a18 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a1c : bv 32 := 0x00a90023.
Lemma F_22a1c : fetch_word Plain.M.loaded_segments (0x22a1c : word) = Some W_22a1c.
Proof. vm_refl. Qed.
Lemma D_22a1c : decode_any W_22a1c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a20 : bv 32 := 0x00040513.
Lemma F_22a20 : fetch_word Plain.M.loaded_segments (0x22a20 : word) = Some W_22a20.
Proof. vm_refl. Qed.
Lemma D_22a20 : decode_any W_22a20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a24 : bv 32 := 0x02813083.
Lemma F_22a24 : fetch_word Plain.M.loaded_segments (0x22a24 : word) = Some W_22a24.
Proof. vm_refl. Qed.
Lemma D_22a24 : decode_any W_22a24 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a28 : bv 32 := 0x02013403.
Lemma F_22a28 : fetch_word Plain.M.loaded_segments (0x22a28 : word) = Some W_22a28.
Proof. vm_refl. Qed.
Lemma D_22a28 : decode_any W_22a28 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a2c : bv 32 := 0x01813483.
Lemma F_22a2c : fetch_word Plain.M.loaded_segments (0x22a2c : word) = Some W_22a2c.
Proof. vm_refl. Qed.
Lemma D_22a2c : decode_any W_22a2c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a30 : bv 32 := 0x01013903.
Lemma F_22a30 : fetch_word Plain.M.loaded_segments (0x22a30 : word) = Some W_22a30.
Proof. vm_refl. Qed.
Lemma D_22a30 : decode_any W_22a30 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a34 : bv 32 := 0x00813983.
Lemma F_22a34 : fetch_word Plain.M.loaded_segments (0x22a34 : word) = Some W_22a34.
Proof. vm_refl. Qed.
Lemma D_22a34 : decode_any W_22a34 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a38 : bv 32 := 0x03010113.
Lemma F_22a38 : fetch_word Plain.M.loaded_segments (0x22a38 : word) = Some W_22a38.
Proof. vm_refl. Qed.
Lemma D_22a38 : decode_any W_22a38 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a3c : bv 32 := 0x61d0706f.
Lemma F_22a3c : fetch_word Plain.M.loaded_segments (0x22a3c : word) = Some W_22a3c.
Proof. vm_refl. Qed.
Lemma D_22a3c : decode_any W_22a3c = Some (Jal 0 32284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a40 : bv 32 := 0x00008067.
Lemma F_22a40 : fetch_word Plain.M.loaded_segments (0x22a40 : word) = Some W_22a40.
Proof. vm_refl. Qed.
Lemma D_22a40 : decode_any W_22a40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a44 : bv 32 := 0xfd010113.
Lemma F_22a44 : fetch_word Plain.M.loaded_segments (0x22a44 : word) = Some W_22a44.
Proof. vm_refl. Qed.
Lemma D_22a44 : decode_any W_22a44 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a48 : bv 32 := 0x02113423.
Lemma F_22a48 : fetch_word Plain.M.loaded_segments (0x22a48 : word) = Some W_22a48.
Proof. vm_refl. Qed.
Lemma D_22a48 : decode_any W_22a48 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a4c : bv 32 := 0x02813023.
Lemma F_22a4c : fetch_word Plain.M.loaded_segments (0x22a4c : word) = Some W_22a4c.
Proof. vm_refl. Qed.
Lemma D_22a4c : decode_any W_22a4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a50 : bv 32 := 0x00913c23.
Lemma F_22a50 : fetch_word Plain.M.loaded_segments (0x22a50 : word) = Some W_22a50.
Proof. vm_refl. Qed.
Lemma D_22a50 : decode_any W_22a50 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a54 : bv 32 := 0x01213823.
Lemma F_22a54 : fetch_word Plain.M.loaded_segments (0x22a54 : word) = Some W_22a54.
Proof. vm_refl. Qed.
Lemma D_22a54 : decode_any W_22a54 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a58 : bv 32 := 0x01313423.
Lemma F_22a58 : fetch_word Plain.M.loaded_segments (0x22a58 : word) = Some W_22a58.
Proof. vm_refl. Qed.
Lemma D_22a58 : decode_any W_22a58 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a5c : bv 32 := 0x00050493.
Lemma F_22a5c : fetch_word Plain.M.loaded_segments (0x22a5c : word) = Some W_22a5c.
Proof. vm_refl. Qed.
Lemma D_22a5c : decode_any W_22a5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a60 : bv 32 := 0x0003a517.
Lemma F_22a60 : fetch_word Plain.M.loaded_segments (0x22a60 : word) = Some W_22a60.
Proof. vm_refl. Qed.
Lemma D_22a60 : decode_any W_22a60 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a64 : bv 32 := 0x6e050993.
Lemma F_22a64 : fetch_word Plain.M.loaded_segments (0x22a64 : word) = Some W_22a64.
Proof. vm_refl. Qed.
Lemma D_22a64 : decode_any W_22a64 = Some (OpImm ALU_ADD 19 10 1760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a68 : bv 32 := 0x00498413.
Lemma F_22a68 : fetch_word Plain.M.loaded_segments (0x22a68 : word) = Some W_22a68.
Proof. vm_refl. Qed.
Lemma D_22a68 : decode_any W_22a68 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a6c : bv 32 := 0x00040513.
Lemma F_22a6c : fetch_word Plain.M.loaded_segments (0x22a6c : word) = Some W_22a6c.
Proof. vm_refl. Qed.
Lemma D_22a6c : decode_any W_22a6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a70 : bv 32 := 0x361070ef.
Lemma F_22a70 : fetch_word Plain.M.loaded_segments (0x22a70 : word) = Some W_22a70.
Proof. vm_refl. Qed.
Lemma D_22a70 : decode_any W_22a70 = Some (Jal 1 31584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a74 : bv 32 := 0x0009c503.
Lemma F_22a74 : fetch_word Plain.M.loaded_segments (0x22a74 : word) = Some W_22a74.
Proof. vm_refl. Qed.
Lemma D_22a74 : decode_any W_22a74 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a78 : bv 32 := 0xfff00913.
Lemma F_22a78 : fetch_word Plain.M.loaded_segments (0x22a78 : word) = Some W_22a78.
Proof. vm_refl. Qed.
Lemma D_22a78 : decode_any W_22a78 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a7c : bv 32 := 0x06051263.
Lemma F_22a7c : fetch_word Plain.M.loaded_segments (0x22a7c : word) = Some W_22a7c.
Proof. vm_refl. Qed.
Lemma D_22a7c : decode_any W_22a7c = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a80 : bv 32 := 0x0109b503.
Lemma F_22a80 : fetch_word Plain.M.loaded_segments (0x22a80 : word) = Some W_22a80.
Proof. vm_refl. Qed.
Lemma D_22a80 : decode_any W_22a80 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a84 : bv 32 := 0x00051663.
Lemma F_22a84 : fetch_word Plain.M.loaded_segments (0x22a84 : word) = Some W_22a84.
Proof. vm_refl. Qed.
Lemma D_22a84 : decode_any W_22a84 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a88 : bv 32 := 0x01898513.
Lemma F_22a88 : fetch_word Plain.M.loaded_segments (0x22a88 : word) = Some W_22a88.
Proof. vm_refl. Qed.
Lemma D_22a88 : decode_any W_22a88 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a8c : bv 32 := 0x00a9b823.
Lemma F_22a8c : fetch_word Plain.M.loaded_segments (0x22a8c : word) = Some W_22a8c.
Proof. vm_refl. Qed.
Lemma D_22a8c : decode_any W_22a8c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a90 : bv 32 := 0x0089a583.
Lemma F_22a90 : fetch_word Plain.M.loaded_segments (0x22a90 : word) = Some W_22a90.
Proof. vm_refl. Qed.
Lemma D_22a90 : decode_any W_22a90 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a94 : bv 32 := 0x02000613.
Lemma F_22a94 : fetch_word Plain.M.loaded_segments (0x22a94 : word) = Some W_22a94.
Proof. vm_refl. Qed.
Lemma D_22a94 : decode_any W_22a94 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a98 : bv 32 := 0x02c59263.
Lemma F_22a98 : fetch_word Plain.M.loaded_segments (0x22a98 : word) = Some W_22a98.
Proof. vm_refl. Qed.
Lemma D_22a98 : decode_any W_22a98 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a9c : bv 32 := 0x20800513.
Lemma F_22a9c : fetch_word Plain.M.loaded_segments (0x22a9c : word) = Some W_22a9c.
Proof. vm_refl. Qed.
Lemma D_22a9c : decode_any W_22a9c = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22aa0 : bv 32 := 0x00100593.
Lemma F_22aa0 : fetch_word Plain.M.loaded_segments (0x22aa0 : word) = Some W_22aa0.
Proof. vm_refl. Qed.
Lemma D_22aa0 : decode_any W_22aa0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22aa4 : bv 32 := 0x3f4000ef.
Lemma F_22aa4 : fetch_word Plain.M.loaded_segments (0x22aa4 : word) = Some W_22aa4.
Proof. vm_refl. Qed.
Lemma D_22aa4 : decode_any W_22aa4 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22aa8 : bv 32 := 0x02050c63.
Lemma F_22aa8 : fetch_word Plain.M.loaded_segments (0x22aa8 : word) = Some W_22aa8.
Proof. vm_refl. Qed.
Lemma D_22aa8 : decode_any W_22aa8 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22aac : bv 32 := 0x00000593.
Lemma F_22aac : fetch_word Plain.M.loaded_segments (0x22aac : word) = Some W_22aac.
Proof. vm_refl. Qed.
Lemma D_22aac : decode_any W_22aac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ab0 : bv 32 := 0x0109b603.
Lemma F_22ab0 : fetch_word Plain.M.loaded_segments (0x22ab0 : word) = Some W_22ab0.
Proof. vm_refl. Qed.
Lemma D_22ab0 : decode_any W_22ab0 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ab4 : bv 32 := 0x00c53023.
Lemma F_22ab4 : fetch_word Plain.M.loaded_segments (0x22ab4 : word) = Some W_22ab4.
Proof. vm_refl. Qed.
Lemma D_22ab4 : decode_any W_22ab4 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ab8 : bv 32 := 0x00a9b823.
Lemma F_22ab8 : fetch_word Plain.M.loaded_segments (0x22ab8 : word) = Some W_22ab8.
Proof. vm_refl. Qed.
Lemma D_22ab8 : decode_any W_22ab8 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22abc : bv 32 := 0x00000913.
Lemma F_22abc : fetch_word Plain.M.loaded_segments (0x22abc : word) = Some W_22abc.
Proof. vm_refl. Qed.
Lemma D_22abc : decode_any W_22abc = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ac0 : bv 32 := 0x00359613.
Lemma F_22ac0 : fetch_word Plain.M.loaded_segments (0x22ac0 : word) = Some W_22ac0.
Proof. vm_refl. Qed.
Lemma D_22ac0 : decode_any W_22ac0 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ac4 : bv 32 := 0x00c50533.
Lemma F_22ac4 : fetch_word Plain.M.loaded_segments (0x22ac4 : word) = Some W_22ac4.
Proof. vm_refl. Qed.
Lemma D_22ac4 : decode_any W_22ac4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ac8 : bv 32 := 0x00000617.
Lemma F_22ac8 : fetch_word Plain.M.loaded_segments (0x22ac8 : word) = Some W_22ac8.
Proof. vm_refl. Qed.
Lemma D_22ac8 : decode_any W_22ac8 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22acc : bv 32 := 0x00158593.
Lemma F_22acc : fetch_word Plain.M.loaded_segments (0x22acc : word) = Some W_22acc.
Proof. vm_refl. Qed.
Lemma D_22acc : decode_any W_22acc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ad0 : bv 32 := 0x04060613.
Lemma F_22ad0 : fetch_word Plain.M.loaded_segments (0x22ad0 : word) = Some W_22ad0.
Proof. vm_refl. Qed.
Lemma D_22ad0 : decode_any W_22ad0 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ad4 : bv 32 := 0x00c53423.
Lemma F_22ad4 : fetch_word Plain.M.loaded_segments (0x22ad4 : word) = Some W_22ad4.
Proof. vm_refl. Qed.
Lemma D_22ad4 : decode_any W_22ad4 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ad8 : bv 32 := 0x10953423.
Lemma F_22ad8 : fetch_word Plain.M.loaded_segments (0x22ad8 : word) = Some W_22ad8.
Proof. vm_refl. Qed.
Lemma D_22ad8 : decode_any W_22ad8 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22adc : bv 32 := 0x00b9a423.
Lemma F_22adc : fetch_word Plain.M.loaded_segments (0x22adc : word) = Some W_22adc.
Proof. vm_refl. Qed.
Lemma D_22adc : decode_any W_22adc = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ae0 : bv 32 := 0x00040513.
Lemma F_22ae0 : fetch_word Plain.M.loaded_segments (0x22ae0 : word) = Some W_22ae0.
Proof. vm_refl. Qed.
Lemma D_22ae0 : decode_any W_22ae0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ae4 : bv 32 := 0x575070ef.
Lemma F_22ae4 : fetch_word Plain.M.loaded_segments (0x22ae4 : word) = Some W_22ae4.
Proof. vm_refl. Qed.
Lemma D_22ae4 : decode_any W_22ae4 = Some (Jal 1 32116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ae8 : bv 32 := 0x00090513.
Lemma F_22ae8 : fetch_word Plain.M.loaded_segments (0x22ae8 : word) = Some W_22ae8.
Proof. vm_refl. Qed.
Lemma D_22ae8 : decode_any W_22ae8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22aec : bv 32 := 0x02813083.
Lemma F_22aec : fetch_word Plain.M.loaded_segments (0x22aec : word) = Some W_22aec.
Proof. vm_refl. Qed.
Lemma D_22aec : decode_any W_22aec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22af0 : bv 32 := 0x02013403.
Lemma F_22af0 : fetch_word Plain.M.loaded_segments (0x22af0 : word) = Some W_22af0.
Proof. vm_refl. Qed.
Lemma D_22af0 : decode_any W_22af0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22af4 : bv 32 := 0x01813483.
Lemma F_22af4 : fetch_word Plain.M.loaded_segments (0x22af4 : word) = Some W_22af4.
Proof. vm_refl. Qed.
Lemma D_22af4 : decode_any W_22af4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22af8 : bv 32 := 0x01013903.
Lemma F_22af8 : fetch_word Plain.M.loaded_segments (0x22af8 : word) = Some W_22af8.
Proof. vm_refl. Qed.
Lemma D_22af8 : decode_any W_22af8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22afc : bv 32 := 0x00813983.
Lemma F_22afc : fetch_word Plain.M.loaded_segments (0x22afc : word) = Some W_22afc.
Proof. vm_refl. Qed.
Lemma D_22afc : decode_any W_22afc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b00 : bv 32 := 0x03010113.
Lemma F_22b00 : fetch_word Plain.M.loaded_segments (0x22b00 : word) = Some W_22b00.
Proof. vm_refl. Qed.
Lemma D_22b00 : decode_any W_22b00 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b04 : bv 32 := 0x00008067.
Lemma F_22b04 : fetch_word Plain.M.loaded_segments (0x22b04 : word) = Some W_22b04.
Proof. vm_refl. Qed.
Lemma D_22b04 : decode_any W_22b04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b08 : bv 32 := 0x00050067.
Lemma F_22b08 : fetch_word Plain.M.loaded_segments (0x22b08 : word) = Some W_22b08.
Proof. vm_refl. Qed.
Lemma D_22b08 : decode_any W_22b08 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b0c : bv 32 := 0x00008067.
Lemma F_22b0c : fetch_word Plain.M.loaded_segments (0x22b0c : word) = Some W_22b0c.
Proof. vm_refl. Qed.
Lemma D_22b0c : decode_any W_22b0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b10 : bv 32 := 0xfe010113.
Lemma F_22b10 : fetch_word Plain.M.loaded_segments (0x22b10 : word) = Some W_22b10.
Proof. vm_refl. Qed.
Lemma D_22b10 : decode_any W_22b10 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b14 : bv 32 := 0x00113c23.
Lemma F_22b14 : fetch_word Plain.M.loaded_segments (0x22b14 : word) = Some W_22b14.
Proof. vm_refl. Qed.
Lemma D_22b14 : decode_any W_22b14 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b18 : bv 32 := 0x00813823.
Lemma F_22b18 : fetch_word Plain.M.loaded_segments (0x22b18 : word) = Some W_22b18.
Proof. vm_refl. Qed.
Lemma D_22b18 : decode_any W_22b18 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b1c : bv 32 := 0x00913423.
Lemma F_22b1c : fetch_word Plain.M.loaded_segments (0x22b1c : word) = Some W_22b1c.
Proof. vm_refl. Qed.
Lemma D_22b1c : decode_any W_22b1c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b20 : bv 32 := 0x00009517.
Lemma F_22b20 : fetch_word Plain.M.loaded_segments (0x22b20 : word) = Some W_22b20.
Proof. vm_refl. Qed.
Lemma D_22b20 : decode_any W_22b20 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b24 : bv 32 := 0x00009597.
Lemma F_22b24 : fetch_word Plain.M.loaded_segments (0x22b24 : word) = Some W_22b24.
Proof. vm_refl. Qed.
Lemma D_22b24 : decode_any W_22b24 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b28 : bv 32 := 0xf3053503.
Lemma F_22b28 : fetch_word Plain.M.loaded_segments (0x22b28 : word) = Some W_22b28.
Proof. vm_refl. Qed.
Lemma D_22b28 : decode_any W_22b28 = Some (Load SZ8 true 10 10 3888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b2c : bv 32 := 0xf345b403.
Lemma F_22b2c : fetch_word Plain.M.loaded_segments (0x22b2c : word) = Some W_22b2c.
Proof. vm_refl. Qed.
Lemma D_22b2c : decode_any W_22b2c = Some (Load SZ8 true 8 11 3892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b30 : bv 32 := 0x00a47c63.
Lemma F_22b30 : fetch_word Plain.M.loaded_segments (0x22b30 : word) = Some W_22b30.
Proof. vm_refl. Qed.
Lemma D_22b30 : decode_any W_22b30 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b34 : bv 32 := 0xff853583.
Lemma F_22b34 : fetch_word Plain.M.loaded_segments (0x22b34 : word) = Some W_22b34.
Proof. vm_refl. Qed.
Lemma D_22b34 : decode_any W_22b34 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b38 : bv 32 := 0xff850493.
Lemma F_22b38 : fetch_word Plain.M.loaded_segments (0x22b38 : word) = Some W_22b38.
Proof. vm_refl. Qed.
Lemma D_22b38 : decode_any W_22b38 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b3c : bv 32 := 0x000580e7.
Lemma F_22b3c : fetch_word Plain.M.loaded_segments (0x22b3c : word) = Some W_22b3c.
Proof. vm_refl. Qed.
Lemma D_22b3c : decode_any W_22b3c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b40 : bv 32 := 0x00048513.
Lemma F_22b40 : fetch_word Plain.M.loaded_segments (0x22b40 : word) = Some W_22b40.
Proof. vm_refl. Qed.
Lemma D_22b40 : decode_any W_22b40 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b44 : bv 32 := 0xfe9468e3.
Lemma F_22b44 : fetch_word Plain.M.loaded_segments (0x22b44 : word) = Some W_22b44.
Proof. vm_refl. Qed.
Lemma D_22b44 : decode_any W_22b44 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b48 : bv 32 := 0x01813083.
Lemma F_22b48 : fetch_word Plain.M.loaded_segments (0x22b48 : word) = Some W_22b48.
Proof. vm_refl. Qed.
Lemma D_22b48 : decode_any W_22b48 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b4c : bv 32 := 0x01013403.
Lemma F_22b4c : fetch_word Plain.M.loaded_segments (0x22b4c : word) = Some W_22b4c.
Proof. vm_refl. Qed.
Lemma D_22b4c : decode_any W_22b4c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b50 : bv 32 := 0x00813483.
Lemma F_22b50 : fetch_word Plain.M.loaded_segments (0x22b50 : word) = Some W_22b50.
Proof. vm_refl. Qed.
Lemma D_22b50 : decode_any W_22b50 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b54 : bv 32 := 0x02010113.
Lemma F_22b54 : fetch_word Plain.M.loaded_segments (0x22b54 : word) = Some W_22b54.
Proof. vm_refl. Qed.
Lemma D_22b54 : decode_any W_22b54 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b58 : bv 32 := 0xfb5ff06f.
Lemma F_22b58 : fetch_word Plain.M.loaded_segments (0x22b58 : word) = Some W_22b58.
Proof. vm_refl. Qed.
Lemma D_22b58 : decode_any W_22b58 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b5c : bv 32 := 0xff010113.
Lemma F_22b5c : fetch_word Plain.M.loaded_segments (0x22b5c : word) = Some W_22b5c.
Proof. vm_refl. Qed.
Lemma D_22b5c : decode_any W_22b5c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b60 : bv 32 := 0x00113423.
Lemma F_22b60 : fetch_word Plain.M.loaded_segments (0x22b60 : word) = Some W_22b60.
Proof. vm_refl. Qed.
Lemma D_22b60 : decode_any W_22b60 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b64 : bv 32 := 0x00813023.
Lemma F_22b64 : fetch_word Plain.M.loaded_segments (0x22b64 : word) = Some W_22b64.
Proof. vm_refl. Qed.
Lemma D_22b64 : decode_any W_22b64 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b68 : bv 32 := 0x00000593.
Lemma F_22b68 : fetch_word Plain.M.loaded_segments (0x22b68 : word) = Some W_22b68.
Proof. vm_refl. Qed.
Lemma D_22b68 : decode_any W_22b68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b6c : bv 32 := 0x00020613.
Lemma F_22b6c : fetch_word Plain.M.loaded_segments (0x22b6c : word) = Some W_22b6c.
Proof. vm_refl. Qed.
Lemma D_22b6c : decode_any W_22b6c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b70 : bv 32 := 0xf5862603.
Lemma F_22b70 : fetch_word Plain.M.loaded_segments (0x22b70 : word) = Some W_22b70.
Proof. vm_refl. Qed.
Lemma D_22b70 : decode_any W_22b70 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b74 : bv 32 := 0x0003a697.
Lemma F_22b74 : fetch_word Plain.M.loaded_segments (0x22b74 : word) = Some W_22b74.
Proof. vm_refl. Qed.
Lemma D_22b74 : decode_any W_22b74 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b78 : bv 32 := 0x7ec68693.
Lemma F_22b78 : fetch_word Plain.M.loaded_segments (0x22b78 : word) = Some W_22b78.
Proof. vm_refl. Qed.
Lemma D_22b78 : decode_any W_22b78 = Some (OpImm ALU_ADD 13 13 2028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b7c : bv 32 := 0x1606a72f.
Lemma F_22b7c : fetch_word Plain.M.loaded_segments (0x22b7c : word) = Some W_22b7c.
Proof. vm_refl. Qed.
Lemma D_22b7c : decode_any W_22b7c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b80 : bv 32 := 0x00b71663.
Lemma F_22b80 : fetch_word Plain.M.loaded_segments (0x22b80 : word) = Some W_22b80.
Proof. vm_refl. Qed.
Lemma D_22b80 : decode_any W_22b80 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b84 : bv 32 := 0x1ec6a7af.
Lemma F_22b84 : fetch_word Plain.M.loaded_segments (0x22b84 : word) = Some W_22b84.
Proof. vm_refl. Qed.
Lemma D_22b84 : decode_any W_22b84 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b88 : bv 32 := 0xfe079ae3.
Lemma F_22b88 : fetch_word Plain.M.loaded_segments (0x22b88 : word) = Some W_22b88.
Proof. vm_refl. Qed.
Lemma D_22b88 : decode_any W_22b88 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b8c : bv 32 := 0x0007059b.
Lemma F_22b8c : fetch_word Plain.M.loaded_segments (0x22b8c : word) = Some W_22b8c.
Proof. vm_refl. Qed.
Lemma D_22b8c : decode_any W_22b8c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b90 : bv 32 := 0x02c58263.
Lemma F_22b90 : fetch_word Plain.M.loaded_segments (0x22b90 : word) = Some W_22b90.
Proof. vm_refl. Qed.
Lemma D_22b90 : decode_any W_22b90 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b94 : bv 32 := 0x02058263.
Lemma F_22b94 : fetch_word Plain.M.loaded_segments (0x22b94 : word) = Some W_22b94.
Proof. vm_refl. Qed.
Lemma D_22b94 : decode_any W_22b94 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b98 : bv 32 := 0x04900893.
Lemma F_22b98 : fetch_word Plain.M.loaded_segments (0x22b98 : word) = Some W_22b98.
Proof. vm_refl. Qed.
Lemma D_22b98 : decode_any W_22b98 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22b9c : bv 32 := 0x00000593.
Lemma F_22b9c : fetch_word Plain.M.loaded_segments (0x22b9c : word) = Some W_22b9c.
Proof. vm_refl. Qed.
Lemma D_22b9c : decode_any W_22b9c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ba0 : bv 32 := 0x00000613.
Lemma F_22ba0 : fetch_word Plain.M.loaded_segments (0x22ba0 : word) = Some W_22ba0.
Proof. vm_refl. Qed.
Lemma D_22ba0 : decode_any W_22ba0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ba4 : bv 32 := 0x00000693.
Lemma F_22ba4 : fetch_word Plain.M.loaded_segments (0x22ba4 : word) = Some W_22ba4.
Proof. vm_refl. Qed.
Lemma D_22ba4 : decode_any W_22ba4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22ba8 : bv 32 := 0x00000513.
Lemma F_22ba8 : fetch_word Plain.M.loaded_segments (0x22ba8 : word) = Some W_22ba8.
Proof. vm_refl. Qed.
Lemma D_22ba8 : decode_any W_22ba8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bac : bv 32 := 0x00000073.
Lemma F_22bac : fetch_word Plain.M.loaded_segments (0x22bac : word) = Some W_22bac.
Proof. vm_refl. Qed.
Lemma E_22bac : is_ecall W_22bac = true.
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bb0 : bv 32 := 0xff9ff06f.
Lemma F_22bb0 : fetch_word Plain.M.loaded_segments (0x22bb0 : word) = Some W_22bb0.
Proof. vm_refl. Qed.
Lemma D_22bb0 : decode_any W_22bb0 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bb4 : bv 32 := 0x00000023.
Lemma F_22bb4 : fetch_word Plain.M.loaded_segments (0x22bb4 : word) = Some W_22bb4.
Proof. vm_refl. Qed.
Lemma D_22bb4 : decode_any W_22bb4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bb8 : bv 32 := 0x00050413.
Lemma F_22bb8 : fetch_word Plain.M.loaded_segments (0x22bb8 : word) = Some W_22bb8.
Proof. vm_refl. Qed.
Lemma D_22bb8 : decode_any W_22bb8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bbc : bv 32 := 0xdbdff0ef.
Lemma F_22bbc : fetch_word Plain.M.loaded_segments (0x22bbc : word) = Some W_22bbc.
Proof. vm_refl. Qed.
Lemma D_22bbc : decode_any W_22bbc = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bc0 : bv 32 := 0xf51ff0ef.
Lemma F_22bc0 : fetch_word Plain.M.loaded_segments (0x22bc0 : word) = Some W_22bc0.
Proof. vm_refl. Qed.
Lemma D_22bc0 : decode_any W_22bc0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bc4 : bv 32 := 0x160020ef.
Lemma F_22bc4 : fetch_word Plain.M.loaded_segments (0x22bc4 : word) = Some W_22bc4.
Proof. vm_refl. Qed.
Lemma D_22bc4 : decode_any W_22bc4 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bc8 : bv 32 := 0x00040513.
Lemma F_22bc8 : fetch_word Plain.M.loaded_segments (0x22bc8 : word) = Some W_22bc8.
Proof. vm_refl. Qed.
Lemma D_22bc8 : decode_any W_22bc8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22bcc : bv 32 := 0xd91ff0ef.
Lemma F_22bcc : fetch_word Plain.M.loaded_segments (0x22bcc : word) = Some W_22bcc.
Proof. vm_refl. Qed.
Lemma D_22bcc : decode_any W_22bcc = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a5d0 : bv 32 := 0x00033597.
Lemma F_2a5d0 : fetch_word Plain.M.loaded_segments (0x2a5d0 : word) = Some W_2a5d0.
Proof. vm_refl. Qed.
Lemma D_2a5d0 : decode_any W_2a5d0 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a5d4 : bv 32 := 0xdbb58683.
Lemma F_2a5d4 : fetch_word Plain.M.loaded_segments (0x2a5d4 : word) = Some W_2a5d4.
Proof. vm_refl. Qed.
Lemma D_2a5d4 : decode_any W_2a5d4 = Some (Load SZ1 true 13 11 3515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a5d8 : bv 32 := 0x1e068863.
Lemma F_2a5d8 : fetch_word Plain.M.loaded_segments (0x2a5d8 : word) = Some W_2a5d8.
Proof. vm_refl. Qed.
Lemma D_2a5d8 : decode_any W_2a5d8 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a7c8 : bv 32 := 0x00008067.
Lemma F_2a7c8 : fetch_word Plain.M.loaded_segments (0x2a7c8 : word) = Some W_2a7c8.
Proof. vm_refl. Qed.
Lemma D_2a7c8 : decode_any W_2a7c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a858 : bv 32 := 0x00052583.
Lemma F_2a858 : fetch_word Plain.M.loaded_segments (0x2a858 : word) = Some W_2a858.
Proof. vm_refl. Qed.
Lemma D_2a858 : decode_any W_2a858 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a85c : bv 32 := 0x0005c463.
Lemma F_2a85c : fetch_word Plain.M.loaded_segments (0x2a85c : word) = Some W_2a85c.
Proof. vm_refl. Qed.
Lemma D_2a85c : decode_any W_2a85c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2a860 : bv 32 := 0x00008067.
Lemma F_2a860 : fetch_word Plain.M.loaded_segments (0x2a860 : word) = Some W_2a860.
Proof. vm_refl. Qed.
Lemma D_2a860 : decode_any W_2a860 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

